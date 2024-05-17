open Proofview.Notations

let () = Mirage_crypto_rng_unix.initialize (module Mirage_crypto_rng.Fortuna)

let client (type a) (url : string) (f : send:(string -> unit) -> receive:(unit -> string option) -> a) : a =
  let open Lwt.Infix in
  let uri =
    match url with
    | _ when url |> String.starts_with ~prefix:"ws://" -> Uri.of_string ("http://" ^ (String.sub url 5 ((String.length url) - 5)))
    | _ when url |> String.starts_with ~prefix:"wss://" -> Uri.of_string ("https://" ^ (String.sub url 6 ((String.length url) - 6)))
    | _ -> CErrors.user_err Pp.(str "Invalid URL: " ++ str url) in
  let conn =
    Lwt_main.run (
      Resolver_lwt.resolve_uri ~uri Resolver_lwt_unix.system >>= fun endp ->
      let ctx = Lazy.force Conduit_lwt_unix.default_ctx in
      Conduit_lwt_unix.endp_to_client ~ctx endp >>= fun client ->
      Websocket_lwt_unix.connect ~ctx client uri
    ) in
  let closed = ref false in
  let r =
    f
      ~send:(fun t ->
        Lwt_main.run (Websocket_lwt_unix.write conn (Websocket.Frame.create ~content:t ()))
      )
      ~receive:(fun () ->
        let result = ref None in
        while not !closed && !result = None do
          match Lwt_main.run (Websocket_lwt_unix.read conn) with
          | {opcode = Ping; _} ->
            Lwt_main.run (Websocket_lwt_unix.write conn (Websocket.Frame.create ~opcode:Pong ()))
          | {opcode = Close; _} ->
            Lwt_main.run (Websocket_lwt_unix.write conn (Websocket.Frame.close 1000))
          | {opcode = Pong; _} ->
            ()
          | {opcode = Text; content; _} ->
            result := Some content
          | _ ->
            closed := true
        done;
        !result
      ) in
  (* Lwt_main.run (Websocket_lwt_unix.close_transport conn); *)
  r

type internal_id = int
  [@@deriving yojson { variants = `Internal "type"; exn = true }]

let internal_id_ctr : internal_id ref = ref 0

let new_internal_id () : internal_id = incr internal_id_ctr; !internal_id_ctr

module InternalIdMap = Map.Make(Int)

let internal_map: Obj.t InternalIdMap.t ref = ref InternalIdMap.empty

module Internal = struct
  type 'a t = {v: 'a}

  type repr = {internal_id : internal_id}
    [@@deriving yojson { variants = `Internal "type"; exn = true }]

  let make (type a) (v : a) : a t = {v}

  let to_yojson (type a) (v : a t) : Yojson.Safe.t =
    let internal_id = new_internal_id () in
    internal_map := !internal_map |> InternalIdMap.add internal_id (Obj.magic v);
    [%to_yojson: repr] {internal_id = internal_id}

  let of_yojson_exn (type a) (j : Yojson.Safe.t) : a t =
    let repr = [%of_yojson: repr] j |> Result.get_ok in
    !internal_map |> InternalIdMap.find repr.internal_id |> Obj.magic
end

type external_id = int
  [@@deriving yojson { variants = `Internal "type"; exn = true }]

module External = struct
  [@warning "-27"]
  type 'a t = {external_id : external_id}
    [@@deriving yojson { variants = `Internal "type"; exn = true }]

  let to_yojson v = to_yojson (fun _ -> assert false) v
  let of_yojson j = of_yojson (fun _ -> assert false) j
  let of_yojson_exn j = of_yojson_exn (fun _ -> assert false) j
end

type (_, _) local_request_aux =
  | LocalRequestUnit :
    (unit Internal.t, unit) local_request_aux
  | LocalRequestTacticReturn :
    {
      value : 'a Internal.t;
    } -> ('a Proofview.tactic Internal.t, 'a) local_request_aux
  | LocalRequestTacticBind :
    {
      tac : 'a Proofview.tactic Internal.t;
      f : ('a Internal.t -> 'b Proofview.tactic Internal.t) External.t;
    } -> ('b Proofview.tactic Internal.t, unit) local_request_aux
  | LocalRequestTacticMessage :
    {
      msg : string;
    } -> (unit Proofview.tactic Internal.t, unit) local_request_aux

type _ local_request = LocalRequest : ('r, 'a) local_request_aux -> 'r local_request

type any_local_request = AnyLocalRequest : 'r local_request -> any_local_request

let any_local_request_of_yojson_exn (local_request_j : Yojson.Safe.t) : any_local_request =
  match local_request_j with
  | `Assoc ["type", `String "LocalRequestUnit"] ->
    AnyLocalRequest (LocalRequest LocalRequestUnit)
  | `Assoc ["type", `String "LocalRequestTacticReturn"; "value", value_j] ->
    let value = Internal.of_yojson_exn value_j in
    AnyLocalRequest (LocalRequest (LocalRequestTacticReturn {value}))
  | `Assoc ["type", `String "LocalRequestTacticBind"; "tac", tac_j; "f", f_j] ->
    let tac = Internal.of_yojson_exn tac_j in
    let f = External.of_yojson_exn f_j in
    AnyLocalRequest (LocalRequest (LocalRequestTacticBind {tac; f}))
  | `Assoc ["type", `String "LocalRequestTacticMessage"; "msg", msg_j] ->
    let msg = [%of_yojson: string] msg_j |> Result.get_ok in
    AnyLocalRequest (LocalRequest (LocalRequestTacticMessage {msg}))
  | _ -> failwith "unknown local request"

let local_request_result_to_yojson (type r) (local_request : r local_request) (result : r) : Yojson.Safe.t =
  match local_request with
  | LocalRequest LocalRequestUnit ->
    Internal.to_yojson result
  | LocalRequest (LocalRequestTacticReturn _) ->
    Internal.to_yojson result
  | LocalRequest (LocalRequestTacticBind _) ->
    Internal.to_yojson result
  | LocalRequest (LocalRequestTacticMessage _) ->
    Internal.to_yojson result

type _ remote_request =
  | RemoteRequestApplyFunction :
    {
      f : ('a Internal.t -> 'b Internal.t) External.t;
      x : 'a Internal.t;
    } -> 'b Internal.t remote_request
  | RemoteRequestGetTactic :
    unit Proofview.tactic Internal.t remote_request

let remote_request_to_yojson (type r) (remote_request : r remote_request) : Yojson.Safe.t =
  match remote_request with
  | RemoteRequestApplyFunction {f; x} ->
    let f_j = External.to_yojson f in
    let x_j = Internal.to_yojson x in
    `Assoc ["type", `String "RemoteRequestApplyFunction"; "f", f_j; "x", x_j]
  | RemoteRequestGetTactic ->
    `Assoc ["type", `String "RemoteRequestGetTactic"]

let remote_request_result_of_yojson_exn (type r) (remote_request : r remote_request) (result_j : Yojson.Safe.t) : r =
  match remote_request with
  | RemoteRequestApplyFunction _ ->
    Internal.of_yojson_exn result_j
  | RemoteRequestGetTactic ->
    Internal.of_yojson_exn result_j

exception RemoteException of string

let _ =
  let pr = function
  | RemoteException s -> Some ("RemoteException:\n" ^ s)
  | _ -> None
  in
  Printexc.register_printer pr

let interact (url : string) : unit Proofview.tactic =
  client url (fun ~send ~receive ->
    let handle_local = ref (fun _ -> assert false) in
    let handle_remote_request (type r) (remote_request : r remote_request) : r =
      send ("-> " ^ Yojson.Safe.to_string (remote_request_to_yojson remote_request));
      let rec aux () =
        match receive () with
        | None -> CErrors.user_err (Pp.str "Connection was closed unexpectedly")
        | Some s ->
          match s with
          | _ when s |> String.starts_with ~prefix:"-> " ->
            let t = String.sub s 3 ((String.length s) - 3) in
            !handle_local t;
            aux ()
          | _ when s |> String.starts_with ~prefix:"<- " ->
            let t = String.sub s 3 ((String.length s) - 3) in
            remote_request_result_of_yojson_exn remote_request (Yojson.Safe.from_string t)
          | _ when s |> String.starts_with ~prefix:"!! " ->
            let t = String.sub s 3 ((String.length s) - 3) in
            (match Yojson.Safe.from_string t with
            | `String e -> raise (RemoteException e)
            | _ -> CErrors.user_err Pp.(str "Invalid exception contents: " ++ str s)
            )
          | _ -> CErrors.user_err Pp.(str "Invalid message: " ++ str s) in
      aux () in
    let handle_local_request (type r) (local_request : r local_request) : r =
      match local_request with
      | LocalRequest LocalRequestUnit ->
        Internal.make ()
      | LocalRequest (LocalRequestTacticReturn {value}) ->
        Internal.make (Proofview.tclUNIT value.v)
      | LocalRequest (LocalRequestTacticBind {tac; f}) ->
        Internal.make (
          tac.v >>= fun x ->
          Proofview.wrap_exceptions (fun () ->
            (handle_remote_request (RemoteRequestApplyFunction {f; x = Internal.make x})).v
          )
        )
      | LocalRequest (LocalRequestTacticMessage {msg}) ->
        Internal.make (Proofview.tclLIFT (Proofview.NonLogical.print_info (Pp.str msg))) in
    handle_local := (fun t ->
      let any_local_request = any_local_request_of_yojson_exn (Yojson.Safe.from_string t) in
      match any_local_request with
      | AnyLocalRequest local_request ->
        try
          let result = handle_local_request local_request in
          send ("<- " ^ Yojson.Safe.to_string (local_request_result_to_yojson local_request result))
        with exn when CErrors.noncritical exn ->
          send ("!! " ^ Yojson.Safe.to_string (`String (CErrors.print exn |> Pp.string_of_ppcmds)))
    );
    (handle_remote_request RemoteRequestGetTactic).v
  )
