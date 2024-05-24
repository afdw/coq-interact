open Proofview.Notations

let simple_string_of_ppcmds (c : Pp.t) : string =
  let open Pp in
  let buffer = Buffer.create 512 in
  let rec aux f = function
    | Ppcmd_empty -> ()
    | Ppcmd_string s -> Printf.bprintf buffer "%s" s
    | Ppcmd_glue cs -> List.iter (aux f) (List.map Pp.repr cs)
    | Ppcmd_box (btype, c) ->
      aux (
        match btype with
        | Pp_hbox -> false
        | Pp_vbox _ -> true
        | Pp_hvbox _ -> false
        | Pp_hovbox _ -> false
      ) (Pp.repr c)
    | Ppcmd_tag (_, c) -> (aux f) (Pp.repr c)
    | Ppcmd_print_break (n, _) -> Printf.bprintf buffer "%s" (if f then "\n" else String.make n ' ')
    | Ppcmd_force_newline -> Printf.bprintf buffer "\n"
    | Ppcmd_comment ss -> List.iter (Printf.bprintf buffer "%s") ss in
  aux false (Pp.repr c);
  buffer |> Buffer.to_bytes |> String.of_bytes

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

  let to_yojson (type a) _ (v : a t) : Yojson.Safe.t =
    let internal_id = new_internal_id () in
    internal_map := !internal_map |> InternalIdMap.add internal_id (Obj.magic v);
    [%to_yojson: repr] {internal_id = internal_id}

  let of_yojson (type a) _ (j : Yojson.Safe.t) : (a t, string) result =
    [%of_yojson: repr] j |> Result.map @@ fun repr ->
    !internal_map |> InternalIdMap.find repr.internal_id |> Obj.magic

  let of_yojson_exn (type a) f (j : Yojson.Safe.t) : a t =
    of_yojson f j |> Result.get_ok
end

type external_id = int
  [@@deriving yojson { variants = `Internal "type"; exn = true }]

module External = struct
  [@warning "-27"]
  type 'a t = {external_id : external_id}
    [@@deriving yojson { variants = `Internal "type"; exn = true }]
end

module ConstrRepr = struct
  type t = EConstr.t Internal.t

  let to_yojson v = Internal.to_yojson (fun _ -> assert false) v
  let of_yojson j = Internal.of_yojson (fun _ -> assert false) j
  let of_yojson_exn j = Internal.of_yojson_exn (fun _ -> assert false) j
end

module HypRepr = struct
  type kind =
    | Assumption
    | Definition of {value : ConstrRepr.t}
    [@@deriving yojson { variants = `Internal "type"; exn = true }]

  type t = {
    name : string;
    type_ : ConstrRepr.t;
    kind : kind;
  } [@@deriving yojson { variants = `Internal "type"; exn = true }]
end

module GoalRepr = struct
  type t = {
    hyps : HypRepr.t list;
    concl : ConstrRepr.t;
  } [@@deriving yojson { variants = `Internal "type"; exn = true }]
end

module TacticRepr = struct
  type 'a t = 'a Proofview.tactic Internal.t

  let to_yojson f v = Internal.to_yojson f v
  let of_yojson f j = Internal.of_yojson f j
  let of_yojson_exn f j = Internal.of_yojson_exn f j
end

type _ type_desc =
  | TypeDescUnit : unit type_desc
  | TypeDescList : {element_type_desc : 'a type_desc} -> 'a list type_desc
  | TypeDescInternal : 'a Internal.t type_desc
  | TypeDescHyp : HypRepr.t type_desc
  | TypeDescGoal : GoalRepr.t type_desc

type any_type_desc = AnyTypeDesc : 'a type_desc -> any_type_desc

let rec type_desc_to_yojson : type a. a type_desc -> Yojson.Safe.t = fun type_desc ->
  match type_desc with
  | TypeDescUnit ->
    `Assoc ["type", `String "TypeDescUnit"]
  | TypeDescList {element_type_desc} ->
    let element_type_desc_j = type_desc_to_yojson element_type_desc in
    `Assoc ["type", `String "TypeDescList"; "element_type_desc", element_type_desc_j]
  | TypeDescInternal ->
    `Assoc ["type", `String "TypeDescInternal"]
  | TypeDescHyp ->
    `Assoc ["type", `String "TypeDescHyp"]
  | TypeDescGoal ->
    `Assoc ["type", `String "TypeDescGoal"]
let rec any_type_desc_of_yojson_exn (type_desc_j : Yojson.Safe.t) : any_type_desc =
  match type_desc_j with
  | `Assoc ["type", `String "TypeDescUnit"] ->
    AnyTypeDesc TypeDescUnit
  | `Assoc ["type", `String "TypeDescList"; "element_type_desc", element_type_desc_j] ->
    let element_type_desc_any = any_type_desc_of_yojson_exn element_type_desc_j in
    (match element_type_desc_any with
    | AnyTypeDesc element_type_desc ->
      AnyTypeDesc (TypeDescList {element_type_desc}))
  | `Assoc ["type", `String "TypeDescInternal"] ->
    AnyTypeDesc TypeDescInternal
  | `Assoc ["type", `String "TypeDescHyp"] ->
    AnyTypeDesc TypeDescHyp
  | `Assoc ["type", `String "TypeDescGoal"] ->
    AnyTypeDesc TypeDescGoal
  | _ -> failwith "unknown type desc"

let rec any_to_yojson : type a. a type_desc -> a -> Yojson.Safe.t = fun type_desc any ->
  match type_desc with
  | TypeDescUnit ->
    [%to_yojson: unit] any
  | TypeDescList {element_type_desc} ->
    [%to_yojson: 'a list] (any_to_yojson element_type_desc) any
  | TypeDescInternal ->
    Internal.to_yojson (fun _ -> assert false) any
  | TypeDescHyp ->
    HypRepr.to_yojson any
  | TypeDescGoal ->
    GoalRepr.to_yojson any
let rec any_of_yojson : type a. a type_desc -> Yojson.Safe.t -> (a, string) result = fun type_desc any_j ->
  match type_desc with
  | TypeDescUnit ->
    [%of_yojson: unit] any_j
  | TypeDescList {element_type_desc} ->
    [%of_yojson: 'a list] (any_of_yojson element_type_desc) any_j
  | TypeDescInternal ->
    Internal.of_yojson (fun _ -> assert false) any_j
  | TypeDescHyp ->
    HypRepr.of_yojson any_j
  | TypeDescGoal ->
    GoalRepr.of_yojson any_j
let any_of_yojson_exn (type a) (type_desc : a type_desc) (any_j : Yojson.Safe.t) =
  any_of_yojson type_desc any_j |> Result.get_ok

type (_, _) local_request_aux =
  | LocalRequestConstrPrint :
    {
      constr : ConstrRepr.t;
    } -> (string, unit) local_request_aux
  | LocalRequestTacticReturn :
    {
      type_desc : 'a type_desc;
      value : 'a;
    } -> ('a TacticRepr.t, 'a) local_request_aux
  | LocalRequestTacticBind :
    {
      type_desc : 'a type_desc;
      tac : 'a TacticRepr.t;
      f : ('a -> 'b TacticRepr.t) External.t;
    } -> ('b TacticRepr.t, unit) local_request_aux
  | LocalRequestTacticThen :
    {
      tac_1 : unit TacticRepr.t;
      tac_2 : 'a TacticRepr.t;
    } -> ('a TacticRepr.t, unit) local_request_aux
  | LocalRequestTacticOr :
    {
      tac_1 : 'a TacticRepr.t;
      tac_2 : 'a TacticRepr.t;
    } -> ('a TacticRepr.t, unit) local_request_aux
  | LocalRequestTacticComplete :
    {
      tac : 'a TacticRepr.t;
    } -> ('a TacticRepr.t, unit) local_request_aux
  | LocalRequestTacticGoals :
    (GoalRepr.t list TacticRepr.t, unit) local_request_aux
  | LocalRequestTacticDispatch :
    {
      tacs : 'a TacticRepr.t list;
    } -> ('a list TacticRepr.t, 'a) local_request_aux
  | LocalRequestTacticMessage :
    {
      msg : string;
    } -> (unit TacticRepr.t, unit) local_request_aux
  | LocalRequestTacticLtac :
    {
      tactic : string;
    } -> (unit TacticRepr.t, unit) local_request_aux

type _ local_request = LocalRequest : ('r, 'a) local_request_aux -> 'r local_request

type any_local_request = AnyLocalRequest : 'r local_request -> any_local_request

let any_local_request_of_yojson_exn (local_request_j : Yojson.Safe.t) : any_local_request =
  match local_request_j with
  | `Assoc ["type", `String "LocalRequestConstrPrint"; "constr", constr_j] ->
    let constr = Internal.of_yojson_exn (fun _ -> assert false) constr_j in
    AnyLocalRequest (LocalRequest (LocalRequestConstrPrint {constr}))
  | `Assoc ["type", `String "LocalRequestTacticReturn"; "type_desc", type_desc_j; "value", value_j] ->
    let any_type_desc = any_type_desc_of_yojson_exn type_desc_j in
    (match any_type_desc with
    | AnyTypeDesc type_desc ->
      let value = any_of_yojson_exn type_desc value_j in
      AnyLocalRequest (LocalRequest (LocalRequestTacticReturn {type_desc; value})))
  | `Assoc ["type", `String "LocalRequestTacticBind"; "type_desc", type_desc_j; "tac", tac_j; "f", f_j] ->
    let any_type_desc = any_type_desc_of_yojson_exn type_desc_j in
    (match any_type_desc with
    | AnyTypeDesc type_desc ->
      let tac = Internal.of_yojson_exn (fun _ -> assert false) tac_j in
      let f = External.of_yojson_exn (fun _ -> assert false) f_j in
      AnyLocalRequest (LocalRequest (LocalRequestTacticBind {type_desc; tac; f})))
  | `Assoc ["type", `String "LocalRequestTacticThen"; "tac_1", tac_1_j; "tac_2", tac_2_j] ->
    let tac_1 = Internal.of_yojson_exn (fun _ -> assert false) tac_1_j in
    let tac_2 = Internal.of_yojson_exn (fun _ -> assert false) tac_2_j in
    AnyLocalRequest (LocalRequest (LocalRequestTacticThen {tac_1; tac_2}))
  | `Assoc ["type", `String "LocalRequestTacticOr"; "tac_1", tac_1_j; "tac_2", tac_2_j] ->
    let tac_1 = Internal.of_yojson_exn (fun _ -> assert false) tac_1_j in
    let tac_2 = Internal.of_yojson_exn (fun _ -> assert false) tac_2_j in
    AnyLocalRequest (LocalRequest (LocalRequestTacticOr {tac_1; tac_2}))
  | `Assoc ["type", `String "LocalRequestTacticComplete"; "tac", tac_j] ->
    let tac = Internal.of_yojson_exn (fun _ -> assert false) tac_j in
    AnyLocalRequest (LocalRequest (LocalRequestTacticComplete {tac}))
  | `Assoc ["type", `String "LocalRequestTacticGoals"] ->
    AnyLocalRequest (LocalRequest LocalRequestTacticGoals)
  | `Assoc ["type", `String "LocalRequestTacticDispatch"; "tacs", tacs_j] ->
    let tacs = [%of_yojson: 'a TacticRepr.t list] (fun _ -> assert false) tacs_j |> Result.get_ok in
    AnyLocalRequest (LocalRequest (LocalRequestTacticDispatch {tacs}))
  | `Assoc ["type", `String "LocalRequestTacticMessage"; "msg", msg_j] ->
    let msg = [%of_yojson: string] msg_j |> Result.get_ok in
    AnyLocalRequest (LocalRequest (LocalRequestTacticMessage {msg}))
  | `Assoc ["type", `String "LocalRequestTacticLtac"; "tactic", tactic_j] ->
    let tactic = [%of_yojson: string] tactic_j |> Result.get_ok in
    AnyLocalRequest (LocalRequest (LocalRequestTacticLtac {tactic}))
  | _ -> failwith "unknown local request"

let local_request_result_to_yojson (type r) (local_request : r local_request) (result : r) : Yojson.Safe.t =
  match local_request with
  | LocalRequest (LocalRequestConstrPrint _) ->
    [%to_yojson: string] result
  | LocalRequest (LocalRequestTacticReturn _) ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest (LocalRequestTacticBind _) ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest (LocalRequestTacticThen _) ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest (LocalRequestTacticOr _) ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest (LocalRequestTacticComplete _) ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest LocalRequestTacticGoals ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest (LocalRequestTacticDispatch _) ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest (LocalRequestTacticMessage _) ->
    Internal.to_yojson (fun _ -> assert false) result
  | LocalRequest (LocalRequestTacticLtac _) ->
    Internal.to_yojson (fun _ -> assert false) result


type _ remote_request =
  | RemoteRequestApplyFunction :
    {
      type_desc : 'a type_desc;
      f : ('a -> 'b Internal.t) External.t;
      x : 'a;
    } -> 'b Internal.t remote_request
  | RemoteRequestGetTactic :
    unit TacticRepr.t remote_request

let remote_request_to_yojson (type r) (remote_request : r remote_request) : Yojson.Safe.t =
  match remote_request with
  | RemoteRequestApplyFunction {type_desc; f; x} ->
    let type_desc_j = type_desc_to_yojson type_desc in
    let f_j = External.to_yojson (fun _ -> assert false) f in
    let x_j = any_to_yojson type_desc x in
    `Assoc ["type", `String "RemoteRequestApplyFunction"; "type_desc", type_desc_j; "f", f_j; "x", x_j]
  | RemoteRequestGetTactic ->
    `Assoc ["type", `String "RemoteRequestGetTactic"]

let remote_request_result_of_yojson_exn (type r) (remote_request : r remote_request) (result_j : Yojson.Safe.t) : r =
  match remote_request with
  | RemoteRequestApplyFunction _ ->
    Internal.of_yojson_exn (fun _ -> assert false) result_j
  | RemoteRequestGetTactic ->
    Internal.of_yojson_exn (fun _ -> assert false) result_j

exception RemoteException of string

let _ =
  let pr = function
  | RemoteException s -> Some ("RemoteException:\n" ^ s)
  | _ -> None
  in
  Printexc.register_printer pr

let interact (ist : Geninterp.interp_sign) (url : string) : unit Proofview.tactic =
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
      | LocalRequest (LocalRequestConstrPrint {constr}) ->
        let env = Global.env () in
        let sigma = Evd.from_env env in
        simple_string_of_ppcmds (Printer.pr_econstr_env env sigma constr.v)
      | LocalRequest (LocalRequestTacticReturn {type_desc = _; value}) ->
        Internal.make (Proofview.tclUNIT value)
      | LocalRequest (LocalRequestTacticBind {type_desc; tac; f}) ->
        Internal.make (
          tac.v >>= fun x ->
          Proofview.wrap_exceptions (fun () ->
            (handle_remote_request (RemoteRequestApplyFunction {type_desc; f; x})).v
          )
        )
      | LocalRequest (LocalRequestTacticThen {tac_1; tac_2}) ->
        Internal.make (tac_1.v <*> tac_2.v)
      | LocalRequest (LocalRequestTacticOr {tac_1; tac_2}) ->
        Internal.make (tac_1.v <+> tac_2.v)
      | LocalRequest (LocalRequestTacticComplete {tac}) ->
        Internal.make (Tacticals.tclCOMPLETE tac.v)
      | LocalRequest (LocalRequestTacticMessage {msg}) ->
        Internal.make (Proofview.tclLIFT (Proofview.NonLogical.print_info (Pp.str msg)))
      | LocalRequest LocalRequestTacticGoals ->
        Internal.make (
          Proofview.Goal.goals >>= fun goals ->
          Proofview.Monad.List.map Fun.id goals >>= fun goals ->
          Proofview.tclUNIT (
            goals |> List.map (fun goal ->
              {
                GoalRepr.hyps =
                  goal |> Proofview.Goal.hyps |> List.map (
                    let open Context.Named.Declaration in function
                    | LocalAssum (name, type_) ->
                      {
                        HypRepr.name = name.binder_name |> Names.Id.to_string;
                        HypRepr.type_ = Internal.make type_;
                        HypRepr.kind = Assumption;
                      }
                    | LocalDef (name, value, type_) ->
                      {
                        HypRepr.name = name.binder_name |> Names.Id.to_string;
                        HypRepr.type_ = Internal.make type_;
                        HypRepr.kind = Definition {value = Internal.make value};
                      }
                  );
                GoalRepr.concl = Internal.make (goal |> Proofview.Goal.concl);
              }
            )
          )
        )
      | LocalRequest (LocalRequestTacticDispatch {tacs}) ->
        Internal.make (Proofview.tclDISPATCHL (tacs |> List.map (fun tac -> tac.Internal.v)))
      | LocalRequest (LocalRequestTacticLtac {tactic}) ->
        Internal.make (
          Proofview.tclENV >>= fun env ->
          Proofview.wrap_exceptions (fun () ->
            let raw_tac = Pcoq.parse_string Ltac_plugin.Pltac.tactic_eoi tactic in
            let glob_tac = Ltac_plugin.Tacintern.intern_pure_tactic (Genintern.empty_glob_sign ~strict:false env) raw_tac in
            let tac = Ltac_plugin.Tacinterp.eval_tactic_ist ist glob_tac in
            tac
          )
        ) in
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
