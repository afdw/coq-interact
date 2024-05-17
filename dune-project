(lang dune 3.8)

(name coq-interact)

(generate_opam_files true)

(source
 (github afdw/coq-interact))

(authors "Anton Danilkin")

(maintainers "Anton Danilkin")

(using coq 0.8)

(package
 (name coq-interact)
 (synopsis "Coq tactic for interaction with external programs")
 (description "Coq tactic for interaction with external programs")
 (depends
  ocaml
  dune
  coq-core
  (yojson (>= 2.1.2))
  (ppx_deriving_yojson (>= 3.7.0))
  (lwt (>= 5.7.0))
  (websocket-lwt-unix (>= 2.16))
  (mirage-crypto-rng (>= 0.11.3))))
