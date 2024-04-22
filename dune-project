(lang dune 3.6)

(generate_opam_files true)

(authors "Shiwei Weng <shiwei@prover.me>")

; (source
;  (github arbipher/fancy))

(package
 (name ppx_z3)
 (synopsis "A ppx to derive z3 datatype from OCaml type")
 (description "I shall better \nwrite a better description.")
 (depends
  (alcotest :with-test)))
