(lang dune 3.4)

(name implifit)

(generate_opam_files true)

(authors "Arad Arbel")

(package
  (name implifit)
  (synopsis "A type checker for system F with higher order pattern unification and implicit parameters")
  (depends ocaml dune menhir))

(using menhir 2.1)