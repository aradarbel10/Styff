(lang dune 3.4)

(name styff)

(generate_opam_files true)

(authors "Arad Arbel")

(package
  (name styff)
  (synopsis "A functional language with (system F-omega) polymorphism and GADTs")
  (depends ocaml dune menhir))

(using menhir 2.1)
(using directory-targets 0.1)