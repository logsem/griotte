(lang dune 3.21)
(using rocq 0.11)

(name griotte)

(generate_opam_files false)

(authors "June Rousseau"
         "Aina Linn Georges")

(maintainers "June Rousseau")

(license expat)

(documentation TODO)

(package
 (name griotte)
 (synopsis "Griotte")
 (description "Griotte")
 (depends ocaml dune rocq-iris equations)
 (tags
  (Rocq CHERIoT "capability machine" Iris)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
