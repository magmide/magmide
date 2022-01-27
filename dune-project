(lang dune 2.9)
(name magmide)
(using coq 0.3)

(generate_opam_files true)

(package
	(name magmide)
	(depends
		(ocaml (= 4.13.1))
		(coq (= 8.15.0))))
