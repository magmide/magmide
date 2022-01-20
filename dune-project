(lang dune 2.9)
(name magmide)
(using coq 0.3)

(generate_opam_files true)

(source (github magmide/magmide))
(homepage "https://github.com/magmide/magmide/")
(package
	(name magmide)
	(synopsis "A dependently-typed language intended to make provably correct code possible for working software engineers. ")
	(description "A dependently-typed language intended to make provably correct code possible for working software engineers.")
	(depends
		(ocaml (= 4.13.1))
		(coq (= 8.15.0))))
