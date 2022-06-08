(lang dune 2.9)
(name magmide)
(using coq 0.3)

(generate_opam_files true)

(package
	(name magmide)
	(depends
		(ocaml (= 4.13.1))
		(coq (= 8.15.0))
		(sexplib (= 0.15.0))
		(ppxlib (= 0.26.0))
		(ppx_compare (= 0.15.0))
		(ppx_sexp_conv (= 0.15.1))
		(ppx_inline_test (= 0.15.0))
	)
)
