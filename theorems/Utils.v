Inductive Result (T: Type) (E: Type): Type :=
	| Ok (value: T)
	| Err (error: E).

Arguments Ok {T} {E} _.
Arguments Err {T} {E} _.
