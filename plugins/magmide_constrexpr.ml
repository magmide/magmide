open Constrexpr

let dbg_qualid = Libnames.string_of_qualid

let dbg_unknown _ = "???"

let dbg_option opt some_dbg = match opt with
	| None -> "None"
	| Some v -> some_dbg v

let dbg_prim_token tok = match tok with
	| Number numtok -> NumTok.Signed.sprint numtok
	| String str -> str

let rec dbg_constrexpr e = CAst.with_val (fun (e) -> match e with
	| CRef (qualident, instance_expr_option) -> "Ref("^ dbg_qualid qualident ^", "^ dbg_option instance_expr_option dbg_unknown ^")"
	(* | CFix of lident * fix_expr list *)
	| CFix _ -> "Fix"
	(* | CCoFix of lident * cofix_expr list *)
	| CCoFix _ -> "CoFix"
	(* | CProdN of local_binder_expr list * constr_expr *)
	| CProdN _ -> "ProdN"
	(* | CLambdaN of local_binder_expr list * constr_expr *)
	| CLambdaN _ -> "LambdaN"
	(* | CLetIn of lname * constr_expr * constr_expr option * constr_expr *)
	| CLetIn _ -> "LetIn"
	(* | CAppExpl of (qualid * instance_expr option) * constr_expr list *)
	| CAppExpl _ -> "AppExpl"
	(* | CApp of constr_expr * (constr_expr * explicitation CAst.t option) list *)
	| CApp (e, l) -> "(App " ^ dbg_constrexpr e ^ " " ^ String.concat " " (List.map dbg_explicated l) ^ ")"
	(* | CProj of explicit_flag * (qualid * instance_expr option) * (constr_expr * explicitation CAst.t option) list * constr_expr *)
	| CProj _ -> "Proj"
	(* | CRecord of (qualid * constr_expr) list *)
	| CRecord _ -> "Record"
	(* | CCases of Constr.case_style * constr_expr option * case_expr list * branch_expr list *)
	| CCases _ -> "Cases"
	(* | CLetTuple of lname list * (lname option * constr_expr option) * constr_expr * constr_expr *)
	| CLetTuple _ -> "LetTuple"
	(* | CIf of constr_expr * (lname option * constr_expr option) * constr_expr * constr_expr *)
	| CIf _ -> "If"
	(* | CHole of Evar_kinds.t option * Namegen.intro_pattern_naming_expr * Genarg.raw_generic_argument option *)
	| CHole _ -> "Hole"
	(* | CPatVar of Pattern.patvar *)
	| CPatVar _ -> "PatVar"
	(* | CEvar of Glob_term.existential_name CAst.t * (lident * constr_expr) list *)
	| CEvar _ -> "Evar"
	(* | CSort of sort_expr *)
	| CSort _ -> "Sort"
	(* | CCast of constr_expr * Constr.cast_kind * constr_expr *)
	| CCast _ -> "Cast"
	(* | CNotation of notation_with_optional_scope option * notation * constr_notation_substitution *)
	| CNotation _ -> "Notation"
	(* | CGeneralization of Glob_term.binding_kind * constr_expr *)
	| CGeneralization _ -> "Generalization"
	(* | CPrim of prim_token *)
	| CPrim (token) -> "Prim("^ dbg_prim_token token ^")"
	(* | CDelimiters of string * constr_expr *)
	| CDelimiters _ -> "Delimiters"
	(* | CArray of instance_expr option * constr_expr array * constr_expr * constr_expr *)
	| CArray _ -> "Array"
) e

and dbg_explicated x = match x with
        | (e, None) -> "(" ^ dbg_constrexpr e ^ ", No explicitation)"
        | (e, Some x) -> "(" ^ dbg_constrexpr e ^ ", Some explicitation)"



(* let cnt = ref 0

let display csr =
	let rec term_display c = match Constr.kind c with
	| Constr.Rel n -> "Rel("^(string_of_int n)^")"
	| Constr.Meta n -> "Meta("^(string_of_int n)^")"
	| Constr.Var id -> "Var("^(Names.Id.to_string id)^")"
	| Constr.Sort s -> "Sort("^(sort_display s)^")"
	| Constr.Cast (c,k, t) ->
			"Cast("^(term_display c)^","^(cast_kind_display k)^","^(term_display t)^")"
	| Constr.Prod (na,t,c) ->
			"Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
	| Constr.Lambda (na,t,c) ->
			"Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
	| Constr.LetIn (na,b,t,c) ->
			"LetIn("^(name_display na)^","^(term_display b)^","
			^(term_display t)^","^(term_display c)^")"
	| Constr.App (c,l) -> "App("^(term_display c)^","^(array_display l)^")\n"
	| Constr.Evar (e,l) -> "Evar("^(Pp.string_of_ppcmds (Evar.print e))^","^(array_display (Array.of_list l))^")"
	| Constr.Const (c,u) -> "Const("^(Names.Constant.to_string c)^","^(universes_display u)^")"
	| Constr.Ind ((sp,i),u) ->
			"MutInd("^(Names.MutInd.to_string sp)^","^(string_of_int i)^","^(universes_display u)^")"
	| Constr.Construct (((sp,i),j),u) ->
			"MutConstruct(("^(Names.MutInd.to_string sp)^","^(string_of_int i)^"),"
			^","^(universes_display u)^(string_of_int j)^")"
	| Constr.Proj (p, c) -> "Proj("^(Names.Constant.to_string (Names.Projection.constant p))^","^term_display c ^")"
	| Constr.Case (ci,u,pms,(_,p),iv,c,bl) ->
			"MutCase(<abs>,"^(term_display p)^","^(term_display c)^","
			^(array_display (Array.map snd bl))^")"
	| Constr.Fix ((t,i),(lna,tl,bl)) ->
			"Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
				then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
			^(array_display tl)^",[|"
			^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
				then (";"^i) else "")) lna "")^"|],"
			^(array_display bl)^")"
	| Constr.CoFix(i,(lna,tl,bl)) ->
			"CoFix("^(string_of_int i)^"),"
			^(array_display tl)^","
			^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
				then (";"^i) else "")) lna "")^","
			^(array_display bl)^")"
	| Constr.Int i ->
			"Int("^(Uint63.to_string i)^")"
	| Constr.Float f ->
			"Float("^(Float64.to_string f)^")"
	| Constr.Array (u,t,def,ty) -> "Array("^(array_display t)^","^(term_display def)^","^(term_display ty)^")@{" ^universes_display u^"\n"

	and array_display v = "["^ (Array.fold_right
		(fun x i -> (term_display x)^(if not(i="") then ("; "^i) else "")) v ""
	) ^"]"

	and univ_display u =
		incr cnt; "with " ^ string_of_int !cnt ^ " " ^ string_of_ppcmds(Univ.pr_uni u)

	and level_display u =
		incr cnt; "with " ^ string_of_int  !cnt ^ " " ^ string_of_ppcmds(Univ.Level.pr u)

	and sort_display s = match s with
		| Sorts.SProp -> "SProp"
		| Sorts.Set -> "Set"
		| Sorts.Prop -> "Prop"
		| Sorts.Type u -> (univ_display u)^ "Type("^(string_of_int !cnt)^")"

	and universes_display l =
		Array.fold_right (fun x i -> level_display x ^ (string_of_int !cnt)^(if not(i="")
				then (" "^i) else "")) (Univ.Instance.to_array l) ""

	and name_display x = match x.binder_name with
		| Name id -> "Name("^(Names.Id.to_string id)^")"
		| Anonymous -> "Anonymous"

	and cast_kind_display k = match k with
	  | VMcast -> "VMcast"
	  | DEFAULTcast -> "DEFAULTcast"
	  | NATIVEcast -> "NATIVEcast"

	in
	(str (term_display csr) ++fnl ()) *)

(* Feedback.msg_debug (display EConstr.Unsafe.(to_constr t)) *)
	(* Feedback.msg_debug (Ppconstr.pr_lconstr_expr env sigma e) *)
