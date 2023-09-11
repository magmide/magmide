// use std::collections::{HashMap, HashSet};

// // a Ctx is a map of *mere Idents* (which for now will be strings but later will be intern ids) to CtxItems
// // a "Path" isn't a thing held by a Ctx, a Path is the *result of chained accessors*

// // when you build a Ctx, you only add the base Idents available at this point
// // the Ctx for all the items in a module includes all the other items in the module, the base names of the siblings of the module, and "crate" and "super"
// // within a block of statements, the Ctx inherits all the items from the parent scope (either a Module or another block of statements), and iteratively adds things to the Ctx as it goes

// #[derive(Debug, Clone, PartialEq)]
// struct Module {
// 	name: String,
// 	items: Vec<ModuleItem>,
// }


// // TODO at some point this will be some kind of id to an interned string
// type Ident = String;
// // a simple identifier can refer either to some global item with a path like a type or function (types and functions defined inside a block of statements are similar to this, but don't have a "path" in the strict sense since they aren't accessible from the outside)
// // or a mere local variable
// #[derive(Debug)]
// struct Ctx {
// 	scope: HashMap<Ident, CtxItem>,
// 	errors: Vec<String>,
// }

// impl Ctx {
// 	fn from<const N: usize>(pairs: [(Ident, CtxItem); N]) -> Ctx {
// 		Ctx { scope: HashMap::from(pairs), errors: Vec::new() }
// 	}
// 	// from_iter

// 	fn checked_insert(&mut self, ident: Ident, ctx_item: CtxItem) {
// 		if let Some(existing_item) = self.scope.insert(ident, ctx_item) {
// 			self.add_error(format!("name {ident} has already been used"));
// 		}
// 	}

// 	fn add_error(&mut self, error: String) {
// 		self.errors.push(error);
// 	}
// }

// #[derive(Debug)]
// enum CtxItem {
// 	Module(Module),
// 	Prop(PropDefinition),
// 	Theorem(TheoremDefinition),
// 	Local(Term),
// }


// fn type_check_program(modules: Vec<Module>) -> CheckResult<()> {
// 	// TODO add all the prelude uses!
// 	// `use crate::std` for example
// 	let crate_module = Module { name: "crate".into(), items: modules.into_iter().map(|m| ModuleItem::Module(m)) };
// 	// TODO this is where resolutions of all the imported crates would go!
// 	let crate_ctx = Ctx::from([("crate", crate_module), ("super", crate_module)]);
// 	type_check_module(crate_module.clone(), crate_ctx, &crate_module)
// }

// fn type_check_module(module: Module, parent_ctx: Ctx, crate_module: &Module) -> CheckResult<()> {
// 	if module.name == "crate" || module.name == "super" || module.name == "self" {
// 		errors.push(format!("can't name a module reserved word {module.name}"));
// 	}
// 	// TODO clone from parent? this means errors needs to be a global Arc or something, so every cloned Ctx points to the same thing
// 	let mut ctx = parent_ctx.clone();

// 	// this first pass does nothing but build the ctx which checks for name collisions
// 	for item in module.items {
// 		name_pass_type_check_module_item(item, &parent_ctx, &mut ctx);
// 	}

// 	let ctx = ctx;
// 	for item in module.items {
// 		main_pass_type_check_module_item(item, &ctx, &crate_module, &module);
// 	}
// }

// fn name_pass_type_check_module_item(module_item: ModuleItem, parent_ctx: &Ctx, ctx: &mut Ctx) {
// 	match module_item {
// 		Use(use_tree) => {
// 			// when checking a use_tree, it can only refer to what's available *before* all the other items in this module are defined
// 			// but it of course adds things to the ctx
// 			type_check_use_tree_module_level(use_tree, &parent_ctx, &mut ctx);
// 		},
// 		Module(child_module) => {
// 			ctx.checked_insert(child_module.name, CtxItem::Module(child_module))
// 		},
// 		Prop(prop_definition) => {
// 			ctx.checked_insert(prop_definition.name, CtxItem::Prop(prop_definition));
// 		},
// 		Theorem(theorem_definition) => {
// 			ctx.checked_insert(theorem_definition.name, CtxItem::Theorem(theorem_definition));
// 		},
// 		Log(term) => {
// 			// logging can't effect the Ctx, but it *can* refer to anything in the file so checking must be deferred
// 		},
// 	}
// }

// fn main_pass_type_check_module_item(module_item: ModuleItem, ctx: &Ctx, crate_module: &Module, super_module: &Module) {
// 	match module_item {
// 		Use(_) => { /* nothing to do, already checked this */ },
// 		Module(child_module) => {
// 			let child_ctx = HashMap::from([("crate": crate_module), ("super", super_module)]);
// 			type_check_module(child_module, child_ctx, &crate_module);
// 		},
// 		Prop(prop_definition) => {
// 			type_check_prop_definition(prop_definition, &ctx)
// 		},
// 		Theorem(theorem_definition) => {
// 			type_check_theorem_definition(theorem_definition, &ctx)
// 		},
// 		Log(term) => {
// 			type_check_term(term, &ctx);
// 		},
// 	}
// }

// fn type_check_statements(statements: Vec<Statement>, parent_ctx: &Ctx, crate_module: &Module, super_module: &Module) -> CheckResult<()> {
// 	let mut ctx = parent_ctx.clone();

// 	for statement in statements {
// 		match statement {
// 			_ => { /* nothing to do for these on this pass */ },
// 			InnerModuleItem(module_item) => {
// 				name_pass_type_check_module_item(module_item, &parent_ctx, &ctx);
// 			},
// 		}
// 	}

// 	for statement in statements {
// 		match statement {
// 			Let { name, term } => {
// 				type_check_term(term, &ctx);
// 				// TODO mark this term as invalid?
// 				ctx.checked_insert(name, CtxItem::Local(term));
// 			},
// 			Bare(term) => {
// 				// this must be a return
// 			},
// 			// TODO this is problematic, since this ordering would imply inner module items can refer to lets?
// 			InnerModuleItem(module_item) => {
// 				main_pass_type_check_module_item(module_item, &ctx, &crate_module, &super_module);
// 			},
// 		}
// 	}
// }



// fn do_accessors(ctx: &Ctx, mut current_item: CtxItem, accessor_idents: Vec<Ident>) -> CheckResult<(Option<Ident>, CtxItem)> {
// 	let mut current_item = current_item;
// 	let mut current_ident = None;
// 	for accessor_ident in accessor_idents {
// 		// TODO handle super and crate
// 		current_item = ctx.checked_access_path(current_item, accessor_ident)?;
// 		current_ident = Some(accessor_ident);
// 	}
// 	(current_ident, current_item)
// }

// fn type_check_use_tree(use_tree: UseTree, parent_ctx: &Ctx, ctx: &mut Ctx) -> CheckResult<()> {
// 	let (base_ident, rest_idents) = use_tree.path_idents;
// 	let (current_ident, current_item) = do_accessors(&ctx, parent_ctx.checked_get(base_ident)?, rest_idents)?;
// 	let current_ident = current_ident.unwrap_or(base_ident);

// 	match &use_tree.cap {
// 		None => {
// 			ctx.checked_insert(current_ident, current_item);
// 		},
// 		Some(cap) => match cap {
// 			// TODO in case you want to not have two levels of nesting
// 			// UseTreeCap::Empty => ctx.checked_insert(current_ident, current_item),
// 			UseTreeCap::All => ctx.checked_insert_all(current_item),
// 			UseTreeCap::AsName(as_name) => {
// 				ctx.checked_insert(as_name, current_item);
// 			},
// 			UseTreeCap::InnerTrees(inner_trees) => {
// 				for inner_tree in inner_trees {
// 					// TODO don't short circuit on each of these, the internal errors are good enough
// 					let _ = type_check_use_tree(inner_tree, &parent_ctx, &mut ctx);
// 				}
// 			},
// 		},
// 	}
// }


// #[derive(Debug, Clone, PartialEq)]
// enum TypeBody {
// 	Unit,
// 	// Tuple(Vec<TypeReference>),
// 	// Record(Vec<FieldDefinition>),
// 	// Union(Vec<VariantDefinition>),
// 	// AnonymousUnion(Vec<TypeReference>)
// }

// // #[derive(Debug)]
// // struct FieldDefinition {
// // 	name: String,
// // 	type: TypeReference,
// // }

// // #[derive(Debug)]
// // struct VariantDefinition {
// // 	name: String,
// // 	type_body: TypeBody,
// // }

// #[derive(Debug)]
// enum Pattern {
// 	// for now only qualified *nominal* patterns are accepted? otherwise these constructor_names would be Option?
// 	Unit { constructor_name: String },
// 	Compound { constructor_name: String, inner_patterns: Vec<NamedPattern>, is_record: bool },
// 	Union(Vec<Pattern>),
// }

// #[derive(Debug)]
// struct NamedPattern {
// 	name: String,
// 	pattern: Option<Pattern>,
// }

// #[derive(Debug, Clone, PartialEq)]
// enum ModuleItem {
// 	Use(UseTree),
// 	Module(Module),
// 	Prop(PropDefinition),
// 	Theorem(TheoremDefinition),
// 	Log(Term),
// 	// Model,
// 	// Procedure,
// }

// impl ModuleItem {
// 	fn give_name(&self) -> Option<&String> {
// 		match self {
// 			ModuleItem::Use(_) => None,
// 			ModuleItem::Prop(PropDefinition { name, .. }) => Some(name),
// 			ModuleItem::Theorem(TheoremDefinition { name, .. }) => Some(name),
// 		}
// 	}
// }


// #[derive(Debug, Clone, PartialEq)]
// struct UseTree {
// 	path_idents: (String, Vec<String>),
// 	cap: UseTreeCap,
// }

// #[derive(Debug, Clone, PartialEq)]
// enum UseTreeCap {
// 	Empty,
// 	All,
// 	AsName(String),
// 	InnerTrees(Vec<UseTree>),
// }

// impl UseTree {
// 	fn basic(base_path: &'static str) -> UseTree {
// 		UseTree { base_path: base_path.into(), cap: UseTreeCap::Empty }
// 	}
// 	fn basic_as(base_path: &'static str, as_name: &'static str) -> UseTree {
// 		UseTree { base_path: base_path.into(), cap: UseTreeCap::AsName(as_name.into()) }
// 	}
// }

// impl UseTreeCap {
// 	fn inners<const N: usize>(static_inner_paths: [&'static str; N]) -> UseTreeCap {
// 		let mut inner_paths = vec![];
// 		for static_inner_path in static_inner_paths {
// 			inner_paths.push(UseTree::basic(static_inner_path));
// 		}
// 		UseTreeCap::InnerTrees(inner_paths)
// 	}
// }

// #[derive(Debug, Clone, PartialEq)]
// struct PropDefinition {
// 	name: String,
// 	type_body: TypeBody
// }

// #[derive(Debug, Clone, PartialEq)]
// struct TheoremDefinition {
// 	name: String,
// 	// parameters: Vec<(NamedPattern, Option<Term>)>,
// 	return_type: Term,
// 	statements: Vec<Statement>,
// }

// #[derive(Debug, Clone, PartialEq)]
// enum Statement {
// 	Bare(Term),
// 	Let { name: String, term: Term },
// 	// Return(Term),
// 	InnerModuleItem(ModuleItem),
// }

// #[derive(Debug, Clone, PartialEq)]
// enum Term {
// 	Lone(String),
// 	Chain(String, Vec<ChainItem>),
// 	Block { statements: Vec<Term> },
// 	Match {
// 		discriminant: Term,
// 		// discriminant_pattern: Pattern,
// 		return_type: Term,
// 		arms: Vec<MatchArm>
// 	},
// 	Func { parameters: Vec<NamedPattern>, return_type: Term, statements: Vec<Term> },
// }

// #[derive(Debug)]
// struct MatchArm {
// 	pattern: Pattern,
// 	statements: Vec<Term>,
// }

// #[derive(Debug)]
// enum ChainItem {
// 	Access(String),
// 	Call { arguments: Vec<Term> },
// 	// IndexCall { arguments: Vec<Term> },
// 	// TODO yikes? using a complex term to return a function that's called freestanding?
// 	FreeCall { target: Term, arguments: Vec<Term> },
// 	// tapping is only useful for debugging, and should be understood as provably not changing the current type
// 	CatchCall { parameters: Either<NamedPattern, Vec<NamedPattern>>, statements: Vec<Term>, is_tap: bool },
// 	ChainedMatch { return_type: Term, arms: Vec<MatchArm> },
// }



// fn type_check_module_item(item: ModuleItem) {
// 	match item {
// 		ModuleItem::Use(use_tree) => type_check_use_tree(use_tree),
// 		ModuleItem::Prop(PropDefinition { name, type_body }) => {
// 			// TODO check that the name hasn't already been used, or perhaps that's handled by earlier stages?
// 			// maybe instead check if this definition has already been flagged, and skip checking if it has

// 			// check that the definition only refers to things that exist and are valid
// 			match type_body {
// 				Unit => { /* nothing to check! perhaps warn to just use std library's "Trivial" prop though */ },
// 				// Tuple => ,
// 				// Record,
// 				// Union,
// 			}
// 		},
// 		ModuleItem::Theorem(TheoremDefinition { name, return_type, statements }) => {
// 			// TODO check name isn't already used?

// 			// TODO check function doesn't have infinite recursion
// 			// check that return type matches type implied by statements
// 			match type_check_statements(statements) {
// 				None => {
// 					invalid_items.insert(make_path_absolute(name));
// 				},
// 				Some(inferred_type) => {
// 					if !type_assignable(inferred_type, return_type) {
// 						invalid_items.push(item);
// 						errors.push(not_assignable_error(inferred_type, return_type));
// 					}
// 				},
// 			}
// 		},

// 		ModuleItem::Log(term) => {
// 			// TODO make sure this can actually be performed but otherwise do nothing to the context
// 		},
// 	}
// }

// fn type_check_statements(statements: Vec<Statement>) -> TypeReference {
// 	// TODO have to build this from existing module_ctx
// 	let mut local_ctx = HashMap::new();

// 	let mut statements = statements.into_iter().peekable();
// 	while let Some(statement) = statements.next()  {
// 		match statement {
// 			Statement::Let { name, term } => {
// 				let inferred_type = type_check_term(term);

// 				let existing_item = local_ctx.insert(name, inferred_type);
// 				if existing_item.is_some() {
// 					errors.push(format!("variable {name} is already defined"));
// 				}
// 			},

// 			Statement::InnerModuleItem(module_item) => {
// 				// TODO add this module item to the running local_ctx
// 			},

// 			// this is proof checker, which means there's no such thing as mutation or effects,
// 			// which means leaving a term bare can only mean this should be the resolved value of this line of statements
// 			Statement::Bare(term) => {
// 				if statements.peek().is_some() {
// 					errors.push(format!("unreachable code"));
// 				}
// 				return Some(type_check_term(term, local_ctx));
// 			},

// 			// TODO return is a control flow concept that could still be interesting and useful in an immutable language, since a `let` could have a block or match or if or "functional for" (a function that is being called with a block) where return captures control flow
// 			// this means a return can effect the inferred type of a line of statements *above* this one

// 			// "control flow" in this context is *actually* just desugaring to a version of the function where things like a match have been moved up a level
// 			// let a = match something { one => return 1, two => do_something_else() }; a + 2 // same as
// 			// match something { one => 1, two => let a = do_something_else(); a + 2 }
// 			// Term::Return(term)
// 		}
// 	}

// 	errors.push(format!("statements never resolve to a value, which doesn't make sense in a proof checker"));
// 	None
// }

// fn type_check_term(term: Term, ctx: &Ctx) -> Term {
// 	match term {
// 		Term::Ident(ident) => {
// 			// TODO why am I afraid this isn't correct or will recurse infinitely?
// 			ctx.infer_term_type(ident)
// 		},
// 		Term::Block { statements } => {
// 			type_check_statements(statements)
// 		},
// 		Term::Match { discriminant, return_type, arms } => {
// 			let discriminant_type = unimplemented!();
// 			for arm in arms {
// 				check_pattern_compatible(discriminant_type, arm.pattern);
// 				// all the magic is hiding in check_assignable, which has to do reduction and things in complex cases
// 				check_assignable(type_check_statements(arm.statements), return_type)
// 			}
// 		},
// 		Term::Chain(first, rest) => {
// 			let mut chain_ctx = ctx.clone();
// 			let mut current_type = type_check_chain_root(first, &mut chain_ctx)?;
// 			for chain_item in rest {
// 				current_type = type_check_chain_item(chain_item, current_type, &mut chain_ctx)?;
// 			}
// 			current_type
// 		},
// 		Term::Func { parameters, return_type, statements } => {
// 			type_check_named_patterns(parameters, local_ctx);
// 			check_assignable(type_check_statements(statements), return_type)
// 		},
// 	}
// }

// fn type_check_named_patterns(named_patterns: Vec<NamedPattern>, pattern_names: &mut HashSet<String>) {
// 	for named_pattern in named_patterns {
// 		pattern_names.insert(named_pattern.name)?.get_mad_if_exists();
// 		if let Some(pattern) = named_pattern.pattern {
// 			type_check_pattern(pattern, pattern_names);
// 		}
// 	}
// }

// fn type_check_pattern(pattern: Pattern, pattern_names: &mut HashSet<String>) {
// 	match expr {
// 		Pattern::Unit { constructor_name } => {
// 			// TODO look up this constructor_name and see if it exists and is compatible with being a type
// 		},
// 		Pattern::Compound { constructor_name, inner_patterns, is_record } => {
// 			// TODO check constructor_name exists and matches with is_record
// 			type_check_named_patterns(inner_patterns, pattern_names);
// 		},
// 		Pattern::Union(patterns) => {
// 			for pattern in patterns {
// 				type_check_pattern(pattern, pattern_names);
// 			}
// 		},
// 	}
// }

// fn type_check_chain_root(chain_root: ChainRoot, chain_ctx: &mut HashMap<String, Term>) -> Term {
// 	match chain_root {
// 		ChainRoot::Path(path) => {
// 			// TODO look up this path in the context
// 		},
// 		ChainRoot::Call { path, arguments } => {
// 			// TODO check the path exists, is callable, and its parameters match the arguments
// 		},
// 	}
// }

// fn type_check_chain_item(chain_item: ChainItem, current_type: Term, chain_ctx: &mut HashMap<String, Term>) -> Term {
// 	match chain_item {
// 		ChainItem::FreeCall { path, arguments, is_bare } => {
// 			if let Some(_) = current_type && is_bare {
// 				errors.push(format!("used a bare call in the middle of a chain"));
// 				return
// 			}
// 		},
// 		ChainItem::Access(accessor) => {
// 			// TODO check this accessor exists on this type, give type of accessor
// 		},
// 		ChainItem::AccessCall { accessor, arguments } => {
// 			// TODO check the accessor exists, is callable, and its parameters match the arguments
// 		},
// 		ChainItem::CatchCall { parameters, statements, is_tap } => {
// 			match parameters {
// 				Either::Left(parameter) => {
// 					check_assignable(current_type, parameter)
// 					// return if fail?
// 				},
// 				Either::Right(parameters) => {
// 					// TODO type check current_type is a spreadable thing that matches the parameters
// 				},
// 			}
// 			// TODO enrich the ctx with the parameters
// 			let inferred_type = type_check_statements(statements);
// 			// a tapping call is only good for debugging, and doesn't effect the type
// 			if is_tap { current_type } else { inferred_type }
// 		},
// 	}
// }

// fn type_check_use_tree(use_tree: UseTree) {
// 	let UseTree { base_path, cap } = use_tree;
// 	// check that base_path exists
// 	if !module_ctx.has(base_path) {
// 		errors.push(format!("{base_path} doesn't exist"));
// 	}

// 	match cap {
// 		UseTreeCap::Empty => { /* nothing to check if final segment name has already been checked for validity */ }
// 		UseTreeCap::All => {
// 			// TODO check base_path refers to something with importable members
// 		},
// 		UseTreeCap::AsName(as_name) => {
// 			// TODO check that as_name hasn't already been used, or perhaps that's handled by earlier stages?
// 		},
// 		UseTreeCap::InnerTrees(inner_trees) => {
// 			for inner_tree in inner_trees {
// 				type_check_use_tree(inner_tree);
// 			}
// 		},
// 	}
// }


// fn check_assignable(observed_type: Term, desired_type: Term) -> Term {
// 	if !type_assignable(observed_type, desired_type) {
// 		errors.push(format!("{observed_type} not assignable to {desired_type}"));
// 	}
// 	observed_type
// }

// // TODO this is a proof checker, which means types are just terms
// // this is where we need to do canonicalization and reduction and check for equivalance
// fn type_assignable(observed_type: Term, desired_type: Term) -> bool {
// 	unimplemented!()
// }


// #[cfg(test)]
// mod tests {
// 	use super::*;

// 	fn make_path(path: Path) -> Term {
// 		Term::Lone(ChainRoot::Path("true"))
// 	}
// 	fn make_call(path: Path, arguments: Vec<Term>) -> Term {
// 		Term::Lone(ChainRoot::Call { path: "invert", arguments: vec![make_true()] })
// 	}

// 	fn make_trivial_prop() -> ModuleItem {
// 		ModuleItem::Prop(PropDefinition {
// 			name: "trivial".into(),
// 			type_body: TypeBody::Unit,
// 		})
// 	}
// 	fn make_give_trivial_thm() -> ModuleItem {
// 		ModuleItem::Theorem(TheoremDefinition {
// 			name: "give_trivial".into(),
// 			return_type: Term::Ident("trivial".into()),
// 			statements: vec![
// 				Statement::Return(Term::Ident("trivial".into())),
// 			],
// 		})
// 	}

// 	#[test]
// 	fn test_reduce_term(arg: Type) -> RetType {
// 		// type bool = true | false
// 		// use bool::*
// 		// proc invert(b: bool): bool; match b; true; false, false; true
// 		let program = Program { modules: vec![
// 			Module { name: "main".into(), items: vec![make_bool_type(), make_invert_proc()], child_modules: vec![] },
// 		] };

// 		let term = make_call("invert", vec![make_path("true")]);
// 		assert_eq!(reduce_term(term, local_ctx), make_path("crate::main::bool::false"));

// 		let term = make_call("invert", vec![make_path("b")]);
// 		// TODO enrich local_ctx with b: bool, so its some opaque thing
// 		// match b; true; false, false; true
// 		assert_eq!(reduce_term(term, local_ctx), make_match("b", vec![("true", "false"), ("false", "true")]));


// 		// prop trivial
// 		// thm trivial_proven: trivial = trivial

// 		let term = make_path("trivial_proven");
// 		assert_eq!(reduce_term(term, local_ctx), make_path("crate::main::trivial"));
// 	}


// 	#[test]
// 	fn test_type_check_trivial() {
// 		let program = Program { modules: vec![
// 			Module { name: "main".into(), items: vec![make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] },
// 		] };

// 		let mut errors = vec![];
// 		type_check_program(program, &mut errors);
// 		assert_eq!(errors, vec![]);
// 	}

// 	#[test]
// 	fn test_build_program_path_index() {
// 		let trivial_prop = make_trivial_prop();
// 		let give_trivial_thm = make_give_trivial_thm();

// 		let program_path_index = build_program_path_index(Program { modules: vec![
// 			Module { name: "main".into(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![] },
// 		] });

// 		let expected = HashMap::from([
// 			("crate::main::trivial".into(), trivial_prop.clone()),
// 			("crate::main::give_trivial".into(), give_trivial_thm.clone()),
// 		]);
// 		assert_eq!(program_path_index, expected);


// 		let program_path_index = build_program_path_index(Program { modules: vec![
// 			Module { name: "main".into(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![
// 				Module { name: "main_child".into(), items: vec![give_trivial_thm.clone()], child_modules: vec![] },
// 			] },

// 			Module { name: "side".into(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![
// 				Module { name: "side_child".into(), items: vec![give_trivial_thm.clone()], child_modules: vec![] },
// 			] },
// 		] });

// 		let expected = HashMap::from([
// 			("crate::main::trivial".into(), trivial_prop.clone()),
// 			("crate::main::give_trivial".into(), give_trivial_thm.clone()),
// 			("crate::main::main_child::give_trivial".into(), give_trivial_thm.clone()),

// 			("crate::side::trivial".into(), trivial_prop.clone()),
// 			("crate::side::give_trivial".into(), give_trivial_thm.clone()),
// 			("crate::side::side_child::give_trivial".into(), give_trivial_thm.clone()),
// 		]);
// 		assert_eq!(program_path_index, expected);
// 	}

// 	#[test]
// 	fn test_build_module_ctx() {
// 		let module_path = "crate";

// 		let side_use = ModuleItem::Use(UseTree {
// 			// TODO "bare" references like this are assumed to be "relative", so at the same level as the current module
// 			// TODO you could also do super and root
// 			base_path: "side".into(),
// 			cap: UseTreeCap::inners(["whatever", "other"]),
// 		});
// 		let module = Module { name: "main".into(), items: vec![side_use, make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] };

// 		let expected = HashMap::from([
// 			("trivial".into(), "crate::main::trivial".into()),
// 			("give_trivial".into(), "crate::main::give_trivial".into()),
// 			("whatever".into(), "crate::side::whatever".into()),
// 			("other".into(), "crate::side::other".into()),
// 		]);
// 		assert_eq!(build_module_ctx(module_path, &module), expected);


// 		let side_use = ModuleItem::Use(UseTree {
// 			base_path: "crate::side::child".into(),
// 			cap: UseTreeCap::InnerTrees(vec![
// 				UseTree::basic("whatever"),
// 				UseTree::basic_as("other", "different"),
// 				UseTree { base_path: "nested::thing".into(), cap: UseTreeCap::inners(["self", "a", "b"]) },
// 			]),
// 		});
// 		let module = Module { name: "main".into(), items: vec![side_use, make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] };

// 		let expected = HashMap::from([
// 			("trivial".into(), "crate::main::trivial".into()),
// 			("give_trivial".into(), "crate::main::give_trivial".into()),
// 			("whatever".into(), "crate::side::child::whatever".into()),
// 			("different".into(), "crate::side::child::other".into()),
// 			("thing".into(), "crate::side::child::nested::thing".into()),
// 			("a".into(), "crate::side::child::nested::thing::a".into()),
// 			("b".into(), "crate::side::child::nested::thing::b".into()),
// 		]);
// 		assert_eq!(build_module_ctx(module_path, &module), expected);
// 	}

// 	#[test]
// 	fn test_make_path_absolute() {
// 		for (current_absolute_path, possibly_relative_path, expected) in [
// 			("crate", "crate::m", "crate::m"),
// 			("crate", "m", "crate::m"),
// 			("crate", "m::child", "crate::m::child"),
// 			("crate", "crate::m::child", "crate::m::child"),

// 			("crate::a::b::c", "crate::m", "crate::m"),
// 			("crate::a::b::c", "crate::m::child", "crate::m::child"),
// 			("crate::a::b::c", "m", "crate::a::b::c::m"),
// 			("crate::a::b::c", "m::child", "crate::a::b::c::m::child"),
// 		] {
// 			assert_eq!(make_path_absolute(current_absolute_path, possibly_relative_path), expected);
// 		}
// 	}

// 	#[test]
// 	fn test_resolve_reference() {
// 		let program_path_index = HashMap::from([
// 			("crate::main::trivial".into(), make_trivial_prop()),
// 			("crate::main::give_trivial".into(), make_give_trivial_thm()),
// 		]);
// 		let ctx = HashMap::from([]);
// 		let current_path = "crate::main::";

// 		assert_eq!(
// 			resolve_reference(ctx, current_path, "trivial"),
// 			"crate::main::trivial"
// 		);

// 		let ctx = HashMap::from([
// 			("main"),
// 		]);
// 		let current_path = "crate::side::";
// 	}

// 	// #[test]
// 	// fn test_resolve_term_type() {
// 	// 	// in a scope with nothing "included" from higher scopes, identifiers resolve to the name of this scope

// 	// 	assert_eq!(
// 	// 		resolve_term_type("MyType", "some_module", {}),
// 	// 		// if we refer to MyType while in some_module, and there aren't any references to that name, it must be local
// 	// 		vec!["some_module", "MyType"],
// 	// 	);

// 	// 	assert_eq!(
// 	// 		resolve_term_type("MyType", "some_module", { "MyType": "other_module", "WhateverType": "yo_module" }),
// 	// 		// if we refer to it while in some_module but something like a `use` introduced that name from another place, it's that place
// 	// 		vec!["other_module", "MyType"],
// 	// 	);
// 	// }

// 	// #[test]
// 	// fn trivial_type_and_fn() {
// 	// 	// prop trivial
// 	// 	// thm give_trivial: trivial;
// 	// 	// 	return trivial

// 	// 	let program = vec![
// 	// 		make_trivial_prop(),
// 	// 		make_give_trivial_thm(),
// 	// 	];

// 	// 	assert!(type_check_program(program).is_some());

// 	// 	// assert the whole program type checks
// 	// 	// assert querying give_trivial returns trivial, resolved
// 	// }

// 	// #[test]
// 	// fn things() {
// 	// 	// model bool; true | false
// 	// 	// prop trival
// 	// 	// prop impossible; |

// 	// 	// model Thing; a: A, b: B, other: Z

// 	// 	// @(P, Q); prop And(P, Q)

// 	// 	// @(P, Q)
// 	// 	// prop And; (P, Q)

// 	// 	// @(P, Q);
// 	// 	// 	prop And; (P, Q)

// 	// 	// prop And; (@P, @Q)

// 	// 	let and_type = TypeDefinition {
// 	// 		name: "And".into(),
// 	// 		kind: Kind::Prop,
// 	// 		generics: vec![
// 	// 			Pattern{name: "P", type: None},
// 	// 			Pattern{name: "Q", type: None},
// 	// 		],
// 	// 		definition: TypeBody::Tuple(vec![bare("P"), bare("Q")]),
// 	// 	};

// 	// }
// }

// // prop Or; Left(@P) | Right(@Q)
// // Or.Left
// // Or/Left
// // using slash as the "namespace" separator gives a nice similarity to modules and the filesystem
// // that might be a bad thing! although Rust also blends the two by using :: for both
// // honestly I think just `.` is the best, it's just the "access namespace" operator
// // accessing the namespace of a struct is similar to accessing the namespace of a module or a type

// // // anonymous unions
// // alias A = 'a' | 'A' | int

// // fn do_a = |: :match;
// // 	'a' | 'A'; :do_something()
// // 	int; :do_int_thing()

// // `|` is for creating a function, `&` is for creating an assertion
// // `|>` creates a function and catches, `|:` creates a function and chains
// // TODO blaine what about return type annotation for anonymous functions?
// // `&(n; , , )` creates an assertion and catches, `&( , , )` creates an assertion and chains (chains is the default)
// // `&(n; )` creates an assertion and catches, `&` creates an assertion and chains (chains is the default)


// // examples of the "forall" type
// // @(a: A) -> Z
// // @(a: A, b: B, inferred, d: D) -> Z

// // examples of the "simple function" type
// // (A) -> Z
// // (A, B) -> Z

// // there's no such thing as "terms" that only apply specifically for each of these,
// // since there's *only* simple functions in the actual concrete language.

// // "theorems" are functions which return things of kind Prop
// // "algorithms" are functions which return things of kind Model, which may or may not have prop assertions on them

// // "functions" are concrete and computational, have completely different rules




// // TODO in general all of this path stuff should just reuse rustc functions, but I need something to play with for now

// fn make_path_absolute(current_absolute_path: &str, possibly_relative_path: &str) -> String {
// 	if possibly_relative_path.starts_with("crate") {
// 		possibly_relative_path.to_owned()
// 	}
// 	// // TODO need to handle multiple "super" using a while loop?
// 	// else if possibly_relative_path.startswith("super") {
// 	// 	let trimmed_current_absolute_path = current_absolute_path.split("::").skip_last().unwrap();
// 	// 	// TODO can't just trim as many times as you want, have to count how many
// 	// 	let reduced_relative_path = possibly_relative_path.trim_start_matches("super::");
// 	// 	let reduced_relative_path = reduced_relative_path.trim_start_matches("super");
// 	// 	format!("{trimmed_current_absolute_path}::{reduced_relative_path}", )
// 	// }
// 	else {
// 		format!("{current_absolute_path}::{possibly_relative_path}")
// 	}
// }



// // fn make_dir_module(dirname: String, modules: Vec<Module>) -> Module {
// // 	Module { name: dirname, items: modules.into_iter.map(|m| ModuleItem::Module(m)) }
// // }
// // TODO make a function that walks a directory and recursively calls make_dir_module
