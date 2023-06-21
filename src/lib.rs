use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
struct Program {
	modules: Vec<Module>,
}

#[derive(Debug, Clone, PartialEq)]
struct Module {
	name: String,
	items: Vec<ModuleItem>,
	child_modules: Vec<Module>,
}

// TODO in general all of this path stuff should just reuse rustc functions, but I need something to play with for now

fn make_path_absolute(current_absolute_path: &str, possibly_relative_path: &str) -> String {
	if possibly_relative_path.starts_with("crate") {
		possibly_relative_path.to_owned()
	}
	// // TODO need to handle multiple "super" using a while loop?
	// else if possibly_relative_path.startswith("super") {
	// 	let trimmed_current_absolute_path = current_absolute_path.split("::").skip_last().unwrap();
	// 	// TODO can't just trim as many times as you want, have to count how many
	// 	let reduced_relative_path = possibly_relative_path.trim_start_matches("super::");
	// 	let reduced_relative_path = reduced_relative_path.trim_start_matches("super");
	// 	format!("{trimmed_current_absolute_path}::{reduced_relative_path}", )
	// }
	else {
		format!("{current_absolute_path}::{possibly_relative_path}")
	}
}

// TODO at some point this will some kind of arena id
type ModuleItemId = String;

type PathIndex = HashMap<ModuleItemId, ModuleItem>;
type ModuleCtx = HashMap<String, ModuleItemId>;

fn build_program_path_index(program: Program) -> PathIndex {
	let mut program_path_index = HashMap::new();
	for module in program.modules {
		update_program_path_index_with_module(&mut program_path_index, "crate", module);
	};
	program_path_index
}

fn update_program_path_index_with_module(
	program_path_index: &mut PathIndex,
	parent_path: &str,
	module: Module,
	// module_ctx: &mut HashMap<String, String>,
) {
	let module_name = module.name;
	let path = format!("{parent_path}::{module_name}");
	for item in module.items {
		if let Some(item_name) = item.give_name() {
			// TODO handle conflict case
			program_path_index.insert(format!("{path}::{item_name}"), item);

			// TODO update module ctx as well
		}
	}

	for child_module in module.child_modules {
		update_program_path_index_with_module(program_path_index, &path, child_module);
	}
}

fn build_module_ctx(parent_path: &str, module: &Module) -> ModuleCtx {
	let mut module_ctx = HashMap::new();
	let module_name = &module.name;
	let module_path = format!("{parent_path}::{module_name}");
	for item in &module.items {
		match item {
			ModuleItem::Use(use_tree) => {
				// TODO format the path onto use_tree.base_path here, including finding stem
				add_use_tree_to_module_ctx("crate", &use_tree, &mut module_ctx);
			},
			// both of these we just add the resolved path
			ModuleItem::Prop(PropDefinition { name, .. }) | ModuleItem::Theorem(TheoremDefinition { name, .. }) => {
				module_ctx.insert(name.into(), format!("{module_path}::{name}"));
			},
		}
	}
	module_ctx
}

fn add_use_tree_to_module_ctx(base_path_prefix: &str, use_tree: &UseTree, module_ctx: &mut ModuleCtx) {
	let base_path = if use_tree.base_path == "self" { base_path_prefix.to_owned() } else {
		// TODO this is wrong, a root reference is only valid at the top of the use
		let next_base_path = use_tree.base_path.trim_start_matches("crate::");
		format!("{base_path_prefix}::{next_base_path}")
	};

	match &use_tree.cap {
		None => {
			let base_path_last = base_path.split("::").last().unwrap().to_owned();
			module_ctx.insert(base_path_last, base_path);
		},
		Some(cap) => match cap {
			UseTreeCap::All => unimplemented!(),
			UseTreeCap::AsName(as_name) => {
				module_ctx.insert(as_name.into(), base_path);
			},
			UseTreeCap::InnerTrees(inner_trees) => {
				for inner_tree in inner_trees {
					add_use_tree_to_module_ctx(&base_path, &inner_tree, module_ctx);
				}
			},
		},
	}
}


#[derive(Debug, Clone, PartialEq)]
enum TypeBody {
	Unit,
	// Tuple(Vec<TypeReference>),
	// Record(Vec<FieldDefinition>),
	// Union(Vec<VariantDefinition>),
	// AnonymousUnion(Vec<TypeReference>)
}

// TODO this will be something more complex at some point
// type TypeReference = String;

// #[derive(Debug)]
// struct FieldDefinition {
// 	name: String,
// 	type: TypeReference,
// }

// #[derive(Debug)]
// struct VariantDefinition {
// 	name: String,
// 	type_body: TypeBody,
// }

#[derive(Debug, Clone, PartialEq)]
enum ModuleItem {
	Use(UseTree),
	Prop(PropDefinition),
	Theorem(TheoremDefinition),
	// Model,
	// Algorithm,
	// Struct,
	// Fn,
}

impl ModuleItem {
	fn give_name(&self) -> Option<&String> {
		match self {
			ModuleItem::Use(_) => None,
			ModuleItem::Prop(PropDefinition { name, .. }) => Some(name),
			ModuleItem::Theorem(TheoremDefinition { name, .. }) => Some(name),
		}
	}
}


#[derive(Debug, Clone, PartialEq)]
struct UseTree {
	base_path: String,
	cap: Option<UseTreeCap>,
}

#[derive(Debug, Clone, PartialEq)]
enum UseTreeCap {
	All,
	AsName(String),
	InnerTrees(Vec<UseTree>),
}

impl UseTree {
	fn basic(base_path: &'static str) -> UseTree {
		UseTree { base_path: base_path.into(), cap: None }
	}
	fn basic_as(base_path: &'static str, as_name: &'static str) -> UseTree {
		UseTree { base_path: base_path.into(), cap: Some(UseTreeCap::AsName(as_name.into())) }
	}
}

impl UseTreeCap {
	fn inners<const N: usize>(static_inner_paths: [&'static str; N]) -> UseTreeCap {
		let mut inner_paths = vec![];
		for static_inner_path in static_inner_paths {
			inner_paths.push(UseTree::basic(static_inner_path));
		}
		UseTreeCap::InnerTrees(inner_paths)
	}
}

#[derive(Debug, Clone, PartialEq)]
struct PropDefinition {
	name: String,
	type_body: TypeBody
}

#[derive(Debug, Clone, PartialEq)]
struct TheoremDefinition {
	name: String,
	return_type: Term,
	statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq)]
enum Statement {
	Bare(Term),
	Let {
		name: String,
		term: Term,
	},
	// Return(Term),
	// InnerModuleItem(ModuleItem),
}

#[derive(Debug, Clone, PartialEq)]
enum Term {
	Ident(String),
	// Match
	// Call
	// Chain
}



fn type_check_program(program: Program) {
	for module in program.modules {
		type_check_module(module);
	}
}

fn type_check_module(module: Module) {
	for item in module.items {
		type_check_module_item(item);
	}
	for child_module in module.child_modules {
		type_check_module(child_module);
	}
}

fn type_check_module_item(item: ModuleItem) {
	match item {
		Use(use_tree) => type_check_use_tree(use_tree),
		Prop(PropDefinition { name, type_body }) => {
			// TODO check that the name hasn't already been used, or perhaps that's handled by earlier stages?
			// maybe instead check if this definition has already been flagged, and skip checking if it has

			// check that the definition only refers to things that exist and are valid
			match type_body {
				Unit => { /* nothing to check! perhaps warn to just use std library's "Trivial" prop though! */ },
				// Tuple => ,
				// Record,
				// Union,
			}
		},
		Theorem(TheoremDefinition { name, return_type, statements }) => {
			// TODO check name isn't already used?

			// check that return type matches type implied by statements
			match infer_type_of_statements(statements) {
				None => {
					invalid_items.insert(make_path_absolute(name));
				},
				Some(inferred_type) => {
					if !type_assignable(inferred_type, return_type) {
						errors.push(format!("{inferred_type} not assignable to {return_type}"));
					}
				},
			}
		},
	}
}

fn infer_type_of_statements(statements: Vec<Statement>) -> TypeReference {
	// TODO have to build this from existing module_ctx
	let mut local_ctx = HashMap::new();

	let mut statements = statements.into_iter().peekable();
	while let Some(statement) = statements.next()  {
		match statement {
			Term::Let { name, term } => {
				let inferred_type = infer_type_of_term(term);

				let existing_item = local_ctx.insert(name, inferred_type);
				if existing_item.is_some() {
					errors.push(format!("variable {name} is already defined"));
				}
			},

			// this is proof checker, which means there's no such thing as mutation or effects,
			// which means leaving a term bare can only mean this should be the resolved value of this line of statements
			Term::Bare(term) => {
				if statements.peek().is_some() {
					errors.push(format!("unreachable code"));
				}
				return Some(infer_type_of_term(term, local_ctx));
			},

			// TODO return is a control flow concept that could still be interesting and useful in an immutable language, since a `let` could have a block or match or if or "functional for" (a function that is being called with a block) where return captures control flow
			// this means a return can effect the inferred type of a line of statements *above* this one

			// "control flow" in this context is *actually* just desugaring to a version of the function where things like a match have been moved up a level
			// let a = match something { one => return 1, two => do_something_else() }; a + 2 // same as
			// match something { one => 1, two => let a = do_something_else(); a + 2 }
			// Term::Return(term)
		}
	}

	errors.push(format!("statements never resolve to a value, which doesn't make sense in a proof checker"));
	None
}

fn infer_type_of_term(term: Term, local_ctx: HashMap<String, TypeReference>) -> TypeReference {
	match term {
		Some(expr) => expr,
		None => expr,
	}
}

// TODO this is a proof checker, which probably means types are just terms right?
// this is likely where we need to do reduction/canonicalization to check for equivalance
fn type_assignable(observed_type: TypeReference, desired_type: TypeReference) -> bool {
	unimplemented!()
}

fn type_check_use_tree(use_tree: UseTree) {
	let UseTree { base_path, cap } = use_tree;
	// check that base_path exists
	if !module_ctx.has(base_path) {
		errors.push(format!("{base_path} doesn't exist"));
	}

	// TODO check that all items exist and are importable
	match cap {
		None => { /* nothing to check if final segment name has already been checked for validity */ },
		Some(cap) => match cap {
			UseTreeCap::All => {
				// TODO check base_path refers to something with importable members
			},
			UseTreeCap::AsName(as_name) => {
				// TODO check that as_name hasn't already been used, or perhaps that's handled by earlier stages?
			},
			UseTreeCap::InnerTrees(inner_trees) => {
				for inner_tree in inner_trees {
					type_check_use_tree(inner_tree);
				}
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn make_trivial_prop() -> ModuleItem {
		ModuleItem::Prop(PropDefinition {
			name: "trivial".into(),
			type_body: TypeBody::Unit,
		})
	}
	fn make_give_trivial_thm() -> ModuleItem {
		ModuleItem::Theorem(TheoremDefinition {
			name: "give_trivial".into(),
			return_type: Term::Ident("trivial".into()),
			statements: vec![
				Statement::Return(Term::Ident("trivial".into())),
			],
		})
	}

	// #[test]
	// fn test_type_check_trivial_prop() {
	// 	unimplemented!();
	// }

	#[test]
	fn test_type_check_trivial() {
		let program = Program { modules: vec![
			Module { name: "main".into(), items: vec![make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] },
		] };

		let mut errors = vec![];
		type_check_program(program, &mut errors);
		assert_eq!(errors, vec![]);
	}

	#[test]
	fn test_build_program_path_index() {
		let trivial_prop = make_trivial_prop();
		let give_trivial_thm = make_give_trivial_thm();

		let program_path_index = build_program_path_index(Program { modules: vec![
			Module { name: "main".into(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![] },
		] });

		let expected = HashMap::from([
			("crate::main::trivial".into(), trivial_prop.clone()),
			("crate::main::give_trivial".into(), give_trivial_thm.clone()),
		]);
		assert_eq!(program_path_index, expected);


		let program_path_index = build_program_path_index(Program { modules: vec![
			Module { name: "main".into(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![
				Module { name: "main_child".into(), items: vec![give_trivial_thm.clone()], child_modules: vec![] },
			] },

			Module { name: "side".into(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![
				Module { name: "side_child".into(), items: vec![give_trivial_thm.clone()], child_modules: vec![] },
			] },
		] });

		let expected = HashMap::from([
			("crate::main::trivial".into(), trivial_prop.clone()),
			("crate::main::give_trivial".into(), give_trivial_thm.clone()),
			("crate::main::main_child::give_trivial".into(), give_trivial_thm.clone()),

			("crate::side::trivial".into(), trivial_prop.clone()),
			("crate::side::give_trivial".into(), give_trivial_thm.clone()),
			("crate::side::side_child::give_trivial".into(), give_trivial_thm.clone()),
		]);
		assert_eq!(program_path_index, expected);
	}

	#[test]
	fn test_build_module_ctx() {
		let module_path = "crate";

		let side_use = ModuleItem::Use(UseTree {
			// TODO "bare" references like this are assumed to be "relative", so at the same level as the current module
			// TODO you could also do super and root
			base_path: "side".into(),
			cap: Some(UseTreeCap::inners(["whatever", "other"])),
		});
		let module = Module { name: "main".into(), items: vec![side_use, make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] };

		let expected = HashMap::from([
			("trivial".into(), "crate::main::trivial".into()),
			("give_trivial".into(), "crate::main::give_trivial".into()),
			("whatever".into(), "crate::side::whatever".into()),
			("other".into(), "crate::side::other".into()),
		]);
		assert_eq!(build_module_ctx(module_path, &module), expected);


		let side_use = ModuleItem::Use(UseTree {
			base_path: "crate::side::child".into(),
			cap: Some(UseTreeCap::InnerTrees(vec![
				UseTree::basic("whatever"),
				UseTree::basic_as("other", "different"),
				UseTree { base_path: "nested::thing".into(), cap: Some(UseTreeCap::inners(["self", "a", "b"])) },
			])),
		});
		let module = Module { name: "main".into(), items: vec![side_use, make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] };

		let expected = HashMap::from([
			("trivial".into(), "crate::main::trivial".into()),
			("give_trivial".into(), "crate::main::give_trivial".into()),
			("whatever".into(), "crate::side::child::whatever".into()),
			("different".into(), "crate::side::child::other".into()),
			("thing".into(), "crate::side::child::nested::thing".into()),
			("a".into(), "crate::side::child::nested::thing::a".into()),
			("b".into(), "crate::side::child::nested::thing::b".into()),
		]);
		assert_eq!(build_module_ctx(module_path, &module), expected);
	}

	#[test]
	fn test_make_path_absolute() {
		for (current_absolute_path, possibly_relative_path, expected) in [
			("crate", "crate::m", "crate::m"),
			("crate", "m", "crate::m"),
			("crate", "m::child", "crate::m::child"),
			("crate", "crate::m::child", "crate::m::child"),

			("crate::a::b::c", "crate::m", "crate::m"),
			("crate::a::b::c", "crate::m::child", "crate::m::child"),
			("crate::a::b::c", "m", "crate::a::b::c::m"),
			("crate::a::b::c", "m::child", "crate::a::b::c::m::child"),
		] {
			assert_eq!(make_path_absolute(current_absolute_path, possibly_relative_path), expected);
		}
	}

	// #[test]
	// fn test_resolve_reference() {
	// 	let program_path_index = HashMap::from([
	// 		("crate::main::trivial".into(), make_trivial_prop()),
	// 		("crate::main::give_trivial".into(), make_give_trivial_thm()),
	// 	]);
	// 	let ctx = HashMap::from([]);
	// 	let current_path = "crate::main::";

	// 	assert_eq!(
	// 		resolve_reference(ctx, current_path, "trivial"),
	// 		"crate::main::trivial"
	// 	);

	// 	let ctx = HashMap::from([
	// 		("main"),
	// 	]);
	// 	let current_path = "crate::side::";
	// }

	// #[test]
	// fn test_resolve_term_type() {
	// 	// in a scope with nothing "included" from higher scopes, identifiers resolve to the name of this scope

	// 	assert_eq!(
	// 		resolve_term_type("MyType", "some_module", {}),
	// 		// if we refer to MyType while in some_module, and there aren't any references to that name, it must be local
	// 		vec!["some_module", "MyType"],
	// 	);

	// 	assert_eq!(
	// 		resolve_term_type("MyType", "some_module", { "MyType": "other_module", "WhateverType": "yo_module" }),
	// 		// if we refer to it while in some_module but something like a `use` introduced that name from another place, it's that place
	// 		vec!["other_module", "MyType"],
	// 	);
	// }

	// #[test]
	// fn trivial_type_and_fn() {
	// 	// prop trivial
	// 	// thm give_trivial: trivial;
	// 	// 	return trivial

	// 	let program = vec![
	// 		make_trivial_prop(),
	// 		make_give_trivial_thm(),
	// 	];

	// 	assert!(type_check_program(program).is_some());

	// 	// assert the whole program type checks
	// 	// assert querying give_trivial returns trivial, resolved
	// }

	// #[test]
	// fn things() {
	// 	// model bool; true | false
	// 	// prop trival
	// 	// prop impossible; |

	// 	// model Thing; a: A, b: B, other: Z

	// 	// @(P, Q); prop And(P, Q)

	// 	// @(P, Q)
	// 	// prop And; (P, Q)

	// 	// @(P, Q);
	// 	// 	prop And; (P, Q)

	// 	// prop And; (@P, @Q)

	// 	let and_type = TypeDefinition {
	// 		name: "And".into(),
	// 		kind: Kind::Prop,
	// 		generics: vec![
	// 			Pattern{name: "P", type: None},
	// 			Pattern{name: "Q", type: None},
	// 		],
	// 		definition: TypeBody::Tuple(vec![bare("P"), bare("Q")]),
	// 	};

	// }
}

// prop Or; Left(@P) | Right(@Q)
// Or.Left
// Or/Left
// using slash as the "namespace" separator gives a nice similarity to modules and the filesystem
// that might be a bad thing! although Rust also blends the two by using :: for both
// honestly I think just `.` is the best, it's just the "access namespace" operator
// accessing the namespace of a struct is similar to accessing the namespace of a module or a type

// // anonymous unions
// alias A = 'a' | 'A' | int

// fn do_a = |: :match;
// 	'a' | 'A'; :do_something()
// 	int; :do_int_thing()

// `|` is for creating a function, `&` is for creating an assertion
// `|>` creates a function and catches, `|:` creates a function and chains
// TODO blaine what about return type annotation for anonymous functions?
// `&(n; , , )` creates an assertion and catches, `&( , , )` creates an assertion and chains (chains is the default)
// `&(n; )` creates an assertion and catches, `&` creates an assertion and chains (chains is the default)


// examples of the "forall" type
// @(a: A) -> Z
// @(a: A, b: B, inferred, d: D) -> Z

// examples of the "simple function" type
// (A) -> Z
// (A, B) -> Z

// there's no such thing as "terms" that only apply specifically for each of these,
// since there's *only* simple functions in the actual concrete language.

// "theorems" are functions which return things of kind Prop
// "algorithms" are functions which return things of kind Model, which may or may not have prop assertions on them

// "functions" are concrete and computational, have completely different rules
