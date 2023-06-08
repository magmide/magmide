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

type PathIndex = HashMap<String, ModuleItem>;
type ModuleCtx = HashMap<String, String>;

fn build_program_path_index(program: Program) -> PathIndex {
	let mut program_path_index = HashMap::new();
	for module in program.modules {
		update_program_path_index_with_module(&mut program_path_index, "", module);
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
				add_use_tree_to_module_ctx("", &use_tree, &mut module_ctx);
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
		let next_base_path = use_tree.base_path.trim_start_matches("::");
		format!("{base_path_prefix}::{next_base_path}")
	};

	match &use_tree.cap {
		None => {
			let base_path_stem = base_path.split("::").last().unwrap().to_owned();
			module_ctx.insert(base_path_stem, base_path);
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
	// Tuple,
}

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
	Return(Term),
	Let {
		name: String,
		term: Term,
	},
	// InnerModuleItem(ModuleItem),
}

#[derive(Debug, Clone, PartialEq)]
enum Term {
	Ident(String),
	// Match
	// Call
	// Chain
}


// fn type_check_program(program: Vec<ModuleItem>) -> Option<()> {
// 	let indexed = index_program(program)?;

// 	for (program_item_name, program_item) in indexed.iter() {
// 		match program_item {
// 			ModuleItem::Prop(definition) => type_check_prop_definition(&indexed, definition),
// 			ModuleItem::Theorem(definition) => type_check_theorem_definition(&indexed, definition),
// 		}?;
// 	};

// 	Some(())
// }

// fn type_check_prop_definition(indexed: &ProgramIndex, definition: &PropDefinition) -> Option<()> {
// 	match definition.type_body {
// 		Unit => Some(()),
// 	}
// }
// fn type_check_theorem_definition(indexed: &ProgramIndex, definition: &TheoremDefinition) -> Option<()> {
// 	match resolve_term_type(&indexed, &definition.return_type) == resolve_statements_type(&indexed, &definition.statements) {
// 		true => Some(()),
// 		false => None,
// 	}
// }


// type FullPath = Vec<String>;

// fn resolve_term_type(indexed: &ProgramIndex, term: &Term) -> FullPath {
// 	unimplemented!()
// }
// fn resolve_statements_type(indexed: &ProgramIndex, statements: &Vec<Statement>) -> FullPath {
// 	unimplemented!()
// }

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

	#[test]
	fn test_build_program_path_index() {
		let trivial_prop = make_trivial_prop();
		let give_trivial_thm = make_give_trivial_thm();

		let program_path_index = build_program_path_index(Program { modules: vec![
			Module { name: "main".into(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![] },
		] });

		let expected = HashMap::from([
			("::main::trivial".into(), trivial_prop.clone()),
			("::main::give_trivial".into(), give_trivial_thm.clone()),
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
			("::main::trivial".into(), trivial_prop.clone()),
			("::main::give_trivial".into(), give_trivial_thm.clone()),
			("::main::main_child::give_trivial".into(), give_trivial_thm.clone()),

			("::side::trivial".into(), trivial_prop.clone()),
			("::side::give_trivial".into(), give_trivial_thm.clone()),
			("::side::side_child::give_trivial".into(), give_trivial_thm.clone()),
		]);
		assert_eq!(program_path_index, expected);
	}

	#[test]
	fn test_build_module_ctx() {
		let module_path = "";

		let side_use = ModuleItem::Use(UseTree {
			// TODO "bare" references like this are assumed to be "relative", so at the same level as the current module
			// TODO you could also do super and root
			base_path: "side".into(),
			cap: Some(UseTreeCap::inners(["whatever", "other"])),
		});
		let module = Module { name: "main".into(), items: vec![side_use, make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] };

		let expected = HashMap::from([
			("trivial".into(), "::main::trivial".into()),
			("give_trivial".into(), "::main::give_trivial".into()),
			("whatever".into(), "::side::whatever".into()),
			("other".into(), "::side::other".into()),
		]);
		assert_eq!(build_module_ctx(module_path, &module), expected);


		let side_use = ModuleItem::Use(UseTree {
			base_path: "::side::child".into(),
			cap: Some(UseTreeCap::InnerTrees(vec![
				UseTree::basic("whatever"),
				UseTree::basic_as("other", "different"),
				UseTree { base_path: "nested::thing".into(), cap: Some(UseTreeCap::inners(["self", "a", "b"])) },
			])),
		});
		let module = Module { name: "main".into(), items: vec![side_use, make_trivial_prop(), make_give_trivial_thm()], child_modules: vec![] };

		let expected = HashMap::from([
			("trivial".into(), "::main::trivial".into()),
			("give_trivial".into(), "::main::give_trivial".into()),
			("whatever".into(), "::side::child::whatever".into()),
			("different".into(), "::side::child::other".into()),
			("thing".into(), "::side::child::nested::thing".into()),
			("a".into(), "::side::child::nested::thing::a".into()),
			("b".into(), "::side::child::nested::thing::b".into()),
		]);
		assert_eq!(build_module_ctx(module_path, &module), expected);
	}

	// #[test]
	// fn test_resolve_reference() {
	// 	let program_path_index = HashMap::from([
	// 		("::main::trivial".into(), make_trivial_prop()),
	// 		("::main::give_trivial".into(), make_give_trivial_thm()),
	// 	]);
	// 	let ctx = HashMap::from([]);
	// 	let current_path = "::main::";

	// 	assert_eq!(
	// 		resolve_reference(ctx, current_path, "trivial"),
	// 		"::main::trivial"
	// 	);

	// 	let ctx = HashMap::from([
	// 		("main"),
	// 	]);
	// 	let current_path = "::side::";
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
