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

fn build_program_path_index(program: Program) -> PathIndex {
	let mut program_path_index = HashMap::new();
	for module in program.modules {
		update_program_path_index_with_module(&mut program_path_index, "", module);
	};
	program_path_index
}

fn update_program_path_index_with_module(
	program_path_index: &mut PathIndex,
	parent_prefix: &str,
	module: Module,
) {
	let module_name = module.name;
	let prefix = format!("{parent_prefix}::{module_name}");
	for item in module.items {
		let item_name = item.give_name();
		// TODO handle existence case
		program_path_index.insert(format!("{prefix}::{item_name}"), item);
	}

	for child_module in module.child_modules {
		update_program_path_index_with_module(program_path_index, &prefix, child_module);
	}
}

#[derive(Debug, Clone, PartialEq)]
enum TypeBody {
	Unit,
	// Tuple,
}

#[derive(Debug, Clone, PartialEq)]
enum ModuleItem {
	Prop(PropDefinition),
	Theorem(TheoremDefinition),
	// Model,
	// Algorithm,
	// Struct,
	// Fn,
}

impl ModuleItem {
	fn give_name(&self) -> &String {
		match self {
			ModuleItem::Prop(PropDefinition { name, .. }) => name,
			ModuleItem::Theorem(TheoremDefinition { name, .. }) => name,
		}
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
}

#[derive(Debug, Clone, PartialEq)]
enum Term {
	Ident(String),
	// Match
	// Call
	// Chain
}


// type ProgramIndex = HashMap<String, ModuleItem>;

// fn index_program(program: Vec<ModuleItem>) -> Option<ProgramIndex> {
// 	let mut indexed = HashMap::new();
// 	for program_item in program.into_iter() {
// 		let key = program_item.give_name().to_owned();
// 		if indexed.contains_key(&key) { return None }

// 		indexed.insert(key, program_item);
// 	};
// 	Some(indexed)
// }


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
			name: "trivial".to_string(),
			type_body: TypeBody::Unit,
		})
	}
	fn make_give_trivial_thm() -> ModuleItem {
		ModuleItem::Theorem(TheoremDefinition {
			name: "give_trivial".to_string(),
			return_type: Term::Ident("trivial".to_string()),
			statements: vec![
				Statement::Return(Term::Ident("trivial".to_string())),
			],
		})
	}

	#[test]
	fn test_build_program_path_index() {
		let trivial_prop = make_trivial_prop();
		let give_trivial_thm = make_give_trivial_thm();

		let program_path_index = build_program_path_index(Program { modules: vec![
			Module { name: "main".to_string(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![] },
		] });

		let expected = HashMap::from([
			("::main::trivial".to_string(), trivial_prop.clone()),
			("::main::give_trivial".to_string(), give_trivial_thm.clone()),
		]);
		assert_eq!(program_path_index, expected);


		let program_path_index = build_program_path_index(Program { modules: vec![
			Module { name: "main".to_string(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![
				Module { name: "main_child".to_string(), items: vec![give_trivial_thm.clone()], child_modules: vec![] },
			] },

			Module { name: "side".to_string(), items: vec![trivial_prop.clone(), give_trivial_thm.clone()], child_modules: vec![
				Module { name: "side_child".to_string(), items: vec![give_trivial_thm.clone()], child_modules: vec![] },
			] },
		] });

		let expected = HashMap::from([
			("::main::trivial".to_string(), trivial_prop.clone()),
			("::main::give_trivial".to_string(), give_trivial_thm.clone()),
			("::main::main_child::give_trivial".to_string(), give_trivial_thm.clone()),

			("::side::trivial".to_string(), trivial_prop.clone()),
			("::side::give_trivial".to_string(), give_trivial_thm.clone()),
			("::side::side_child::give_trivial".to_string(), give_trivial_thm.clone()),
		]);
		assert_eq!(program_path_index, expected);
	}

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
	// 		name: "And".to_string(),
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
