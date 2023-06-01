use std::collections::HashMap;

#[derive(Debug)]
enum TypeBody {
	Unit,
	// Tuple,
}


#[derive(Debug)]
struct PropDefinition {
	name: String,
	type_body: TypeBody
}

#[derive(Debug)]
struct TheoremDefinition {
	name: String,
	return_type: Term,
	statements: Vec<Statement>,
}

#[derive(Debug)]
enum ProgramItem {
	Prop(PropDefinition),
	Theorem(TheoremDefinition),
	// Model,
	// Algorithm,
	// Struct,
	// Fn,
}

impl ProgramItem {
	fn give_name(&self) -> &String {
		match self {
			ProgramItem::Prop(PropDefinition { name, .. }) => name,
			ProgramItem::Theorem(TheoremDefinition { name, .. }) => name,
		}
	}
}

#[derive(Debug)]
enum Statement {
	Bare(Term),
	Return(Term),
	Let {
		name: String,
		term: Term,
	},
}

#[derive(Debug)]
enum Term {
	Ident(String),
	// Match
	// Call
	// Chain
}


type ProgramIndex = HashMap<String, ProgramItem>;

fn index_program(program: Vec<ProgramItem>) -> Option<ProgramIndex> {
	let mut indexed = HashMap::new();
	for program_item in program.into_iter() {
		let key = program_item.give_name().to_owned();
		if indexed.contains_key(&key) { return None }

		indexed.insert(key, program_item);
	};
	Some(indexed)
}


fn type_check_program(program: Vec<ProgramItem>) -> Option<()> {
	let indexed = index_program(program)?;

	for (program_item_name, program_item) in indexed.iter() {
		match program_item {
			ProgramItem::Prop(definition) => type_check_prop_definition(&indexed, definition),
			ProgramItem::Theorem(definition) => type_check_theorem_definition(&indexed, definition),
		}?;
	};

	Some(())
}

fn type_check_prop_definition(indexed: &ProgramIndex, definition: &PropDefinition) -> Option<()> {
	match definition.type_body {
		Unit => Some(()),
	}
}
fn type_check_theorem_definition(indexed: &ProgramIndex, definition: &TheoremDefinition) -> Option<()> {
	match resolve_term_type(&indexed, &definition.return_type) == resolve_statements_type(&indexed, &definition.statements) {
		true => Some(()),
		false => None,
	}
}


//

fn resolve_term_type(indexed: &ProgramIndex, term: &Term) -> FullPath {
	unimplemented!()
}
fn resolve_statements_type(indexed: &ProgramIndex, statements: &Vec<Statement>) -> FullPath {
	unimplemented!()
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn trivial_type_and_fn() {
		// prop trivial
		// thm give_trivial: trivial;
		// 	return trivial

		let program = vec![
			ProgramItem::Prop(PropDefinition {
				name: "trivial".to_string(),
				type_body: TypeBody::Unit,
			}),
			ProgramItem::Theorem(TheoremDefinition {
				name: "give_trivial".to_string(),
				return_type: Term::Ident("trivial".to_string()),
				statements: vec![
					Statement::Return(Term::Ident("trivial".to_string())),
				],
			}),
		];

		assert!(type_check_program(program).is_some());

		// assert the whole program type checks
		// assert querying give_trivial returns trivial, resolved
	}

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
