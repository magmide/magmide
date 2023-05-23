#[derive(Debug)]
struct NamingPattern {
	ident: String,
	type: Option<TypeReference>,
};

fn bare(ident: String) -> Parameter {
	Parameter { ident: ident.to_string(), type: None }
}


#[derive(Debug)]
struct Variant {
	name: String,
	// TODO circularity here?
	// enums can define nested enums?
	// this makes sense for anonymous unions but not struct enums
	body: TypeBody,
}


#[derive(Debug)]
enum TypeBody {
	Tuple(Vec<TypeReference>),
	Record(Vec<Field>),
	Union(Vec<Variant>)
}

#[derive(Debug)]
enum Kind {
	Prop,
	// ModelStatic(usize),
	// ModelPolymorphic(usize),
	// Struct,
}

#[derive(Debug)]
struct TypeDefinition {
	name: String,
	kind: Kind,
	generics: Vec<NamingPattern>,
	body: TypeBody,
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn things() {
		// model bool; true | false
		// prop trival
		// prop impossible; |

		// model Thing; a: A, b: B, other: Z

		// @(P, Q); prop And(P, Q)

		// @(P, Q)
		// prop And; (P, Q)

		// @(P, Q);
		// 	prop And; (P, Q)

		// prop And; (@P, @Q)

		let and_type = TypeDefinition {
			name: "And".to_string(),
			kind: Kind::Prop,
			generics: vec![
				Pattern{name: "P", type: None},
				Pattern{name: "Q", type: None},
			],
			definition: TypeBody::Tuple(vec![bare("P"), bare("Q")]),
		};

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
		// `&(n; , , )` creates an assertion and catches, `&()` creates an assertion and chains (chains is the default)
		// `&(n; , , )` creates an assertion and catches, `&` creates an assertion and chains (chains is the default)
	}
}
