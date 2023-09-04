// #[derive(Debug)]
// enum TypeBody {
// 	Unit,
// 	Tuple { name: String, items: Vec<String> },
// 	Record { name: String },
// }

#[derive(Debug, PartialEq)]
pub enum TypeBody {
	Unit,
	Union { branches: Vec<String> },
	// Record { fields: Vec<(String, String)> },
}

#[derive(Debug, PartialEq)]
pub enum ModuleItem {
	TypeDefinition {
		name: String,
		body: TypeBody,
	},
	ProcedureDefinition {
		name: String,
		parameters: Vec<(String, String)>,
		return_type: String,
		statements: Vec<Term>,
	},
	Debug(Term),
}

#[derive(Debug, PartialEq)]
pub enum Term {
	Lone(String),
	Chain(String, Vec<ChainItem>),
	Match {
		discriminant: String,
		arms: Vec<MatchArm>,
	},
}

#[derive(Debug, PartialEq)]
pub struct MatchArm {
	// pattern: Pattern,
	pub pattern: Term,
	// statements: Vec<Term>,
	pub statement: Term,
}

#[derive(Debug, PartialEq)]
pub enum ChainItem {
	Access(String),
	Call { arguments: Vec<Term> },
	// // IndexCall { arguments: Vec<Term> },
	// // TODO yikes? using a complex term to return a function that's called freestanding?
	// FreeCall { target: Term, arguments: Vec<Term> },
	// // tapping is only useful for debugging, and should be understood as provably not changing the current type
	// CatchCall { parameters: Either<NamedPattern, Vec<NamedPattern>>, statements: Vec<Term>, is_tap: bool },
	// ChainedMatch { return_type: Term, arms: Vec<MatchArm> },
}
