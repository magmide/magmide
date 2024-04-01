#[derive(Debug, Eq, PartialEq)]
pub enum TypeBody {
	Unit,
	Union { branches: Vec<String> },
	// Tuple {  },
	// Record { fields: Vec<(String, String)> },
}

// #[derive(Debug, Eq, PartialEq)]
// pub enum Statement {
// 	// Use(UseTree),
// 	Let(LetStatement),
// 	Debug(DebugStatement),
// 	Named(ModuleItem),
// }
pub type Statement = Term;

#[derive(Debug, Eq, PartialEq)]
pub struct TypeDefinition {
	pub name: String,
	pub body: TypeBody,
}

#[derive(Debug, Eq, PartialEq)]
pub struct ProcedureDefinition {
	pub name: String,
	pub parameters: Vec<(String, String)>,
	pub return_type: String,
	pub statements: Vec<Statement>,
}

// #[derive(Debug)]
// pub enum Statement {
// 	Bare(Term),
// 	Let(),
// 	// Module
// }
// TODO
// pub type Statement = Term;

#[derive(Debug, Eq, PartialEq)]
pub struct LetStatement {
	// pub pattern: Pattern,
	pub pattern: String,
	pub type_declaration: Option<Term>,
	pub term: Term,
}

#[derive(Debug, Eq, PartialEq)]
pub struct DebugStatement {
	pub term: Term,
}



#[derive(Debug, Eq, PartialEq)]
pub enum ModuleItem {
	Type(TypeDefinition),
	Procedure(ProcedureDefinition),
	Debug(DebugStatement),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Term {
	Lone(String),
	Chain(String, Vec<ChainItem>),
	Match {
		discriminant: Box<Term>,
		arms: Vec<MatchArm>,
	},
}

#[derive(Debug, Eq, PartialEq)]
pub struct MatchArm {
	// pattern: Pattern,
	pub pattern: Term,
	// statements: Vec<Term>,
	pub statement: Term,
}

#[derive(Debug, Eq, PartialEq)]
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
