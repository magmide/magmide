// #[derive(Debug)]
// enum TypeBody {
// 	Unit,
// 	Tuple { name: String, items: Vec<String> },
// 	Record { name: String },
// }

// #[salsa::tracked]
// pub struct Span {
// 	pub start: usize,
// 	pub end: usize,
// }



#[derive(Debug, Eq, PartialEq)]
pub enum TypeBody {
	Unit,
	Union { branches: Vec<String> },
	// Tuple {  },
	// Record { fields: Vec<(String, String)> },
}


// #[salsa::tracked]
// pub struct Program {
// 	#[return_ref]
// 	pub modules: Vec<Module>,
// }

// #[salsa::tracked]
// pub struct FileModule {
// 	#[return_ref]
// 	pub module_items: Vec<ModuleItem>,
// }

#[salsa::interned]
pub struct Ident {
	#[return_ref]
	pub text: String,
}

#[derive(Debug)]
pub enum Statement {
	// Use(UseTree),
	Let(LetStatement),
	Debug(DebugStatement),
	Named(ModuleItem),
}


#[salsa::tracked]
pub struct TypeDefinition {
	#[id]
	pub name: Ident,
	#[return_ref]
	pub body: TypeBody,
}

#[derive(Debug, Eq, PartialEq)]
pub struct RawTypeDefinition {
	pub name: String,
	pub body: TypeBody,
}

#[salsa::tracked]
pub struct ProcedureDefinition {
	#[id]
	pub name: Ident,
	#[return_ref]
	pub parameters: Vec<(String, String)>,
	#[return_ref]
	pub return_type: String,
	#[return_ref]
	pub statements: Vec<Statement>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct RawProcedureDefinition {
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
pub type Statement = Term;

#[derive(Debug, Eq, PartialEq)]
pub struct LetStatement {
	// pub pattern: Pattern,
	pub pattern: Ident,
	pub type: Option<Term>,
	pub term: Term,
}

#[derive(Debug, Eq, PartialEq)]
pub struct DebugStatement {
	pub term: Term,
}

#[salsa::tracked]
pub struct Statements {
	pub statements: Vec<>,
}





#[derive(Debug, Eq, PartialEq)]
pub enum ModuleItem {
	Type(RawTypeDefinition),
	Procedure(RawProcedureDefinition),
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

#[salsa::accumulator]
pub struct Diagnostic(String);
