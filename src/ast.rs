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
pub enum Ast {
	TypeDefinition {
		name: String,
		body: TypeBody,
	},
}
