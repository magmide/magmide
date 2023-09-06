// http://adam.chlipala.net/cpdt/html/Universes.html
use std::collections::HashMap;

pub mod ast;
use ast::*;

pub mod parser;

// TODO at some point this will be some kind of id to an interned string, therefore Copy
type Ident = String;
// a simple identifier can refer either to some global item with a path like a type or function (types and functions defined inside a block of statements are similar to this, but don't have a "path" in the strict sense since they aren't accessible from the outside)
// or a mere local variable
struct Scope<'a> {
	scope: HashMap<&'a Ident, ScopeItem<'a>>,
}

#[derive(Debug, PartialEq, Clone)]
enum ScopeItem<'a> {
	// Module(Module),
	Type(&'a TypeDefinition),
	Procedure(&'a ProcedureDefinition),
	// Prop(PropDefinition),
	// Theorem(TheoremDefinition),
	// Local(Term),
	Data(Constructor),
}

#[derive(Debug, PartialEq, Clone)]
struct Constructor {
	name: String,
	type_path: String,
	construction: Construction,
}

#[derive(Debug, PartialEq, Clone)]
enum Construction {
	NotConstructed,
	Unit,
	// Tuple,
	// Record,
}

impl<'a> Scope<'a> {
	fn new() -> (Scope<'a>, Ctx) {
		(Scope{ scope: HashMap::new() }, Ctx{ errors: Vec::new(), debug_trace: Vec::new() })
	}

	// fn from<const N: usize>(pairs: &[(Ident, ScopeItem); N]) -> Ctx<'a> {
	// 	Ctx { scope: HashMap::from(pairs), errors: Vec::new(), debug_trace: Vec::new() }
	// }

	fn checked_insert(&mut self, ctx: &mut Ctx, ident: &'a Ident, scope_item: ScopeItem<'a>) {
		if let Some(existing_item) = self.scope.insert(ident, scope_item) {
			ctx.add_error(format!("name {ident} has already been used"));
		}
	}

	fn type_check_module(&mut self, ctx: &mut Ctx, module_items: &'a Vec<ModuleItem>) {
		for module_item in module_items {
			self.name_pass_type_check_module_item(ctx, module_item);
		}

		for module_item in module_items {
			self.main_pass_type_check_module_item(ctx, module_item);
		}
	}

	fn name_pass_type_check_module_item(&mut self, ctx: &mut Ctx, module_item: &'a ModuleItem) {
		match module_item {
			ModuleItem::Type(type_definition) => {
				self.checked_insert(ctx, &type_definition.name, ScopeItem::Type(type_definition));
			},
			ModuleItem::Procedure(procedure_definition) => {
				self.checked_insert(ctx, &procedure_definition.name, ScopeItem::Procedure(procedure_definition));
			},
			ModuleItem::Debug(_) => {},
		}
	}

	fn main_pass_type_check_module_item(&self, ctx: &mut Ctx, module_item: &ModuleItem) {
		match module_item {
			ModuleItem::Type(_type_definition) => {
				// self.type_check_type_definition(type_definition);
			},
			ModuleItem::Procedure(_procedure_definition) => {
				// self.type_check_type_definition(procedure_definition);
			},
			ModuleItem::Debug(debug_statement) => {
				self.type_check_debug_statement(ctx, debug_statement);
			},
		}
	}

	fn type_check_debug_statement(&self, ctx: &mut Ctx, debug_statement: &DebugStatement) {
		// self.type_check_term(&debug_statement.term);
		// TODO this probably actually deserves an unwrap/panic, reduction should always work after type checking
		if let Some(item) = self.reduce_term(ctx, &debug_statement.term) {
			ctx.debug_trace.push(format!("{:?}", item));
		}
	}

	// fn type_check_term(&mut self, term: &Term) {
	// 	match term {
	// 		Term::Lone(ident) => {
	// 			unimplemented!();
	// 		},
	// 		Term::Chain(first, rest) => {},
	// 		Term::Match { discriminant, arms } => {},
	// 	}
	// }

	fn reduce_term(&self, ctx: &mut Ctx, term: &Term) -> Option<ScopeItem> {
		let reduced = match term {
			Term::Lone(ident) => {
				self.checked_get(ctx, ident)?.clone()
			},
			Term::Chain(first, chain_items) => {
				let mut current_item = self.checked_get(ctx, first)?.clone();
				for chain_item in chain_items {
					match chain_item {
						ChainItem::Access(path) => {
							current_item = self.checked_access_path(ctx, &current_item, path)?;
						},
						// Call { arguments } => {
						// 	let arguments = arguments.iter().map(|a| self.reduce_term(a)).collect()?;
						// 	current_item = self.checked_call(current_item, arguments)?;
						// },
						_ => unimplemented!(),
					}
				}

				current_item
			},
			// Term::Match { discriminant, arms } => {
			// 	//
			// },
			_ => unimplemented!(),
		};

		Some(reduced)
	}

	fn checked_access_path(&self, ctx: &mut Ctx, item: &ScopeItem, path: &Ident) -> Option<ScopeItem> {
		match item {
			ScopeItem::Type(type_definition) => {
				// look through the type_definition to see if it has a constructor with this name
				match &type_definition.body {
					TypeBody::Unit => {
						ctx.add_error(format!("can't access property {path} on unit type {}", type_definition.name));
						None
					},
					TypeBody::Union{ branches } => {
						let branch = branches.iter().find(|b| b == &path)?;
						Some(ScopeItem::Data(Constructor{ type_path: type_definition.name.clone(), name: branch.clone(), construction: Construction::Unit }))
					},
				}
			},
			ScopeItem::Procedure(procedure_definition) => {
				ctx.add_error(format!("can't access property {path} on procedure {}", procedure_definition.name));
				None
			},
			// ScopeItem::Data(constructor) => {
			// 	//
			// },
			_ => unimplemented!(),
		}
	}

	fn checked_get<'s>(&'s self, ctx: &mut Ctx, ident: &Ident) -> Option<&'s ScopeItem<'a>> {
		match self.scope.get(ident) {
			Some(item) => Some(item),
			None => {
				ctx.add_error(format!("{ident} can't be found"));
				None
			},
		}
	}
}

#[derive(Debug)]
struct Ctx {
	errors: Vec<String>,
	debug_trace: Vec<String>,
}

impl Ctx {
	fn add_error(&mut self, error: String) {
		self.errors.push(error);
	}
	fn add_debug(&mut self, debug: String) {
		self.debug_trace.push(debug);
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_foundations_day_of_week() {
		let i = r#"
			type Day;
				| Monday
				| Tuesday
				| Wednesday
				| Thursday
				| Friday
				| Saturday
				| Sunday

			proc next_weekday(d: Day): Day;
				match d;
					Day.Monday => Day.Tuesday
					Day.Tuesday => Day.Wednesday
					Day.Wednesday => Day.Thursday
					Day.Thursday => Day.Friday
					Day.Friday => Day.Monday
					Day.Saturday => Day.Monday
					Day.Sunday => Day.Monday
		"#;
		let (remaining, module_items) = parser::parse_input_with_indentation(3, i).unwrap();
		assert_eq!(remaining.trim(), "");

		let (mut scope, mut ctx) = Scope::new();
		scope.type_check_module(&mut ctx, &module_items);
		assert!(ctx.errors.is_empty());
		assert!(ctx.debug_trace.is_empty());

		let term = parser::parse_expression(0, "Day").unwrap().1;
		assert_eq!(scope.reduce_term(&mut ctx, &term).unwrap(), *scope.scope.get(&"Day".to_string()).unwrap());
		assert!(ctx.errors.is_empty());

		let term = parser::parse_expression(0, "Day.Monday").unwrap().1;
		assert_eq!(
			scope.reduce_term(&mut ctx, &term).unwrap(),
			ScopeItem::Data(Constructor{ name: "Monday".into(), type_path: "Day".into(), construction: Construction::Unit }),
		);
		assert!(ctx.errors.is_empty());

		// let term = parser::parse_expression(0, "next_weekday(Day.Monday)").unwrap().1;
		// let expected = parser::parse_expression(0, "Day.Tuesday").unwrap().1;
		// assert_eq!(ctx.reduce_term(&mut ctx, &term).unwrap(), expected);
		// assert!(ctx.errors.is_empty());

		// let i = r#"
		// 	debug next_weekday(Day.Friday)
		// 	debug next_weekday(next_weekday(Day.Saturday))
		// "#;
		// let (remaining, debug_items) = parser::parse_input_with_indentation(3, i).unwrap();
		// assert_eq!(remaining.trim(), "");

		// ctx.type_check_module(&debug_items);
		// assert!(ctx.errors.is_empty());
		// assert_eq!(ctx.debug_trace, vec!["Day.Monday", "Day.Tuesday"]);
	}
}
