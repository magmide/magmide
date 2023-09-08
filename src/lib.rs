// http://adam.chlipala.net/cpdt/html/Universes.html
use std::collections::HashMap;

pub mod ast;
use ast::*;

pub mod parser;

// TODO at some point this will be some kind of id to an interned string, therefore Copy
type Ident = String;
// a simple identifier can refer either to some global item with a path like a type or function (types and functions defined inside a block of statements are similar to this, but don't have a "path" in the strict sense since they aren't accessible from the outside)
// or a mere local variable
#[derive(Debug, Clone)]
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

	fn checked_insert(&mut self, ctx: &mut Ctx, ident: &'a Ident, scope_item: ScopeItem<'a>) -> Option<()> {
		match self.scope.insert(ident, scope_item) {
			Some(_) => {
				ctx.add_error(format!("name {ident} has already been used"));
				None
			},
			None => Some(()),
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

	fn reduce_term(&self, ctx: &mut Ctx, term: &Term) -> Option<ScopeItem<'a>> {
		match term {
			Term::Lone(ident) => {
				Some(self.checked_get(ctx, ident)?.clone())
			},
			Term::Chain(first, chain_items) => {
				let mut current_item = self.checked_get(ctx, first)?.clone();
				for chain_item in chain_items {
					match chain_item {
						ChainItem::Access(path) => {
							current_item = self.checked_access_path(ctx, &current_item, path)?;
						},
						ChainItem::Call { arguments } => {
							let arguments = arguments.iter().map(|arg| self.reduce_term(ctx, arg)).collect::<Option<_>>()?;
							current_item = self.checked_call(ctx, &current_item, arguments)?;
						},
					}
				}

				Some(current_item)
			},
			Term::Match { discriminant, arms } => {
				let discriminant = self.reduce_term(ctx, discriminant)?;
				for MatchArm { pattern, statement } in arms {
					if self.pattern_matches(ctx, pattern, &discriminant) {
						return self.reduce_term(ctx, statement);
					}
				}
				None
			},
		}
	}

	fn pattern_matches(&self, ctx: &mut Ctx, pattern: &Term, discriminant: &ScopeItem) -> bool {
		// this pattern matching code will be one of the most complicated parts of the entire language
		// for now, we're just going to go through the arms and reduce everything and check equality
		match pattern {
			Term::Lone(s) if s == "_" => true,
			pattern => {
				if let Some(pattern) = self.reduce_term(ctx, pattern) {
					pattern == *discriminant
				}
				else { false }
			},
		}
	}

	fn reduce_statements(&mut self, ctx: &mut Ctx, statements: &Vec<Term>) -> Option<ScopeItem<'a>> {
		let mut current_item = None;
		for statement in statements {
			current_item = Some(self.reduce_term(ctx, statement)?);
		}
		current_item
	}

	fn checked_call(&self, ctx: &mut Ctx, item: &ScopeItem<'a>, arguments: Vec<ScopeItem<'a>>) -> Option<ScopeItem<'a>> {
		match item {
			ScopeItem::Type(type_definition) => {
				ctx.add_error(format!("type {} is a type, not a callable", type_definition.name));
				None
			},
			ScopeItem::Procedure(procedure_definition) => {
				let mut call_scope: Scope<'a> = self.clone();
				for (arg, (param_name, _)) in std::iter::zip(arguments.into_iter(), procedure_definition.parameters.iter()) {
					call_scope.checked_insert(ctx, &param_name, arg)?;
				}
				call_scope.reduce_statements(ctx, &procedure_definition.statements)
			},
			// TODO look up original type definition, and use to build a construction of type tuple
			// ScopeItem::Data(constructor) => Some(constructor),
			_ => unimplemented!(),
		}
	}

	fn checked_access_path(&self, ctx: &mut Ctx, item: &ScopeItem<'a>, path: &Ident) -> Option<ScopeItem<'a>> {
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
						// TODO construction will get more complex as the nature of a branch gets more complex
						Some(ScopeItem::Data(Constructor{ type_path: type_definition.name.clone(), name: branch.clone(), construction: Construction::Unit }))
					},
				}
			},
			ScopeItem::Procedure(procedure_definition) => {
				ctx.add_error(format!("can't access property {path} on procedure {}", procedure_definition.name));
				None
			},
			data => Some(data.clone()),
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
					_ => Day.Monday

			proc same_day(d: Day): Day;
				d
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

		fn make_day(day: &str) -> ScopeItem {
			ScopeItem::Data(Constructor{ name: day.into(), type_path: "Day".into(), construction: Construction::Unit })
		}

		for (input, expected) in [
			("Day.Monday", "Monday"),
			("same_day(Day.Monday)", "Monday"),
			("next_weekday(Day.Friday)", "Monday"),
			("next_weekday(next_weekday(Day.Friday))", "Tuesday"),
		] {
			let term = parser::parse_expression(0, input).unwrap().1;
			assert_eq!(scope.reduce_term(&mut ctx, &term).unwrap(), make_day(expected));
			assert!(ctx.errors.is_empty());
		}

		// let i = r#"
		// 	prop Eq(@T: type): [T, T];
		// 		(t: T): [t, t]

		// 	thm example_next_weekday: Eq[next_weekday(Day.Saturday), Day.Monday];
		// 		Eq(Day.Monday)

		// 	thm example_next_weekday_cleaner: next_weekday(Day.Saturday) :Eq Day.Monday; _
		// 	thm example_next_weekday_sugar: next_weekday(Day.Saturday) == Day.Monday; _
		// "#;
		// let (remaining, proof_items) = parser::parse_input_with_indentation(3, i).unwrap();
		// assert_eq!(remaining.trim(), "");

		// scope.type_check_module(&mut ctx, &proof_items);
		// assert!(ctx.errors.is_empty());
		// assert!(ctx.debug_trace.is_empty());


		// let i = r#"
		// 	debug next_weekday(Day.Friday)
		// 	debug next_weekday(next_weekday(Day.Saturday))
		// "#;
		// let (remaining, debug_items) = parser::parse_input_with_indentation(3, i).unwrap();
		// assert_eq!(remaining.trim(), "");

		// scope.type_check_module(&mut ctx, &debug_items);
		// assert!(ctx.errors.is_empty());
		// assert_eq!(ctx.debug_trace, vec!["Day.Monday", "Day.Tuesday"]);
	}
}
