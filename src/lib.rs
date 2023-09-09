// http://adam.chlipala.net/cpdt/html/Universes.html
use std::collections::{HashMap};

pub mod ast;
use ast::*;

pub mod parser;

// TODO at some point this will be some kind of id to an interned string, therefore Copy
pub type Ident = String;
// a simple identifier can refer either to some global item with a path like a type or function (types and functions defined inside a block of statements are similar to this, but don't have a "path" in the strict sense since they aren't accessible from the outside)
// or a mere local variable
#[derive(Debug, Clone)]
pub struct Scope<'a> {
	scope: HashMap<&'a Ident, ScopeItem<'a>>,
}

// TODO should probably manually implement PartialEq in terms of pointer equality (std::ptr::eq)
#[derive(Debug, PartialEq, Clone)]
pub enum ScopeItem<'a> {
	// Module(Module),
	Type(&'a TypeDefinition),
	Procedure(&'a ProcedureDefinition),
	// Prop(PropDefinition),
	// Theorem(TheoremDefinition),
	// Local(Term),
	Data(Data),
	Placeholder,
}

trait DebugDisplay {
	fn debug_display(&self) -> String;
}

impl<'a> DebugDisplay for ScopeItem<'a> {
	fn debug_display(&self) -> String {
		match self {
			ScopeItem::Type(type_definition) => type_definition.name.clone(),
			ScopeItem::Procedure(procedure_definition) => procedure_definition.name.clone(),
			// ScopeItem::Prop(PropDefinition),
			// ScopeItem::Theorem(TheoremDefinition),
			// ScopeItem::Local(Term),
			ScopeItem::Data(data) => format!("{}.{}{}", data.type_path, data.name, data.body.debug_display()),
			ScopeItem::Placeholder => unimplemented!(),
		}
	}
}

#[derive(Debug, PartialEq, Clone)]
pub struct Data {
	pub name: String,
	pub type_path: String,
	pub body: Body,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Body {
	NotConstructed,
	Unit,
	// Tuple,
	// Record,
}

impl DebugDisplay for Body {
	fn debug_display(&self) -> String {
		"".into()
	}
}

impl<'a> Scope<'a> {
	pub fn new() -> (Scope<'a>, Ctx) {
		(Scope{ scope: HashMap::new() }, Ctx{ errors: Vec::new(), debug_trace: Vec::new() })
	}

	pub fn from<const N: usize>(pairs: [(&'a Ident, ScopeItem<'a>); N]) -> (Scope<'a>, Ctx) {
		(Scope{ scope: HashMap::from(pairs) }, Ctx{ errors: Vec::new(), debug_trace: Vec::new() })
	}

	pub fn checked_insert(&mut self, ctx: &mut Ctx, ident: &'a Ident, scope_item: ScopeItem<'a>) -> Option<()> {
		match self.scope.insert(ident, scope_item) {
			Some(_) => {
				ctx.add_error(format!("name {ident} has already been used"));
				None
			},
			None => Some(()),
		}
	}

	pub fn type_check_module(&mut self, ctx: &mut Ctx, module_items: &'a Vec<ModuleItem>) {
		for module_item in module_items {
			self.name_pass_type_check_module_item(ctx, module_item);
		}

		for module_item in module_items {
			self.main_pass_type_check_module_item(ctx, module_item);
		}
	}

	pub fn name_pass_type_check_module_item(&mut self, ctx: &mut Ctx, module_item: &'a ModuleItem) {
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

	pub fn main_pass_type_check_module_item(&self, ctx: &mut Ctx, module_item: &ModuleItem) {
		match module_item {
			ModuleItem::Type(type_definition) => {
				self.type_check_type_definition(ctx, type_definition);
			},
			ModuleItem::Procedure(procedure_definition) => {
				self.type_check_procedure_definition(ctx, procedure_definition);
			},
			ModuleItem::Debug(debug_statement) => {
				self.type_check_debug_statement(ctx, debug_statement);
			},
		}
	}

	pub fn type_check_type_definition(&self, _ctx: &mut Ctx, type_definition: &TypeDefinition) {
		match &type_definition.body {
			TypeBody::Unit => {},
			TypeBody::Union { branches } => {
				for _branch in branches {
					// TODO these are just strings now, but there will be work to do soon
				}
			},
		}
	}
	pub fn type_check_procedure_definition(&self, ctx: &mut Ctx, procedure_definition: &'a ProcedureDefinition) {
		let mut procedure_scope = self.clone();
		procedure_scope.type_check_parameters(ctx, &procedure_definition.parameters);
		let statements_type = procedure_scope.type_check_statements(ctx, &procedure_definition.statements);
		let return_type = self.checked_get(ctx, &procedure_definition.return_type);

		match (statements_type, return_type) {
			(Some(statements_type), Some(return_type)) => {
				self.checked_assignable_to(ctx, &statements_type, return_type);
			},
			_ => {},
		}
	}

	pub fn type_check_parameters(&mut self, ctx: &mut Ctx, parameters: &'a Vec<(String, String)>) {
		for (param_name, param_type) in parameters {
			let param_type = self.checked_get(ctx, param_type).unwrap_or(&ScopeItem::Placeholder).clone();
			self.checked_insert(ctx, param_name, param_type);
		}
	}

	pub fn type_check_statements(&mut self, ctx: &mut Ctx, statements: &Vec<Statement>) -> Option<ScopeItem<'a>> {
		let mut statements_type = None;
		for statement in statements {
			statements_type = self.type_check_term(ctx, statement);
		}
		statements_type
	}
	pub fn reduce_statements(&mut self, ctx: &mut Ctx, statements: &Vec<Statement>) -> Option<ScopeItem<'a>> {
		let mut current_item = None;
		for statement in statements {
			current_item = Some(self.reduce_term(ctx, statement)?);
		}
		current_item
	}

	pub fn checked_assignable_to(&self, ctx: &mut Ctx, proposed: &ScopeItem<'a>, demanded: &ScopeItem<'a>) {
		// TODO this will be more complicated, but for now it's just equality
		if *proposed == ScopeItem::Placeholder || *demanded == ScopeItem::Placeholder {
			return;
		}
		if proposed != demanded {
			ctx.add_error(format!("{} isn't assignable to {}", proposed.debug_display(), demanded.debug_display()));
		}
	}

	pub fn type_check_debug_statement(&self, ctx: &mut Ctx, debug_statement: &DebugStatement) -> Option<()> {
		self.type_check_term(ctx, &debug_statement.term)?;
		// TODO this probably actually deserves an unwrap/panic, reduction should always work after type checking
		// let item = self.reduce_term(ctx, &debug_statement.term)?;
		// ctx.debug_trace.push(format!("{:?}", item));
		Some(())
	}

	pub fn type_check_term(&self, ctx: &mut Ctx, term: &Term) -> Option<ScopeItem<'a>> {
		match term {
			Term::Lone(ident) => {
				Some(self.checked_get(ctx, ident)?.clone())
			},
			Term::Chain(first, chain_items) => {
				let mut current_type = self.checked_get(ctx, first)?.clone();
				for chain_item in chain_items {
					match chain_item {
						ChainItem::Access(path) => {
							current_type = self.type_check_access_path(ctx, &current_type, path)?;
						},
						ChainItem::Call { arguments } => {
							let argument_types = arguments.iter().map(|arg| self.type_check_term(ctx, arg)).collect::<Option<_>>()?;
							current_type = self.type_check_call(ctx, &current_type, argument_types)?;
						},
					}
				}

				Some(current_type)
			},
			Term::Match { discriminant, arms } => {
				let discriminant_type = self.type_check_term(ctx, discriminant)?;
				// make sure discriminant_type is always assignable to the patterns,
				// and that all the arms have the same inferred type, which is difficult because it's more about universal assignability
				let mut arm_types = Vec::new();
				for MatchArm { pattern, statement } in arms {
					self.type_check_pattern_matches(ctx, pattern, &discriminant_type);
					let arm_type = self.type_check_term(ctx, statement);
					arm_types.push(arm_type);
				}

				// TODO also have to make sure all branches are covered by the arms

				let arm_types: Vec<_> = arm_types.into_iter().collect::<Option<_>>()?;
				// if there aren't any arm_types then either arms were ill-typed or there aren't any arms,
				// which either means
				// - the arms don't cover the type and *that* will be an error
				// - the type is empty, in which case TODO what should we do here? there won't be any errors, because we won't check for assignability to anything, but we also won't have a type to return
				// honestly this entire function will just change in the future, since we'll probably accept some suggested inferred type or something
				// which means that matches over empty types will just be allowed to infer to whatever was inferred from the outside of this function
				let (first_arm_type, rest_arm_types) = arm_types.split_first()?;
				for rest_arm_type in rest_arm_types {
					self.checked_assignable_to(ctx, rest_arm_type, first_arm_type);
				}

				Some(first_arm_type.clone())
			},
		}
	}
	pub fn reduce_term(&self, ctx: &mut Ctx, term: &Term) -> Option<ScopeItem<'a>> {
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
					if self.test_pattern_matches(ctx, pattern, &discriminant) {
						return self.reduce_term(ctx, statement);
					}
				}
				None
			},
		}
	}

	pub fn type_check_pattern_matches(&self, ctx: &mut Ctx, pattern: &Term, discriminant_type: &ScopeItem) {
		// this pattern matching code will be one of the most complicated parts of the entire language
		// for now, we're just going to go through the arms and reduce everything and check equality
		match pattern {
			Term::Lone(s) if s == "_" => {},
			pattern => {
				if let Some(pattern) = self.type_check_term(ctx, pattern) {
					if pattern != *discriminant_type {
						ctx.add_error(format!("{} isn't a match for {}", pattern.debug_display(), discriminant_type.debug_display()));
					}

				}
			},
		}
	}
	pub fn test_pattern_matches(&self, ctx: &mut Ctx, pattern: &Term, discriminant: &ScopeItem) -> bool {
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

	pub fn type_check_call(&self, ctx: &mut Ctx, item: &ScopeItem<'a>, argument_types: Vec<ScopeItem<'a>>) -> Option<ScopeItem<'a>> {
		match item {
			ScopeItem::Type(type_definition) => {
				// TODO this isn't accurate if the type is a tuple variant
				ctx.add_error(format!("type {} is a type, not a callable", type_definition.name));
				None
			},
			ScopeItem::Procedure(procedure_definition) => {
				// TODO this is one of those situations where incremental compilation will be helpful
				// in the future, we won't in any way recheck this procedure definition,
				// we'll just query for its already checked information and compare that against the arguments
				// that already checked information can potentially be poisoned/placeholder, so we'll just not bother
				let return_type = self.placeholder_get(&procedure_definition.return_type);

				let num_arguments = argument_types.len();
				let num_params = procedure_definition.parameters.len();
				if num_arguments != num_params {
					ctx.add_error(format!("{} takes {} parameters but this call gave {}", procedure_definition.name, num_params, num_arguments));
				}
				else {
					for (arg_type, (_, param_type)) in std::iter::zip(argument_types.into_iter(), procedure_definition.parameters.iter()) {
						let param_type = self.placeholder_get(param_type);
						self.checked_assignable_to(ctx, &arg_type, param_type);
					}
				}
				Some(return_type.clone())
			},
			// TODO look up original type definition, and use to build a body of type tuple
			ScopeItem::Data(_data) => unimplemented!(),
			ScopeItem::Placeholder => None,
		}
	}
	pub fn checked_call(&self, ctx: &mut Ctx, item: &ScopeItem<'a>, arguments: Vec<ScopeItem<'a>>) -> Option<ScopeItem<'a>> {
		match item {
			ScopeItem::Type(_) => None,
			ScopeItem::Procedure(procedure_definition) => {
				let mut call_scope: Scope<'a> = self.clone();
				for (arg, (param_name, _)) in std::iter::zip(arguments.into_iter(), procedure_definition.parameters.iter()) {
					call_scope.checked_insert(ctx, &param_name, arg)?;
				}
				call_scope.reduce_statements(ctx, &procedure_definition.statements)
			},
			// TODO look up original type definition, and use to build a body of type tuple
			ScopeItem::Data(_data) => unimplemented!(),
			ScopeItem::Placeholder => None,
		}
	}

	pub fn type_check_access_path(&self, ctx: &mut Ctx, item: &ScopeItem<'a>, path: &Ident) -> Option<ScopeItem<'a>> {
		match item {
			ScopeItem::Type(type_definition) => {
				// look through the type_definition to see if it has a constructor with this name
				match &type_definition.body {
					TypeBody::Unit => {
						ctx.add_error(format!("can't access property {path} on unit type {}", type_definition.name));
						None
					},
					TypeBody::Union{ branches } => {
						branches.iter().find(|b| b == &path)?;
						Some(ScopeItem::Type(type_definition))
					},
				}
			},
			ScopeItem::Procedure(procedure_definition) => {
				ctx.add_error(format!("can't access property {path} on procedure {}", procedure_definition.name));
				None
			},
			ScopeItem::Data(_) => unimplemented!(),
			ScopeItem::Placeholder => None,
		}
	}
	pub fn checked_access_path(&self, _ctx: &mut Ctx, item: &ScopeItem<'a>, path: &Ident) -> Option<ScopeItem<'a>> {
		match item {
			ScopeItem::Type(type_definition) => {
				match &type_definition.body {
					TypeBody::Unit => None,
					TypeBody::Union{ branches } => {
						let branch = branches.iter().find(|b| b == &path)?;
						// TODO body will get more complex as the nature of a branch gets more complex
						Some(ScopeItem::Data(Data{ type_path: type_definition.name.clone(), name: branch.clone(), body: Body::Unit }))
					},
				}
			},
			ScopeItem::Procedure(_) => None,
			ScopeItem::Placeholder => None,
			data => Some(data.clone()),
		}
	}

	pub fn placeholder_get<'s>(&'s self, ident: &Ident) -> &'s ScopeItem<'a> {
		self.scope.get(ident).unwrap_or(&ScopeItem::Placeholder)
	}

	pub fn checked_get<'s>(&'s self, ctx: &mut Ctx, ident: &Ident) -> Option<&'s ScopeItem<'a>> {
		match self.scope.get(ident) {
			None => {
				ctx.add_error(format!("{ident} can't be found"));
				None
			},
			item => item,
		}
	}

	// pub fn checked_exists(arg: Type) -> RetType {
	// 	unimplemented!()
	// }
}

#[derive(Debug)]
pub struct Ctx {
	pub errors: Vec<String>,
	pub debug_trace: Vec<String>,
}

impl Ctx {
	pub fn add_error(&mut self, error: String) {
		self.errors.push(error);
	}
	pub fn add_debug(&mut self, debug: String) {
		self.debug_trace.push(debug);
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn basic_type_errors() {
		let i = r#"
			type Day;
				| Monday
				| Tuesday
				| Wednesday
				| Thursday
				| Friday
				| Saturday
				| Sunday

			type Bool;
				| True
				| False
		"#;
		let (remaining, module_items) = parser::parse_file_with_indentation(3, i).unwrap();
		assert_eq!(remaining, "");
		let (mut scope, mut ctx) = Scope::new();
		scope.type_check_module(&mut ctx, &module_items);
		assert!(ctx.errors.is_empty());

		for (input, expected_errors) in [
			(r#"
				proc same_day(d: Nope): Day;
					d
			"#, vec!["Nope can't be found"]),
			(r#"
				proc same_day(d: Day): Nope;
					d
			"#, vec!["Nope can't be found"]),
			(r#"
				proc same_day(a: Day): Day;
					d
			"#, vec!["d can't be found"]),
			(r#"
				proc same_day(d: Day): Day;
					a
			"#, vec!["a can't be found"]),
			(r#"
				proc same_day(): Day;
					d
			"#, vec!["d can't be found"]),
			(r#"
				proc same_day(d: Day, d: Day): Day;
					d
			"#, vec!["name d has already been used"]),
			(r#"
				proc same_day(d: Day): Day;
					d
				proc same_day(d: Day): Day;
					d
			"#, vec!["name same_day has already been used"]),
			(r#"
				proc same_day(d: Day, b: Bool): Day;
					b
			"#, vec!["Bool isn't assignable to Day"]),
			(r#"
				proc same_day(d: Day, b: Bool): Bool;
					d
			"#, vec!["Day isn't assignable to Bool"]),
			(r#"
				proc same_day(d: Day, b: Bool): Bool;
					match d;
						Day.Monday => Day.Monday
						_ => Day.Monday
			"#, vec!["Day isn't assignable to Bool"]),
			(r#"
				proc same_day(d: Day, b: Bool): Day;
					match d;
						Bool.True => Day.Monday
						_ => Day.Monday
			"#, vec!["Bool isn't a match for Day"]),
			(r#"
				proc same_day(d: Day, b: Bool): Day;
					match b;
						Day.Monday => Day.Monday
						_ => Day.Tuesday
			"#, vec!["Day isn't a match for Bool"]),
			(r#"
				proc bool_negate(b: Bool): Day;
					match b;
						Bool.True => Bool.False
						Bool.False => Bool.True
			"#, vec!["Bool isn't assignable to Day"]),
		] {
			let (remaining, module_items) = parser::parse_file_with_indentation(4, input).unwrap();
			assert_eq!(remaining, "");

			let mut loop_scope = scope.clone();
			loop_scope.type_check_module(&mut ctx, &module_items);
			assert_eq!(ctx.errors, expected_errors);
			ctx.errors.clear();
		}
	}

	#[test]
	fn foundations_day_of_week() {
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
		let (remaining, module_items) = parser::parse_file_with_indentation(3, i).unwrap();
		assert_eq!(remaining, "");

		let (mut scope, mut ctx) = Scope::new();
		scope.type_check_module(&mut ctx, &module_items);
		assert!(ctx.errors.is_empty());
		assert!(ctx.debug_trace.is_empty());

		let term = parser::parse_expression(0, "Day").unwrap().1;
		assert_eq!(scope.reduce_term(&mut ctx, &term).unwrap(), *scope.scope.get(&"Day".to_string()).unwrap());
		assert!(ctx.errors.is_empty());

		fn make_day(day: &str) -> ScopeItem {
			ScopeItem::Data(Data{ name: day.into(), type_path: "Day".into(), body: Body::Unit })
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
		// let (remaining, proof_items) = parser::parse_file_with_indentation(3, i).unwrap();
		// assert_eq!(remaining, "");

		// scope.type_check_module(&mut ctx, &proof_items);
		// assert!(ctx.errors.is_empty());
		// assert!(ctx.debug_trace.is_empty());


		// let i = r#"
		// 	debug next_weekday(Day.Friday)
		// 	debug next_weekday(next_weekday(Day.Saturday))
		// "#;
		// let (remaining, debug_items) = parser::parse_file_with_indentation(3, i).unwrap();
		// assert_eq!(remaining, "");

		// scope.type_check_module(&mut ctx, &debug_items);
		// assert!(ctx.errors.is_empty());
		// assert_eq!(ctx.debug_trace, vec!["Day.Monday", "Day.Tuesday"]);
	}
}
