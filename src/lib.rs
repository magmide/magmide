// https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
// http://adam.chlipala.net/cpdt/html/Universes.html
// https://github.com/rust-analyzer/rowan
// https://github.com/salsa-rs/salsa

// https://github.com/rust-bakery/nom
// https://tfpk.github.io/nominomicon/chapter_1.html
// https://crates.io/crates/nom-peg

use nom::{
	bytes::complete::{tag, take_while, take_while1},
	character::{complete::{tab, newline, char as c}},
	branch::alt,
	combinator::{opt, map},
	multi::{count, many0, many1, separated_list0, separated_list1},
	sequence::{preceded, delimited, separated_pair, /*tuple*/},
	// Finish,
	IResult,
};
pub mod ast;
use ast::*;

type DiscardingResult<T> = Result<T, nom::Err<nom::error::Error<T>>>;

fn is_underscore(chr: char) -> bool {
	chr == '_'
}
fn is_ident(chr: char) -> bool {
	chr.is_ascii_alphanumeric() || is_underscore(chr)
}
fn is_start_ident(chr: char) -> bool {
	chr.is_ascii_alphabetic() || is_underscore(chr)
}

fn ident(i: &str) -> IResult<&str, String> {
	let (i, first) = take_while1(is_start_ident)(i)?;
	let (i, rest) = take_while(is_ident)(i)?;
	Ok((i, format!("{}{}", first, rest)))
}

fn parse_branch(_: usize, i: &str) -> IResult<&str, String> {
	let (i, b) = preceded(tag("| "), ident)(i)?;
	Ok((i, b.into()))
}

fn indents(i: &str, indentation: usize) -> DiscardingResult<&str> {
	Ok(count(tab, indentation)(i)?.0)
}
fn newlines(i: &str) -> DiscardingResult<&str> {
	Ok(many0(newline)(i)?.0)
}

fn indented_line<T>(indentation: usize, i: &str, line_parser: fn(usize, &str) -> IResult<&str, T>) -> IResult<&str, T> {
	let i = indents(i, indentation)?;
	line_parser(indentation, i)
}

fn indented_block<T>(indentation: usize, i: &str, line_parser: fn(usize, &str) -> IResult<&str, T>) -> IResult<&str, Vec<T>> {
	let indentation = indentation + 1;
	let i = newlines(i)?;
	let (i, items) = separated_list1(many1(newline), |i| indented_line(indentation, i, line_parser))(i)?;

	Ok((i, items))
}

fn parse_input(i: &str) -> IResult<&str, Vec<ModuleItem>> {
	separated_list1(many1(newline), |i| parse_module_item(0, i))(i)
}

fn parse_input_with_indentation(indentation: usize, i: &str) -> IResult<&str, Vec<ModuleItem>> {
	separated_list1(many1(newline), |i| parse_module_item(indentation, i))(i)
}

fn parse_module_item(indentation: usize, i: &str) -> IResult<&str, ModuleItem> {
	let i = newlines(i)?;
	let i = indents(i, indentation)?;

	alt((
		|i| parse_type_definition(indentation, i),
		|i| parse_procedure_definition(indentation, i),
		|i| parse_debug(indentation, i),
	))(i)
}

fn parse_type_definition(indentation: usize, i: &str) -> IResult<&str, ModuleItem> {
	let (i, name) = preceded(tag("type "), ident)(i)?;
	let here_branch = |i| indented_block(indentation, i, parse_branch);
	let (i, branches) = opt(preceded(c(';'), here_branch))(i)?;
	let body = match branches {
		Some(branches) => TypeBody::Union{ branches },
		None => TypeBody::Unit,
	};

	Ok((i, ModuleItem::TypeDefinition{ name: name.into(), body }))
}

fn parse_procedure_definition(indentation: usize, i: &str) -> IResult<&str, ModuleItem> {
	let (i, name) = preceded(tag("proc "), ident)(i)?;
	let (i, parameters) = delimited(c('('), parse_parameters, c(')'))(i)?;
	let (i, return_type) = preceded(tag(": "), ident)(i)?;
	let here_statement = |i| indented_block(indentation, i, parse_statement);
	let (i, statements) = preceded(c(';'), here_statement)(i)?;

	Ok((i, ModuleItem::ProcedureDefinition{ name: name.into(), parameters, return_type: return_type.into(), statements }))
}

fn parse_debug(indentation: usize, i: &str) -> IResult<&str, ModuleItem> {
	map(preceded(tag("debug "), |i| parse_term(indentation, i)), ModuleItem::Debug)(i)
}

// fn parse_parameters(indentation: usize) -> impl Fn(&str) -> IResult<&str, ModuleItem> {
fn parse_parameters(i: &str) -> IResult<&str, Vec<(String, String)>> {
	separated_list1(tag(", "), parse_parameter)(i)
}
fn parse_parameter(i: &str) -> IResult<&str, (String, String)> {
	separated_pair(ident, tag(": "), ident)(i)
}

fn parse_statement(indentation: usize, i: &str) -> IResult<&str, Term> {
	parse_term(indentation, i)
}

fn parse_term(indentation: usize, i: &str) -> IResult<&str, Term> {
	alt((
		|i| parse_match(indentation, i),
		|i| parse_expression(indentation, i),
	))(i)
}

fn parse_match(indentation: usize, i: &str) -> IResult<&str, Term> {
	let (i, discriminant) = delimited(tag("match "), parse_pattern, c(';'))(i)?;
	println!("past match");
	let (i, arms) = indented_block(indentation, i, parse_match_arm)?;
	println!("past arms");

	Ok((i, Term::Match{ discriminant: discriminant.into(), arms }))
}

fn parse_match_arm(indentation: usize, i: &str) -> IResult<&str, MatchArm> {
	println!("in match arm");
	let here_term = |i| parse_term(indentation, i);
	let (i, (pattern, statement)) = separated_pair(here_term, tag(" => "), here_term)(i)?;
	println!("past statement");
	Ok((i, MatchArm{ pattern, statement }))
}

// fn parse_pattern(i: &str) -> IResult<&str, Pattern> {
fn parse_pattern(i: &str) -> IResult<&str, String> {
	ident(i)
}

fn parse_expression(indentation: usize, i: &str) -> IResult<&str, Term> {
	let (i, first) = ident(i)?;
	let (i, rest) = many0(|i| chain_item(indentation, i))(i)?;
	let term =
		if rest.len() == 0 { Term::Lone(first) }
		else { Term::Chain(first, rest) };
	Ok((i, term))
}

fn chain_item(indentation: usize, i: &str) -> IResult<&str, ChainItem> {
	alt((
		map(preceded(c('.'), ident), ChainItem::Access),
		map(
			delimited(c('('), separated_list0(tag(", "), |i| parse_expression(indentation, i)), c(')')),
			|arguments| ChainItem::Call{ arguments },
		),
	))(i)
}

#[cfg(test)]
mod tests {
	use super::*;

	fn make_lone(s: &str) -> Term {
		Term::Lone(s.into())
	}
	fn make_day(day: &str) -> Term {
		Term::Chain("Day".into(), vec![ChainItem::Access(day.into())])
	}

	#[test]
	fn test_parse_expression() {
		let i = "Day.Monday";
		assert_eq!(
			parse_expression(0, i).unwrap().1,
			make_day("Monday"),
		);

		let i = "fn(next, hello)";
		assert_eq!(
			parse_expression(0, i).unwrap().1,
			Term::Chain("fn".into(), vec![ChainItem::Call{ arguments: vec![make_lone("next"), make_lone("hello")] }]),
		);
	}

	#[test]
	fn test_parse_match() {
		let i = r#"
			match d;
				Day.Monday => Day.Tuesday
				Day.Tuesday => Day.Wednesday
		"#.trim();
		assert_eq!(
			parse_match(3, i).unwrap().1,
			Term::Match{ discriminant: "d".into(), arms: vec![
				MatchArm{ pattern: make_day("Monday"), statement: make_day("Tuesday") },
				MatchArm{ pattern: make_day("Tuesday"), statement: make_day("Wednesday") },
			] },
		);
	}

	#[test]
	fn test_parse_type_definition() {
		let i = r#"
			type Day;
				| Monday
				| Tuesday
		"#.trim();
		assert_eq!(
			parse_type_definition(3, i).unwrap().1,
			ModuleItem::TypeDefinition{
				name: "Day".into(),
				body: TypeBody::Union{ branches: vec!["Monday".into(), "Tuesday".into()] },
			},
		);
	}

	#[test]
	fn test_parse_procedure() {
		let i = r#"
			proc dumb(d: Day): Day;
				d
		"#.trim();
		assert_eq!(
			parse_procedure_definition(3, i).unwrap().1,
			ModuleItem::ProcedureDefinition{
				name: "dumb".into(), parameters: vec![("d".into(), "Day".into())],
				return_type: "Day".into(), statements: vec![Term::Lone("d".into())],
			},
		);
	}

	#[test]
	fn test_parse_debug() {
		let i = r#"
			debug next_weekday(next_weekday(d))
		"#.trim();
		assert_eq!(
			parse_debug(3, i).unwrap().1,
			ModuleItem::Debug(
				Term::Chain("next_weekday".into(), vec![ChainItem::Call{ arguments: vec![
					Term::Chain("next_weekday".into(), vec![ChainItem::Call{ arguments: vec![make_lone("d")] }]),
				]}]),
			),
		);
	}

	#[test]
	fn test_parse_foundations_day_of_week() {
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

			debug next_weekday(Day.Friday)
			debug next_weekday(next_weekday(Day.Saturday))
		"#;
		let (remaining, ast) = dbg!(parse_input_with_indentation(3, i)).unwrap();
		assert_eq!(remaining.trim(), "");

		// assert_eq!(ast, Ast::TypeDefinition{ name: "Day".into(), body: TypeBody::Union {
		// 	branches: vec![
		// 		"Monday".into(),
		// 		"Tuesday".into(),
		// 		"Wednesday".into(),
		// 		"Thursday".into(),
		// 		"Friday".into(),
		// 		"Saturday".into(),
		// 		"Sunday".into(),
		// 	]
		// } });
	}
}

// fn deindent_to_base(s: &str) -> String {
// 	let s = s.strip_prefix("\n").unwrap_or(s);
// 	let (s, base_tabs) = match is_a("\t")(s) {
// 		Ok((s, tabs)) => (s, tabs.len()),
// 		Err(_) => { return s.into() },
// 	};


// 	let mut final_s = String::new();
// 	for line in s.split("\n") {
// 		// take base_tabs number of tabs, always expecting
// 	}

// 	s.into()
// }
