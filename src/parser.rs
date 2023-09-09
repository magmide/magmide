// https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
// https://github.com/rust-analyzer/rowan
// https://github.com/salsa-rs/salsa

// https://github.com/rust-bakery/nom
// https://tfpk.github.io/nominomicon/chapter_1.html
// https://crates.io/crates/nom-peg

use nom::{
	bytes::complete::{tag, take_while, take_while1},
	character::{complete::{tab, newline, char as c}},
	branch::alt,
	combinator::{opt, map, all_consuming},
	multi::{count, many0, many1, separated_list0, separated_list1},
	sequence::{preceded, delimited, separated_pair, terminated, tuple},
	// Finish,
	IResult,
};
use crate::ast::*;


pub type DiscardingResult<T> = Result<T, nom::Err<nom::error::Error<T>>>;

fn is_underscore(chr: char) -> bool {
	chr == '_'
}
fn is_ident(chr: char) -> bool {
	chr.is_ascii_alphanumeric() || is_underscore(chr)
}
fn is_start_ident(chr: char) -> bool {
	chr.is_ascii_alphabetic() || is_underscore(chr)
}

pub fn parse_ident(i: &str) -> IResult<&str, String> {
	let (i, first) = take_while1(is_start_ident)(i)?;
	let (i, rest) = take_while(is_ident)(i)?;
	Ok((i, format!("{}{}", first, rest)))
}

pub fn parse_branch(_: usize, i: &str) -> IResult<&str, String> {
	let (i, b) = preceded(tag("| "), parse_ident)(i)?;
	Ok((i, b.into()))
}

fn parse_indents(indentation: usize, i: &str) -> IResult<&str, Vec<char>> {
	count(tab, indentation)(i)
}
fn indents(i: &str, indentation: usize) -> DiscardingResult<&str> {
	Ok(parse_indents(indentation, i)?.0)
}
fn parse_newlines(i: &str) -> IResult<&str, Vec<char>> {
	many0(newline)(i)
}
fn newlines(i: &str) -> DiscardingResult<&str> {
	Ok(parse_newlines(i)?.0)
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

pub fn parse_file(i: &str) -> IResult<&str, Vec<ModuleItem>> {
	parse_file_with_indentation(0, i)
}

pub fn parse_file_with_indentation(indentation: usize, i: &str) -> IResult<&str, Vec<ModuleItem>> {
	all_consuming(
		terminated(
			|i| parse_module_items_with_indentation(indentation, i),
			tuple((parse_newlines, |i| parse_indents(usize::max(indentation - 1, 0), i), parse_newlines)),
		)
	)(i)
}

pub fn parse_module_items(i: &str) -> IResult<&str, Vec<ModuleItem>> {
	parse_module_items_with_indentation(0, i)
}

pub fn parse_module_items_with_indentation(indentation: usize, i: &str) -> IResult<&str, Vec<ModuleItem>> {
	separated_list1(many1(newline), |i| parse_module_item(indentation, i))(i)
}

pub fn parse_module_item(indentation: usize, i: &str) -> IResult<&str, ModuleItem> {
	let i = newlines(i)?;
	let i = indents(i, indentation)?;

	alt((
		map(|i| parse_type_definition(indentation, i), ModuleItem::Type),
		map(|i| parse_procedure_definition(indentation, i), ModuleItem::Procedure),
		map(|i| parse_debug_statement(indentation, i), ModuleItem::Debug),
	))(i)
}

pub fn parse_type_definition(indentation: usize, i: &str) -> IResult<&str, TypeDefinition> {
	let (i, name) = preceded(tag("type "), parse_ident)(i)?;
	let here_branch = |i| indented_block(indentation, i, parse_branch);
	let (i, branches) = opt(preceded(c(';'), here_branch))(i)?;
	let body = match branches {
		Some(branches) => TypeBody::Union{ branches },
		None => TypeBody::Unit,
	};

	Ok((i, TypeDefinition{ name: name.into(), body }))
}

pub fn parse_procedure_definition(indentation: usize, i: &str) -> IResult<&str, ProcedureDefinition> {
	let (i, name) = preceded(tag("proc "), parse_ident)(i)?;
	let (i, parameters) = delimited(c('('), parse_parameters, c(')'))(i)?;
	let (i, return_type) = preceded(tag(": "), parse_ident)(i)?;
	let here_statement = |i| indented_block(indentation, i, parse_statement);
	let (i, statements) = preceded(c(';'), here_statement)(i)?;

	Ok((i, ProcedureDefinition{ name: name.into(), parameters, return_type: return_type.into(), statements }))
}

pub fn parse_debug_statement(indentation: usize, i: &str) -> IResult<&str, DebugStatement> {
	let (i, term) = preceded(tag("debug "), |i| parse_term(indentation, i))(i)?;
	Ok((i, DebugStatement{ term }))
}

// fn parse_parameters(indentation: usize) -> impl Fn(&str) -> IResult<&str, ModuleItem> {
pub fn parse_parameters(i: &str) -> IResult<&str, Vec<(String, String)>> {
	separated_list0(tag(", "), parse_parameter)(i)
}
pub fn parse_parameter(i: &str) -> IResult<&str, (String, String)> {
	separated_pair(parse_ident, tag(": "), parse_ident)(i)
}

pub fn parse_statement(indentation: usize, i: &str) -> IResult<&str, Term> {
	parse_term(indentation, i)
}

pub fn parse_term(indentation: usize, i: &str) -> IResult<&str, Term> {
	alt((
		|i| parse_match(indentation, i),
		|i| parse_expression(indentation, i),
	))(i)
}

pub fn parse_match(indentation: usize, i: &str) -> IResult<&str, Term> {
	// TODO need to figure out how to use the full parse_term for the discriminant
	let (i, discriminant) = delimited(tag("match "), |i| parse_expression(indentation, i), c(';'))(i)?;
	let (i, arms) = indented_block(indentation, i, parse_match_arm)?;

	Ok((i, Term::Match{ discriminant: discriminant.into(), arms }))
}

pub fn parse_match_arm(indentation: usize, i: &str) -> IResult<&str, MatchArm> {
	let here_term = |i| parse_term(indentation, i);
	let (i, (pattern, statement)) = separated_pair(here_term, tag(" => "), here_term)(i)?;
	Ok((i, MatchArm{ pattern, statement }))
}

// pub fn parse_pattern(i: &str) -> IResult<&str, Pattern> {
pub fn parse_pattern(i: &str) -> IResult<&str, String> {
	parse_ident(i)
}

pub fn parse_expression(indentation: usize, i: &str) -> IResult<&str, Term> {
	let (i, first) = parse_ident(i)?;
	let (i, rest) = many0(|i| parse_chain_item(indentation, i))(i)?;
	let term =
		if rest.len() == 0 { Term::Lone(first) }
		else { Term::Chain(first, rest) };
	Ok((i, term))
}

pub fn parse_chain_item(indentation: usize, i: &str) -> IResult<&str, ChainItem> {
	alt((
		map(preceded(c('.'), parse_ident), ChainItem::Access),
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
			Term::Match{ discriminant: Box::new(Term::Lone("d".into())), arms: vec![
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
			TypeDefinition{
				name: "Day".into(),
				body: TypeBody::Union{ branches: vec!["Monday".into(), "Tuesday".into()] },
			},
		);
	}

	#[test]
	fn test_parse_procedure() {
		let i = r#"
			proc same_day(d: Day): Day;
				d
		"#.trim();
		assert_eq!(
			parse_procedure_definition(3, i).unwrap().1,
			ProcedureDefinition{
				name: "same_day".into(), parameters: vec![("d".into(), "Day".into())],
				return_type: "Day".into(), statements: vec![Term::Lone("d".into())],
			},
		);

		let i = r#"
			proc same_day(): Day;
				d
		"#.trim();
		assert_eq!(
			parse_procedure_definition(3, i).unwrap().1,
			ProcedureDefinition{
				name: "same_day".into(), parameters: vec![],
				return_type: "Day".into(), statements: vec![Term::Lone("d".into())],
			},
		);
	}

	#[test]
	fn test_parse_debug_statement() {
		let i = r#"
			debug next_weekday(next_weekday(d))
		"#.trim();
		assert_eq!(
			parse_debug_statement(3, i).unwrap().1,
			DebugStatement{
				term: Term::Chain("next_weekday".into(), vec![ChainItem::Call{ arguments: vec![
					Term::Chain("next_weekday".into(), vec![ChainItem::Call{ arguments: vec![make_lone("d")] }]),
				]}]),
			},
		);
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
