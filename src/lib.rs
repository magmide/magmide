// https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
// http://adam.chlipala.net/cpdt/html/Universes.html
// https://github.com/rust-analyzer/rowan
// https://github.com/salsa-rs/salsa

// https://github.com/rust-bakery/nom
// https://tfpk.github.io/nominomicon/chapter_1.html
// https://crates.io/crates/nom-peg

use nom::{
	bytes::complete::{tag, take_while, take_while1, is_a},
	// branch::alt,
	character::{complete::{tab, newline}},
	combinator::{opt},
	multi::{count, many0, many1, separated_list1},
	sequence::{preceded, delimited, /*tuple*/},
	// Finish,
	IResult,
};
pub mod ast;
use ast::*;

type DiscardingResult<T> = Result<T, nom::Err<nom::error::Error<T>>>;
type ParseFn<T> = fn(&str) -> IResult<&str, T>;

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

fn branch(i: &str) -> IResult<&str, String> {
	let (i, b) = preceded(tag("| "), ident)(i)?;
	Ok((i, b.into()))
}

fn indents(i: &str, indentation: usize) -> DiscardingResult<&str> {
	Ok(count(tab, indentation)(i)?.0)
}
fn newlines(i: &str) -> DiscardingResult<&str> {
	Ok(many0(newline)(i)?.0)
}

fn indented_line<T>(indentation: usize, item: ParseFn<T>) -> impl Fn(&str) -> IResult<&str, T> {
	move |i| {
		let i = indents(i, indentation)?;
		item(i)
	}
}

fn indented_block<T>(indentation: usize, item: ParseFn<T>) -> impl Fn(&str) -> IResult<&str, Vec<T>> {
	let indentation = indentation + 1;
	move |i| {
		let i = newlines(i)?;
		let (i, items) = separated_list1(many1(newline), indented_line(indentation, item))(i)?;

		Ok((i, items))
	}
}

fn parse_ast(i: &str, indentation: usize) -> IResult<&str, Ast> {
	let i = newlines(i)?;
	let i = indents(i, indentation)?;

	let (i, name) = delimited(tag("type "), ident, tag(" ="))(i)?;
	let (i, branches) = opt(indented_block(indentation, branch))(i)?;
	let body = match branches {
		Some(branches) => TypeBody::Union{ branches },
		None => TypeBody::Unit,
	};

	Ok((i, Ast::TypeDefinition{ name: name.into(), body }))
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn parse_day_of_week() {
		let i = r#"
			type Day =

				| Monday

				| Tuesday
				| Wednesday
				| Thursday
				| Friday

				| Saturday
				| Sunday
		"#;
		let (_i, ast) = dbg!(parse_ast(i, 3).unwrap());

		assert_eq!(ast, Ast::TypeDefinition{ name: "Day".into(), body: TypeBody::Union {
			branches: vec![
				"Monday".into(),
				"Tuesday".into(),
				"Wednesday".into(),
				"Thursday".into(),
				"Friday".into(),
				"Saturday".into(),
				"Sunday".into(),
			]
		} });
	}


	// #[test]
	// fn test_deindent() {
	// 	unimplemented!();
	// }
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
