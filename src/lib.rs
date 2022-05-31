use anyhow::Error;
use inkwell::{builder::Builder, context::Context, types::IntType, values::IntValue};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete,
    combinator::map,
    sequence::{delimited, separated_pair},
    Finish, IResult,
};
use ocaml_interop::{impl_conv_ocaml_variant, ocaml_export, OCaml, OCamlInt, OCamlRef, ToOCaml};
use std::{fs::read, path::Path, str::from_utf8};

#[derive(Debug, PartialEq)]
pub enum AST {
    Add(Box<AST>, Box<AST>),
    Number(i32),
}

impl_conv_ocaml_variant! {
    AST {
        AST::Add(a: AST, b: AST),
        AST::Number(n: OCamlInt),
    }
}

pub fn parse_file(filename: &str) -> Result<AST, Error> {
    parse(from_utf8(read(filename)?.as_slice())?)
}

fn parse<'a>(i: &'a str) -> Result<AST, Error> {
    let x = ast(i).map_err(|err| err.to_owned()).finish().map(|x| x.1)?;
    println!("{:?}", x);
    Ok(x)
    // Ok(ast(i).map_err(|err| err.to_owned()).finish().map(|x| x.1)?)
}

fn number(i: &str) -> IResult<&str, AST> {
    map(complete::i32, AST::Number)(i)
}

fn add(i: &str) -> IResult<&str, AST> {
    map(
        delimited(tag("("), separated_pair(ast, tag(" + "), ast), tag(")")),
        |(a, b)| AST::Add(Box::new(a), Box::new(b)),
    )(i)
}

fn ast(i: &str) -> IResult<&str, AST> {
    alt((number, add))(i)
}

pub fn render(ast: &AST, to: &str) {
    let context = Context::create();
    let module = context.create_module("lab");
    let builder = context.create_builder();

    let i32_type = context.i32_type();
    let fn_type = i32_type.fn_type(&[], false);
    let function = module.add_function("main", fn_type, None);
    let basic_block = context.append_basic_block(function, "doit");

    builder.position_at_end(basic_block);

    fn build<'ctx>(env: (&Builder<'ctx>, IntType<'ctx>), ast: &AST) -> IntValue<'ctx> {
        match ast {
            AST::Number(x) => env.1.const_int(*x as u64, false),
            AST::Add(a, b) => env.0.build_int_add(build(env, a), build(env, b), "sum"),
        }
    }

    builder.build_return(Some(&build((&builder, i32_type), ast)));
    module.write_bitcode_to_path(&Path::new(to));
}

ocaml_export! {
    fn rust_parse(cr, expr: OCamlRef<String>) -> OCaml<Result<AST, String>> {
        let expr: String = expr.to_rust(&cr);
        parse(expr.as_str()).map_err(|err| format!("{:#}", err)).to_ocaml(cr)
    }

    fn rust_parse_file(cr, filename: OCamlRef<String>) -> OCaml<Result<AST, String>> {
        let filename: String = filename.to_rust(&cr);
        parse_file(filename.as_str()).map_err(|err| format!("{:#}", err)).to_ocaml(cr)
    }

    fn rust_render(cr, ast: OCamlRef<AST>, to: OCamlRef<String>) {
        let to: String = to.to_rust(&cr);
        render(&ast.to_rust(&cr), to.as_str());
        OCaml::unit()
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use std::{fmt::Debug, fs};

    fn err_to_string<T, E: Debug>(r: Result<T, E>) -> Result<T, String> {
        r.map_err(|err| format!("{:?}", err))
    }

    macro_rules! test_parse {
        ($name:ident, $in:expr, $out:expr) => {
            #[test]
            fn $name() {
                assert_eq!(err_to_string(parse($in)), $out);
            }
        };
    }

    fn num(n: i32) -> AST {
        AST::Number(n)
    }
    fn add(a: AST, b: AST) -> AST {
        AST::Add(Box::new(a), Box::new(b))
    }

    test_parse!(four, "4", Ok(num(4)));
    test_parse!(plus, "(2 + 3)", Ok(add(num(2), num(3))));
    test_parse!(
        nest_plus,
        "(0 + ((1 + (2 + 3)) + 4))",
        Ok(add(num(0), add(add(num(1), add(num(2), num(3))), num(4))))
    );

    #[test]
    fn from_file() {
        assert_eq!(err_to_string(fs::write("test.mg", b"(1 + 2)")), Ok(()));
        let result = err_to_string(parse_file("test.mg"));
        assert_eq!(err_to_string(fs::remove_file("test.mg")), Ok(()));
        assert_eq!(result, Ok(add(num(1), num(2))));
    }
}
