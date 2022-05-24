use anyhow::Error;
use inkwell::{builder::Builder, context::Context, types::IntType, values::IntValue};
use nom::{
    branch::alt, bytes::complete::tag, character::complete, combinator::map,
    sequence::separated_pair, Finish, IResult,
};
use ocaml_interop::{impl_conv_ocaml_variant, ocaml_export, OCaml, OCamlInt, OCamlRef, ToOCaml};
use std::{fs::read, str::from_utf8};

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

pub fn parse(filename: &str) -> Result<AST, Error> {
    parse_bytes(from_utf8(read(filename)?.as_slice())?)
}

fn parse_bytes<'a>(i: &'a str) -> Result<AST, Error> {
    Ok(ast(i).map_err(|err| err.to_owned()).finish().map(|x| x.1)?)
}

fn number(i: &str) -> IResult<&str, AST> {
    map(complete::i32, AST::Number)(i)
}

fn add(i: &str) -> IResult<&str, AST> {
    map(separated_pair(ast, tag("+"), ast), |(a, b)| {
        AST::Add(Box::new(a), Box::new(b))
    })(i)
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
    module.write_bitcode_to_path(&std::path::Path::new(to));
}

ocaml_export! {
    fn ocaml_parse(cr, filename: OCamlRef<String>) -> OCaml<Result<AST, String>> {
        let filename: String = filename.to_rust(&cr);
        parse(filename.as_str()).map_err(|err| format!("{:#}", err)).to_ocaml(cr)
    }

    fn ocaml_render(cr, ast: OCamlRef<AST>, to: OCamlRef<String>) {
        let to: String = to.to_rust(&cr);
        render(&ast.to_rust(&cr), to.as_str());
        OCaml::unit()
    }
}
