use self::{Instruction::*, Value::*};
use anyhow::Error;
use inkwell::{context::Context, types::IntType, values::IntValue};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete,
    combinator::map,
    multi::separated_list0,
    sequence::{preceded, tuple},
    Finish, IResult,
};
use ocaml_interop::{
    impl_conv_ocaml_variant, ocaml_export, OCaml, OCamlInt, OCamlList, OCamlRef, ToOCaml,
};
use std::{collections::HashMap, fs::read, path::Path, str::from_utf8};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value {
    Const(i32),
    Ref(i32),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Instruction {
    Return(Value),
    Add(i32, Value, Value),
}

impl_conv_ocaml_variant! {
    Value {
        Const(v: OCamlInt),
        Ref(r: OCamlInt),
    }
}

impl_conv_ocaml_variant! {
    Instruction {
        Return(v: Value),
        Add( result: OCamlInt, op1: Value, op2: Value ),
    }
}

pub fn parse_file(filename: &str) -> Result<Vec<Instruction>, Error> {
    parse(from_utf8(read(filename)?.as_slice())?)
}

fn parse(i: &str) -> Result<Vec<Instruction>, Error> {
    // eg:
    //   %0 = 1 + 1
    //   %1 = %0 + 1
    //   return %1
    Ok(separated_list0(tag("\n"), instruction)(i)
        .map_err(|err| err.to_owned())
        .finish()
        .map(|x| x.1)?)
}

fn constant(i: &str) -> IResult<&str, i32> {
    // eg. 42
    complete::i32(i)
}

fn reference(i: &str) -> IResult<&str, i32> {
    // eg. %2
    preceded(tag("%"), complete::i32)(i)
}

fn value(i: &str) -> IResult<&str, Value> {
    alt((map(constant, Const), map(reference, Ref)))(i)
}

fn add(i: &str) -> IResult<&str, Instruction> {
    // eg. %1 = 3 + %0
    map(
        tuple((reference, tag(" = "), value, tag(" + "), value)),
        |(result, _, op1, _, op2)| Add(result, op1, op2),
    )(i)
}

fn ret(i: &str) -> IResult<&str, Instruction> {
    // eg. return 4
    map(preceded(tag("return "), value), Return)(i)
}

fn instruction(i: &str) -> IResult<&str, Instruction> {
    alt((add, ret))(i)
}

pub fn render<P: AsRef<Path>>(instructions: &[Instruction], to: P) {
    let context = Context::create();
    let module = context.create_module("lab");
    let builder = context.create_builder();

    let i32_type = context.i32_type();
    let fn_type = i32_type.fn_type(&[], false);
    let function = module.add_function("main", fn_type, None);
    let basic_block = context.append_basic_block(function, "doit");

    builder.position_at_end(basic_block);

    let mut env = (HashMap::new(), i32_type);
    fn val<'ctx>(env: &(HashMap<i32, IntValue<'ctx>>, IntType<'ctx>), v: Value) -> IntValue<'ctx> {
        match v {
            Const(i) => env.1.const_int(i as u64, false),
            Ref(r) => *env.0.get(&r).unwrap(),
        }
    }

    for instruction in instructions {
        match instruction {
            Return(v) => {
                builder.build_return(Some(&val(&env, *v)));
                break;
            }
            Add(result, op1, op2) => {
                let a = val(&env, *op1);
                let b = val(&env, *op2);
                env.0.insert(*result, builder.build_int_add(a, b, ""));
            }
        }
    }

    module.write_bitcode_to_path(to.as_ref());
}

pub fn magmide(filename: &str) -> Result<Vec<Instruction>, Error> {
    let prog = parse_file(filename)?;
    render(&prog, Path::new(filename).with_extension("bc"));
    Ok(prog)
}

ocaml_export! {
    fn rust_parse(cr, expr: OCamlRef<String>) -> OCaml<Result<OCamlList<Instruction>, String>> {
        let expr: String = expr.to_rust(&cr);
        parse(expr.as_str()).map_err(|err| format!("{:#}", err)).to_ocaml(cr)
    }

    fn rust_parse_file(cr, filename: OCamlRef<String>) -> OCaml<Result<OCamlList<Instruction>, String>> {
        let filename: String = filename.to_rust(&cr);
        parse_file(filename.as_str()).map_err(|err| format!("{:#}", err)).to_ocaml(cr)
    }

    fn rust_magmide(cr, filename: OCamlRef<String>) -> OCaml<Result<OCamlList<Instruction>, String>> {
        let filename: String = filename.to_rust(&cr);
        magmide(filename.as_str()).map_err(|err| format!("{:#}", err)).to_ocaml(cr)
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

    test_parse!(noop, "", Ok(vec![]));
    test_parse!(four, "return 4", Ok(vec![Return(Const(4))]));
    test_parse!(
        plus,
        "%0 = 2 + 3\nreturn %0",
        Ok(vec![Add(0, Const(2), Const(3)), Return(Ref(0))])
    );
    test_parse!(
        nest_plus,
        "%0 = 2 + 3
%1 = 1 + %0
%2 = %1 + 4
%3 = 0 + %2
return %3",
        Ok(vec![
            Add(0, Const(2), Const(3)),
            Add(1, Const(1), Ref(0)),
            Add(2, Ref(1), Const(4)),
            Add(3, Const(0), Ref(2)),
            Return(Ref(3)),
        ])
    );

    #[test]
    fn from_file() {
        assert_eq!(err_to_string(fs::write("test.mg", b"return 0")), Ok(()));
        let result = err_to_string(parse_file("test.mg"));
        assert_eq!(err_to_string(fs::remove_file("test.mg")), Ok(()));
        assert_eq!(result, Ok(vec![Return(Const(0))]));
    }
}
