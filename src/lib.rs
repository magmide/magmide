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

pub fn emit_to_file<P: AsRef<Path>>(instructions: &[Instruction], to: P) {
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

pub fn parse_file_and_emit(filename: &str) -> Result<Vec<Instruction>, Error> {
	let prog = parse_file(filename)?;
	emit_to_file(&prog, Path::new(filename).with_extension("bc"));
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

	fn rust_parse_file_and_emit(cr, filename: OCamlRef<String>) -> OCaml<Result<OCamlList<Instruction>, String>> {
		let filename: String = filename.to_rust(&cr);
		parse_file_and_emit(filename.as_str()).map_err(|err| format!("{:#}", err)).to_ocaml(cr)
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



// // use inkwell::OptimizationLevel;
// // use inkwell::builder::Builder;
// use inkwell::context::Context;
// // use inkwell::execution_engine::{ExecutionEngine, JitFunction};
// // use inkwell::module::Module;
// use std::error::Error;

// // type SumFunc = unsafe extern "C" fn(u64, u64, u64) -> u64;

// // struct CodeGen<'ctx> {
// // 	context: &'ctx Context,
// // 	module: Module<'ctx>,
// // 	builder: Builder<'ctx>,
// // 	// execution_engine: ExecutionEngine<'ctx>,
// // }

// // impl<'ctx> CodeGen<'ctx> {
// // 	fn jit_compile_sum(&self) -> Option<JitFunction<SumFunc>> {
// // 		let i32_type = self.context.i32_type();
// // 		let fn_type = i32_type.fn_type(&[i32_type.into(), i32_type.into(), i32_type.into()], false);
// // 		let function = self.module.add_function("sum", fn_type, None);
// // 		let basic_block = self.context.append_basic_block(function, "entry");

// // 		self.builder.position_at_end(basic_block);

// // 		let x = function.get_nth_param(0)?.into_int_value();
// // 		let y = function.get_nth_param(1)?.into_int_value();
// // 		let z = function.get_nth_param(2)?.into_int_value();

// // 		let sum = self.builder.build_int_add(x, y, "sum");
// // 		let sum = self.builder.build_int_add(sum, z, "sum");

// // 		self.builder.build_return(Some(&sum));

// // 		unsafe { self.execution_engine.get_function("sum").ok() }
// // 	}
// // }


// fn main() -> Result<(), Box<dyn Error>> {
// 	let context = Context::create();
// 	let module = context.create_module("lab");
// 	let builder = context.create_builder();
// 	// let execution_engine = module.create_jit_execution_engine(OptimizationLevel::None)?;
// 	// let codegen = CodeGen {
// 	// 	context: &context,
// 	// 	module,
// 	// 	builder: context.create_builder(),
// 	// 	// execution_engine,
// 	// };

// 	let i32_type = context.i32_type();
// 	let fn_type = i32_type.fn_type(&[], false);
// 	let function = module.add_function("main", fn_type, None);
// 	let basic_block = context.append_basic_block(function, "doit");

// 	builder.position_at_end(basic_block);
// 	let sum = builder.build_int_add(i32_type.const_int(2, false), i32_type.const_int(4, false), "sum");
// 	let sum = builder.build_int_add(sum, sum, "sum");
// 	builder.build_return(Some(&sum));
// 	module.write_bitcode_to_path(&std::path::Path::new("lab.bc"));

// 	// let sum = codegen.jit_compile_sum().ok_or("Unable to JIT compile `sum`")?;

// 	// let x = 1u64;
// 	// let y = 2u64;
// 	// let z = 3u64;

// 	// unsafe {
// 	// 	println!("{} + {} + {} = {}", x, y, z, sum.call(x, y, z));
// 	// 	assert_eq!(sum.call(x, y, z), x + y + z);
// 	// }

// 	Ok(())
// }
