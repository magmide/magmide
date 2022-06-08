// use inkwell::OptimizationLevel;
// use inkwell::builder::Builder;
use inkwell::context::Context;
// use inkwell::execution_engine::{ExecutionEngine, JitFunction};
// use inkwell::module::Module;
use std::error::Error;

// type SumFunc = unsafe extern "C" fn(u64, u64, u64) -> u64;

// struct CodeGen<'ctx> {
// 	context: &'ctx Context,
// 	module: Module<'ctx>,
// 	builder: Builder<'ctx>,
// 	// execution_engine: ExecutionEngine<'ctx>,
// }

// impl<'ctx> CodeGen<'ctx> {
// 	fn jit_compile_sum(&self) -> Option<JitFunction<SumFunc>> {
// 		let i32_type = self.context.i32_type();
// 		let fn_type = i32_type.fn_type(&[i32_type.into(), i32_type.into(), i32_type.into()], false);
// 		let function = self.module.add_function("sum", fn_type, None);
// 		let basic_block = self.context.append_basic_block(function, "entry");

// 		self.builder.position_at_end(basic_block);

// 		let x = function.get_nth_param(0)?.into_int_value();
// 		let y = function.get_nth_param(1)?.into_int_value();
// 		let z = function.get_nth_param(2)?.into_int_value();

// 		let sum = self.builder.build_int_add(x, y, "sum");
// 		let sum = self.builder.build_int_add(sum, z, "sum");

// 		self.builder.build_return(Some(&sum));

// 		unsafe { self.execution_engine.get_function("sum").ok() }
// 	}
// }


fn main() -> Result<(), Box<dyn Error>> {
	let context = Context::create();
	let module = context.create_module("lab");
	let builder = context.create_builder();
	// let execution_engine = module.create_jit_execution_engine(OptimizationLevel::None)?;
	// let codegen = CodeGen {
	// 	context: &context,
	// 	module,
	// 	builder: context.create_builder(),
	// 	// execution_engine,
	// };

	let i32_type = context.i32_type();
	let fn_type = i32_type.fn_type(&[], false);
	let function = module.add_function("main", fn_type, None);
	let basic_block = context.append_basic_block(function, "doit");

	builder.position_at_end(basic_block);
	let sum = builder.build_int_add(i32_type.const_int(2, false), i32_type.const_int(4, false), "sum");
	let sum = builder.build_int_add(sum, sum, "sum");
	builder.build_return(Some(&sum));
	module.write_bitcode_to_path(&std::path::Path::new("lab.bc"));

	// let sum = codegen.jit_compile_sum().ok_or("Unable to JIT compile `sum`")?;

	// let x = 1u64;
	// let y = 2u64;
	// let z = 3u64;

	// unsafe {
	// 	println!("{} + {} + {} = {}", x, y, z, sum.call(x, y, z));
	// 	assert_eq!(sum.call(x, y, z), x + y + z);
	// }

	Ok(())
}
