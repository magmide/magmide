// use magmide::ast;
// use magmide::parser;
// use magmide::Database;
// use magmide::checker;

fn main() {
	// let path = PathBuf::from(r"/");

	// // starting from the original source file, we walk the imports (which for now don't exist) and add source files as we go (which probably requires intelligent separation to make sure we can do import tracking without an incremental database present)
	// // or not? things like type checking are incredibly query-oriented, so it probably doesn't make sense

	// let db = magmide::Database::default();
	// let source_file = magmide::SourceFile::new(&db, "bad".into(), 0, path);
	// magmide::tracked_parse_file(&db, source_file);
	// let diagnostics = magmide::tracked_parse_file::accumulated::<magmide::Diagnostic>(&db, source_file);
	// eprintln!("{diagnostics:?}");
}
