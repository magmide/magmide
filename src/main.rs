// use magmide::ast;
// use magmide::parser;
// use magmide::checker;

fn main() {
	let db = magmide::Database::default();
	let source_file = magmide::SourceFile::new(&db, "bad".into());
	magmide::tracked_parse_file(&db, source_file);
	let diagnostics = magmide::tracked_parse_file::accumulated::<magmide::Diagnostic>(&db, source_file);
	eprintln!("{diagnostics:?}");
}
