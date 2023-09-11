pub mod ast;
pub mod parser;
pub mod checker;

// #[salsa::jar(db = Db)]
// struct Jar(
// 	SourceFile,
// 	ParsedFile,
// 	parse_file,

// 	Diagnostic, , , compile, parse, sum,
// );

// use std::{
// 	// path::PathBuf,
// 	sync::Mutex,
// 	// time::Duration,
// };

// trait Db: salsa::DbWithJar<Jar> {
// 	fn input(&self, contents: &str) -> SourceFile;
// }

// #[salsa::db(Jar)]
// struct Database {
// 	storage: salsa::Storage<Self>,
// 	logs: Mutex<Vec<String>>,
// }

// impl Database {
// 	fn new() -> Self {
// 		let storage = Default::default();
// 		Self {
// 			storage,
// 			logs: Default::default(),
// 		}
// 	}
// }

// impl Db for Database {
// 	fn input(&self, contents: &str) -> SourceFile {
// 		SourceFile::new(self, contents)
// 	}
// }

// impl salsa::Database for Database {
// 	fn salsa_event(&self, event: salsa::Event) {
// 		// don't log boring events
// 		if let salsa::EventKind::WillExecute { .. } = event.kind {
// 			self.logs
// 				.lock()
// 				.unwrap()
// 				.push(format!("{:?}", event.debug(self)));
// 		}
// 	}
// }

// #[salsa::accumulator]
// struct Diagnostic(String);

// impl Diagnostic {
// 	fn push_error(db: &dyn Db, file: SourceFile, error: Report) {
// 		Diagnostic::push(
// 			db,
// 			format!(
// 				"Error in file {}: {:?}\n",
// 				file.path(db)
// 					.file_name()
// 					.unwrap_or_else(|| "<unknown>".as_ref())
// 					.to_string_lossy(),
// 				error,
// 			),
// 		)
// 	}
// }

// #[salsa::tracked]
// struct ParsedFile {
// 	value: u32,
// 	#[return_ref]
// 	links: Vec<ParsedFile>,
// }

// #[salsa::tracked]
// fn compile(db: &dyn Db, input: SourceFile) -> u32 {
// 	let parsed = parse(db, input);
// 	sum(db, parsed)
// }

// #[salsa::tracked]
// fn parse(db: &dyn Db, input: SourceFile) -> ParsedFile {
// 	let mut lines = input.contents(db).lines();
// 	let value = match lines.next().map(|line| (line.parse::<u32>(), line)) {
// 		Some((Ok(num), _)) => num,
// 		Some((Err(e), line)) => {
// 			Diagnostic::push_error(
// 				db,
// 				input,
// 				Report::new(e).wrap_err(format!(
// 					"First line ({}) could not be parsed as an integer",
// 					line
// 				)),
// 			);
// 			0
// 		}
// 		None => {
// 			Diagnostic::push_error(db, input, eyre!("SourceFile must contain an integer"));
// 			0
// 		}
// 	};
// 	let links = lines
// 		.filter_map(|path| {
// 			let relative_path = match path.parse::<PathBuf>() {
// 				Ok(path) => path,
// 				Err(err) => {
// 					Diagnostic::push_error(
// 						db,
// 						input,
// 						Report::new(err).wrap_err(format!("Failed to parse path: {}", path)),
// 					);
// 					return None;
// 				}
// 			};
// 			let link_path = input.path(db).parent().unwrap().join(relative_path);
// 			match db.input(link_path) {
// 				Ok(file) => Some(parse(db, file)),
// 				Err(err) => {
// 					Diagnostic::push_error(db, input, err);
// 					None
// 				}
// 			}
// 		})
// 		.collect();
// 	ParsedFile::new(db, value, links)
// }

// #[salsa::tracked]
// fn sum(db: &dyn Db, input: ParsedFile) -> u32 {
// 	input.value(db)
// 		+ input
// 			.links(db)
// 			.iter()
// 			.map(|&file| sum(db, file))
// 			.sum::<u32>()
// }
