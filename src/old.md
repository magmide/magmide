```rust
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ModuleItemBlock {
  pub line: usize,
  pub body: String,
  pub kind: ModuleItemBlockKind,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum ModuleItemBlockKind {
  Procedure{ name: String },
  Type{ name: String },
  Debug,
  Error,
}

pub fn parse_module_item_blocks(indentation: usize, i: &str) -> Vec<ModuleItemBlock> {
  let mut module_item_blocks = Vec::new();
  let mut current_block_body = Vec::new();
  let mut current_block_line = 0;
  let mut current_block_kind = None;

  fn close_block(
    module_item_blocks: &mut Vec<ModuleItemBlock>,
    current_block_body: &mut Vec<&str>,
    line: usize,
    kind: ModuleItemBlockKind,
  ) {
    let body = current_block_body.join("\n");
    current_block_body.clear();
    module_item_blocks.push(ModuleItemBlock{ line, body, kind });
  }

  for (index, body_line) in i.lines().enumerate() {
    let line = index + 1;

    if get_tab_count(body_line) != indentation || body_line.len() == 0 {
      current_block_body.push(body_line);
      continue;
    }

    let trimmed_body_line = body_line.trim_start();
    if trimmed_body_line.starts_with(';') {
      current_block_body.push(body_line);
      if current_block_kind.is_none() {
        current_block_kind = Some(ModuleItemBlockKind::Error);
      }
      continue;
    }

    use ModuleItemBlockKind::*;

    let kind = alt((
      map(preceded(tag("proc "), parse_ident), |name| Procedure{ name: name.to_string() }),
      map(preceded(tag("type "), parse_ident), |name| Type{ name: name.to_string() }),
      value(Debug, tag("debug ")),
    ))(trimmed_body_line)
      .map(|(_, kind)| kind)
      .unwrap_or(ModuleItemBlockKind::Error);

    let previous_kind = std::mem::replace(&mut current_block_kind, Some(kind));
    if let Some(previous_kind) = previous_kind {
      close_block(&mut module_item_blocks, &mut current_block_body, current_block_line, previous_kind);
      current_block_line = line;
    }
    current_block_body.push(body_line);
  }
  close_block(&mut module_item_blocks, &mut current_block_body, current_block_line, current_block_kind.unwrap_or(ModuleItemBlockKind::Error));

  module_item_blocks
}



fn make_block(line: usize, kind: ModuleItemBlockKind, body: &str) -> ModuleItemBlock {
  ModuleItemBlock{ line, body: body.into(), kind }
}

#[test]
fn test_parse_module_item_blocks() {
  let i = r#"
    proc hello
      what
      here
    ;
      actual body
      is::
        arbitary
          nested
        things
      yo

        sup

    type hey; sup
    type yoyo;
      | whatev
      | thing
        and stuff
          and whatever

    bad
    alsobad
      | thing
      | hmm
      sdfjdk
        dkfjdk

    debug hey
    debug sup
      big
      things
        poppin
      and such

    proc same_day(d: Day): Day; asdf

  "#;

  assert_eq!(parse_module_item_blocks(3, i), [
    make_block(0, ModuleItemBlockKind::Procedure{ name: "hello".into() }, "\n\t\t\tproc hello\n\t\t\t\twhat\n\t\t\t\there\n\t\t\t;\n\t\t\t\tactual body\n\t\t\t\tis::\n\t\t\t\t\tarbitary\n\t\t\t\t\t\tnested\n\t\t\t\t\tthings\n\t\t\t\tyo\n\n\t\t\t\t\tsup\n"),
    make_block(15, ModuleItemBlockKind::Type{ name: "hey".into() }, "\t\t\ttype hey; sup"),
    make_block(16, ModuleItemBlockKind::Type{ name: "yoyo".into() }, "\t\t\ttype yoyo;\n\t\t\t\t| whatev\n\t\t\t\t| thing\n\t\t\t\t\tand stuff\n\t\t\t\t\t\tand whatever\n"),
    make_block(22, ModuleItemBlockKind::Error, "\t\t\tbad"),
    make_block(23, ModuleItemBlockKind::Error, "\t\t\talsobad\n\t\t\t\t| thing\n\t\t\t\t| hmm\n\t\t\t\tsdfjdk\n\t\t\t\t\tdkfjdk\n"),
    make_block(29, ModuleItemBlockKind::Debug, "\t\t\tdebug hey"),
    make_block(30, ModuleItemBlockKind::Debug, "\t\t\tdebug sup\n\t\t\t\tbig\n\t\t\t\tthings\n\t\t\t\t\tpoppin\n\t\t\t\tand such\n"),
    make_block(36, ModuleItemBlockKind::Procedure{ name: "same_day".into() }, "\t\t\tproc same_day(d: Day): Day; asdf\n\n\t\t"),
  ]);
}
```
