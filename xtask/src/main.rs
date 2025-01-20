use parser::parse;
use pico_args::Arguments;
use std::{
  fs,
  path::{Path, PathBuf},
};

fn main() -> anyhow::Result<()> {
  let mut args = Arguments::from_env();
  let cmd = args.subcommand()?.unwrap_or_default();

  match cmd.as_str() {
    "parser" => write_parser_output()?,
    _ => eprintln!(
      "Invalid usage:\n\ncargo xtask <SUBCOMMAND>\
\n\nSUBCOMMANDS:\n\tparse"
    ),
  }

  Ok(())
}

fn write_parser_output() -> anyhow::Result<()> {
  let root = workspace_root();
  let test_dir = fs::read_dir(Path::join(&root, "test_files/"))?;

  if matches!(fs::exists(root.join("output/parser/")), Ok(false)) {
    fs::create_dir(root.join("output/parser/"))?;
  }

  let mut wrote = 0;

  for dir in test_dir {
    let path = dir?.path();

    if !path.extension().unwrap().eq_ignore_ascii_case("asm") {
      continue;
    }

    let src = fs::read_to_string(&path)?;
    let ast = parse(&src)?;

    fs::write(
      root.join(&format!(
        "output/parser/{}.txt",
        path.file_stem().unwrap().to_str().unwrap()
      )),
      &ast.to_string(),
    )?;

    wrote += 1;
  }

  eprintln!("Wrote {wrote} parsed files.");

  Ok(())
}

fn workspace_root() -> PathBuf {
  Path::new(&env!("CARGO_MANIFEST_DIR").to_owned())
    .ancestors()
    .nth(1)
    .unwrap()
    .to_path_buf()
}
