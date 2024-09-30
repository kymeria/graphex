use clap::Parser;
use graphex::*;
use std::path::PathBuf;

struct Directory(pub PathBuf);

fn conv(err: std::io::Error) -> graphex::Error {
    graphex::Error::Other(Box::new(err))
}

impl NodeTrait for Directory {
    fn sep(&self) -> &str {
        "/"
    }

    fn next(&self, key: &str) -> Result<Option<Node>> {
        let mut child_path = self.0.clone();
        child_path.push(key);
        if child_path.is_dir() {
            Ok(Some(Box::new(Directory(child_path)).into()))
        } else if child_path.is_file() {
            Ok(Some(Box::new(File(child_path)).into()))
        } else if child_path.is_symlink() {
            Ok(Some(Box::new(Link(child_path)).into()))
        } else {
            Ok(None)
        }
    }
    fn display(&self) -> &dyn Display {
        self
    }
}

impl graphex::Display for Directory {
    fn print(&self, out: &mut graphex::Output) -> Result<()> {
        let mut m = out.mapping(
            &self
                .0
                .file_name()
                .unwrap_or_else(|| self.0.as_os_str())
                .to_string_lossy(),
        )?;
        for entry in self.0.read_dir().map_err(conv)? {
            let entry = entry.map_err(conv)?;
            let file_type = entry.file_type().map_err(conv)?;
            let type_str = if file_type.is_dir() {
                "Dir"
            } else if file_type.is_file() {
                "File"
            } else if file_type.is_symlink() {
                "SymLink"
            } else {
                "Unknown"
            };
            m.item(&entry.file_name().to_string_lossy(), &type_str)?
        }
        Ok(())
    }
}

struct File(pub PathBuf);

impl NodeTrait for File {
    fn next(&self, _key: &str) -> Result<Option<Node>> {
        Ok(None)
    }

    fn display(&self) -> &dyn Display {
        self
    }
}

impl graphex::Display for File {
    fn print(&self, out: &mut Output) -> Result<()> {
        let content = std::fs::read_to_string(&self.0).map_err(conv)?;
        out.write_str(&content)
    }
}

struct Link(pub PathBuf);

impl NodeTrait for Link {
    fn next(&self, _key: &str) -> Result<Option<Node>> {
        Ok(None)
    }

    fn display(&self) -> &dyn Display {
        self
    }
}

impl graphex::Display for Link {
    fn print(&self, out: &mut Output) -> Result<()> {
        let target = self.0.read_link().map_err(conv)?;
        write!(out, "{}", target.display())
    }
}

#[derive(Parser)]
struct Cli {
    path: PathBuf,

    key: String,
}

fn main() {
    let cli = Cli::parse();

    let root = Directory(cli.path.clone());

    println!("{}", graphex::explore_to_string(&root, &cli.key).unwrap());
}
