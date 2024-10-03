use clap::Parser;
use graphex::*;
use std::path::PathBuf;

struct Directory(pub PathBuf);

fn conv(err: std::io::Error) -> graphex::Error {
    graphex::Error::Other(Box::new(err))
}

impl Node for Directory {
    fn sep(&self) -> &str {
        "/"
    }

    fn next(&self, key: &str) -> ExploreResult {
        let mut child_path = self.0.clone();
        child_path.push(key);
        if child_path.is_dir() {
            Ok(Box::new(Directory(child_path)).into())
        } else if child_path.is_file() {
            Ok(Box::new(File(child_path)).into())
        } else if child_path.is_symlink() {
            Ok(Box::new(Link(child_path)).into())
        } else {
            Err(Error::key(key))
        }
    }
    fn display(&self) -> &dyn Display {
        self
    }
}

impl graphex::Display for Directory {
    fn header_footer(&self) -> Option<(String, String)> {
        let header = self
            .0
            .file_name()
            .unwrap_or_else(|| self.0.as_os_str())
            .to_string_lossy()
            .to_string();
        Some((header, String::new()))
    }
    fn print_content(&self, out: &mut graphex::Output) -> Result {
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
            out.item(&entry.file_name().to_string_lossy(), &type_str)?
        }
        Ok(())
    }
}

struct File(pub PathBuf);

impl Node for File {
    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }

    fn display(&self) -> &dyn Display {
        self
    }
}

impl graphex::Display for File {
    fn print_content(&self, out: &mut Output) -> Result {
        let content = std::fs::read_to_string(&self.0).map_err(conv)?;
        out.write_str(&content)
    }
}

struct Link(pub PathBuf);

impl Node for Link {
    fn next(&self, key: &str) -> ExploreResult {
        Err(Error::key(key))
    }

    fn display(&self) -> &dyn Display {
        self
    }
}

impl graphex::Display for Link {
    fn print_content(&self, out: &mut Output) -> Result {
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
