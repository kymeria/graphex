use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Formating error")]
    Fmt(std::fmt::Error),

    #[error("Key {0} is not valid")]
    Key(String),

    #[error(transparent)]
    Other(Box<dyn std::error::Error>),
}

impl Error {
    pub fn key(k: &str) -> Self {
        Self::Key(k.to_string())
    }
}

pub type Result<T = ()> = std::result::Result<T, Error>;
