#[derive(Debug, PartialEq, Eq)]
pub enum TokenType {
    Let,
    Fn,
    Ident(String),
    Equals,
    Number(i32),
    OpenBrace,
    CloseBrace,
    OpenParen,
    CloseParen,
    Comma,
    Semicolon,
    Plus,
    Minus,
    Slash,
    Asterisk,
    Ampersand,
}
