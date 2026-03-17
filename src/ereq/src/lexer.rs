/// token tags emitted by the lexer.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TOKEN {
    COMMENT = 1,
    SEMICOLON = 2,
    COMMA = 3,
    HEADER = 4,
    WS = 5,
    INT = 6,
    NOTIN = 7,
    IN = 8,
    VAR1 = 9,
    VAR2 = 10,
    PRED = 11,
    ASSERT = 12,
    ALL1 = 13,
    EX1 = 14,
    VARNAME = 15,
    LPAREN = 16,
    RPAREN = 17,
    PLUS = 18,
    AND = 19,
    OR = 20,
    COLON = 21,
    NOTEQUAL = 22,
    NOT = 23,
    GE = 24,
    LE = 25,
    ARROW = 26,
    EQUAL = 27,
    LT = 28,
    GT = 29,
    EQUIV = 30,
    LBRACE = 31,
    RBRACE = 32,
    SUB = 33,
    EX2 = 34,
    ALL2 = 35,
}

#[inline]
fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

#[inline]
fn is_ident_cont(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'\''
}

pub fn main(input: &[u8], mut emit: impl FnMut(usize, TOKEN)) -> usize {
    let len = input.len();
    let mut pos = 0;

    while pos < len {
        let start = pos;
        let b = input[pos];
        pos += 1;

        match b {
            b' ' | b'\t' | b'\r' | b'\n' => {
                while pos < len && matches!(input[pos], b' ' | b'\t' | b'\r' | b'\n') {
                    pos += 1;
                }
                emit(pos, TOKEN::WS);
            }

            b'#' => {
                while pos < len && input[pos] != b'\n' {
                    pos += 1;
                }
                emit(pos, TOKEN::COMMENT);
            }

            b'/' => {
                if pos < len && input[pos] == b'*' {
                    pos += 1;
                    loop {
                        if pos + 1 >= len {
                            return start; // unterminated comment
                        }
                        if input[pos] == b'*' && input[pos + 1] == b'/' {
                            pos += 2;
                            break;
                        }
                        pos += 1;
                    }
                    emit(pos, TOKEN::COMMENT);
                } else {
                    return start; // bare '/' 
                }
            }

            b';' => emit(pos, TOKEN::SEMICOLON),
            b',' => emit(pos, TOKEN::COMMA),
            b'(' => emit(pos, TOKEN::LPAREN),
            b')' => emit(pos, TOKEN::RPAREN),
            b'+' => emit(pos, TOKEN::PLUS),
            b'&' => emit(pos, TOKEN::AND),
            b'|' => emit(pos, TOKEN::OR),
            b':' => emit(pos, TOKEN::COLON),
            b'{' => emit(pos, TOKEN::LBRACE),
            b'}' => emit(pos, TOKEN::RBRACE),

            b'~' => {
                if pos < len && input[pos] == b'=' {
                    pos += 1;
                    emit(pos, TOKEN::NOTEQUAL);
                } else {
                    emit(pos, TOKEN::NOT);
                }
            }

            b'<' => {
                if pos < len && input[pos] == b'=' {
                    pos += 1;
                    if pos < len && input[pos] == b'>' {
                        pos += 1;
                        emit(pos, TOKEN::EQUIV);
                    } else {
                        emit(pos, TOKEN::LE);
                    }
                } else {
                    emit(pos, TOKEN::LT);
                }
            }

            b'>' => {
                if pos < len && input[pos] == b'=' {
                    pos += 1;
                    emit(pos, TOKEN::GE);
                } else {
                    emit(pos, TOKEN::GT);
                }
            }

            b'=' => {
                if pos < len && input[pos] == b'>' {
                    pos += 1;
                    emit(pos, TOKEN::ARROW);
                } else {
                    emit(pos, TOKEN::EQUAL);
                }
            }

            b'0'..=b'9' => {
                while pos < len && input[pos].is_ascii_digit() {
                    pos += 1;
                }
                emit(pos, TOKEN::INT);
            }

            _ if is_ident_start(b) => {
                while pos < len && is_ident_cont(input[pos]) {
                    pos += 1;
                }
                let word = &input[start..pos];
                let tag = match word {
                    b"var1" => TOKEN::VAR1,
                    b"var2" => TOKEN::VAR2,
                    b"pred" => TOKEN::PRED,
                    b"assert" => TOKEN::ASSERT,
                    b"all1" => TOKEN::ALL1,
                    b"ex1" => TOKEN::EX1,
                    b"notin" => TOKEN::NOTIN,
                    b"in" => TOKEN::IN,
                    b"sub" => TOKEN::SUB,
                    b"ex2" => TOKEN::EX2,
                    b"all2" => TOKEN::ALL2,
                    b"ws1s" | b"ws2s" => TOKEN::HEADER,
                    b"m2l" if matches!(input.get(pos..pos + 4), Some(b"-str")) => {
                        pos += 4;
                        TOKEN::HEADER
                    }
                    _ => TOKEN::VARNAME,
                };
                emit(pos, tag);
            }

            _ => return start,
        }
    }

    pos
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(input: &str) -> Vec<(TOKEN, String)> {
        let mut tokens = Vec::new();
        let bytes = input.as_bytes();
        let mut prev = 0;
        let end = main(bytes, |pos, tag| {
            tokens.push((tag, input[prev..pos].to_string()));
            prev = pos;
        });
        assert_eq!(end, input.len(), "lexer stopped early at {end}");
        tokens
    }

    fn lex_tags(input: &str) -> Vec<TOKEN> {
        lex(input).into_iter().map(|(t, _)| t).collect()
    }

    #[test]
    fn single_tokens() {
        assert_eq!(lex_tags(";"), vec![TOKEN::SEMICOLON]);
        assert_eq!(lex_tags(","), vec![TOKEN::COMMA]);
        assert_eq!(lex_tags("("), vec![TOKEN::LPAREN]);
        assert_eq!(lex_tags(")"), vec![TOKEN::RPAREN]);
        assert_eq!(lex_tags("+"), vec![TOKEN::PLUS]);
        assert_eq!(lex_tags("&"), vec![TOKEN::AND]);
        assert_eq!(lex_tags("|"), vec![TOKEN::OR]);
        assert_eq!(lex_tags(":"), vec![TOKEN::COLON]);
        assert_eq!(lex_tags("{"), vec![TOKEN::LBRACE]);
        assert_eq!(lex_tags("}"), vec![TOKEN::RBRACE]);
    }

    #[test]
    fn multi_char_operators() {
        assert_eq!(lex_tags("~"), vec![TOKEN::NOT]);
        assert_eq!(lex_tags("~="), vec![TOKEN::NOTEQUAL]);
        assert_eq!(lex_tags("<"), vec![TOKEN::LT]);
        assert_eq!(lex_tags("<="), vec![TOKEN::LE]);
        assert_eq!(lex_tags("<=>"), vec![TOKEN::EQUIV]);
        assert_eq!(lex_tags(">"), vec![TOKEN::GT]);
        assert_eq!(lex_tags(">="), vec![TOKEN::GE]);
        assert_eq!(lex_tags("="), vec![TOKEN::EQUAL]);
        assert_eq!(lex_tags("=>"), vec![TOKEN::ARROW]);
    }

    #[test]
    fn keywords() {
        assert_eq!(lex_tags("var1"), vec![TOKEN::VAR1]);
        assert_eq!(lex_tags("var2"), vec![TOKEN::VAR2]);
        assert_eq!(lex_tags("all1"), vec![TOKEN::ALL1]);
        assert_eq!(lex_tags("ex1"), vec![TOKEN::EX1]);
        assert_eq!(lex_tags("notin"), vec![TOKEN::NOTIN]);
        assert_eq!(lex_tags("pred"), vec![TOKEN::PRED]);
        assert_eq!(lex_tags("assert"), vec![TOKEN::ASSERT]);
    }

    #[test]
    fn headers() {
        assert_eq!(lex_tags("m2l-str"), vec![TOKEN::HEADER]);
    }

    #[test]
    fn identifiers_and_ints() {
        assert_eq!(lex_tags("foo"), vec![TOKEN::VARNAME]);
        assert_eq!(lex_tags("x1"), vec![TOKEN::VARNAME]);
        assert_eq!(lex_tags("42"), vec![TOKEN::INT]);
        assert_eq!(lex_tags("0"), vec![TOKEN::INT]);
    }

    #[test]
    fn comments() {
        assert_eq!(lex_tags("# hello"), vec![TOKEN::COMMENT]);
        assert_eq!(lex_tags("/* block */"), vec![TOKEN::COMMENT]);
    }

    #[test]
    fn whitespace_skipped() {
        let tags = lex_tags("x + 1");
        assert_eq!(
            tags,
            vec![
                TOKEN::VARNAME,
                TOKEN::WS,
                TOKEN::PLUS,
                TOKEN::WS,
                TOKEN::INT,
            ]
        );
    }

    #[test]
    fn full_declaration() {
        let tags = lex_tags("var2 A, B;");
        assert_eq!(
            tags,
            vec![
                TOKEN::VAR2,
                TOKEN::WS,
                TOKEN::VARNAME,
                TOKEN::COMMA,
                TOKEN::WS,
                TOKEN::VARNAME,
                TOKEN::SEMICOLON,
            ]
        );
    }

    #[test]
    fn contextual_keywords() {
        assert_eq!(lex_tags("in"), vec![TOKEN::IN]);
        assert_eq!(lex_tags("sub"), vec![TOKEN::SUB]);
        // "in" prefix doesn't match longer identifiers
        assert_eq!(lex_tags("inside"), vec![TOKEN::VARNAME]);
    }

    #[test]
    fn quantifier_expr() {
        let tags = lex_tags("ex1 x: x in A");
        assert_eq!(
            tags,
            vec![
                TOKEN::EX1,
                TOKEN::WS,
                TOKEN::VARNAME,
                TOKEN::COLON,
                TOKEN::WS,
                TOKEN::VARNAME,
                TOKEN::WS,
                TOKEN::IN,
                TOKEN::WS,
                TOKEN::VARNAME,
            ]
        );
    }
}
