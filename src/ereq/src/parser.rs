use pomelo::pomelo;

use crate::{ExprBuilder, lexer::TOKEN};

pomelo! {
    %module mona_lalr;

    %include {
        use crate::ExprId;
        use crate::ExprBuilder;
        type Span = (usize, usize);
    }

    %parser pub struct Parser<'a> {};
    %extra_argument (&'a str, ExprBuilder<'a>);

    %stack_size 512;

    %error String;
    %parse_fail { "parse failed".to_string() };
    %syntax_error { Err(format!("syntax error: {:?}", token)) }

    %token #[derive(Debug, Clone)] pub enum Token {};

    // tokens with data
    %type Varname Span;
    %type IntTok i32;
    %type CommentTok Span;
    %type HeaderTok Span;

    // operator/keyword tokens
    %left Semicolon;
    %left Comma;
    %left Colon;
    %left LParen;
    %left RParen;
    %left Var1;
    %left Var2;
    %left All1Kw;
    %left Ex1Kw;
    %left Not;
    %left Arrow;
    %left Equiv;
    %left And;
    %left Or;
    %left In;
    %left Notin;
    %left Sub;
    %left Equal;
    %left NotEqual;
    %left Lt;
    %left Gt;
    %left Le;
    %left Ge;
    %left Plus;
    %left True;
    %left False;
    %left LBrace;
    %left RBrace;

    // rule types
    %type mona ();
    %type decls ();
    %type declaration ();
    %type varname_list Vec<Span>;
    %type int_list Vec<i32>;
    %type expr ExprId;
    %type expr3 ExprId;
    %type expr2 ExprId;
    %type expr1 ExprId;
    %type expr0 ExprId;

    %start_symbol mona;

    // top-level
    mona ::= decls { () };
    mona ::= HeaderTok Semicolon decls { () };

    decls ::= declaration Semicolon { () };
    decls ::= decls declaration Semicolon { () };

    // declarations
    declaration ::= CommentTok(s) {
        let input = extra.0;
        extra.1.comment(&input[s.0..s.1])
    };
    declaration ::= Var2 varname_list(spans) {
        let input = extra.0;
        let vars: Vec<&str> = spans.iter().map(|s| &input[s.0..s.1]).collect();
        extra.1.declare_var2(vars)
    };
    declaration ::= Var1 varname_list(spans) {
        let input = extra.0;
        let vars: Vec<&str> = spans.iter().map(|s| &input[s.0..s.1]).collect();
        extra.1.declare_var1(&vars)
    };
    declaration ::= expr(e) {
        extra.1.declare_expr(e)
    };

    // comma-separated variable names
    varname_list ::= Varname(n) { vec![n] };
    varname_list ::= varname_list(mut v) Comma Varname(n) { v.push(n); v };

    // space-separated integer list (for eqset)
    int_list ::= IntTok(n) { vec![n] };
    int_list ::= int_list(mut v) IntTok(n) { v.push(n); v };

    // expr: quantifiers (lowest precedence)
    expr ::= Ex1Kw varname_list(spans) Colon expr(e) {
        let input = extra.0;
        let vars: Vec<&str> = spans.iter().map(|s| &input[s.0..s.1]).collect();
        extra.1.expr_ex1(vars, e)
    };
    expr ::= All1Kw varname_list(spans) Colon expr(e) {
        let input = extra.0;
        let vars: Vec<&str> = spans.iter().map(|s| &input[s.0..s.1]).collect();
        extra.1.expr_all1(vars, e)
    };
    expr ::= Not Ex1Kw varname_list(spans) Colon expr(e) {
        let input = extra.0;
        let vars: Vec<&str> = spans.iter().map(|s| &input[s.0..s.1]).collect();
        let inner = extra.1.expr_ex1(vars, e);
        extra.1.expr_not(inner)
    };
    expr ::= Not All1Kw varname_list(spans) Colon expr(e) {
        let input = extra.0;
        let vars: Vec<&str> = spans.iter().map(|s| &input[s.0..s.1]).collect();
        let inner = extra.1.expr_all1(vars, e);
        extra.1.expr_not(inner)
    };
    expr ::= expr3(e) { e };

    // expr3: implication / equivalence
    expr3 ::= expr3(e0) Arrow expr2(e1) { extra.1.expr_implies(e0, e1) };
    expr3 ::= expr3(e0) Equiv expr2(e1) { extra.1.expr_equiv(e0, e1) };
    expr3 ::= expr2(e) { e };

    // expr2: boolean connectives
    expr2 ::= expr2(e0) And expr1(e1) { extra.1.expr_and(e0, e1) };
    expr2 ::= expr2(e0) Or expr1(e1) { extra.1.expr_or(e0, e1) };
    expr2 ::= Not expr0(e) { extra.1.expr_not(e) };
    expr2 ::= expr1(e) { e };

    // expr1: relational / membership
    expr1 ::= expr1(e0) In expr0(e1) { extra.1.expr_in(e0, e1) };
    expr1 ::= expr1(e0) Notin expr0(e1) { extra.1.expr_notin(e0, e1) };
    expr1 ::= expr1(e0) Sub expr0(e1) { extra.1.expr_sub(e0, e1) };
    expr1 ::= expr1(e0) Equal LBrace int_list(nums) RBrace { extra.1.expr_eqset(e0, nums) };
    expr1 ::= expr1(e0) Equal expr0(e1) { extra.1.expr_eq(e0, e1) };
    expr1 ::= expr1(e0) NotEqual expr0(e1) { extra.1.expr_ne(e0, e1) };
    expr1 ::= expr1(e0) Lt expr0(e1) { extra.1.expr_lt(e0, e1) };
    expr1 ::= expr1(e0) Gt expr0(e1) { extra.1.expr_gt(e0, e1) };
    expr1 ::= expr1(e0) Le expr0(e1) { extra.1.expr_le(e0, e1) };
    expr1 ::= expr1(e0) Ge expr0(e1) { extra.1.expr_ge(e0, e1) };
    expr1 ::= expr0(e) { e };

    // expr0: atoms (highest precedence)
    expr0 ::= LParen expr(e) RParen { e };
    expr0 ::= IntTok(n) { extra.1.expr_int(n) };
    expr0 ::= True { ExprId::TRUE };
    expr0 ::= False { ExprId::FALSE };
    expr0 ::= Varname(s) { extra.1.expr_ident(&extra.0[s.0..s.1]) };
    expr0 ::= expr0(e) Plus IntTok(n) { extra.1.expr_add(e, n) };
}

pub fn mona_token_from_tag(
    tag: TOKEN,
    start: usize,
    end: usize,
    text: &str,
) -> Option<self::mona_lalr::Token> {
    use self::mona_lalr::Token;
    let span = (start, end);
    match tag {
        TOKEN::COMMENT => None,
        TOKEN::SEMICOLON => Some(Token::Semicolon),
        TOKEN::COMMA => Some(Token::Comma),
        TOKEN::WS => None,
        TOKEN::HEADER => Some(Token::HeaderTok(span)),
        TOKEN::VAR1 => Some(Token::Var1),
        TOKEN::VAR2 => Some(Token::Var2),
        TOKEN::NOTIN => Some(Token::Notin),
        TOKEN::IN => Some(Token::In),
        TOKEN::SUB => Some(Token::Sub),
        TOKEN::ALL1 => Some(Token::All1Kw),
        TOKEN::EX1 => Some(Token::Ex1Kw),
        TOKEN::LPAREN => Some(Token::LParen),
        TOKEN::RPAREN => Some(Token::RParen),
        TOKEN::PLUS => Some(Token::Plus),
        TOKEN::AND => Some(Token::And),
        TOKEN::OR => Some(Token::Or),
        TOKEN::COLON => Some(Token::Colon),
        TOKEN::NOTEQUAL => Some(Token::NotEqual),
        TOKEN::EQUAL => Some(Token::Equal),
        TOKEN::GE => Some(Token::Ge),
        TOKEN::LE => Some(Token::Le),
        TOKEN::LT => Some(Token::Lt),
        TOKEN::GT => Some(Token::Gt),
        TOKEN::NOT => Some(Token::Not),
        TOKEN::ARROW => Some(Token::Arrow),
        TOKEN::EQUIV => Some(Token::Equiv),
        TOKEN::LBRACE => Some(Token::LBrace),
        TOKEN::RBRACE => Some(Token::RBrace),
        TOKEN::VARNAME => match text {
            "true" => Some(Token::True),
            "false" => Some(Token::False),
            _ => Some(Token::Varname(span)),
        },
        TOKEN::INT => Some(Token::IntTok(text.parse().unwrap())),
        _ => None,
    }
}

/// lex + parse a MONA M2L-STR input using the DFA lexer and pomelo parser.
/// takes ExprBuilder by value and returns it after parsing to avoid lifetime issues.
pub fn parse_mona<'a>(input: &'a str) -> Result<crate::ExprBuilder<'a>, String> {
    let builder = ExprBuilder::new();
    let bytes = input.as_bytes();
    let mut prev_pos = 0;
    let mut tokens = Vec::new();

    let endlex = crate::lexer::main(bytes, |pos, tag| {
        let text = &input[prev_pos..pos];
        if let Some(token) = mona_token_from_tag(tag, prev_pos, pos, text) {
            tokens.push(token);
        }
        prev_pos = pos;
    });

    if endlex < input.len() {
        return Err(format!(
            "lexer failed at position {} of {}",
            endlex,
            input.len()
        ));
    }

    let mut parser = mona_lalr::Parser::new((input, builder));
    for token in tokens {
        parser.parse(token)?;
    }
    let ((), (_, builder)) = parser.end_of_input()?;
    Ok(builder)
}
