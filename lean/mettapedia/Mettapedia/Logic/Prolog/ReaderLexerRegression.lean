import Mettapedia.Logic.Prolog.ReaderLexer

/-!
# Prolog lexer regressions

The fixtures pin source-order tokens, comment layout, quoting, character-code
lexemes, and source positions before operator parsing begins.
-/

namespace Mettapedia.Logic.Prolog.ReaderLexerRegression

open ReaderLexer

def tokenKinds (source : String) : Option (List Kind) :=
  match scan source with
  | .error _ => none
  | .ok tokens => some (tokens.map Token.kind)

#guard tokenKinds "p(X) :- q(X), !.\n" = some [
  .atom "p",
  .punctuation .leftParen,
  .variable "X",
  .punctuation .rightParen,
  .atom ":-",
  .atom "q",
  .punctuation .leftParen,
  .variable "X",
  .punctuation .rightParen,
  .punctuation .comma,
  .atom "!",
  .punctuation .fullStop
]

-- Block comments are layout, including immediately after a full stop.
#guard tokenKinds "p./* nested /* block */ comment */q." = some [
  .atom "p", .punctuation .fullStop,
  .atom "q", .punctuation .fullStop
]

-- Quotes decode doubled delimiters and the SWI escape used by PeTTa's
-- colored diagnostic strings.
#guard tokenKinds "q('a''b', \"\\e\")." = some [
  .atom "q", .punctuation .leftParen, .atom "a'b",
  .punctuation .comma, .string (String.singleton '\u001b'),
  .punctuation .rightParen, .punctuation .fullStop
]

-- ISO character-code syntax consumes the quoted character even when that
-- character is itself a quote or escaped backslash.
#guard tokenKinds r#"x(0'",0'\\)."# = some [
  .atom "x", .punctuation .leftParen, .number "0'\"",
  .punctuation .comma, .number "0'\\\\",
  .punctuation .rightParen, .punctuation .fullStop
]

def secondLinePositionExact : Bool :=
  match scan "p.\n  q." with
  | .ok (_ :: _ :: token :: _) =>
      token.kind == .atom "q" && token.span.start.line == 2 &&
        token.span.start.column == 3 && token.span.start.offset == 5
  | _ => false

#guard secondLinePositionExact

def rejectsUnknownEscape : Bool :=
  match scan "p(\"\\Q\")." with
  | .error { kind := .unsupportedEscape 'Q', .. } => true
  | _ => false

#guard rejectsUnknownEscape

end Mettapedia.Logic.Prolog.ReaderLexerRegression
