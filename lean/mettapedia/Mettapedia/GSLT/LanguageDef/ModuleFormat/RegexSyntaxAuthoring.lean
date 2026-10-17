import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
import Mettapedia.GSLT.Parsing.ParserProfileWire

/-!
# Authored pattern-text grammar

This declaration is independent of the native historical module reader. Its
portable export can be compared with the core read from RegexSyntax.module.
The structural compiler laws retain every terminal/nonterminal occurrence and
apply in both directions after lexical admission. Scalar-class interpretation,
the packed forest and the selected-source projection remain distinct seams.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSyntaxAuthoring

open Mettapedia.OSLF.MeTTaIL.Syntax

open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL in
def authored : LanguageDef := languageDef! {
  name : "PatternText"
  types {
    RxPattern RxSequence RxRepeat RxAtom RxScalar RxEscScalar
    RxClassScalar RxClassFirstScalar RxClass RxClassFirst RxClassTail RxClassItem
    RxDigits RxDigit RxName RxNameChar RxFlags RxFlag
    RxPropertyName RxPropertyChar RxHexDigits RxHexDigit
    RxClassUnion RxClassAmpTail RxClassTildeTail RxClassEndpoint RxClassFirstEndpoint
  }
  terms {
    «re-src:pattern». body:RxSequence |- body : RxPattern;
    «re-src:alt». left:RxPattern, right:RxSequence |- left "|" right : RxPattern;
    «re-src:empty». |- : RxSequence;
    «re-src:sequence». head:RxRepeat, tail:RxSequence |- head tail : RxSequence;
    «re-src:atom». body:RxAtom |- body : RxRepeat;
    «re-src:star». body:RxAtom |- body "*" : RxRepeat;
    «re-src:star-lazy». body:RxAtom |- body "*?" : RxRepeat;
    «re-src:plus». body:RxAtom |- body "+" : RxRepeat;
    «re-src:plus-lazy». body:RxAtom |- body "+?" : RxRepeat;
    «re-src:optional». body:RxAtom |- body "?" : RxRepeat;
    «re-src:optional-lazy». body:RxAtom |- body "??" : RxRepeat;
    «re-src:exact». body:RxAtom, count:RxDigits |- body "{" count "}" : RxRepeat;
    «re-src:at-least». body:RxAtom, count:RxDigits |- body "{" count ",}" : RxRepeat;
    «re-src:bounded». body:RxAtom, low:RxDigits, high:RxDigits |- body "{" low "," high "}" : RxRepeat;
    «re-src:exact-lazy». body:RxAtom, count:RxDigits |- body "{" count "}?" : RxRepeat;
    «re-src:at-least-lazy». body:RxAtom, count:RxDigits |- body "{" count ",}?" : RxRepeat;
    «re-src:bounded-lazy». body:RxAtom, low:RxDigits, high:RxDigits |- body "{" low "," high "}?" : RxRepeat;
    «re-src:literal». value:RxScalar |- value : RxAtom;
    «re-src:dot». |- "." : RxAtom;
    «re-src:start». |- "^" : RxAtom;
    «re-src:end». |- "$" : RxAtom;
    «re-src:capture». body:RxPattern |- "(" body ")" : RxAtom;
    «re-src:group». body:RxPattern |- "(?:" body ")" : RxAtom;
    «re-src:named». «name»:RxName, body:RxPattern |- "(?<" «name» ">" body ")" : RxAtom;
    «re-src:named-python». «name»:RxName, body:RxPattern |- "(?P<" «name» ">" body ")" : RxAtom;
    «re-src:flags». flags:RxFlags |- "(?" flags ")" : RxAtom;
    «re-src:scoped-flags». flags:RxFlags, body:RxPattern |- "(?" flags ":" body ")" : RxAtom;
    «re-src:lookahead». body:RxPattern |- "(?=" body ")" : RxAtom;
    «re-src:not-lookahead». body:RxPattern |- "(?!" body ")" : RxAtom;
    «re-src:lookbehind». body:RxPattern |- "(?<=" body ")" : RxAtom;
    «re-src:not-lookbehind». body:RxPattern |- "(?<!" body ")" : RxAtom;
    «re-src:escape». value:RxEscScalar |- "\\" value : RxAtom;
    «re-src:class». body:RxClass |- "[" body "]" : RxAtom;
    «re-src:class-not». body:RxClass |- "[^" body "]" : RxAtom;
    «re-src:class-empty». |- : RxClassUnion;
    «re-src:class-first». head:RxClassFirst, tail:RxClassTail |- head tail : RxClassUnion;
    «re-src:class-initial-dash». tail:RxClassTail |- "-" tail : RxClassUnion;
    «re-src:first-char». value:RxClassFirstScalar |- value : RxClassFirst;
    «re-src:first-escape». value:RxEscScalar |- "\\" value : RxClassFirst;
    «re-src:first-range». low:RxClassFirstEndpoint, high:RxClassEndpoint |- low "-" high : RxClassFirst;
    «re-src:class-tail-empty». |- : RxClassTail;
    «re-src:class-tail-dash». |- "-" : RxClassTail;
    «re-src:class-tail». head:RxClassItem, tail:RxClassTail |- head tail : RxClassTail;
    «re-src:class-char». value:RxClassScalar |- value : RxClassItem;
    «re-src:class-escape». value:RxEscScalar |- "\\" value : RxClassItem;
    «re-src:class-range». low:RxClassEndpoint, high:RxClassEndpoint |- low "-" high : RxClassItem;
    «re-src:digits-one». value:RxDigit |- value : RxDigits;
    «re-src:digits-more». head:RxDigit, tail:RxDigits |- head tail : RxDigits;
    «re-src:name-one». value:RxNameChar |- value : RxName;
    «re-src:name-more». head:RxNameChar, tail:RxName |- head tail : RxName;
    «re-src:flags-one». value:RxFlag |- value : RxFlags;
    «re-src:flags-more». head:RxFlag, tail:RxFlags |- head tail : RxFlags;
    «re-src:flag-i». |- "i" : RxFlag;
    «re-src:flag-m». |- "m" : RxFlag;
    «re-src:flag-s». |- "s" : RxFlag;
    «re-src:flag-x». |- "x" : RxFlag;
    «re-src:flag-u». |- "u" : RxFlag;
    «re-src:flag-U». |- "U" : RxFlag;
    «re-src:flag-minus». |- "-" : RxFlag;
    «re-src:property». «name»:RxPropertyName |- "\\p{" «name» "}" : RxAtom;
    «re-src:not-property». «name»:RxPropertyName |- "\\P{" «name» "}" : RxAtom;
    «re-src:first-property». «name»:RxPropertyName |- "\\p{" «name» "}" : RxClassFirst;
    «re-src:first-not-property». «name»:RxPropertyName |- "\\P{" «name» "}" : RxClassFirst;
    «re-src:class-property». «name»:RxPropertyName |- "\\p{" «name» "}" : RxClassItem;
    «re-src:class-not-property». «name»:RxPropertyName |- "\\P{" «name» "}" : RxClassItem;
    «re-src:hex». digits:RxHexDigits |- "\\x{" digits "}" : RxAtom;
    «re-src:unicode-hex». digits:RxHexDigits |- "\\u{" digits "}" : RxAtom;
    «re-src:first-hex». digits:RxHexDigits |- "\\x{" digits "}" : RxClassFirst;
    «re-src:class-hex». digits:RxHexDigits |- "\\x{" digits "}" : RxClassItem;
    «re-src:property-one». value:RxPropertyChar |- value : RxPropertyName;
    «re-src:property-more». head:RxPropertyChar, tail:RxPropertyName |- head tail : RxPropertyName;
    «re-src:hex-one». value:RxHexDigit |- value : RxHexDigits;
    «re-src:hex-more». head:RxHexDigit, tail:RxHexDigits |- head tail : RxHexDigits;
    «re-src:class-union». body:RxClassUnion |- body : RxClass;
    «re-src:class-intersection». left:RxClass, right:RxClassUnion |- left "&&" right : RxClass;
    «re-src:class-difference». left:RxClass, right:RxClassUnion |- left "--" right : RxClass;
    «re-src:class-symmetric-difference». left:RxClass, right:RxClassUnion |- left "~~" right : RxClass;
    «re-src:first-nested». body:RxClass |- "[" body "]" : RxClassFirst;
    «re-src:first-nested-not». body:RxClass |- "[^" body "]" : RxClassFirst;
    «re-src:class-nested». body:RxClass |- "[" body "]" : RxClassItem;
    «re-src:class-nested-not». body:RxClass |- "[^" body "]" : RxClassItem;
    «re-src:first-open». |- "[" : RxClassFirst;
    «re-src:class-first-amp». tail:RxClassAmpTail |- "&" tail : RxClassUnion;
    «re-src:class-first-tilde». tail:RxClassTildeTail |- "~" tail : RxClassUnion;
    «re-src:class-tail-amp». tail:RxClassAmpTail |- "&" tail : RxClassTail;
    «re-src:class-tail-tilde». tail:RxClassTildeTail |- "~" tail : RxClassTail;
    «re-src:class-amp-empty». |- : RxClassAmpTail;
    «re-src:class-amp-dash». |- "-" : RxClassAmpTail;
    «re-src:class-amp-item». head:RxClassItem, tail:RxClassTail |- head tail : RxClassAmpTail;
    «re-src:class-amp-tilde». tail:RxClassTildeTail |- "~" tail : RxClassAmpTail;
    «re-src:class-tilde-empty». |- : RxClassTildeTail;
    «re-src:class-tilde-dash». |- "-" : RxClassTildeTail;
    «re-src:class-tilde-item». head:RxClassItem, tail:RxClassTail |- head tail : RxClassTildeTail;
    «re-src:class-tilde-amp». tail:RxClassAmpTail |- "&" tail : RxClassTildeTail;
    «re-src:endpoint-char». value:RxClassScalar |- value : RxClassEndpoint;
    «re-src:endpoint-escape». value:RxEscScalar |- "\\" value : RxClassEndpoint;
    «re-src:endpoint-hex». digits:RxHexDigits |- "\\x{" digits "}" : RxClassEndpoint;
    «re-src:endpoint-unicode-hex». digits:RxHexDigits |- "\\u{" digits "}" : RxClassEndpoint;
    «re-src:first-endpoint-char». value:RxClassFirstScalar |- value : RxClassFirstEndpoint;
    «re-src:first-endpoint-escape». value:RxEscScalar |- "\\" value : RxClassFirstEndpoint;
    «re-src:first-endpoint-hex». digits:RxHexDigits |- "\\x{" digits "}" : RxClassFirstEndpoint;
    «re-src:first-endpoint-unicode-hex». digits:RxHexDigits |- "\\u{" digits "}" : RxClassFirstEndpoint;
    «re-src:first-unicode-hex». digits:RxHexDigits |- "\\u{" digits "}" : RxClassFirst;
    «re-src:class-unicode-hex». digits:RxHexDigits |- "\\u{" digits "}" : RxClassItem;
    «re-src:backref». value:RxDigits |- "\\" value : RxAtom;
    «re-src:backref-name». «name»:RxName |- "\\k<" «name» ">" : RxAtom;
    «re-src:backref-python». «name»:RxName |- "(?P=" «name» ")" : RxAtom;
    «re-src:endpoint-amp». |- "&" : RxClassEndpoint;
    «re-src:endpoint-tilde». |- "~" : RxClassEndpoint;
    «re-src:endpoint-open». |- "[" : RxClassEndpoint;
    «re-src:first-endpoint-amp». |- "&" : RxClassFirstEndpoint;
    «re-src:first-endpoint-tilde». |- "~" : RxClassFirstEndpoint;
    «re-src:first-endpoint-open». |- "[" : RxClassFirstEndpoint;
  }
  equations {}
  rewrites {}
}

def portableText : String := Text.render (Portable.coreCodec.encode authored)

theorem portable_recovery :
    (Text.read? portableText).bind Portable.coreCodec.decode = some authored := by
  simp [portableText, Portable.coreCodec.decode_encode]

theorem sort_count : authored.types.length = 27 := by decide
theorem rule_count : authored.terms.length = 113 := by decide

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence

def binding : Binding where
  literalRef := fun text => some ("literal:" ++ text)
  lexicalSortRef := fun sort =>
    if ["RxScalar", "RxEscScalar", "RxClassScalar", "RxClassFirstScalar", "RxDigit", "RxNameChar",
      "RxPropertyChar", "RxHexDigit"].contains sort
    then some ("lexical:" ++ sort) else none
  categoryRef := fun sort => "category:" ++ sort
  ruleRef := fun label => "rule:" ++ label

/-- The real structural compiler accepts every source row. Lexical recognition
is an independently supplied class realization, not invented by this proof. -/
theorem structural_compilation_accepts : (compileRules? binding authored).isSome = true := by decide

def compiledRules : List CompiledRule := (compileRules? binding authored).getD []

theorem compiled_exact : compileRules? binding authored = some compiledRules := by rfl

theorem compiled_retains_all_rows : compiledRules.map CompiledRule.source = authored.terms :=
  compileRules_sourceRules binding authored compiledRules compiled_exact

theorem compiled_retains_all_syntax :
    compiledRules.map (fun rule => rule.atoms.map StructuralAtom.sourceSyntax) =
      authored.terms.map GrammarRule.syntaxPattern :=
  compileRules_sourceSyntax binding authored compiledRules compiled_exact

/-- Preserve and reflect the token-level grammar relation. This does not turn
the theorem into raw-byte lexical or packed-forest adequacy. -/
theorem structural_derivation_iff (sort : String) (tokens : List String) (tree : Pattern) :
    CompiledDerives compiledRules sort tokens tree ↔
      Mettapedia.OSLF.Framework.GrammarDerives.Derives authored sort tokens tree :=
  compileRules_derivation_iff compiled_exact sort tokens tree

open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-- Unicode 16.0.0 decimal blocks. Each digit is interpreted separately, so
mixing decimal blocks does not impose a script-homogeneity condition. -/
def decimalStarts : List Nat := [
  48,1632,1776,1984,2406,2534,2662,2790,2918,3046,3174,3302,3430,3558,3664,3792,
  3872,4160,4240,6112,6160,6470,6608,6784,6800,6992,7088,7232,7248,42528,43216,
  43264,43472,43504,43600,44016,65296,66720,68912,68928,69734,69872,69942,70096,
  70384,70736,70864,71248,71360,71376,71386,71472,71904,72016,72688,72784,73040,
  73120,73552,90416,92768,92864,93008,93552,118000,120782,120792,120802,120812,
  120822,123200,123632,124144,124401,125264,130032]

def decimalPoints : List Nat :=
  decimalStarts.flatMap fun first => (List.range 10).map (first + ·)

/-- Scalar classes and token result sorts stay an explicit independent layer.
No whitespace is erased implicitly by this lexical interpretation. -/
def profile : ParserProfileLayer where
  name := "RegexPatternSyntaxV1"
  startSort := "RxPattern"
  classes := [
    ⟨"RxLiteralClass", .except [36, 40, 41, 42, 43, 46, 63, 91, 92, 93, 94, 123, 124, 125]⟩,
    ⟨"RxEscapedClass", .except (decimalPoints.take 10 ++ [80, 107, 112, 117, 120] ++ decimalPoints.drop 10)⟩,
    ⟨"RxClassLiteralClass", .except [38, 45, 91, 92, 93, 126]⟩,
    ⟨"RxClassFirstLiteralClass", .except [38, 45, 91, 92, 93, 94, 126]⟩,
    ⟨"RxDigitClass", .points decimalPoints⟩,
    ⟨"RxNameClass", .except [10, 13, 40, 41, 62]⟩,
    ⟨"RxPropertyNameClass", .except [10, 13, 40, 41, 123, 125]⟩,
    ⟨"RxHexDigitClass", .points [48,49,50,51,52,53,54,55,56,57,
      65,66,67,68,69,70,97,98,99,100,101,102]⟩]
  states := [
    ⟨"RxScalar", "RxLiteralClass", "re-src:lex-scalar"⟩,
    ⟨"RxEscScalar", "RxEscapedClass", "re-src:lex-escaped"⟩,
    ⟨"RxClassScalar", "RxClassLiteralClass", "re-src:lex-class"⟩,
    ⟨"RxClassFirstScalar", "RxClassFirstLiteralClass", "re-src:lex-class-first"⟩,
    ⟨"RxDigit", "RxDigitClass", "re-src:lex-digit"⟩,
    ⟨"RxNameChar", "RxNameClass", "re-src:lex-name"⟩,
    ⟨"RxPropertyChar", "RxPropertyNameClass", "re-src:lex-property"⟩,
    ⟨"RxHexDigit", "RxHexDigitClass", "re-src:lex-hex"⟩]

def profileText := Mettapedia.GSLT.Parsing.ParserProfileWire.render profile

namespace Controls

theorem empty_sequence_is_retained :
    authored.terms[2]?.map GrammarRule.syntaxPattern = some [] := rfl

theorem alternatives_retain_order :
    authored.terms[1]?.map GrammarRule.syntaxPattern = some
      [.nonTerminal "left", .terminal "|", .nonTerminal "right"] := rfl

theorem bounded_repeat_keeps_both_bounds :
    authored.terms[13]?.map GrammarRule.syntaxPattern = some
      [.nonTerminal "body", .terminal "{", .nonTerminal "low", .terminal ",",
       .nonTerminal "high", .terminal "}"] := rfl

theorem range_separator_is_not_literal_member :
    authored.terms[45]?.map GrammarRule.syntaxPattern ≠
      some [.nonTerminal "low", .nonTerminal "high"] := by
  intro same
  have lengths := congrArg (Option.map List.length) same
  change (some 3 : Option Nat) = some 2 at lengths
  cases lengths

theorem lexical_space_and_unicode_preserved :
    profile.classAccepts? "RxLiteralClass" 32 = some true ∧
      profile.classAccepts? "RxLiteralClass" 955 = some true := by decide

theorem operator_is_not_a_literal_token :
    profile.classAccepts? "RxLiteralClass" 42 = some false := by decide

theorem complements_do_not_include_surrogates_or_out_of_range :
    profile.classAccepts? "RxEscapedClass" 55296 = some false ∧
      profile.classAccepts? "RxEscapedClass" 1114112 = some false := by decide

theorem mixed_decimal_blocks_are_accepted :
    profile.classAccepts? "RxDigitClass" 49 = some true ∧
      profile.classAccepts? "RxDigitClass" 1634 = some true ∧
      profile.classAccepts? "RxDigitClass" 65299 = some true := by decide

theorem hexadecimal_is_not_any_unicode_number :
    profile.classAccepts? "RxHexDigitClass" 70 = some true ∧
      profile.classAccepts? "RxHexDigitClass" 1634 = some false := by decide

theorem property_names_retain_separators_but_not_closing_brace :
    profile.classAccepts? "RxPropertyNameClass" 61 = some true ∧
      profile.classAccepts? "RxPropertyNameClass" 125 = some false := by decide

theorem extended_escape_prefixes_are_not_generic_escapes :
    profile.classAccepts? "RxEscapedClass" 112 = some false ∧
      profile.classAccepts? "RxEscapedClass" 120 = some false ∧
      profile.classAccepts? "RxEscapedClass" 110 = some true := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSyntaxAuthoring
