import Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax

/-! Printing retained source derivations uses their authored production
occurrences, decoded terminals and lexical leaves. It does not look up or
slice the input text. Equal constructor labels need not select the same row.
The full-span law preserves literal spelling, comments and Unicode scalars.
Constructing a source derivation from a semantic program is a separate task. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence LanguageDefScalarSyntax

variable {literalScalars? : String → Option (List Nat)} {profile : ParserProfileLayer}
  {language : LanguageDef} {input : List Nat}

mutual
  def render {sort : String} {start stop : Nat} {tree : CST}
      (derivation : DerivesAt literalScalars? profile language input sort start stop tree) : List Nat :=
    match derivation with
    | @DerivesAt.lexical _ _ _ _ _ point _ _ _ => [point]
    | .structural _ body => renderItems body
    termination_by structural derivation

  def renderItems {rule : GrammarRule} {items : List SyntaxItem} {start stop : Nat}
      {children : List CST}
      (derivation : ItemsDeriveAt literalScalars? profile language input rule items start stop children) :
      List Nat :=
    match derivation with
    | .nil => []
    | @ItemsDeriveAt.terminal _ _ _ _ _ codepoints _ _ _ _ _ _ _ _ rest =>
        codepoints ++ renderItems rest
    | .nonterminal _ first rest => render first ++ renderItems rest
    termination_by structural derivation
end

def sequence_append {first second : List Nat} {start middle stop : Nat}
    (left : ScalarSequenceMatchesAt input first start middle)
    (right : ScalarSequenceMatchesAt input second middle stop) :
    ScalarSequenceMatchesAt input (first ++ second) start stop :=
  match left with
  | .nil _ => right
  | .cons lookup rest => .cons lookup (sequence_append rest right)
termination_by structural left

theorem sequence_length {codepoints : List Nat} {start stop : Nat}
    (matched : ScalarSequenceMatchesAt input codepoints start stop) :
    stop = start + codepoints.length := by
  induction matched with
  | nil => simp
  | cons _ _ ih => simp only [List.length_cons]; omega

theorem sequence_lookup {codepoints : List Nat} {start stop : Nat}
    (matched : ScalarSequenceMatchesAt input codepoints start stop)
    (position : Fin codepoints.length) :
    input[start + position.val]? = some codepoints[position.val] := by
  induction matched with
  | nil => exact Fin.elim0 position
  | @cons start point points stop lookup _ ih =>
    rcases position with ⟨position, bounded⟩
    cases position with
    | zero => simpa using lookup
    | succ position =>
      have bound : position < points.length := Nat.lt_of_succ_lt_succ bounded
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih ⟨position, bound⟩

mutual
  def render_matches {sort : String} {start stop : Nat} {tree : CST}
      (derivation : DerivesAt literalScalars? profile language input sort start stop tree) :
      ScalarSequenceMatchesAt input (render derivation) start stop :=
    match derivation with
    | .lexical _ lookup _ => .cons lookup (.nil _)
    | .structural _ body => renderItems_matches body
    termination_by structural derivation

  def renderItems_matches {rule : GrammarRule} {items : List SyntaxItem} {start stop : Nat}
      {children : List CST}
      (derivation : ItemsDeriveAt literalScalars? profile language input rule items start stop children) :
      ScalarSequenceMatchesAt input (renderItems derivation) start stop :=
    match derivation with
    | .nil => .nil _
    | .terminal _ matched rest => sequence_append matched (renderItems_matches rest)
    | .nonterminal _ first rest => sequence_append (render_matches first) (renderItems_matches rest)
    termination_by structural derivation
end

theorem full_source {sort : String} {tree : CST}
    (derivation : DerivesAt literalScalars? profile language input sort 0 input.length tree) :
    render derivation = input := by
  have matched := render_matches derivation
  have length : (render derivation).length = input.length := by
    have measured := sequence_length matched
    omega
  apply List.ext_getElem length
  intro position printedBound sourceBound
  have found := sequence_lookup matched ⟨position, printedBound⟩
  have same : input[position] = (render derivation)[position] := by
    simpa only [Nat.zero_add, List.getElem?_eq_getElem sourceBound, Option.some.injEq] using found
  exact same.symm

def stringScalars (source : String) : List Nat := source.toList.map Char.toNat

def renderText {source : String} {sort : String} {tree : CST}
    (derivation : DerivesAt literalScalars? profile language (stringScalars source)
      sort 0 (stringScalars source).length tree) : String :=
  String.ofList ((render derivation).map Char.ofNat)

theorem full_text {source : String} {sort : String} {tree : CST}
    (derivation : DerivesAt literalScalars? profile language (stringScalars source)
      sort 0 (stringScalars source).length tree) :
    renderText derivation = source := by
  rw [renderText, full_source derivation]
  simp [stringScalars, List.map_map, Function.comp_def]

#print axioms render_matches
#print axioms full_source
#print axioms full_text

end Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
