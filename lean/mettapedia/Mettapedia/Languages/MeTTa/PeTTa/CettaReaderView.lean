import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# Boolean representation at the PeTTa reader boundary

CeTTa's compiled PeTTa reader retains bare Booleans as the symbols `true` and
`false`; the source model uses grounded Boolean values. Quoted strings and
variable identities remain separate. This module gives a structural view
between those representations and proves its connection to the existing
source reader. The native-shaped reader uses the independent source grammar,
so these laws do not verify the compiled reader or native evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaReaderView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing.ExactDecimalLexeme (parseInteger?)

mutual
  def semanticView : Atom → Atom
    | .symbol name =>
        if name = "true" then .grounded (.bool true)
        else if name = "false" then .grounded (.bool false)
        else .symbol name
    | .expression items => .expression (semanticViews items)
    | .var name => .var name
    | .grounded value => .grounded value

  def semanticViews : List Atom → List Atom
    | [] => []
    | first :: rest => semanticView first :: semanticViews rest
end

mutual
  theorem semanticView_idempotent (atom : Atom) :
      semanticView (semanticView atom) = semanticView atom := by
    cases atom with
    | symbol name =>
        simp only [semanticView]
        split
        · rfl
        · split
          · rfl
          · simp_all [semanticView]
    | var name => rfl
    | grounded value => rfl
    | expression items =>
        exact congrArg Atom.expression (semanticViews_idempotent items)

  theorem semanticViews_idempotent (atoms : List Atom) :
      semanticViews (semanticViews atoms) = semanticViews atoms := by
    cases atoms with
    | nil => rfl
    | cons first rest =>
        simp only [semanticViews, semanticView_idempotent first, semanticViews_idempotent rest]
end

theorem semanticViews_length (atoms : List Atom) :
    (semanticViews atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons first rest ih => simp only [semanticViews, List.length_cons, ih]

/-- Token conversion in the native representation. Grammar parsing and
numeric admission remain separately checked boundaries. -/
def readToken (token : String) : Except String Atom :=
  match SpaceSemantics.readPlainString token with
  | some value => .ok (.grounded (.string value))
  | none =>
      if token.startsWith "$" then
        let name := (token.drop 1).toString
        if name.isEmpty then .error "empty source variable" else .ok (.var name)
      else if token = "True" || token = "true" then .ok (.symbol "true")
      else if token = "False" || token = "false" then .ok (.symbol "false")
      else if token.startsWith "\"" then do
        match ← Lean.Json.parse token with
        | .str value => .ok (.grounded (.string value))
        | _ => .error "expected a quoted string"
      else
        match parseInteger? token with
        | some value => .ok (.grounded (.int value))
        | none => .ok (.symbol token)

theorem token_view (token : String) :
    (readToken token).map semanticView = SpaceSemantics.readToken token := by
  unfold readToken SpaceSemantics.readToken
  cases plain : SpaceSemantics.readPlainString token with
  | some value => rfl
  | none =>
      dsimp only
      by_cases isVar : token.startsWith "$"
      · simp only [isVar, ↓reduceIte]
        split <;> rfl
      · simp only [isVar, Bool.false_eq_true, ↓reduceIte]
        by_cases positive : token = "True" ∨ token = "true"
        · rcases positive with rfl | rfl <;> rfl
        · have notPositive : (decide (token = "True") || decide (token = "true")) = false := by
            simp [(not_or.mp positive).1, (not_or.mp positive).2]
          simp only [notPositive, Bool.false_eq_true, ↓reduceIte]
          by_cases negative : token = "False" ∨ token = "false"
          · rcases negative with rfl | rfl <;> rfl
          · have notNegative : (decide (token = "False") || decide (token = "false")) = false := by
              simp [(not_or.mp negative).1, (not_or.mp negative).2]
            simp only [notNegative, Bool.false_eq_true, ↓reduceIte]
            split
            · cases parsed : Lean.Json.parse token <;>
                simp only [bind, Except.bind, Except.map]
              case ok value => cases value <;> rfl
            · cases integer : parseInteger? token with
              | some value => rfl
              | none =>
                  have nt : token ≠ "true" := fun same => positive (Or.inr same)
                  have nf : token ≠ "false" := fun same => negative (Or.inr same)
                  simp [semanticView, nt, nf, Except.map]

mutual
  def readExpression : SExpr → Except String Atom
    | .atom token => readToken token
    | .list items => .expression <$> readExpressions items

  def readExpressions : List SExpr → Except String (List Atom)
    | [] => .ok []
    | first :: rest => do
        return (← readExpression first) :: (← readExpressions rest)
end

mutual
  theorem expression_view (expression : SExpr) :
      (readExpression expression).map semanticView = SpaceSemantics.readExpression expression := by
    cases expression with
    | atom token => exact token_view token
    | list items =>
        simp only [readExpression, SpaceSemantics.readExpression]
        rw [← expressions_view items]
        cases parsed : readExpressions items <;> rfl

  theorem expressions_view (expressions : List SExpr) :
      (readExpressions expressions).map semanticViews = SpaceSemantics.readExpressions expressions := by
    cases expressions with
    | nil => rfl
    | cons first rest =>
        simp only [readExpressions, SpaceSemantics.readExpressions]
        rw [← expression_view first, ← expressions_view rest]
        cases head : readExpression first <;> cases tail : readExpressions rest <;> rfl
end

def readSource (source : String) : Except String (List Atom) := do
  let expressions ← (Algorithms.MeTTa.Simple.Parser.parseSExprProgramWithDetailed
    MeTTailCore.MeTTaSyntax.petta source).mapError toString
  readExpressions (expressions.map Prod.snd)

theorem source_view (source : String) :
    (readSource source).map semanticViews = SpaceSemantics.readSource source := by
  unfold readSource SpaceSemantics.readSource
  cases parsed : (Algorithms.MeTTa.Simple.Parser.parseSExprProgramWithDetailed
      MeTTailCore.MeTTaSyntax.petta source).mapError toString with
  | error _ => rfl
  | ok expressions => exact expressions_view (expressions.map Prod.snd)

theorem native_boolean_tokens :
    readToken "True" = .ok (.symbol "true") ∧
      readToken "false" = .ok (.symbol "false") := by decide +kernel

theorem quoted_boolean_is_distinct :
    semanticView (.grounded (.string "True")) = .grounded (.string "True") ∧
      semanticView (.var "true") = .var "true" ∧
      semanticView (.symbol "true") ≠ .grounded (.string "True") := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.CettaReaderView
