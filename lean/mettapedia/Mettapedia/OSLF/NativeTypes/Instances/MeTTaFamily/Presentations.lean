import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# Operational presentations that display their sites

A generated hypercube sees only what a rewrite's source displays. Three
readings put the operational site of a language into the source:

* `programLanguage`: a MeTTa program's equations `(= lhs rhs)` are the
  rewrites `lhs ⇝ rhs` over the shared ground-atom codec. Expressions keep
  their ordered children, so the head of a call is an ordinary displayed
  occurrence, as in HE's data model. (Reading a head as a constructor label,
  as `OSLFCore.Bridge.atomToPattern` does, removes that occurrence.)
* `piSigmaIdShape`: the two-sort dependent calculus with the identity
  eliminator `J` and its computation rule `J A C d a a (refl a) ⇝ d a` added
  beside the Π-β and Σ-projection rules.
* `checkingLanguage`: an inference calculus read as proof checking: a rule
  node over its premise judgments rewrites to its conclusion, so each premise
  position is a site.

These are presentations, not semantics theorems: `programLanguage` performs
one equation application at the root, the operational site of equation
evaluation; congruence and the interpreter's evaluation order are separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData (schema)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)

/-! ## MeTTa programs -/

/-- An equation `(= left right)` as a displayed rewrite. -/
def equationRule (index : Nat) (left right : Atom) : RewriteRule where
  name := "equation-" ++ toString index
  typeContext := ((atomFreeVars left ++ atomFreeVars right).dedup).map
    fun name => (name, .base "GroundAtom")
  premises := []
  left := schema left
  right := schema right

/-- A MeTTa program as an operational presentation over the ground-atom codec. -/
def programLanguage (name : String) (program : List (Atom × Atom)) : LanguageDef :=
  { Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData.dataLanguage with
    name := name
    rewrites := program.zipIdx.map fun entry => equationRule entry.2 entry.1.1 entry.1.2 }

/-- The call `(head argument)`. -/
def call (head : String) (argument : Atom) : Atom := .expression [.symbol head, argument]

/-- `(= (f $x) (g $x))`, `(= (g a) b)`, `(= (g a) c)`: one forwarding equation
and two equations for the same call. -/
def sampleProgram : List (Atom × Atom) :=
  [(call "f" (.var "x"), call "g" (.var "x")),
   (call "g" (.symbol "a"), .symbol "b"),
   (call "g" (.symbol "a"), .symbol "c")]

/-- The same program without its last equation. -/
def sampleProgramPrefix : List (Atom × Atom) := sampleProgram.take 2

/-! ## The shape of the Π/Σ/Id computation rules -/

/-- The identity eliminator `J A C d a b p`. -/
def identityEliminator : GrammarRule where
  label := "J"
  category := "Tm"
  params := ["A", "C", "d", "a", "b", "p"].map fun name => TermParam.simple name (.base "Tm")
  syntaxPattern := []

/-- Based path induction computes on reflexivity: `J A C d a a (refl a) ⇝ d a`. -/
def identityComputation : RewriteRule where
  name := "J-refl"
  typeContext := ["A", "C", "d", "a"].map fun name => (name, TypeExpr.base "Tm")
  premises := []
  left := .apply "J" [.fvar "A", .fvar "C", .fvar "d", .fvar "a", .fvar "a",
    .apply "Refl" [.fvar "a"]]
  right := .apply "App" [.fvar "d", .fvar "a"]

open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core in
/-- Π-β, the two Σ projections and the computation rule of `J`. -/
def piSigmaIdShape : LanguageDef where
  name := "PiSigmaIdShape"
  types := twoSortDependent.types
  terms := twoSortDependent.terms ++ [identityEliminator]
  equations := []
  rewrites := twoSortDependent.rewrites ++ [identityComputation]

/-! ## Inference calculi as proof checking -/

open Mettapedia.GSLT.LanguageDef (CalculusLanguageDef)

/-- A judgment head as a constructor of the judgment carrier. -/
def judgmentConstructor (dataSort : String) (judgment : JudgmentDecl) : GrammarRule where
  label := judgment.head
  category := "Judgment"
  params := (List.range judgment.arity).map fun position =>
    TermParam.simple ("argument" ++ toString position) (.base dataSort)
  syntaxPattern := []

/-- A rule node over its premise judgments. -/
def ruleConstructor (rule : RuleSchema) : GrammarRule where
  label := rule.id.value
  category := "Judgment"
  params := (List.range rule.premises.length).map fun position =>
    TermParam.simple ("premise" ++ toString position) (.base "Judgment")
  syntaxPattern := []

/-- Checking a rule node yields its conclusion. -/
def checkingRule (dataSort : String) (rule : RuleSchema) : RewriteRule where
  name := rule.id.value
  typeContext := rule.metavariables.map fun entry => (entry.1, .base dataSort)
  premises := []
  left := .apply rule.id.value rule.premises
  right := rule.conclusion

/-- An inference calculus read as proof checking. -/
def checkingLanguage (calculus : CalculusLanguageDef) (dataSort : String) : LanguageDef where
  name := calculus.name ++ "-checking"
  types := calculus.types ++ [TypeDecl.plain "Judgment"]
  terms := calculus.terms ++ calculus.judgments.map (judgmentConstructor dataSort) ++
    calculus.rules.map ruleConstructor
  equations := []
  rewrites := calculus.rules.map (checkingRule dataSort)

end Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily
