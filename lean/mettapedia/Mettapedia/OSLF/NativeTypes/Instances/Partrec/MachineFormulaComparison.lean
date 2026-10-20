import Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison
import Mettapedia.OSLF.NativeTypes.Runtime.Local
import Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.OSLF.Framework

/-!
# The retained native machine agrees with the independent Partrec checker

The same certified local cursor that is installed by the public generator
checks the translated shared modal fragment. Its total work budget counts
all nested formula and matcher jobs once. Agreement is proved for every
admitted open configuration and every formula in the shared fragment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.MachineFormulaComparison

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Formula
open Mettapedia.OSLF.SatisfactionUndecidable
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Formula Test denotation)
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend (theory Source)
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaComparison (fromLegacy? noLeaves denotation_iff_original
  translation_recognizes_fragment)

/-- A leaf-free formula can use the actual generated constructor catalogue
without supplying fabricated constructor predicates. -/
def lift : Formula Empty → Formula Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Leaf
  | .atom impossible => nomatch impossible
  | .top => .top
  | .bottom => .bottom
  | .conj left right => .conj (lift left) (lift right)
  | .disj left right => .disj (lift left) (lift right)
  | .neg inner => .neg (lift inner)
  | .imp left right => .imp (lift left) (lift right)
  | .possibility inner => .possibility (lift inner)
  | .outgoingUniversal inner => .outgoingUniversal (lift inner)
  | .separating index left right => .separating index (lift left) (lift right)

theorem lifted_meaning (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (formula : Formula Empty) :
    denotation (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.tests configuration bound) (lift formula) =
      denotation (noLeaves bound) formula := by
  induction formula with
  | atom impossible => nomatch impossible
  | top => rfl
  | bottom => rfl
  | conj left right leftIH rightIH => simp only [lift, denotation, leftIH, rightIH]
  | disj left right leftIH rightIH => simp only [lift, denotation, leftIH, rightIH]
  | neg inner ih => simp only [lift, denotation, ih]
  | imp left right leftIH rightIH => simp only [lift, denotation, leftIH, rightIH]
  | possibility inner ih => simp only [lift, denotation, ih]
  | outgoingUniversal inner ih => simp only [lift, denotation, ih]
  | separating index left right leftIH rightIH => simp only [lift, denotation, leftIH, rightIH]

def run (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (formula : Formula Empty) (source : Pattern) (typed : Source bound source) (budget : Nat) : Option Bool :=
  let runtime := Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound
  (Mettapedia.OSLF.NativeTypes.Decision.Machine.run runtime.cursor runtime.leaves (lift formula) source typed budget).outcome.answer

def totalBound (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (formula : Formula Empty) (source : Pattern) (typed : Source bound source) : Nat :=
  let runtime := Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound
  Mettapedia.OSLF.NativeTypes.Decision.Machine.totalBound runtime.cursor runtime.leaves (lift formula) source typed

theorem whole_fragment_meaning (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    (interpretation : AtomSem) {original : OSLFFormula} {formula : Formula Empty}
    (translated : fromLegacy? original = some formula) (source : Pattern) (typed : Source bound source) :
    Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation
        (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound).leaves (lift formula) (.empty _) source ↔
      sem Mettapedia.Languages.PartrecMachine.Reduces interpretation original source := by
  have equal := Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation_comparison
    (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound).leaves
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.tests configuration bound)
    (Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound).leaf_meaning (lift formula)
  have atSource := congrArg (fun predicate : GSLTTypeSynthesis.EquationPredicate (theory bound) =>
    predicate source) (equal.trans (lifted_meaning configuration bound formula))
  exact (Iff.of_eq atSource).trans (denotation_iff_original bound interpretation translated source typed)

theorem executable_answers_agree (configuration : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.Configuration) (bound : List TypeExpr)
    {original : OSLFFormula} {formula : Formula Empty} (translated : fromLegacy? original = some formula)
    (source : Pattern) (typed : Source bound source) (budget : Nat)
    (enough : totalBound configuration bound formula source typed ≤ budget) :
    run configuration bound formula source typed budget = some (decideModalSearch original source) := by
  let runtime := Mettapedia.OSLF.NativeTypes.Runtime.Local.partrecRuntime configuration bound
  have supported := (translation_recognizes_fragment original).mp ⟨formula, translated⟩
  have correct := whole_fragment_meaning configuration bound (fun _ _ => False) translated source typed
  obtain ⟨answer, read⟩ := Mettapedia.OSLF.NativeTypes.Decision.Machine.complete_at_bound
    runtime.cursor runtime.leaves (lift formula) source typed budget enough
  change run configuration bound formula source typed budget = some answer at read
  rw [read]
  apply congrArg some
  cases answer with
  | true =>
      have positive := Mettapedia.OSLF.NativeTypes.Decision.Machine.positive
        runtime.cursor runtime.leaves (lift formula) source typed budget read
      exact ((decideModalSearch_iff supported source).mpr (correct.mp positive)).symm
  | false =>
      have negative := Mettapedia.OSLF.NativeTypes.Decision.Machine.negative
        runtime.cursor runtime.leaves (lift formula) source typed budget read
      cases actual : decideModalSearch original source with
      | false => rfl
      | true => exact (negative (correct.mpr ((decideModalSearch_iff supported source).mp actual))).elim

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.MachineFormulaComparison
