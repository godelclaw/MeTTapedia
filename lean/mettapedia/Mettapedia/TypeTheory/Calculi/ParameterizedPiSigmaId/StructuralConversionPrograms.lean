import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCertificate
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionChecking
import Mettapedia.TypeTheory.Authority

/-!
# Programmable conversion results with exact endpoints

The bounded producer returns the existing checked certificate. The authority
outcome retains unsuccessful search as incomplete; no inequality is inferred.
Retyping additionally requires the source judgment and the target's formation.
An identity proof is not an input to the structural conversion decoder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionPrograms

open StructuralConversionCode AuthorityTheory

variable {Head : Type} [DecidableEq Head]
variable {root : RootComputation Head} {headEq : Head → Head → Prop} [DecidableRel headEq]
variable (decoder : RootDecoder root)
variable (search : {n : Nat} → Tm Head n → Option (decoder.Code n))

theorem compare_checked (fuel : Nat) {n : Nat} (left right : Tm Head n)
    (code : Code Head decoder.Code n)
    (accepted : StructuralConversionSearch.compare decoder search
      (headEq := headEq) fuel left right = some code) :
    code.check headEq decoder.decode left right = true := by
  dsimp only [StructuralConversionSearch.compare] at accepted
  cases matched : StructuralConversionSearch.compareShape (RootCode := decoder.Code)
      (StructuralConversionSearch.produce decoder.decode search fuel left).term
      (StructuralConversionSearch.produce decoder.decode search fuel right).term with
  | none => simp [matched] at accepted
  | some middle =>
      simp only [matched, Option.bind_eq_bind, Option.bind_some] at accepted
      split at accepted
      · rename_i checked
        cases Option.some.inj accepted
        exact checked
      · cases accepted

/-- This procedure has no negative-evidence branch. Its inputs already lie
in the scoped term grammar; raw reader boundaries are handled before it. -/
def compareOutcome (fuel : Nat) {n : Nat} (left right : Tm Head n) :
    Outcome (Certificate headEq decoder.decode left right) Empty Empty Nat :=
  match found : StructuralConversionSearch.compare decoder search (headEq := headEq) fuel left right with
  | none => .incomplete fuel
  | some code => .established ⟨code, compare_checked decoder search fuel left right code found⟩

theorem compareOutcome_incomplete_iff (fuel : Nat) {n : Nat} (left right : Tm Head n) :
    (compareOutcome decoder search (headEq := headEq) fuel left right).asBool = none ↔
      StructuralConversionSearch.compare decoder search (headEq := headEq) fuel left right = none := by
  unfold compareOutcome
  split <;> simp_all [Outcome.asBool]

theorem certificate_conversion {n : Nat} {left right : Tm Head n}
    (certificate : Certificate headEq decoder.decode left right) : Conv headEq left right root :=
  Code.check_sound decoder certificate.checked

/-- An admitted term may change its displayed type only after formation of
the target type and checking the selected conversion recipe. -/
def retypeOutcome {R : Rules Head} [DecidableRel R.headEq]
    (decoder : RootDecoder R.computation)
    (search : {n : Nat} → Tm Head n → Option (decoder.Code n))
    (fuel : Nat) {n : Nat} {context : Ctx Head n} {term sourceType targetType : Tm Head n}
    {sortHead : Head} (source : FormationSensitive.Judgment R context term sourceType)
    (targetFormation : FormationSensitive.Typing R context targetType (.head sortHead))
    (isUniverse : R.isUniverse sortHead) :
    Outcome {_certificate : Certificate R.headEq decoder.decode sourceType targetType //
      FormationSensitive.Judgment R context term targetType} Empty Empty Nat :=
  match compareOutcome decoder search (headEq := R.headEq) fuel sourceType targetType with
  | .established certificate => .established ⟨certificate,
      source.convertChecked decoder targetFormation isUniverse certificate.checked⟩
  | .refuted impossible => nomatch impossible
  | .outsideFragment impossible => nomatch impossible
  | .incomplete fuel => .incomplete fuel

/-- A genuine beta equality can remain unfinished at zero search budget.
The control uses different endpoint syntax, so reflexivity cannot mask it. -/
theorem zero_budget_can_miss_beta (head : Head) :
    (compareOutcome decoder search (headEq := headEq) 0
      (.app (.lam (.var 0)) (.head head) : Tm Head 0) (.head head)).asBool = none ∧
    Conv headEq (.app (.lam (.var 0)) (.head head) : Tm Head 0) (.head head) root := by
  constructor
  · rw [compareOutcome_incomplete_iff]
    simp [StructuralConversionSearch.compare, StructuralConversionSearch.produce,
      StructuralConversionSearch.compareShape]
  · simpa only [inst0, subst, subst0, Fin.cases_zero] using
      (Relation.EqvGen.rel _ _ (Step.betaPi (.var 0 : Tm Head 1) (.head head : Tm Head 0)) :
        Conv headEq _ _ root)

#print axioms compare_checked
#print axioms certificate_conversion
#print axioms zero_budget_can_miss_beta

end StructuralConversionPrograms
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
