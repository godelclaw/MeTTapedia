import Mettapedia.GSLT.LanguageDef.IndexedInductiveVectorMeaning

/-!
# Dependent meaning and forward-execution boundary controls

The actual source vector append has a forward path to its complete ordered
list value. The output representation distinguishes missing, extra, reordered
and changed payloads. A deliberately extended runtime retains that good path
while adding a wrong answer: forward existence alone is not semantic hosting.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.MeaningControls

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies IndexedInductiveNatVec Meaning VectorMeaning

def payload (value : Bool) : Tower.Tm 0 := if value then .const `True else .const `False
def parameter : Tower.Tm 0 := .const `Bool
def motive : Tower.Tm 0 := .const `ListReadout

def program : Tower.Tm 0 := vecEliminateApp parameter motive (quoteList payload [false])
  consMethod (succApp zeroTm) (vconsApp parameter zeroTm (payload true) (vnilApp parameter))
def expected : Tower.Tm 0 := quoteList payload [true, false]
def swapped : Tower.Tm 0 := quoteList payload [false, true]

/-- This path uses the real generated vector rules and the proved beta
method. Its target comes from the independently defined source append. -/
theorem append_two_values : Steps (root Bool) program expected := by
  have path := append_reduces parameter motive payload
    (Vectors.cons true Vectors.nil) (Vectors.cons false Vectors.nil)
  rw [Vectors.append_two_payloads] at path
  exact path

theorem readout_two_values : Steps (root Bool)
    (vecEliminateApp parameter motive (.const `List.Empty) consMethod
      (succApp (succApp zeroTm))
      (vconsApp parameter (succApp zeroTm) (payload true)
        (vconsApp parameter zeroTm (payload false) (vnilApp parameter)))) expected :=
  readout_reduces parameter motive payload (Vectors.cons true (Vectors.cons false Vectors.nil))

theorem payload_injective : Function.Injective payload := by
  intro first second equal
  cases first <;> cases second <;> simp_all [payload]

theorem output_retains_every_value {first second : List Bool}
    (samePacket : quoteList payload first = quoteList payload second) : first = second :=
  quoteList_injective payload_injective samePacket

/-- The constructor-only quotation certificate cannot be extended silently
to an arithmetic expression whose interpretation is the same natural value. -/
theorem computed_index_not_literal :
    ¬ QuotedCode (TypedControls.indexSyntax Bool) (quoteData payload) quoteIndex
      (Code.result (.addition .zero .zero) : Code (Vectors.interface Bool) []) := by
  intro compatible
  have impossible := compatible PUnit.unit
  cases impossible

def verdicts : List (String × Bool) := [
  ("complete ordered payload", decide (expected = .pair (payload true) (.pair (payload false) (.const `List.Empty)))),
  ("missing payload changes result", decide (expected ≠ quoteList payload [true])),
  ("extra payload changes result", decide (expected ≠ quoteList payload [true, false, false])),
  ("equal length does not preserve order", decide (expected ≠ swapped)),
  ("equal length does not preserve values", decide (expected ≠ quoteList payload [true, true])),
  ("actual parameter remains in constructor", decide
    (vconsApp parameter zeroTm (payload true) (vnilApp parameter) ≠
      vconsApp (.const `AnotherType) zeroTm (payload true) (vnilApp (.const `AnotherType)))),
  ("recursive result is not the original tail", decide
    (Tm.pair (payload true) (quoteList payload [false]) ≠
      Tm.pair (payload true) (vnilApp parameter))),
  ("length checking alone misses payload corruption", decide
    (([true, false] : List Bool).length = [false, true].length ∧ expected ≠ swapped))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

/-- One extra closed output rule, intentionally outside the source contract. -/
def forgedTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [⟨0, expected, swapped⟩]

def forgedRoot := (SchemaTableConversionCode.retained forgedTable (fun _ => true)).support

noncomputable def extendedRoot : RootComputation Tower.Head where
  step left right := (root Bool).step left right ∨ forgedRoot.step left right
  rename := by
    intro n m ren left right step
    exact step.elim (fun step => Or.inl ((root Bool).rename ren step))
      (fun step => Or.inr (forgedRoot.rename ren step))
  substitute := by
    intro n m sub left right step
    exact step.elim (fun step => Or.inl ((root Bool).substitute sub step))
      (fun step => Or.inr (forgedRoot.substitute sub step))

private theorem liftStep {n : Nat} {left right : Tower.Tm n}
    (step : StepCore (root Bool) (fun _ _ => False) left right) :
    StepCore extendedRoot (fun _ _ => False) left right := by
  induction step with
  | root step => exact .root (Or.inl step)
  | betaPi body argument => exact .betaPi body argument
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head impossible => exact impossible.elim
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

theorem extended_still_has_correct_path : Steps extendedRoot program expected := by
  exact Relation.ReflTransGen.mono (fun _ _ step => liftStep step) _ _ append_two_values

theorem extended_has_wrong_answer : Steps extendedRoot program swapped := by
  apply extended_still_has_correct_path.trans
  apply Relation.ReflTransGen.single
  apply StepCore.root
  apply Or.inr
  exact SchemaTableConversionCode.decode_sound forgedTable (fun _ => true)
    ⟨0, []⟩ (by decide +kernel)

/-- Preserving a good execution does not exclude unauthorized output. -/
theorem forward_existence_not_exclusivity :
    Steps extendedRoot program expected ∧ Steps extendedRoot program swapped ∧ expected ≠ swapped :=
  ⟨extended_still_has_correct_path, extended_has_wrong_answer, by decide +kernel⟩

#eval verdicts
#print axioms append_two_values
#print axioms readout_two_values
#print axioms forward_existence_not_exclusivity

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.MeaningControls
