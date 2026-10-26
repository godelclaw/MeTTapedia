import Mettapedia.GSLT.LanguageDef.IndexedInductiveVectorMeaning
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestControls

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

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.MeaningControls.PositionCodec
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples
open Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Meaning

/-- Two recursive fields separated by a data binder require different indices. -/
def mixedCode : Code Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples.Vectors.interface [] :=
  .data .length (.recursive (.variable .here)
    (.data .payload (.recursive (.successor (.variable (.there .here))) (.result (.literal 0)))))

def mixedShape : Shape mixedCode PUnit.unit (0 : Nat) := ⟨(3 : Nat), true, ⟨⟨rfl⟩⟩⟩

def first : Position mixedCode mixedShape := none
def second : Position mixedCode mixedShape := some none

def firstOrdinal : Fin (recursiveCount mixedCode) := ⟨0, by change 0 < 2; decide⟩
def secondOrdinal : Fin (recursiveCount mixedCode) := ⟨1, by change 1 < 2; decide⟩

theorem two_recursive_fields : recursiveCount mixedCode = 2 := rfl

theorem first_roundtrip : positionOfFin mixedCode mixedShape (positionToFin mixedCode mixedShape first) = first :=
  positionOfFin_toFin mixedCode mixedShape first

theorem second_roundtrip : positionOfFin mixedCode mixedShape (positionToFin mixedCode mixedShape second) = second :=
  positionOfFin_toFin mixedCode mixedShape second

theorem second_ordinal_roundtrip :
    positionToFin mixedCode mixedShape (positionOfFin mixedCode mixedShape secondOrdinal) = secondOrdinal :=
  positionToFin_ofFin mixedCode mixedShape secondOrdinal

theorem distinct_slots : positionToFin mixedCode mixedShape first ≠ positionToFin mixedCode mixedShape second := by
  decide +kernel

theorem first_index : next mixedCode mixedShape (positionOfFin mixedCode mixedShape firstOrdinal) = (3 : Nat) :=
  next_positionOfFin mixedCode mixedShape firstOrdinal

theorem second_index : next mixedCode mixedShape (positionOfFin mixedCode mixedShape secondOrdinal) = (4 : Nat) :=
  next_positionOfFin mixedCode mixedShape secondOrdinal

def indexedChildren : ∀ position : Position mixedCode mixedShape, Fin (next mixedCode mixedShape position)
  | none => ⟨2, Nat.lt_succ_self 2⟩
  | some none => ⟨3, Nat.lt_succ_self 3⟩
  | some (some impossible) => PEmpty.elim impossible

def indexedVector := childrenVectorEquiv mixedCode mixedShape Fin indexedChildren

theorem vector_first : (indexedVector firstOrdinal).val = 2 := rfl

theorem vector_second : (indexedVector secondOrdinal).val = (3 : Nat) := rfl

theorem indexed_roundtrip :
    (childrenVectorEquiv mixedCode mixedShape Fin).symm indexedVector = indexedChildren :=
  (childrenVectorEquiv mixedCode mixedShape Fin).symm_apply_apply indexedChildren

theorem repeated_values_retained : results mixedCode mixedShape (fun _ => (7 : Nat)) = [7, 7] :=
  results_positionVector mixedCode mixedShape (fun _ => (7 : Nat))

theorem deduplicating_changes_count : ([7, 7] : List Nat).eraseDups.length ≠ recursiveCount mixedCode := by
  decide +kernel

def zeroCode : Code Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples.Vectors.interface [] := .result (.literal 0)

def zeroShape : Shape zeroCode PUnit.unit (0 : Nat) := ⟨⟨rfl⟩⟩

theorem empty_slots : recursiveCount zeroCode = 0 := rfl

theorem zero_position_eliminates (position : Position zeroCode zeroShape) : False := PEmpty.elim position

open Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec

noncomputable def naturalVectorEquiv := inventoryVectorFixEquiv Natural.constructors PUnit.unit ()

theorem natural_roundtrip :
    naturalVectorEquiv.symm (naturalVectorEquiv (Natural.succ Natural.zero)) = Natural.succ Natural.zero :=
  naturalVectorEquiv.symm_apply_apply _

#print axioms first_roundtrip
#print axioms first_index
#print axioms indexed_roundtrip
#print axioms repeated_values_retained
#print axioms natural_roundtrip
end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.MeaningControls.PositionCodec

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.MeaningControls.PositionCodec
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Meaning

private abbrev indices := Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls.Vector.indexSyntax
private abbrev quoteData := Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls.Vector.quoteData (n := 0)
private abbrev quoteIndex := Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls.numeral (n := 0)

theorem mixed_quoted : QuotedCode indices quoteData quoteIndex mixedCode := by
  exact ⟨Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls.Vector.indexCompatibility _,
    Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls.Vector.indexCompatibility _,
    Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Controls.Vector.indexCompatibility _⟩

def repeatedSyntax : Position mixedCode mixedShape → Tm Unit 0 := fun _ => .const `child

def recursiveCall (index child : Tm Unit 0) : Tm Unit 0 := .app (.app (.const `recurse) index) child

theorem mixed_guest_positionVector :
    (recursiveArguments indices mixedCode (quoteEnv quoteData PUnit.unit)
      (fields quoteData mixedCode mixedShape repeatedSyntax)).map
      (fun pair => recursiveCall pair.1 pair.2) =
      List.ofFn (fun ordinal => recursiveCall
        (quoteIndex (recursiveIndexAt mixedCode mixedShape ordinal))
        (repeatedSyntax (positionOfFin mixedCode mixedShape ordinal))) :=
  recursiveArguments_fields_positionVector indices quoteData quoteIndex mixedCode mixed_quoted
    mixedShape repeatedSyntax recursiveCall

#print axioms mixed_quoted
#print axioms mixed_guest_positionVector


def verdicts : List (String × Bool) :=
  [("recursive slot codec counts two occurrences", decide (recursiveCount mixedCode = 2)),
   ("recursive slot codec separates repeated positions", decide
      ((positionToFin mixedCode mixedShape first).val ≠ (positionToFin mixedCode mixedShape second).val)),
   ("recursive slot codec retains first dependent index",
      Nat.beq (recursiveIndexAt mixedCode mixedShape firstOrdinal) 3),
   ("recursive slot codec retains later dependent index",
      Nat.beq (recursiveIndexAt mixedCode mixedShape secondOrdinal) 4),
   ("recursive child vector preserves supplied values", decide
      ((indexedVector firstOrdinal).val = 2 ∧ (indexedVector secondOrdinal).val = 3)),
   ("recursive result traversal retains duplicate payloads", decide
      (results mixedCode mixedShape (fun _ => (7 : Nat)) = [7, 7]))]

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.MeaningControls.PositionCodec
