import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestInstantiation
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackageControls

/-!
# Explicit-parameter receipt controls

These raw computation controls compare the generated table with independently
written vector constructor and eliminator applications. They retain the actual
parameter, field order and recursive calls. They do not assert that arbitrary
raw supplied parameters or method constants have the required guest types.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.InstantiationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies
open DeclarationControls

def motive : Tower.Tm 0 := .const `Example.Motive
def nilMethod : Tower.Tm 0 := .const `Example.NilMethod
def consMethod : Tower.Tm 0 := .const `Example.ConsMethod
def payload : Tower.Tm 0 := .const `Example.Payload
def firstParameter : Tower.Tm 0 := .const `Example.FirstElementType
def secondParameter : Tower.Tm 0 := .const `Example.SecondElementType

def nilReceipt (parameter : Tower.Tm 0) : SchemaTableConversionCode.Code Tower.Head 0 :=
  ⟨0, [consMethod, nilMethod, motive, parameter]⟩

def consReceipt (parameter : Tower.Tm 0) : SchemaTableConversionCode.Code Tower.Head 0 :=
  ⟨1, [vnilApp parameter, payload, zeroTm, consMethod, nilMethod, motive, parameter]⟩

def nilSource (parameter : Tower.Tm 0) : Tower.Tm 0 :=
  vecEliminateApp parameter motive nilMethod consMethod zeroTm (vnilApp parameter)

def consSource (parameter : Tower.Tm 0) : Tower.Tm 0 :=
  vecEliminateApp parameter motive nilMethod consMethod (succApp zeroTm)
    (vconsApp parameter zeroTm payload (vnilApp parameter))

def consTarget (parameter : Tower.Tm 0) : Tower.Tm 0 :=
  Declaration.IndexedFamily.applyArgs consMethod
    [zeroTm, payload, vnilApp parameter, nilSource parameter]

def replay := SchemaTableConversionCode.decode (n := 0) PackageControls.runtimeTable (fun _ => true)

/-- Exact comparison with source-generated syntax, not only with its row
count or the independent fixture's declared result. -/
theorem replay_generated (receipt : SchemaTableConversionCode.Code Tower.Head 0) :
    replay receipt = SchemaTableConversionCode.decode
      (Package.table (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames
        (IndexedInductiveNatVec.Vectors.admitted Bool)) (fun _ => true) receipt := rfl

def verdicts : List (String × Bool) := [
  ("nil retains its actual parameter", decide (replay (nilReceipt firstParameter) =
    some (nilSource firstParameter, nilMethod))),
  ("cons retains parameter in the recursive call", decide (replay (consReceipt firstParameter) =
    some (consSource firstParameter, consTarget firstParameter))),
  ("a second parameter works without rebuilding the table", decide (replay (consReceipt secondParameter) =
    some (consSource secondParameter, consTarget secondParameter))),
  ("changed parameter cannot certify the original source", decide (replay (consReceipt secondParameter) ≠
    some (consSource firstParameter, consTarget firstParameter))),
  ("recursive call cannot silently change parameter", decide (replay (consReceipt firstParameter) ≠
    some (consSource firstParameter, Declaration.IndexedFamily.applyArgs consMethod
      [zeroTm, payload, vnilApp firstParameter, nilSource secondParameter]))),
  ("recursive result cannot be dropped", decide (replay (consReceipt firstParameter) ≠
    some (consSource firstParameter, Declaration.IndexedFamily.applyArgs consMethod
      [zeroTm, payload, vnilApp firstParameter]))),
  ("swapping payload and child changes the claimed transition", decide (replay
      ⟨1, [payload, vnilApp firstParameter, zeroTm, consMethod, nilMethod, motive, firstParameter]⟩ ≠
    some (consSource firstParameter, consTarget firstParameter))),
  ("omitted explicit parameter is refused", (replay
      ⟨1, [vnilApp firstParameter, payload, zeroTm, consMethod, nilMethod, motive]⟩).isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

private theorem checked (index : Fin verdicts.length) : (verdicts.get index).2 = true :=
  (List.all_eq_true.mp all_verdicts) _ (List.get_mem verdicts index)

/-- This actual finite receipt reaches the source-defined unfolding relation
through the generic two-sided theorem. -/
theorem cons_source_unfolding :
    Instantiation.Unfold (IndexedInductiveNatVec.Vectors.admitted Bool)
      (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames
      (consSource firstParameter) (consTarget firstParameter) := by
  apply (Instantiation.decoded_iff_unfold _ _ _ _ _ _).mp
  refine ⟨consReceipt firstParameter, ?_⟩
  rw [← replay_generated]
  exact of_decide_eq_true (checked ⟨1, by decide⟩)

theorem all_unfoldings_have_receipts (left right : Tower.Tm 0)
    (source : Instantiation.Unfold (IndexedInductiveNatVec.Vectors.admitted Bool)
      (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames left right) :
    ∃ receipt, replay receipt = some (left, right) := by
  obtain ⟨receipt, accepted⟩ :=
    (Instantiation.decoded_iff_unfold _ _ _ _ left right).mpr source
  exact ⟨receipt, (replay_generated receipt).trans accepted⟩

#eval verdicts
#print axioms cons_source_unfolding
#print axioms all_unfoldings_have_receipts
#print axioms all_verdicts

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.InstantiationControls
