import Mettapedia.TypeTheory.IndexedPolynomialFunctionPayload
import Mettapedia.GSLT.LanguageDef.IndexedInductiveConstructorDataControls

/-!
# Function payloads of admitted Vector constructor data

The actual constructor inventory supplies the schema. A nonempty tuple keeps
its constructor occurrence, round-trips through the guarded function image,
and remains distinct from a tuple with a changed length. The absent marker is
distinct from present data. The inverse is semantic rather than executable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.FunctionPayloadControls

open Mettapedia.TypeTheory
open IndexedPolynomial.Description
open IndexedInductiveNatVec

noncomputable def first : InventoryData (Vectors.constructors Bool) :=
  ⟨⟨1, by decide⟩, ConstructorDataControls.consData (Natural.succ Natural.zero) true⟩
noncomputable def changed : InventoryData (Vectors.constructors Bool) :=
  ⟨⟨1, by decide⟩, ConstructorDataControls.consData Natural.zero true⟩

theorem first_roundtrip :
    (FunctionPayload.representation (Vectors.constructors Bool)).symm
      (FunctionPayload.representation (Vectors.constructors Bool) first) = first :=
  (FunctionPayload.representation (Vectors.constructors Bool)).symm_apply_apply first

theorem occurrence_preserved :
    (FunctionPayload.dataEquivalence (Vectors.constructors Bool) first).1.val = (1 : Nat) :=
  FunctionPayload.occurrence_preserved (Vectors.constructors Bool) first

theorem length_distinguished :
    FunctionPayload.encode (Vectors.constructors Bool) first ≠
      FunctionPayload.encode (Vectors.constructors Bool) changed := by
  intro same
  have inputs := FunctionPayload.encode_injective (Vectors.constructors Bool) same
  have fields := eq_of_heq (Sigma.mk.inj inputs).2
  have counts := congrArg (fun data => Natural.toNat data.1) fields
  change (1 : Nat) = 0 at counts
  cases counts

theorem absent_distinguished :
    FunctionPayload.encodeOption (Vectors.constructors Bool) none ≠
      FunctionPayload.encodeOption (Vectors.constructors Bool) (some first) := by
  intro same
  have impossible := FunctionPayload.encodeOption_injective (Vectors.constructors Bool) same
  cases impossible

theorem shape_absence_distinguished :
    FunctionPayload.encodeShape (Vectors.constructors Bool) PUnit.unit none ≠
      FunctionPayload.encodeShape (Vectors.constructors Bool) PUnit.unit
        (some ((inventoryDataEquiv (Vectors.constructors Bool) PUnit.unit).symm first)) := by
  intro same
  have impossible := FunctionPayload.encodeShape_injective (Vectors.constructors Bool) PUnit.unit same
  cases impossible

noncomputable def vector := Vectors.cons true (Vectors.cons false Vectors.nil)
noncomputable def vectorRepresentation :=
  FunctionPayload.familyRepresentation (Vectors.constructors Bool) PUnit.unit
    (Natural.succ (Natural.succ Natural.zero))

theorem vector_roundtrip : vectorRepresentation.symm (vectorRepresentation vector) = vector :=
  vectorRepresentation.symm_apply_apply vector

theorem vector_order_preserved : vectorRepresentation vector ≠
    vectorRepresentation (Vectors.cons false (Vectors.cons true Vectors.nil)) := by
  intro same
  have source := vectorRepresentation.injective same
  have lists := congrArg (fun value => (Vectors.toList value).val) source
  change [true, false] = [false, true] at lists
  cases List.cons.inj lists |>.1

#print axioms first_roundtrip
#print axioms length_distinguished
#print axioms absent_distinguished
#print axioms shape_absence_distinguished
#print axioms vector_roundtrip
#print axioms vector_order_preserved

end Mettapedia.GSLT.LanguageDef.IndexedInductive.FunctionPayloadControls
