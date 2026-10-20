import Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples
import Mettapedia.TypeTheory.NaturalVectorCoherence

/-!
# Authored indexed vectors and the existing append client

The admitted vector document and the existing polynomial vector family share
ordinary length-checked lists as a proved representation. Composing those
equivalences preserves nil and cons. The authored append operation is the
existing dependent append transported through that comparison; its result is
ordinary ordered list concatenation, including the complete payload.

This is semantic representation transport. It supplies neither guest conversion
authority nor a qualified runtime decoder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.AuthoredIndexedVector

open Mettapedia.TypeTheory
open IndexedPolynomial

open Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples

/-- Both routes use independently length-checked ordinary list storage. -/
noncomputable def representation (length : Nat) :
    Vectors.Vector length ≃ VectorExample.VectorP Bool length :=
  (Vectors.listEquiv length).trans ((VectorRepresentation.listRepresentation Bool).toEquiv .star length).symm

@[simp] theorem representation_nil :
    representation 0 Vectors.nil = VectorExample.nil := rfl

@[simp] theorem representation_cons {length : Nat} (head : Bool)
    (tail : Vectors.Vector length) :
    representation (length + 1) (Vectors.cons head tail) =
      VectorExample.cons head (representation length tail) := by
  change VectorRepresentation.decode (Vectors.toList (Vectors.cons head tail)) =
    VectorExample.cons head (VectorRepresentation.decode (Vectors.toList tail))
  have same : Vectors.toList (Vectors.cons head tail) =
      VectorRepresentation.listCons head (Vectors.toList tail) :=
    Subtype.ext (Vectors.toList_cons head tail)
  rw [same, VectorRepresentation.decode_cons]

@[simp] theorem representation_symm_nil :
    (representation 0).symm VectorExample.nil = Vectors.nil := rfl

@[simp] theorem representation_symm_cons {length : Nat} (head : Bool)
    (tail : VectorExample.VectorP Bool length) :
    (representation (length + 1)).symm (VectorExample.cons head tail) =
      Vectors.cons head ((representation length).symm tail) := by
  exact Vectors.fromListVector_listCons head (VectorRepresentation.encode length tail)

@[simp] theorem storage_representation {length : Nat} (vector : Vectors.Vector length) :
    VectorRepresentation.encode length (representation length vector) = Vectors.toList vector :=
  VectorRepresentation.encode_decode (Vectors.toList vector)

@[simp] theorem storage_representation_symm {length : Nat}
    (vector : VectorExample.VectorP Bool length) :
    Vectors.toList ((representation length).symm vector) = VectorRepresentation.encode length vector :=
  Vectors.toList_fromListVector (VectorRepresentation.encode length vector)

/-- Reuse the existing append client; no second recursive append is introduced. -/
noncomputable def append {n m : Nat} (left : Vectors.Vector n)
    (right : Vectors.Vector m) : Vectors.Vector (n + m) :=
  (representation (n + m)).symm
    (NaturalVectorCoherence.append (representation n left) (representation m right))

/-- The translated operation is exactly the established dependent append. -/
theorem append_representation {n m : Nat} (left : Vectors.Vector n)
    (right : Vectors.Vector m) :
    representation (n + m) (append left right) =
      NaturalVectorCoherence.append (representation n left) (representation m right) :=
  (representation (n + m)).apply_symm_apply _

/-- The operation preserves the entire ordered payload and its sum index. -/
theorem append_storage {n m : Nat} (left : Vectors.Vector n)
    (right : Vectors.Vector m) :
    Vectors.toList (append left right) =
      VectorRepresentation.listAppend (Vectors.toList left) (Vectors.toList right) := by
  unfold append
  rw [storage_representation_symm]
  change VectorRepresentation.encode (n + m)
    (VectorRepresentation.append (representation n left) (representation m right)) = _
  rw [VectorRepresentation.append_representation, storage_representation, storage_representation]

theorem append_payload {n m : Nat} (left : Vectors.Vector n)
    (right : Vectors.Vector m) :
    (Vectors.toList (append left right)).val =
      (Vectors.toList left).val ++ (Vectors.toList right).val :=
  congrArg Subtype.val (append_storage left right)

/-- Every observation on the existing client is pulled back along the same
constructor-preserving comparison. No extra decision procedure is asserted. -/
theorem append_observation_iff {n m : Nat}
    (observation : VectorExample.VectorP Bool (n + m) → Prop)
    (left : Vectors.Vector n) (right : Vectors.Vector m) :
    observation (representation (n + m) (append left right)) ↔
      observation (NaturalVectorCoherence.append
        (representation n left) (representation m right)) := by
  rw [append_representation]

theorem append_two_payloads :
    (Vectors.toList (append (Vectors.cons true Vectors.nil)
      (Vectors.cons false Vectors.nil))).val = [true, false] := by
  rw [append_payload]
  rfl

theorem reversed_payload_rejected :
    (Vectors.toList (append (Vectors.cons true Vectors.nil)
      (Vectors.cons false Vectors.nil))).val ≠ [false, true] := by
  rw [append_two_payloads]
  decide

#print axioms representation_cons
#print axioms representation_symm_cons
#print axioms append_storage
#print axioms append_payload
#print axioms reversed_payload_rejected

end Mettapedia.OSLF.Bridges.TypeTheory.AuthoredIndexedVector
