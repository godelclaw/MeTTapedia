import Mettapedia.TypeTheory.NaturalDependentRepresentations
import Mettapedia.TypeTheory.IndexedPolynomialVectorRepresentation

/-!
# Coherent representation changes and indexed append

Append is defined once on the existing indexed-polynomial vectors, with result
length `n + m`. A natural-number representation transports its two input fibres
and the sum index together. Changing representations before or after append
gives the same indexed vector; successive changes agree with the direct change.

These are semantic equalities, including the equality transports in dependent
fibres. Material and surreal instances retain their noncomputable decoders.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NaturalVectorCoherence

universe u v w x

open IndexedPolynomial
open NaturalVectorTransport
open NaturalAlgebra NaturalRepresentations

variable {Element : Type u} {First : Type v} {Second : Type w} {Third : Type x}

/-- Appending preserves the element order and has the sum of the two lengths. -/
noncomputable def append {n m : Nat} (left : VectorExample.VectorP Element n)
    (right : VectorExample.VectorP Element m) : VectorExample.VectorP Element (n + m) :=
  VectorRepresentation.append left right

@[simp] theorem append_nil {m : Nat} (right : VectorExample.VectorP Element m) :
    append VectorExample.nil right = (Nat.zero_add m).symm ▸ right := by
  unfold append
  rw [VectorRepresentation.append_nil]
  exact eq_of_heq ((cast_heq _ _).trans (eqRec_heq _ _).symm)

@[simp] theorem append_cons {n m : Nat} (head : Element)
    (left : VectorExample.VectorP Element n) (right : VectorExample.VectorP Element m) :
    append (VectorExample.cons head left) right =
      (Nat.succ_add n m).symm ▸ VectorExample.cons head (append left right) := by
  unfold append
  rw [VectorRepresentation.append_cons]
  exact eq_of_heq ((cast_heq _ _).trans (eqRec_heq _ _).symm)

/-- The existing natural-representation client uses the generic dependent
eliminator, and its list realization retains every output element. -/
theorem append_list_realization {n m : Nat}
    (left : VectorExample.VectorP Element n) (right : VectorExample.VectorP Element m) :
    VectorRepresentation.encode (n + m) (append left right) =
      VectorRepresentation.representedAppend
        (VectorRepresentation.encode n left) (VectorRepresentation.encode m right) :=
  VectorRepresentation.append_transport left right

private theorem erase_cast {n m : Nat} (same : n = m)
    (vector : VectorExample.VectorP Element n) :
    VectorExample.erase m (same ▸ vector) = VectorExample.erase n vector := by
  cases same
  rfl

/-- The typed operation computes ordinary list concatenation after erasure. -/
theorem append_elements {n m : Nat} (left : VectorExample.VectorP Element n)
    (right : VectorExample.VectorP Element m) :
    ListExample.toList (VectorExample.erase (n + m) (append left right)) =
      ListExample.toList (VectorExample.erase n left) ++
        ListExample.toList (VectorExample.erase m right) := by
  apply VectorExample.eliminate (fun n left =>
    ListExample.toList (VectorExample.erase (n + m) (append left right)) =
      ListExample.toList (VectorExample.erase n left) ++
        ListExample.toList (VectorExample.erase m right))
  · rw [append_nil, erase_cast]
    simp
  · intro n head tail hypothesis
    rw [append_cons, erase_cast]
    simpa using congrArg (List.cons head) hypothesis

/-- Addition on a represented natural-number carrier. -/
def representedAdd (representation : Nat ≃ First) (left right : First) : First :=
  representation (representation.symm left + representation.symm right)

@[simp] theorem representedAdd_encode (representation : Nat ≃ First) (n m : Nat) :
    representedAdd representation (representation n) (representation m) =
      representation (n + m) := by
  simp [representedAdd]

/-- The ergonomic dependent signature at any natural representation. -/
noncomputable def appendFamily (representation : Nat ≃ First) {n m : First}
    (left : Family representation Element n) (right : Family representation Element m) :
    Family representation Element (representedAdd representation n m) :=
  cast (congrArg (VectorExample.VectorP Element)
    (representation.symm_apply_apply (representation.symm n + representation.symm m)).symm)
    (append left right)

/-- Append with its represented result index retained. -/
noncomputable def appendTotal (representation : Nat ≃ First)
    (left right : Total representation Element) : Total representation Element :=
  let sourceLeft := (totalEquiv representation).symm left
  let sourceRight := (totalEquiv representation).symm right
  totalEquiv representation
    ⟨sourceLeft.1 + sourceRight.1, append sourceLeft.2 sourceRight.2⟩

theorem appendTotal_fibres (representation : Nat ≃ First)
    (left right : Total representation Element) :
    appendTotal representation left right =
      ⟨representedAdd representation left.1 right.1,
        appendFamily representation left.2 right.2⟩ := by
  refine Sigma.ext ?_ ?_
  · rfl
  · exact (eqRec_heq _ _).trans (cast_heq _ _).symm

@[simp] theorem appendTotal_length (representation : Nat ≃ First)
    (left right : Total representation Element) :
    (appendTotal representation left right).1 = representedAdd representation left.1 right.1 := rfl

@[simp] theorem appendTotal_encode (representation : Nat ≃ First)
    {n m : Nat} (left : VectorExample.VectorP Element n)
    (right : VectorExample.VectorP Element m) :
    appendTotal representation (totalEquiv representation ⟨n, left⟩)
      (totalEquiv representation ⟨m, right⟩) =
    totalEquiv representation ⟨n + m, append left right⟩ := by
  unfold appendTotal
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[simp] theorem changeRepresentation_encode
    (first : Nat ≃ First) (second : Nat ≃ Second)
    {n : Nat} (vector : VectorExample.VectorP Element n) :
    changeRepresentation first second (totalEquiv first ⟨n, vector⟩) =
      totalEquiv second ⟨n, vector⟩ := by
  change totalEquiv second ((totalEquiv first).symm (totalEquiv first _)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem changeRepresentation_identity (representation : Nat ≃ First)
    (vector : Total representation Element) :
    changeRepresentation representation representation vector = vector :=
  (totalEquiv representation).apply_symm_apply vector

/-- Representation changes compose on the complete indexed value. -/
@[simp] theorem changeRepresentation_composition
    (first : Nat ≃ First) (second : Nat ≃ Second) (third : Nat ≃ Third)
    (vector : Total first Element) :
    changeRepresentation second third (changeRepresentation first second vector) =
      changeRepresentation first third vector := by
  change totalEquiv third ((totalEquiv second).symm
    (totalEquiv second ((totalEquiv first).symm vector))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem changeRepresentation_identity_equiv (representation : Nat ≃ First) :
    changeRepresentation representation representation (Element := Element) = Equiv.refl _ := by
  apply Equiv.ext
  exact changeRepresentation_identity representation

theorem changeRepresentation_composition_equiv
    (first : Nat ≃ First) (second : Nat ≃ Second) (third : Nat ≃ Third) :
    (changeRepresentation first second (Element := Element)).trans
      (changeRepresentation second third) = changeRepresentation first third := by
  apply Equiv.ext
  exact changeRepresentation_composition first second third

/-- Appending commutes with representation change, including the result fibre. -/
theorem changeRepresentation_append (first : Nat ≃ First) (second : Nat ≃ Second)
    (left right : Total first Element) :
    changeRepresentation first second (appendTotal first left right) =
      appendTotal second (changeRepresentation first second left)
        (changeRepresentation first second right) := by
  obtain ⟨⟨n, left⟩, rfl⟩ := (totalEquiv first).surjective left
  obtain ⟨⟨m, right⟩, rfl⟩ := (totalEquiv first).surjective right
  simp

theorem representedAdd_changeRepresentation (first : Nat ≃ First) (second : Nat ≃ Second)
    (left right : First) :
    second (first.symm (representedAdd first left right)) =
      representedAdd second (second (first.symm left)) (second (first.symm right)) := by
  simp [representedAdd]

/-- A structured comparison between natural algebras also preserves the sum
used by the dependent append signature. -/
theorem representedAdd_iso {source : Algebra First} {target : Algebra Second}
    (first : Iso natAlgebra source) (second : Iso natAlgebra target)
    (route : Iso source target) (left right : First) :
    route.toEquiv (representedAdd first.toEquiv left right) =
      representedAdd second.toEquiv (route.toEquiv left) (route.toEquiv right) := by
  have maps := (initialHom_unique nat_initial target
    (Hom.comp route.toHom first.toHom)).trans
      (initialHom_unique nat_initial target second.toHom).symm
  have encoded : ∀ number, route.toEquiv (first.toEquiv number) = second.toEquiv number :=
    fun number => congrArg (fun hom : Hom natAlgebra target => hom number) maps
  obtain ⟨n, rfl⟩ := first.toEquiv.surjective left
  obtain ⟨m, rfl⟩ := first.toEquiv.surjective right
  simp only [representedAdd_encode, encoded]

/-- Reindexing does not alter the independently defined vector erasure. -/
theorem erase_encode (representation : Nat ≃ First) {n : Nat}
    (vector : VectorExample.VectorP Element n) :
    erase representation (totalEquiv representation ⟨n, vector⟩) =
      VectorExample.erase n vector := by
  apply VectorExample.eliminate (fun n vector =>
    erase representation (totalEquiv representation ⟨n, vector⟩) = VectorExample.erase n vector)
  · change erase representation (nil representation) = VectorExample.erase 0 VectorExample.nil
    simp
  · intro n head tail hypothesis
    rw [← cons_encode, erase_cons, VectorExample.erase_cons, hypothesis]

theorem appendTotal_elements (representation : Nat ≃ First)
    (left right : Total representation Element) :
    ListExample.toList (erase representation (appendTotal representation left right)) =
      ListExample.toList (erase representation left) ++
        ListExample.toList (erase representation right) := by
  obtain ⟨⟨n, left⟩, rfl⟩ := (totalEquiv representation).surjective left
  obtain ⟨⟨m, right⟩, rfl⟩ := (totalEquiv representation).surjective right
  rw [appendTotal_encode, erase_encode, erase_encode, erase_encode]
  exact append_elements left right

namespace Controls

noncomputable def firstTwo : VectorExample.VectorP Nat 2 :=
  VectorExample.cons 3 (VectorExample.cons 3 VectorExample.nil)

noncomputable def finalOne : VectorExample.VectorP Nat 1 :=
  VectorExample.cons 8 VectorExample.nil

theorem append_retains_order_and_copies :
    ListExample.toList (VectorExample.erase 3 (append firstTwo finalOne)) = [3, 3, 8] := by
  change ListExample.toList (VectorExample.erase (2 + 1) (append firstTwo finalOne)) = _
  rw [append_elements]
  simp [firstTwo, finalOne]

noncomputable def materialLeft : Total natMaterialIso.{0}.toEquiv Nat :=
  totalEquiv _ ⟨2, firstTwo⟩

noncomputable def materialRight : Total natMaterialIso.{0}.toEquiv Nat :=
  totalEquiv _ ⟨1, finalOne⟩

/-- Changing directly or via host naturals gives the same vector, not merely
the same erased elements. -/
theorem material_surreal_two_routes :
    changeRepresentation (Equiv.refl Nat) natSurrealIso.toEquiv
      (changeRepresentation natMaterialIso.toEquiv (Equiv.refl Nat)
        (appendTotal natMaterialIso.toEquiv materialLeft materialRight)) =
    changeRepresentation natMaterialIso.toEquiv natSurrealIso.toEquiv
      (appendTotal natMaterialIso.toEquiv materialLeft materialRight) :=
  changeRepresentation_composition _ _ _ _

theorem material_surreal_append_naturality :
    changeRepresentation natMaterialIso.toEquiv natSurrealIso.toEquiv
      (appendTotal natMaterialIso.toEquiv materialLeft materialRight) =
    appendTotal natSurrealIso.toEquiv
      (changeRepresentation natMaterialIso.toEquiv natSurrealIso.toEquiv materialLeft)
      (changeRepresentation natMaterialIso.toEquiv natSurrealIso.toEquiv materialRight) :=
  changeRepresentation_append _ _ _ _

theorem material_append_length_three :
    (appendTotal natMaterialIso.toEquiv materialLeft materialRight).1 =
      MaterialSets.Hypersets.NaturalOrdinalModel.naturalMembers 3 := by
  rw [materialLeft, materialRight, appendTotal_encode]
  exact natMaterialIso_encode 3

theorem surreal_append_length_three :
    (changeRepresentation natMaterialIso.toEquiv natSurrealIso.toEquiv
      (appendTotal natMaterialIso.toEquiv materialLeft materialRight)).1 = surrealEncode 3 := by
  rw [materialLeft, materialRight, appendTotal_encode, changeRepresentation_encode]
  exact natSurrealIso_encode 3

theorem material_append_elements :
    ListExample.toList (erase natMaterialIso.toEquiv
      (appendTotal natMaterialIso.toEquiv materialLeft materialRight)) = [3, 3, 8] := by
  rw [materialLeft, materialRight, appendTotal_encode, erase_encode]
  exact append_retains_order_and_copies

theorem surreal_append_elements :
    ListExample.toList (erase natSurrealIso.toEquiv
      (changeRepresentation natMaterialIso.toEquiv natSurrealIso.toEquiv
        (appendTotal natMaterialIso.toEquiv materialLeft materialRight))) = [3, 3, 8] := by
  rw [erase_changeRepresentation]
  exact material_append_elements

theorem material_append_not_empty :
    appendTotal natMaterialIso.toEquiv materialLeft materialRight ≠ nil natMaterialIso.toEquiv := by
  intro same
  have decoded := congrArg
    (fun vector => ((totalEquiv natMaterialIso.toEquiv).symm vector).1) same
  rw [materialLeft, materialRight, appendTotal_encode] at decoded
  simp only [nil, Equiv.symm_apply_apply] at decoded
  contradiction

end Controls

end Mettapedia.TypeTheory.NaturalVectorCoherence
