import Mettapedia.TypeTheory.IndexedPolynomialVectorRepresentation

/-!
# Controls for indexed representation transport

Length preservation alone cannot qualify a representation: changing payloads
violates its constructor algebra even when the fibre map is an equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.RepresentationControls

open VectorExample VectorRepresentation

universe u

noncomputable section

/-- A storage transformation that preserves every length. -/
def flip {n : Nat} (xs : ListVector Bool n) : ListVector Bool n :=
  ⟨xs.val.map Bool.not, by simp only [List.length_map, xs.property]⟩

@[simp] theorem flip_flip {n : Nat} (xs : ListVector Bool n) : flip (flip xs) = xs := by
  apply Subtype.ext
  simp [flip, List.map_map, Function.comp_def]

/-- A genuine equivalence in each index fibre can nevertheless change all the
observable elements. -/
def flipEquiv (n : Nat) : ListVector Bool n ≃ ListVector Bool n where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

/-- Constructor preservation rejects this length-preserving equivalence. -/
theorem flip_not_algebra_hom :
    ¬ ∃ route : Algebra.Hom (listAlgebra Bool) (listAlgebra Bool),
      ∀ n (xs : ListVector Bool n), route.toFun .star n xs = flip xs := by
  rintro ⟨route, agrees⟩
  have h := agrees 1 (listCons true listNil)
  rw [list_route_is_identity] at h
  have payload := congrArg Subtype.val h
  simp [flip, listCons, listNil] at payload

/-- A representation cannot discard a singleton, even before payload
preservation is checked. -/
theorem singleton_cannot_drop {A : Type u} :
    ¬ ∃ xs : ListVector A 1, xs.val = [] := by
  rintro ⟨xs, erased⟩
  have h := xs.property
  rw [erased] at h
  cases h

/-- Distinct constructor payloads remain distinct at the same length. -/
theorem singleton_payload_distinct {A : Type u} {a b : A} (different : a ≠ b) :
    encode 1 (cons a nil) ≠ encode 1 (cons b nil) := by
  intro equal
  have payload := congrArg Subtype.val equal
  exact different (List.cons.inj payload).1

/-- The inherited dependent program produces the expected independent payload. -/
theorem represented_append_example :
    (representedAppend (⟨[2, 3], rfl⟩ : ListVector Nat 2)
      (⟨[5], rfl⟩ : ListVector Nat 1)).val = [2, 3, 5] := by
  rw [representedAppend_eq_listAppend]
  rfl

/-- Equal output lengths do not excuse a changed element. -/
theorem represented_append_rejects_changed_payload :
    (representedAppend (⟨[true], rfl⟩ : ListVector Bool 1)
      (⟨[false], rfl⟩ : ListVector Bool 1)).val ≠ [false, false] := by
  rw [representedAppend_eq_listAppend]
  decide

#print axioms flip_not_algebra_hom
#print axioms singleton_cannot_drop
#print axioms singleton_payload_distinct
#print axioms represented_append_example
#print axioms represented_append_rejects_changed_payload
#print axioms VectorRepresentation.append_transport
#print axioms VectorRepresentation.listRepresentation

end
end Mettapedia.TypeTheory.IndexedPolynomial.RepresentationControls
