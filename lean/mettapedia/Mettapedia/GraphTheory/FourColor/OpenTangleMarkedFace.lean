import Mettapedia.GraphTheory.FourColor.MarkedFaceReturnRewire
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition

/-!
# Finite marked-face semantics of the actual open-tangle composition

Temporarily fix each unpaired boundary dart under alpha. Sewing is exactly
a permutation supported on these boundary darts, on top of the disjoint
open face permutations. The marked-return law therefore computes actual
cofaciality in `composeRotationSystem`, including face splitting/merging.
The carrier consists of seam darts and explicitly named observations; face
perimeters do not enter its size bound.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleMarkedFace

open GoertzelV24OpenTangleComposition GoertzelV24OrderedCutFaceReturnProfile
open MarkedFaceReturnRewire

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W I J L R : Type*}

/-- An open face permutation: boundary darts are fixed by the provisional
edge involution. This is not itself asserted to be a closed map. -/
def openPhi (data : OpenTangleData V I L) : Equiv.Perm (I ⊕ L) :=
  data.rho * Equiv.sumCongr data.interiorAlpha (Equiv.refl L)

abbrev Carrier (I J L R : Type*) := (I ⊕ L) ⊕ (J ⊕ R)

/-- The actual boundary partner change, with all interior darts fixed. -/
def seamSwap (matching : L ≃ R) : Equiv.Perm (Carrier I J L R) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr l) => .inr (.inr (matching l))
    | .inr (.inl j) => .inr (.inl j)
    | .inr (.inr r) => .inl (.inr (matching.symm r))
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr l) => .inr (.inr (matching l))
    | .inr (.inl j) => .inr (.inl j)
    | .inr (.inr r) => .inl (.inr (matching.symm r))
  left_inv := by rintro ((i | l) | (j | r)) <;> simp
  right_inv := by rintro ((i | l) | (j | r)) <;> simp

def IsSeam : Carrier I J L R → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr (.inl _) => False
  | .inr (.inr _) => True

theorem seamSwap_supported (matching : L ≃ R) (d : Carrier I J L R)
    (h : seamSwap matching d ≠ d) : IsSeam d := by
  rcases d with (i | l) | (j | r) <;> simp_all [seamSwap, IsSeam]

theorem seamSwap_hit (matching : L ≃ R) (hit : Carrier I J L R → Prop)
    (hseam : ∀ d, IsSeam d → hit d) (d : Carrier I J L R) :
    hit (seamSwap matching d) ↔ hit d := by
  rcases d with (i | l) | (j | r)
  · rfl
  · exact iff_of_true (hseam _ trivial) (hseam _ trivial)
  · rfl
  · exact iff_of_true (hseam _ trivial) (hseam _ trivial)

/-- The restricted, concrete seam rewire on the finite observation carrier. -/
def observedSwap (matching : L ≃ R) (hit : Carrier I J L R → Prop)
    (hseam : ∀ d, IsSeam d → hit d) : Equiv.Perm {d // hit d} :=
  (seamSwap matching).subtypePerm (seamSwap_hit matching hit hseam)

theorem observedSwap_extend (matching : L ≃ R) (hit : Carrier I J L R → Prop)
    (hseam : ∀ d, IsSeam d → hit d) :
    Equiv.Perm.ofSubtype (observedSwap matching hit hseam) = seamSwap matching := by
  exact Equiv.Perm.ofSubtype_subtypePerm _
    (fun d hd => hseam d (seamSwap_supported matching d hd))

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The face permutation of the existing physical constructor, not an
abstract replacement postulated to agree with it. -/
theorem compose_phi (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) :
    (left.composeRotationSystem right matching).phi =
      composeDartEquiv.permCongr
        (Equiv.sumCongr (openPhi left) (openPhi right) * seamSwap matching) := by
  ext d
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  rcases x with (i | l) | (j | r) <;> rfl

/-- Finite, compositional calculation of actual cofaciality. Markers may
occur anywhere on either side, including faces which never meet the seam. -/
theorem compose_sameCycle_iff (left : OpenTangleData V I L)
    (right : OpenTangleData W J R) (matching : L ≃ R)
    (hit : Carrier I J L R → Prop) (hseam : ∀ d, IsSeam d → hit d)
    (first second : {d // hit d}) :
    (left.composeRotationSystem right matching).phi.SameCycle
        (composeDartEquiv first.val) (composeDartEquiv second.val) ↔
      (nextHitPerm (Equiv.sumCongr (openPhi left) (openPhi right)) hit *
        observedSwap matching hit hseam).SameCycle first second := by
  rw [compose_phi]
  apply (GoertzelV24OrderedCutFaceReturnProfile.permCongr_sameCycle_iff
    (composeDartEquiv (I := I) (J := J) (L := L) (R := R))
    (Equiv.sumCongr (openPhi left) (openPhi right) * seamSwap matching)
    first.val second.val).trans
  rw [← observedSwap_extend matching hit hseam]
  exact sameCycle_rewire_iff _ hit _ first second

/-- All boundary ports plus the requested dart observations. -/
def observed (marks : Finset (Carrier I J L R)) (d : Carrier I J L R) : Prop :=
  IsSeam d ∨ d ∈ marks

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq R] in
theorem card_seam : Fintype.card {d : Carrier I J L R // IsSeam d} =
    Fintype.card L + Fintype.card R := by
  let e : {d : Carrier I J L R // IsSeam d} ≃ L ⊕ R :=
    { toFun := fun d => match d with
        | ⟨.inl (.inl _), h⟩ => False.elim h
        | ⟨.inl (.inr l), _⟩ => .inl l
        | ⟨.inr (.inl _), h⟩ => False.elim h
        | ⟨.inr (.inr r), _⟩ => .inr r
      invFun := fun d => match d with
        | .inl l => ⟨.inl (.inr l), trivial⟩
        | .inr r => ⟨.inr (.inr r), trivial⟩
      left_inv := by
        rintro ⟨((i | l) | (j | r)), h⟩
        · exact False.elim h
        · rfl
        · exact False.elim h
        · rfl
      right_inv := by rintro (l | r) <;> rfl }
  simpa using Fintype.card_congr e

 /-- No marked-face perimeter appears in the record-size bound. -/
theorem card_observed_le (marks : Finset (Carrier I J L R)) :
    Fintype.card {d // observed marks d} ≤ Fintype.card L + Fintype.card R + marks.card := by
  classical
  unfold observed
  simpa only [card_seam, Fintype.card_coe] using
    (Fintype.card_subtype_or (IsSeam (I := I) (J := J) (L := L) (R := R))
      (fun d => d ∈ marks))

/-- An upper bound for the return-permutation component of the state. Other
Count data and the naming/coordinate transport are not included in this count. -/
theorem card_return_records_le (marks : Finset (Carrier I J L R)) :
    Fintype.card (Equiv.Perm {d // observed marks d}) ≤
      (Fintype.card L + Fintype.card R + marks.card).factorial := by
  rw [Fintype.card_perm]
  exact Nat.factorial_le (card_observed_le marks)

end
end Mettapedia.GraphTheory.FourColor.OpenTangleMarkedFace
