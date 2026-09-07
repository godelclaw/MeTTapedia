import Mettapedia.GraphTheory.FourColor.MarkedFaceReturnRewire

/-! # First returns of a disjoint union

Sewing a replacement to an unchanged exterior uses the disjoint union of
their open face permutations. Its observed return permutation is exactly
the disjoint union of the two local return permutations.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceReturnSum

open GoertzelV24SeamFaceArc GoertzelV24OrderedCutFaceReturnProfile

noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem pow_map (p : Equiv.Perm A) (q : Equiv.Perm B) (f : A → B)
    (hcomm : ∀ a, q (f a) = f (p a)) (n : ℕ) (a : A) :
    (q ^ n) (f a) = f ((p ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, hcomm,
      pow_succ', Equiv.Perm.mul_apply]

theorem returnTime_map (p : Equiv.Perm A) (q : Equiv.Perm B) (f : A → B)
    (hcomm : ∀ a, q (f a) = f (p a)) (ha : A → Prop) (hb : B → Prop)
    (hhit : ∀ a, hb (f a) ↔ ha a) (a : {a // ha a}) :
    firstPositiveHitTime q hb (f a.val) ((hhit _).mpr a.property) =
      firstPositiveHitTime p ha a.val a.property := by
  have hit (n : ℕ) : hb ((q ^ n) (f a.val)) ↔ ha ((p ^ n) a.val) := by
    rw [pow_map p q f hcomm]
    exact hhit _
  apply Nat.le_antisymm
  · apply firstPositiveHitTime_le_of_hit _ _ _ _ (firstPositiveHitTime_pos p ha _ _)
    exact (hit _).mpr (firstPositiveHitTime_hits p ha _ _)
  · apply firstPositiveHitTime_le_of_hit _ _ _ _ (firstPositiveHitTime_pos q hb _ _)
    exact (hit _).mp (firstPositiveHitTime_hits q hb _ _)

theorem nextHit_map (p : Equiv.Perm A) (q : Equiv.Perm B) (f : A → B)
    (hcomm : ∀ a, q (f a) = f (p a)) (ha : A → Prop) (hb : B → Prop)
    (hhit : ∀ a, hb (f a) ↔ ha a) (a : {a // ha a}) :
    (nextHitPerm q hb ⟨f a.val, (hhit _).mpr a.property⟩).val =
      f (nextHitPerm p ha a).val := by
  change (q ^ firstPositiveHitTime q hb _ _) (f a.val) =
    f ((p ^ firstPositiveHitTime p ha _ _) a.val)
  rw [returnTime_map p q f hcomm ha hb hhit a, pow_map p q f hcomm]

/-- The exact return permutation, including observed cycles which never
touch the seam. -/
theorem nextHitPerm_sum (p : Equiv.Perm A) (q : Equiv.Perm B)
    (ha : A → Prop) (hb : B → Prop) :
    nextHitPerm (Equiv.sumCongr p q) (Sum.elim ha hb) =
      Equiv.subtypeSum.symm.permCongr
        (Equiv.sumCongr (nextHitPerm p ha) (nextHitPerm q hb)) := by
  apply Equiv.ext
  intro d
  apply Subtype.ext
  rcases d with ⟨a | b, h⟩
  · exact nextHit_map p (Equiv.sumCongr p q) Sum.inl (fun _ => rfl)
      ha (Sum.elim ha hb) (fun _ => Iff.rfl) ⟨a, h⟩
  · exact nextHit_map q (Equiv.sumCongr p q) Sum.inr (fun _ => rfl)
      hb (Sum.elim ha hb) (fun _ => Iff.rfl) ⟨b, h⟩

variable {C : Type*} [Fintype C] [DecidableEq C]

def sumMatching (ha : A → Prop) {hb : B → Prop} {hc : C → Prop}
    (e : {b // hb b} ≃ {c // hc c}) :
    {d // Sum.elim ha hb d} ≃ {d // Sum.elim ha hc d} :=
  (Equiv.subtypeSum (p := Sum.elim ha hb)).trans
    ((Equiv.sumCongr (Equiv.refl _) e).trans (Equiv.subtypeSum (p := Sum.elim ha hc)).symm)

@[simp] theorem sumMatching_inl (ha : A → Prop) {hb : B → Prop} {hc : C → Prop}
    (e : {b // hb b} ≃ {c // hc c}) (a : {a // ha a}) :
    sumMatching ha e ⟨Sum.inl a.val, a.property⟩ = ⟨Sum.inl a.val, a.property⟩ := rfl

@[simp] theorem sumMatching_inr (ha : A → Prop) {hb : B → Prop} {hc : C → Prop}
    (e : {b // hb b} ≃ {c // hc c}) (b : {b // hb b}) :
    sumMatching ha e ⟨Sum.inr b.val, b.property⟩ = ⟨Sum.inr (e b).val, (e b).property⟩ := rfl

theorem sumMatching_return (p : Equiv.Perm A) (q : Equiv.Perm B) (r : Equiv.Perm C)
    (ha : A → Prop) (hb : B → Prop) (hc : C → Prop)
    (e : {b // hb b} ≃ {c // hc c})
    (he : ∀ b, e (nextHitPerm q hb b) = nextHitPerm r hc (e b))
    (d : {d // Sum.elim ha hb d}) :
    sumMatching ha e (nextHitPerm (Equiv.sumCongr p q) (Sum.elim ha hb) d) =
      nextHitPerm (Equiv.sumCongr p r) (Sum.elim ha hc) (sumMatching ha e d) := by
  rw [nextHitPerm_sum, nextHitPerm_sum]
  rcases d with ⟨a | b, h⟩
  · rfl
  · change (⟨Sum.inr (e (nextHitPerm q hb ⟨b, h⟩)).val, _⟩ :
        {d // Sum.elim ha hc d}) = ⟨Sum.inr (nextHitPerm r hc (e ⟨b, h⟩)).val, _⟩
    simp only [he]

theorem sumMatching_permCongr (p : Equiv.Perm A) (q : Equiv.Perm B) (r : Equiv.Perm C)
    (ha : A → Prop) (hb : B → Prop) (hc : C → Prop)
    (e : {b // hb b} ≃ {c // hc c})
    (he : ∀ b, e (nextHitPerm q hb b) = nextHitPerm r hc (e b)) :
    (sumMatching ha e).permCongr (nextHitPerm (Equiv.sumCongr p q) (Sum.elim ha hb)) =
      nextHitPerm (Equiv.sumCongr p r) (Sum.elim ha hc) := by
  apply Equiv.ext
  intro d
  obtain ⟨a, rfl⟩ := (sumMatching ha e).surjective d
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using
    sumMatching_return p q r ha hb hc e he a

end
end Mettapedia.GraphTheory.FourColor.FaceReturnSum
