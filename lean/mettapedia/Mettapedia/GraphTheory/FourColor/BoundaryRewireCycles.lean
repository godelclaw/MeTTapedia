import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedRegionBoundaryOrder

/-!
# The complete cycle-count change under boundary rewiring

Changing a permutation only at marked points leaves all cycles missing
those points unchanged. For right multiplication by a lifted boundary
permutation, the first-return law then computes the whole cycle-count
change, with no connectedness or single-boundary-cycle assumption.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryRewireCycles

open Equiv Equiv.Perm
open GoertzelV24RetainedSpliceFaceCount GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24RetainedRegionBoundaryOrder

noncomputable section
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
/-- An orbit avoiding the changed points has exactly the same iterates. -/
theorem pow_eq_of_avoids (p q : Perm D) (hit : D → Prop)
    (heq : ∀ d, ¬ hit d → q d = p d) (a : D)
    (ha : ∀ d, p.SameCycle a d → ¬ hit d) (n : ℕ) :
    (q ^ n) a = (p ^ n) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, heq _
      (ha _ (SameCycle.refl p a).pow_right), pow_succ', Perm.mul_apply]

omit [DecidableEq D] in
theorem sameCycle_iff_of_avoids (p q : Perm D) (hit : D → Prop)
    (heq : ∀ d, ¬ hit d → q d = p d) (a : D)
    (ha : ∀ d, p.SameCycle a d → ¬ hit d) (b : D) :
    p.SameCycle a b ↔ q.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, pow_eq_of_avoids p q hit heq a ha, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, ← pow_eq_of_avoids p q hit heq a ha, hn]⟩

/-- The actual untouched cycle, not just a count of untouched cycles. -/
def nonHitMap (p q : Perm D) (hit : D → Prop)
    (heq : ∀ d, ¬ hit d → q d = p d) (o : NonHitOrbit p hit) : NonHitOrbit q hit :=
  ⟨Quotient.mk _ o.1.out, by
    rintro ⟨d, hd, hdo⟩
    have hq : q.SameCycle o.1.out d := (Quotient.exact hdo).symm
    have ha := nonHitOrbit_not_hit_of_sameCycle p hit o
    exact ha d ((sameCycle_iff_of_avoids p q hit heq o.1.out ha d).2 hq) hd⟩

theorem nonHitMap_inverse (p q : Perm D) (hit : D → Prop)
    (heq : ∀ d, ¬ hit d → q d = p d) (o : NonHitOrbit p hit) :
    nonHitMap q p hit (fun d hd => (heq d hd).symm) (nonHitMap p q hit heq o) = o := by
  apply Subtype.ext
  change Quotient.mk _ (nonHitMap p q hit heq o).1.out = o.1
  apply Eq.trans _ (Quotient.out_eq o.1)
  apply Quotient.sound
  have hq : q.SameCycle (nonHitMap p q hit heq o).1.out o.1.out :=
    Quotient.exact (Quotient.out_eq (nonHitMap p q hit heq o).1)
  have ha := nonHitOrbit_not_hit_of_sameCycle p hit o
  exact ((sameCycle_iff_of_avoids p q hit heq o.1.out ha _).2 hq.symm).symm

/-- Any change confined to the marks preserves the non-hit orbit carrier. -/
def nonHitEquiv (p q : Perm D) (hit : D → Prop)
    (heq : ∀ d, ¬ hit d → q d = p d) : NonHitOrbit p hit ≃ NonHitOrbit q hit where
  toFun := nonHitMap p q hit heq
  invFun := nonHitMap q p hit (fun d hd => (heq d hd).symm)
  left_inv := nonHitMap_inverse p q hit heq
  right_inv := nonHitMap_inverse q p hit (fun d hd => (heq d hd).symm)

/-- The change in total cycle count is entirely a boundary change. The
additive equation avoids truncated subtraction of natural numbers. -/
theorem cycle_count_rewire (p : Perm D) (hit : D → Prop) [DecidablePred hit]
    (s : Perm {d // hit d}) :
    (p * ofSubtype s).partition.parts.card + (nextHitPerm p hit).partition.parts.card =
      p.partition.parts.card + (nextHitPerm p hit * s).partition.parts.card := by
  have heq (d : D) (hd : ¬ hit d) : (p * ofSubtype s) d = p d := by
    rw [Perm.mul_apply, ofSubtype_apply_of_not_mem s hd]
  have hnon := Fintype.card_congr (nonHitEquiv p (p * ofSubtype s) hit heq)
  have hp := card_permOrbit_eq_hit_add_nonHit p hit
  have hq := card_permOrbit_eq_hit_add_nonHit (p * ofSubtype s) hit
  rw [card_permOrbit_eq_card_partition_parts, card_hitOrbit_eq_nextHit_partition_card] at hp hq
  rw [nextHitPerm_mul_ofSubtype] at hq
  omega

theorem cycle_count_preserved_iff (p : Perm D) (hit : D → Prop) [DecidablePred hit]
    (s : Perm {d // hit d}) :
    (p * ofSubtype s).partition.parts.card = p.partition.parts.card ↔
      (nextHitPerm p hit * s).partition.parts.card = (nextHitPerm p hit).partition.parts.card := by
  have := cycle_count_rewire p hit s
  omega

end
end Mettapedia.GraphTheory.FourColor.BoundaryRewireCycles
