import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceReturnProfile

/-!
# Marked face returns commute with supported rewiring

Deleting unmarked arc interiors before a supported permutation rewire gives
exactly the same return permutation as rewiring first. Thus cofaciality of
named darts after a seam operation is determined by a finite cyclic return
record, independently of the lengths of intervening faces.

This is the compositional geometry lemma needed to replace whole-face marks
in the frozen-face supplier by named-face connectivity. It does not assert
that the current geometric supplier already selects equal refined records.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedFaceReturnRewire

open GoertzelV24SeamFaceArc GoertzelV24OrderedCutFaceReturnProfile

noncomputable section
attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]
  (p : Equiv.Perm A) (hit : A → Prop) (tau : Equiv.Perm {a // hit a})

/-- Between departure and the first old return, no subsequent rewiring is
encountered. The departure is from `tau root`, not from `root`. -/
theorem pow_until_return (root : {a // hit a}) {n : ℕ}
    (hn : 0 < n)
    (hle : n ≤ firstPositiveHitTime p hit (tau root).val (tau root).property) :
    ((p * Equiv.Perm.ofSubtype tau) ^ n) root.val =
      (p ^ n) (tau root).val := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hzero : n = 0
    · subst n
      simp [Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_mem tau root.property]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
      have hbefore : n < firstPositiveHitTime p hit (tau root).val (tau root).property := by omega
      have hnot := not_hit_before_firstPositiveHitTime p hit
        (tau root).val (tau root).property hnpos hbefore
      rw [pow_succ', Equiv.Perm.mul_apply, ih hnpos (by omega),
        Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_not_mem tau hnot,
        pow_succ', Equiv.Perm.mul_apply]

/-- Supported rewiring changes the chosen outgoing arc, not its first-return
time. This is an exact time identity, not only a cycle equivalence. -/
theorem returnTime_rewire (root : {a // hit a}) :
    firstPositiveHitTime (p * Equiv.Perm.ofSubtype tau) hit root.val root.property =
      firstPositiveHitTime p hit (tau root).val (tau root).property := by
  let old := firstPositiveHitTime p hit (tau root).val (tau root).property
  let new := firstPositiveHitTime (p * Equiv.Perm.ofSubtype tau) hit root.val root.property
  have hop : 0 < old := firstPositiveHitTime_pos p hit _ _
  have hnp : 0 < new := firstPositiveHitTime_pos _ hit _ _
  have hlo : new ≤ old := by
    apply firstPositiveHitTime_le_of_hit _ hit _ _ hop
    rw [pow_until_return p hit tau root hop le_rfl]
    exact firstPositiveHitTime_hits p hit _ _
  have hhi : old ≤ new := by
    by_contra h
    have hlt : new < old := Nat.lt_of_not_ge h
    have hhit := firstPositiveHitTime_hits (p * Equiv.Perm.ofSubtype tau)
      hit root.val root.property
    change hit (((p * Equiv.Perm.ofSubtype tau) ^ new) root.val) at hhit
    rw [pow_until_return p hit tau root hnp hlo] at hhit
    exact not_hit_before_firstPositiveHitTime p hit _ _ hnp hlt hhit
  exact Nat.le_antisymm hlo hhi

/-- Exact commutation law for cyclic return records. Multiplication is in
Lean's convention: the right-hand permutation acts first. -/
theorem nextHitPerm_rewire :
    nextHitPerm (p * Equiv.Perm.ofSubtype tau) hit = nextHitPerm p hit * tau := by
  ext root
  change ((p * Equiv.Perm.ofSubtype tau) ^
      firstPositiveHitTime (p * Equiv.Perm.ofSubtype tau) hit root.val root.property) root.val =
    (p ^ firstPositiveHitTime p hit (tau root).val (tau root).property) (tau root).val
  rw [returnTime_rewire p hit tau root]
  exact pow_until_return p hit tau root (firstPositiveHitTime_pos p hit _ _) le_rfl

/-- The finite record computes both splitting and merging of marked faces. -/
theorem sameCycle_rewire_iff (first second : {a // hit a}) :
    (p * Equiv.Perm.ofSubtype tau).SameCycle first.val second.val ↔
      (nextHitPerm p hit * tau).SameCycle first second := by
  rw [← nextHitPerm_rewire p hit tau]
  exact (nextHitPerm_sameCycle_iff _ hit first second).symm

/-- Equal return records are interchangeable for every supported rewire,
not merely for the rewire used in a finite diagnostic. -/
theorem sameCycle_rewire_congr (q : Equiv.Perm A)
    (heq : nextHitPerm p hit = nextHitPerm q hit)
    (first second : {a // hit a}) :
    (p * Equiv.Perm.ofSubtype tau).SameCycle first.val second.val ↔
      (q * Equiv.Perm.ofSubtype tau).SameCycle first.val second.val := by
  rw [sameCycle_rewire_iff, sameCycle_rewire_iff, heq]

/-- The return record in an ambient-size-independent coordinate type. -/
def profile {n : ℕ} (coordinate : {a // hit a} ≃ Fin n) : Equiv.Perm (Fin n) :=
  coordinate.permCongr (nextHitPerm p hit)

/-- The state cost depends on the number of seam/observation points only. -/
theorem card_profile (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  simp [Fintype.card_perm]

/-- Coherent boundary coordinates transport the rewire as well as the
record. This is the interface for comparing carriers of different sizes. -/
theorem profile_rewire {n : ℕ} (coordinate : {a // hit a} ≃ Fin n)
    (rewire : Equiv.Perm (Fin n)) :
    profile (p * Equiv.Perm.ofSubtype (coordinate.symm.permCongr rewire)) hit coordinate =
      profile p hit coordinate * rewire := by
  simp only [profile, nextHitPerm_rewire, Equiv.permCongr_mul]
  congr 1
  ext i
  simp [Equiv.permCongr_apply]

/-- Exact cofaciality after rewiring, expressed entirely in finite port and
observation coordinates. -/
theorem coordinate_sameCycle_rewire_iff {n : ℕ}
    (coordinate : {a // hit a} ≃ Fin n) (rewire : Equiv.Perm (Fin n))
    (first second : {a // hit a}) :
    (p * Equiv.Perm.ofSubtype (coordinate.symm.permCongr rewire)).SameCycle
        first.val second.val ↔
      (profile p hit coordinate * rewire).SameCycle (coordinate first) (coordinate second) := by
  rw [← profile_rewire]
  exact (nextHitPerm_sameCycle_iff _ hit first second).symm.trans
    (permCongr_sameCycle_iff coordinate _ first second).symm

/-- A genuine replacement may change the entire ambient carrier. Equal
return profiles still give exactly the same answers after every common
rewire. No equality of face lengths or unmarked carriers is required. -/
theorem replacement_congr {B : Type*} [Fintype B] [DecidableEq B]
    (q : Equiv.Perm B) (otherHit : B → Prop) {n : ℕ}
    (left : {a // hit a} ≃ Fin n) (right : {b // otherHit b} ≃ Fin n)
    (heq : profile p hit left = profile q otherHit right)
    (rewire : Equiv.Perm (Fin n)) (i j : Fin n) :
    (p * Equiv.Perm.ofSubtype (left.symm.permCongr rewire)).SameCycle
        (left.symm i).val (left.symm j).val ↔
      (q * Equiv.Perm.ofSubtype (right.symm.permCongr rewire)).SameCycle
        (right.symm i).val (right.symm j).val := by
  rw [coordinate_sameCycle_rewire_iff, coordinate_sameCycle_rewire_iff]
  simp only [Equiv.apply_symm_apply, heq]

/-! A cycle partition is not an adequate replacement for the permutation.
These four-point controls are permutation geometry, not graph configurations. -/

def firstCycle : Equiv.Perm (Fin 4) := finRotate 4
def secondCycle : Equiv.Perm (Fin 4) := (Equiv.swap 1 2).permCongr firstCycle
def testRewire : Equiv.Perm (Fin 4) := Equiv.swap 0 1

theorem same_partition_before :
    ∀ i j : Fin 4, firstCycle.SameCycle i j ∧ secondCycle.SameCycle i j := by
  decide +kernel

theorem different_partition_after :
    (firstCycle * testRewire).SameCycle 0 2 ∧
      ¬ (secondCycle * testRewire).SameCycle 0 2 := by
  decide +kernel

section Rotation
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- On one dart carrier, sewing changes `alpha` while keeping `rho`. The
concrete new face permutation is therefore covered by the return law when
the partner change is supported on the recorded seam and marked points.
No assumption on the length of any face is needed. -/
theorem face_rewire_iff (RS : RotationSystem V E) (hit : RS.D → Prop)
    (tau : Equiv.Perm {d // hit d}) (newAlpha : Equiv.Perm RS.D)
    (halpha : newAlpha = RS.alpha * Equiv.Perm.ofSubtype tau)
    (first second : {d // hit d}) :
    (RS.rho * newAlpha).SameCycle first.val second.val ↔
      (nextHitPerm RS.phi hit * tau).SameCycle first second := by
  subst newAlpha
  rw [← mul_assoc]
  exact sameCycle_rewire_iff RS.phi hit tau first second

end Rotation
end
end Mettapedia.GraphTheory.FourColor.MarkedFaceReturnRewire
