import Mettapedia.GraphTheory.FourColor.MarkedFaceReturnRewire
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Finite return records with persistent names

A name may be absent from a shore, and several names may denote one dart.
Record both the cyclic first-return permutation and these optional name
coordinates. Padding unused coordinates by fixed points gives a carrier
depending only on the number of names, not on face perimeters.

Equality of records constructs an equivalence of the actual observed dart
carriers, preserving all names and first returns. This is the compatibility
ingredient for refining the frozen Count supplier; it does not itself
supply a pair of geometric shores.
-/

namespace Mettapedia.GraphTheory.FourColor.NamedFaceRecord

open GoertzelV24OrderedCutFaceReturnProfile MarkedFaceReturnRewire

noncomputable section
attribute [local instance] Classical.propDecidable

variable {L A B : Type*} [Fintype L] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

def Hit (loc : L → Option A) (a : A) : Prop := ∃ l, loc l = some a

abbrev Point (loc : L → Option A) := {a // Hit loc a}

def point (loc : L → Option A) (l : L) : Option (Point loc) :=
  match h : loc l with
  | none => none
  | some a => some ⟨a, ⟨l, h⟩⟩

theorem point_some_iff (loc : L → Option A) (l : L) (a : Point loc) :
    point loc l = some a ↔ loc l = some a.val := by
  unfold point
  split <;> simp_all only [Option.some.injEq, reduceCtorEq, Subtype.ext_iff]

theorem point_val (loc : L → Option A) (l : L) :
    (point loc l).map Subtype.val = loc l := by
  unfold point
  split <;> simp_all

theorem exists_name (loc : L → Option A) (a : Point loc) :
    ∃ l, point loc l = some a := by
  obtain ⟨l, hl⟩ := a.property
  exact ⟨l, (point_some_iff loc l a).mpr hl⟩

theorem card_point_le (loc : L → Option A) :
    Fintype.card (Point loc) ≤ Fintype.card L := by
  let choose : Point loc → L := fun a => Classical.choose a.property
  apply Fintype.card_le_of_injective choose
  intro a b hab
  have ha : loc (choose a) = some a.val := Classical.choose_spec a.property
  have hb : loc (choose b) = some b.val := Classical.choose_spec b.property
  rw [hab] at ha
  exact Subtype.ext (Option.some.inj (ha.symm.trans hb))

def coordinate (loc : L → Option A) : Point loc ↪ Fin (Fintype.card L) :=
  (Fintype.equivFin (Point loc)).toEmbedding.trans (Fin.castLEEmb (card_point_le loc))

/-- The name map is essential: fixed padding alone cannot distinguish an
unobserved coordinate from a named fixed-point face. -/
abbrev Record (L : Type*) [Fintype L] :=
  Equiv.Perm (Fin (Fintype.card L)) × (L → Option (Fin (Fintype.card L)))

def record (p : Equiv.Perm A) (loc : L → Option A) : Record L :=
  ((nextHitPerm p (Hit loc)).viaEmbedding (coordinate loc),
    fun l => (point loc l).map (coordinate loc))

theorem card_record : Fintype.card (Record L) =
    (Fintype.card L).factorial * (Fintype.card L + 1) ^ Fintype.card L := by
  simp [Record, Fintype.card_perm]

theorem record_apply (p : Equiv.Perm A) (loc : L → Option A) (a : Point loc) :
    (record p loc).1 (coordinate loc a) = coordinate loc (nextHitPerm p (Hit loc) a) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem coordinate_mem_iff (p : Equiv.Perm A) (loc : L → Option A)
    (i : Fin (Fintype.card L)) :
    i ∈ Set.range (coordinate loc) ↔ ∃ l, (record p loc).2 l = some i := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨l, hl⟩ := exists_name loc a
    exact ⟨l, by simp [record, hl]⟩
  · rintro ⟨l, hl⟩
    change (point loc l).map (coordinate loc) = some i at hl
    cases h : point loc l with
    | none => simp [h] at hl
    | some a => exact ⟨a, by simpa [h] using hl⟩

variable (p : Equiv.Perm A) (loc : L → Option A)
  (q : Equiv.Perm B) (other : L → Option B)
  (heq : record p loc = record q other)

include heq in
theorem range_eq : Set.range (coordinate loc) = Set.range (coordinate other) := by
  ext i
  rw [coordinate_mem_iff p loc, coordinate_mem_iff q other, heq]

/-- Equality of the full records yields an actual dart correspondence, not
merely equality of the two cardinalities. -/
def matching : Point loc ≃ Point other :=
  (Equiv.ofInjective (coordinate loc) (coordinate loc).injective).trans
    ((Equiv.setCongr (range_eq p loc q other heq)).trans
      (Equiv.ofInjective (coordinate other) (coordinate other).injective).symm)

theorem coordinate_matching (a : Point loc) :
    coordinate other (matching p loc q other heq a) = coordinate loc a := by
  exact Equiv.apply_ofInjective_symm (coordinate other).injective _

theorem matching_point (l : L) :
    (point loc l).map (matching p loc q other heq) = point other l := by
  cases hl : point loc l with
  | none =>
    have h := congrFun (congrArg Prod.snd heq) l
    change (point loc l).map (coordinate loc) = (point other l).map (coordinate other) at h
    cases hr : point other l <;> simp_all
  | some a =>
    have h := congrFun (congrArg Prod.snd heq) l
    change (point loc l).map (coordinate loc) = (point other l).map (coordinate other) at h
    cases hr : point other l with
    | none => simp [hl, hr] at h
    | some b =>
      simp only [hl, hr, Option.map_some, Option.some.injEq] at h ⊢
      apply (coordinate other).injective
      exact (coordinate_matching p loc q other heq a).trans h

theorem matching_return (a : Point loc) :
    matching p loc q other heq (nextHitPerm p (Hit loc) a) =
      nextHitPerm q (Hit other) (matching p loc q other heq a) := by
  apply (coordinate other).injective
  rw [coordinate_matching, ← record_apply, ← record_apply, coordinate_matching]
  exact congrArg (fun r : Record L => r.1 (coordinate loc a)) heq

theorem matching_named_iff (l : L) (a : Point loc) :
    loc l = some a.val ↔ other l = some (matching p loc q other heq a).val := by
  rw [← point_some_iff, ← point_some_iff]
  constructor
  · intro h
    rw [← matching_point p loc q other heq, h]
    rfl
  · intro h
    apply Option.map_injective (matching p loc q other heq).injective
    rw [matching_point p loc q other heq, Option.map_some, h]

theorem matching_permCongr :
    (matching p loc q other heq).permCongr (nextHitPerm p (Hit loc)) =
      nextHitPerm q (Hit other) := by
  ext b
  obtain ⟨a, rfl⟩ := (matching p loc q other heq).surjective b
  simpa [Equiv.permCongr_apply] using
    congrArg Subtype.val (matching_return p loc q other heq a)

/-- Every corresponding supported rewire preserves and reflects cofaciality.
The two ambient carriers may have different sizes and face perimeters. -/
theorem replacement_congr (tau : Equiv.Perm (Point loc)) (a b : Point loc) :
    (p * Equiv.Perm.ofSubtype tau).SameCycle a.val b.val ↔
      (q * Equiv.Perm.ofSubtype ((matching p loc q other heq).permCongr tau)).SameCycle
        (matching p loc q other heq a).val (matching p loc q other heq b).val := by
  rw [sameCycle_rewire_iff, sameCycle_rewire_iff]
  rw [← matching_permCongr p loc q other heq, ← Equiv.permCongr_mul]
  exact (permCongr_sameCycle_iff (matching p loc q other heq) _ a b).symm

end
end Mettapedia.GraphTheory.FourColor.NamedFaceRecord
