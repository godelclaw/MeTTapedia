import Mettapedia.SetTheory.OpenTower.AntiFounded.Classification

/-!
# At height `ω` the anti-founded stage is uncountable

The closed set `V_ω` of `ZFSet` is countable: it has `ℵ₀` members. The closed stage `B_ℵ₀` of
the hypersets has the same well-founded part `V_ω` (`toZFSet_branching_aleph0`), and it is not
countable (`not_smallMembers_succ_aleph0_branching`): the law "a closed set of height `κ` has
`κ` members" breaks at `ω` once non-well-founded sets are admitted.

The witnesses are streams. For a set `A` of natural numbers, `streamAt A n` has the member
`streamAt A (n + 1)`, and also `∅` when `n ∈ A` (`mem_streamAt`). Each stream has at most two
members at every step, so it is hereditarily finitely branching (`stream_mem_branching`), and
distinct sets give distinct streams (`stream_injective`): `∅ ∈ streamAt A n` exactly when
`n ∈ A` (`empty_mem_streamAt_iff`). No stream is well-founded.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-- The stream graph of a set `A` of natural numbers: node `n` has the child `n + 1`, and the
childless node when `n ∈ A`. -/
def streamEdge (A : Set ℕ) : Option (ULift.{u} ℕ) → Option (ULift.{u} ℕ) → Prop
  | some n, some m => m.down = n.down + 1
  | some n, none => n.down ∈ A
  | none, _ => False

/-- The stream of `A` from step `n`. -/
noncomputable def streamAt (A : Set ℕ) (n : ℕ) : HSet.{u} :=
  HSet.decorate (streamEdge A) (some ⟨n⟩)

variable {A : Set ℕ}

theorem decorate_streamEdge_none (A : Set ℕ) : HSet.decorate (streamEdge.{u} A) none = ∅ :=
  HSet.eq_empty_iff.mpr fun _ hy => by
    obtain ⟨b, hb, _⟩ := HSet.mem_decorate.mp hy
    cases b <;> exact hb

/-- The members of a stream: the next step, and `∅` when `n ∈ A`. -/
theorem mem_streamAt {n : ℕ} {y : HSet.{u}} :
    y ∈ streamAt A n ↔ y = streamAt A (n + 1) ∨ (n ∈ A ∧ y = ∅) := by
  change y ∈ HSet.decorate (streamEdge A) (some ⟨n⟩) ↔ _
  rw [HSet.mem_decorate]
  constructor
  · rintro ⟨b, hb, rfl⟩
    cases b with
    | none => exact Or.inr ⟨hb, decorate_streamEdge_none A⟩
    | some m =>
      obtain ⟨m⟩ := m
      change m = n + 1 at hb
      subst hb
      exact Or.inl rfl
  · rintro (rfl | ⟨hn, rfl⟩)
    · exact ⟨some ⟨n + 1⟩, rfl, rfl⟩
    · exact ⟨none, hn, decorate_streamEdge_none A⟩

theorem streamAt_succ_mem (n : ℕ) : streamAt.{u} A (n + 1) ∈ streamAt A n :=
  mem_streamAt.mpr (Or.inl rfl)

theorem streamAt_ne_empty (n : ℕ) : streamAt.{u} A n ≠ ∅ :=
  fun h => HSet.notMem_empty _ (h ▸ streamAt_succ_mem n)

theorem empty_mem_streamAt_iff {n : ℕ} : (∅ : HSet.{u}) ∈ streamAt A n ↔ n ∈ A := by
  rw [mem_streamAt]
  constructor
  · rintro (h | ⟨hn, _⟩)
    · exact absurd h.symm (streamAt_ne_empty _)
    · exact hn
  · exact fun hn => Or.inr ⟨hn, rfl⟩

theorem streamAt_eq_of_eq_zero {B : Set ℕ} (h : streamAt.{u} A 0 = streamAt B 0) :
    ∀ n, streamAt.{u} A n = streamAt B n
  | 0 => h
  | n + 1 => by
    have member : streamAt.{u} A (n + 1) ∈ streamAt B n := by
      rw [← streamAt_eq_of_eq_zero h n]
      exact streamAt_succ_mem n
    rcases mem_streamAt.mp member with e | ⟨_, e⟩
    · exact e
    · exact absurd e (streamAt_ne_empty _)

/-- **Distinct sets of natural numbers give distinct streams.** -/
theorem stream_injective : Function.Injective fun A : Set ℕ => streamAt.{u} A 0 := by
  intro A B h
  ext n
  have e := streamAt_eq_of_eq_zero h n
  rw [← empty_mem_streamAt_iff (A := A), ← empty_mem_streamAt_iff (A := B), e]

theorem below_streamAt {n : ℕ} {z : HSet.{u}} (h : Below (streamAt A n) z) :
    (∃ m, z = streamAt A m) ∨ z = ∅ := by
  induction h with
  | refl => exact Or.inl ⟨n, rfl⟩
  | tail _ hmem ih =>
    rcases ih with ⟨m, rfl⟩ | rfl
    · rcases mem_streamAt.mp hmem with rfl | ⟨_, rfl⟩
      · exact Or.inl ⟨m + 1, rfl⟩
      · exact Or.inr rfl
    · exact absurd hmem (HSet.notMem_empty _)

/-- A stream has at most two members at each step. -/
theorem smallMembers_streamAt (n : ℕ) : SmallMembers ℵ₀ (streamAt.{u} A n) := by
  classical
  refine ⟨ULift.{u} Bool, fun b => if b.down then streamAt A (n + 1)
    else if n ∈ A then ∅ else streamAt A (n + 1), lt_aleph0_of_finite _, fun y => ?_⟩
  rw [mem_streamAt]
  constructor
  · rintro (rfl | ⟨hn, rfl⟩)
    · exact ⟨⟨true⟩, rfl⟩
    · exact ⟨⟨false⟩, by simp only [Bool.false_eq_true, if_false, if_pos hn]⟩
  · rintro ⟨⟨b⟩, rfl⟩
    cases b
    · by_cases hn : n ∈ A
      · simp [hn]
      · simp [hn]
    · exact Or.inl rfl

/-- Every stream is a member of `B_ℵ₀`. -/
theorem stream_mem_branching (A : Set ℕ) : streamAt.{u} A 0 ∈ branching ℵ₀ := by
  refine mem_branching.mpr fun z hz => ?_
  rcases below_streamAt hz with ⟨m, rfl⟩ | rfl
  · exact smallMembers_streamAt m
  · exact smallMembers_empty aleph0_ne_zero

/-- **`B_ℵ₀` has at least continuum many members.** -/
theorem exists_continuum_members_branching :
    ∃ f : Set ℕ → HSet.{u}, Function.Injective f ∧ ∀ A, f A ∈ branching ℵ₀ :=
  ⟨_, stream_injective, stream_mem_branching⟩

/-- **`B_ℵ₀` is not countable.** -/
theorem not_smallMembers_succ_aleph0_branching :
    ¬ SmallMembers (Order.succ ℵ₀) (branching (ℵ₀ : Cardinal.{u})) := by
  rintro ⟨ι, g, hι, hg⟩
  have hit : ∀ A : Set ℕ, ∃ i, g i = streamAt.{u} A 0 :=
    fun A => (hg _).mp (stream_mem_branching A)
  choose φ hφ using hit
  have injective : Function.Injective φ := fun A B e =>
    stream_injective ((hφ A).symm.trans ((congrArg g e).trans (hφ B)))
  have size := lift_mk_le_lift_mk_of_injective injective
  rw [mk_set, mk_nat, lift_two_power, lift_aleph0, lift_uzero] at size
  have countable : #ι ≤ ℵ₀ := Order.lt_succ_iff.mp hι
  exact (cantor ℵ₀).not_ge (size.trans countable)

/-- `V_ω` is countable. -/
theorem smallMembers_succ_aleph0_vonNeumann_omega :
    SmallMembers (Order.succ ℵ₀) (HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u})) := by
  rw [smallMembers_ofZFSet_iff, ZFSet.card_vonNeumann, preBeth_omega]
  exact Order.lt_succ _

/-- **Two closed stages of height `ω`: one countable, one not.** -/
theorem closed_stages_of_height_omega_differ_in_size :
    HClosed (HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u})) ∧ HClosed (branching (ℵ₀ : Cardinal.{u})) ∧
      HSet.toZFSet (branching (ℵ₀ : Cardinal.{u})) = V_ Ordinal.omega0 ∧
      SmallMembers (Order.succ ℵ₀) (HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u})) ∧
      ¬ SmallMembers (Order.succ ℵ₀) (branching (ℵ₀ : Cardinal.{u})) :=
  ⟨hclosed_ofZFSet_iff.mpr
      ((Strength.InaccessibleLevels.closed_iff _).mpr (Or.inr (Or.inl rfl))),
    hclosed_branching_aleph0, toZFSet_branching_aleph0,
    smallMembers_succ_aleph0_vonNeumann_omega, not_smallMembers_succ_aleph0_branching⟩

#print axioms stream_injective
#print axioms stream_mem_branching
#print axioms not_smallMembers_succ_aleph0_branching
#print axioms closed_stages_of_height_omega_differ_in_size

end Mettapedia.SetTheory.OpenTower.AntiFounded
