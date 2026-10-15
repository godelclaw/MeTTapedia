import Mathlib.Data.Fintype.Powerset
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.VietorisTopology

/-!
# A compact Hausdorff space homeomorphic to its own compact subsets

The tower of compact subsets starts at one point. The empty type has exactly
one compact subset, so a tower begun there repeats this one a step later.
Each later stage is the Vietoris space of compact subsets of the previous
stage. The limit is the space of coherent threads. That limit is homeomorphic
to the Vietoris space of its own compact subsets. A finite stage is not.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Set Topology TopologicalSpace TopologicalSpace.Compacts

/-! ## Finite stages -/

/-- Carrier and Vietoris topology of stage `n`, packaged so the next stage is
definitionally the compact subsets of this one. -/
@[reducible]
def stagePack : ℕ → Σ α : Type, TopologicalSpace α
  | 0 => ⟨PUnit, inferInstance⟩
  | n + 1 =>
    let prev := stagePack n
    ⟨@Compacts.{0} prev.1 prev.2, @Compacts.topology prev.1 prev.2⟩

/-- Stage `0` is one point. Stage `n + 1` is the compact subsets of stage `n`. -/
@[reducible]
def Stage (n : ℕ) : Type := (stagePack n).1

instance (n : ℕ) : TopologicalSpace (Stage n) := (stagePack n).2

example : Nonempty (stagePack 0).1 := ⟨PUnit.unit⟩

example : (⊥ : (stagePack 1).1) ≠ ⊤ := by
  intro h
  have := congrArg (fun s : Stage 1 => (s : Set (Stage 0))) h
  simp at this

theorem stageCompact : (n : ℕ) → CompactSpace (Stage n)
  | 0 => inferInstance
  | n + 1 => (compactSpace_iff (α := Stage n)).2 (stageCompact n)

instance (n : ℕ) : CompactSpace (Stage n) := stageCompact n

theorem stageHausdorff : (n : ℕ) → T2Space (Stage n)
  | 0 => inferInstance
  | n + 1 => (t2Space_iff (α := Stage n)).2 (stageHausdorff n)

instance (n : ℕ) : T2Space (Stage n) := stageHausdorff n

/-- The start is one point. -/
example : Unique (Stage 0) := inferInstance

/-- The stage after the start has an empty set and a full set. -/
theorem stage_one_bot_ne_top : (⊥ : Stage 1) ≠ ⊤ := by
  intro h
  have := congrArg (fun s : Stage 1 => (s : Set (Stage 0))) h
  simp at this

example : Nontrivial (Stage 1) := ⟨⊥, ⊤, stage_one_bot_ne_top⟩

/-- Compact subsets of the empty type are one point, so that start repeats the
one-point tower one step later. -/
example : Subsingleton (Compacts Empty) ∧ Nonempty (Compacts Empty) :=
  ⟨inferInstance, inferInstance⟩

/-- On a finite carrier every subset is compact, so compact subsets are all subsets. -/
noncomputable def compactsEquivSet (α : Type) [TopologicalSpace α] [Finite α] :
    Compacts α ≃ Set α where
  toFun K := (K : Set α)
  invFun s := ⟨s, (finite_univ.subset (subset_univ s)).isCompact⟩
  left_inv _ := Compacts.ext rfl
  right_inv _ := rfl

example : (compactsEquivSet (Stage 0) ⊥ : Set (Stage 0)) = ∅ := by
  simp [compactsEquivSet, coe_bot]

example : (compactsEquivSet (Stage 0) ⊤ : Set (Stage 0)) ≠ ∅ := by
  simp [compactsEquivSet, coe_top]

@[instance_reducible]
noncomputable def fintypeStage : (n : ℕ) → Fintype (Stage n)
  | 0 => inferInstance
  | n + 1 => by
    letI := fintypeStage n
    exact Fintype.ofEquiv (Set (Stage n)) (compactsEquivSet (Stage n)).symm

noncomputable instance (n : ℕ) : Fintype (Stage n) := fintypeStage n

noncomputable instance (n : ℕ) : Fintype (Compacts (Stage n)) := by
  letI := fintypeStage n
  exact Fintype.ofEquiv (Set (Stage n)) (compactsEquivSet (Stage n)).symm

theorem stage_card_succ (n : ℕ) :
    Fintype.card (Stage (n + 1)) = 2 ^ Fintype.card (Stage n) := by
  change Fintype.card (Compacts (Stage n)) = 2 ^ Fintype.card (Stage n)
  exact (Fintype.card_congr (compactsEquivSet (Stage n))).trans Fintype.card_set

/-- No finite stage is homeomorphic to the space of its own compact subsets. -/
theorem stage_not_fixed (n : ℕ) : ¬ Nonempty (Stage n ≃ₜ Compacts (Stage n)) := by
  intro ⟨e⟩
  have hcard := Fintype.card_congr (e.toEquiv.trans (compactsEquivSet (Stage n)))
  rw [Fintype.card_set] at hcard
  exact (Fintype.card (Stage n)).lt_two_pow_self.ne hcard

example : ¬ Nonempty (Stage 0 ≃ₜ Compacts (Stage 0)) := stage_not_fixed 0

example : Fintype.card (Stage 0) < 2 ^ Fintype.card (Stage 0) :=
  (Fintype.card (Stage 0)).lt_two_pow_self

/-! ## Bonding maps -/

noncomputable def bondPack : (n : ℕ) → {f : Stage (n + 1) → Stage n // Continuous f}
  | 0 => ⟨fun _ => PUnit.unit, continuous_const⟩
  | n + 1 =>
    let b := bondPack n
    ⟨Compacts.map b.1 b.2, b.2.compacts_map⟩

/-- The bonding map of the tower. At stage `0` it is the unique map to the point.
At later stages it is the direct image of compact subsets. -/
noncomputable def bond (n : ℕ) : Stage (n + 1) → Stage n := (bondPack n).1

theorem bond_continuous (n : ℕ) : Continuous (bond n) := (bondPack n).2

theorem bond_zero (s : Stage 1) : bond 0 s = PUnit.unit := rfl

theorem bond_succ (n : ℕ) (K : Stage (n + 2)) :
    bond (n + 1) K = Compacts.map (bond n) (bond_continuous n) K := rfl

example : Function.Surjective (bondPack 0).1 := fun y => ⟨⊥, Subsingleton.elim (bond 0 ⊥) y⟩

example : ¬ Function.Injective (Compacts.map (bond 0) (bond_continuous 0)) := by
  intro hinj
  exact stage_one_bot_ne_top <|
    (map_injective_iff (bond_continuous 0)).1 hinj (Subsingleton.elim _ _)

theorem bond_surjective : ∀ n, Function.Surjective (bond n)
  | 0, y => ⟨⊥, Subsingleton.elim _ y⟩
  | n + 1, L => by
    refine ⟨⟨bond n ⁻¹' (L : Set (Stage n)), ?_⟩, ?_⟩
    · exact (L.isCompact.isClosed.preimage (bond_continuous n)).isCompact
    · apply Compacts.ext
      simp only [coe_map, bond_succ]
      exact image_preimage_eq (L : Set (Stage n)) (bond_surjective n)

example : Function.Surjective (bond 0) := bond_surjective 0

example : ¬ Function.Injective (bond 0) := by
  intro hinj
  exact stage_one_bot_ne_top (hinj (Subsingleton.elim (bond 0 ⊥) (bond 0 ⊤)))

/-! ## The limit -/

/-- A thread assigns a point of every stage and respects the bonding maps. -/
def compatibleSet : Set (∀ n, Stage n) :=
  {f | ∀ n, bond n (f (n + 1)) = f n}

theorem compatible_closed : IsClosed compatibleSet := by
  have : compatibleSet = ⋂ n, {f | bond n (f (n + 1)) = f n} := by
    ext f
    simp [compatibleSet, mem_iInter]
  rw [this]
  exact isClosed_iInter fun n =>
    isClosed_eq ((bond_continuous n).comp (continuous_apply (n + 1))) (continuous_apply n)

def emptyStage : ∀ n, Stage n
  | 0 => PUnit.unit
  | _ + 1 => ⊥

def fullStage : ∀ n, Stage n
  | 0 => PUnit.unit
  | _ + 1 => ⊤

theorem empty_compat (n : ℕ) : bond n (emptyStage (n + 1)) = emptyStage n := by
  cases n with
  | zero => rfl
  | succ n =>
    apply Compacts.ext
    simp only [emptyStage]
    rw [bond_succ, coe_map, coe_bot, image_empty, coe_bot]

theorem full_compat (n : ℕ) : bond n (fullStage (n + 1)) = fullStage n := by
  cases n with
  | zero => rfl
  | succ n =>
    apply Compacts.ext
    simp only [fullStage, bond_succ, coe_map]
    rw [coe_top, image_univ, coe_top]
    exact range_eq_univ.2 (bond_surjective n)

example : emptyStage ∈ compatibleSet := empty_compat

def brokenStage : ∀ n, Stage n
  | 0 => PUnit.unit
  | 1 => ⊤
  | _ + 2 => ⊥

example : bond 0 (brokenStage 1) = brokenStage 0 := by
  simp [brokenStage, bond_zero]

example : brokenStage ∉ compatibleSet := by
  intro h
  have hbond : bond 1 (⊥ : Stage 2) = ⊤ := by simpa [brokenStage] using h 1
  have hset := congrArg (fun s : Stage 1 => (s : Set (Stage 0))) hbond
  rw [bond_succ, coe_map, coe_bot, image_empty, coe_top] at hset
  exact empty_ne_univ hset

/-- Coherent threads through the tower, with the subspace topology from the product. -/
@[ext]
structure N where
  atStage : ∀ n, Stage n
  compat : ∀ n, bond n (atStage (n + 1)) = atStage n

def toPi (p : N) : ∀ n, Stage n := p.atStage

instance : TopologicalSpace N := TopologicalSpace.induced toPi inferInstance

theorem range_toPi : range toPi = compatibleSet := by
  ext f
  constructor
  · rintro ⟨p, rfl⟩
    exact p.compat
  · intro hf
    exact ⟨⟨f, hf⟩, rfl⟩

theorem toPi_isClosedEmbedding : IsClosedEmbedding toPi where
  eq_induced := rfl
  injective := by
    intro a b h
    cases a
    cases b
    subst h
    rfl
  isClosed_range := by
    rw [range_toPi]
    exact compatible_closed

instance : CompactSpace N := toPi_isClosedEmbedding.compactSpace

instance : T2Space N := toPi_isClosedEmbedding.isEmbedding.t2Space

def emptyThread : N := ⟨emptyStage, empty_compat⟩

def fullThread : N := ⟨fullStage, full_compat⟩

example : emptyThread ≠ fullThread := by
  intro h
  have := congrArg (fun p : N => p.atStage 1) h
  simp [emptyThread, fullThread, emptyStage, fullStage] at this

example : CompactSpace N ∧ T2Space N := ⟨inferInstance, inferInstance⟩

def proj (n : ℕ) : N → Stage n := fun p => p.atStage n

theorem proj_continuous (n : ℕ) : Continuous (proj n) :=
  (continuous_apply n).comp toPi_isClosedEmbedding.continuous

theorem proj_zero (p : N) : proj 0 p = PUnit.unit := Subsingleton.elim _ _

/-! ## Threads through a prescribed stage -/

/-- The value at stage `k ≤ n` obtained by iterating the bonding maps down from `x`. -/
noncomputable def below : (n : ℕ) → Stage n → (k : ℕ) → k ≤ n → Stage k
  | 0, x, k, hk => (Nat.le_antisymm hk (Nat.zero_le k)) ▸ x
  | n + 1, x, k, hk =>
    if hk' : k = n + 1 then
      hk' ▸ x
    else
      below n (bond n x) k (Nat.le_of_lt_succ (lt_of_le_of_ne hk hk'))

theorem below_self (n : ℕ) (x : Stage n) : below n x n le_rfl = x := by
  cases n with
  | zero => rfl
  | succ n =>
    simp [below]

example : below 1 (⊤ : Stage 1) 0 (Nat.zero_le _) = PUnit.unit := by
  simp [below, bond_zero]

example :
    below 1 (⊥ : Stage 1) 0 (Nat.zero_le _) = below 1 (⊤ : Stage 1) 0 (Nat.zero_le _) ∧
      (⊥ : Stage 1) ≠ ⊤ := by
  refine ⟨?_, stage_one_bot_ne_top⟩
  simp [below, bond_zero]

theorem image_bond_stage (p : N) (k : ℕ) :
    bond k '' (p.atStage (k + 2) : Set (Stage (k + 1))) =
      (p.atStage (k + 1) : Set (Stage k)) := by
  have hcompat := p.compat (k + 1)
  rw [bond_succ] at hcompat
  exact congrArg (fun s : Stage (k + 1) => (s : Set (Stage k))) hcompat

theorem exists_step (p : N) (k : ℕ) (y : Stage k)
    (hy : y ∈ (p.atStage (k + 1) : Set (Stage k))) :
    ∃ z : Stage (k + 1), z ∈ (p.atStage (k + 2) : Set (Stage (k + 1))) ∧ bond k z = y := by
  rw [← image_bond_stage p k] at hy
  simpa [mem_image] using hy

theorem mem_bond_of_mem_succ (p : N) (k : ℕ) (z : Stage (k + 1))
    (hz : z ∈ (p.atStage (k + 2) : Set (Stage (k + 1)))) :
    bond k z ∈ (p.atStage (k + 1) : Set (Stage k)) := by
  rw [← image_bond_stage p k]
  exact ⟨z, hz, rfl⟩

theorem below_mem (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) (hk : k ≤ n) :
    below n x k hk ∈ (p.atStage (k + 1) : Set (Stage k)) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := Nat.le_antisymm hk (Nat.zero_le k)
    subst hk0
    simpa [below] using hx
  | succ n ih =>
    by_cases hk' : k = n + 1
    · subst hk'
      simpa [below] using hx
    · have hx' : bond n x ∈ (p.atStage (n + 1) : Set (Stage n)) :=
        mem_bond_of_mem_succ p n x hx
      have hk'' : k ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hk hk')
      have hbelow : below (n + 1) x k hk = below n (bond n x) k hk'' := by
        simp [below, hk']
      rw [hbelow]
      exact ih (bond n x) hx' k hk''

/-- `d` successive preimages of `x` inside the stage sets of `p`. -/
noncomputable def climb (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) :
    (d : ℕ) → {y : Stage (n + d) // y ∈ (p.atStage (n + d + 1) : Set (Stage (n + d)))}
  | 0 => ⟨x, hx⟩
  | d + 1 =>
    let prev := climb p n x hx d
    let hstep := exists_step p (n + d) prev.1 prev.2
    ⟨Classical.choose hstep, (Classical.choose_spec hstep).1⟩

theorem climb_zero (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) :
    (climb p n x hx 0).1 = x := rfl

theorem climb_bond (p : N) (n d : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) :
    bond (n + d) (climb p n x hx (d + 1)).1 = (climb p n x hx d).1 :=
  (Classical.choose_spec (exists_step p (n + d) (climb p n x hx d).1 (climb p n x hx d).2)).2

theorem mem_top_stage {α : Type} [TopologicalSpace α] [CompactSpace α] (x : α) :
    x ∈ (⊤ : Compacts α) :=
  mem_univ x

example : PUnit.unit ∈ (⊤ : Stage 1) := mem_top_stage _

example : ¬ PUnit.unit ∈ (⊥ : Stage 1) :=
  notMem_empty _

theorem full_one_mem : PUnit.unit ∈ (fullThread.atStage 1 : Set (Stage 0)) := by
  simp only [fullThread, fullStage, SetLike.mem_coe]
  exact mem_univ _

theorem full_bot_mem : (⊥ : Stage 1) ∈ (fullThread.atStage 2 : Set (Stage 1)) := by
  simp only [fullThread, fullStage, SetLike.mem_coe]
  exact mem_univ _

example : (climb fullThread 0 PUnit.unit full_one_mem 0).1 = PUnit.unit := rfl

example : ∃ z : Stage 1, bond 0 z = PUnit.unit ∧
    z ≠ (climb fullThread 0 PUnit.unit full_one_mem 1).1 := by
  by_cases h : (climb fullThread 0 PUnit.unit full_one_mem 1).1 = ⊥
  · exact ⟨⊤, bond_zero _, by simp [h]⟩
  · exact ⟨⊥, bond_zero _, Ne.symm h⟩

noncomputable def throughAt (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) : Stage k :=
  if hk : k ≤ n then
    below n x k hk
  else
    let hle : n ≤ k := (Nat.not_le.mp hk).le
    (Nat.add_sub_of_le hle) ▸ (climb p n x hx (k - n)).1

theorem throughAt_le (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) (hk : k ≤ n) :
    throughAt p n x hx k = below n x k hk := by
  simp [throughAt, hk]

theorem throughAt_self (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) :
    throughAt p n x hx n = x := by
  simp [throughAt, below_self]

theorem throughAt_gt (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) (hk : n < k) :
    throughAt p n x hx k =
      (Nat.add_sub_of_le hk.le) ▸ (climb p n x hx (k - n)).1 := by
  simp [throughAt, hk.not_ge]

theorem cast_stage_mem (p : N) {a b : ℕ} (h : a = b) {y : Stage a}
    (hy : y ∈ (p.atStage (a + 1) : Set (Stage a))) :
    h ▸ y ∈ (p.atStage (b + 1) : Set (Stage b)) := by
  subst h
  exact hy

theorem cast_stage_self {a : ℕ} (h : a = a) (y : Stage a) : h ▸ y = y := by
  cases h
  rfl

theorem throughAt_mem (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) :
    throughAt p n x hx k ∈ (p.atStage (k + 1) : Set (Stage k)) := by
  by_cases hk : k ≤ n
  · rw [throughAt_le p n x hx k hk]
    exact below_mem p n x hx k hk
  · have hlt : n < k := Nat.not_le.mp hk
    rw [throughAt_gt p n x hx k hlt]
    exact cast_stage_mem p (Nat.add_sub_of_le hlt.le) (climb p n x hx (k - n)).2

theorem below_pred (n : ℕ) (x : Stage (n + 1)) (k : ℕ) (hk : k ≤ n)
    (hk' : k ≤ n + 1 := Nat.le_trans hk (Nat.le_succ n)) :
    below (n + 1) x k hk' = below n (bond n x) k hk := by
  conv_lhs => unfold below
  have hne : k ≠ n + 1 := by omega
  simp [hne]

theorem below_bond (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) (hk : k + 1 ≤ n) :
    bond k (below n x (k + 1) hk) =
      below n x k (Nat.le_trans (Nat.le_succ k) hk) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases hk_top : k + 1 = n + 1
    · have hk_eq : k = n := by omega
      cases hk_eq
      have hleft : below (n + 1) x (n + 1) hk = x := by
        simp [below]
      have hright : below (n + 1) x n (Nat.le_trans (Nat.le_succ n) hk) = bond n x := by
        rw [below_pred n x n (Nat.le_refl n) (Nat.le_trans (Nat.le_succ n) hk)]
        exact below_self n (bond n x)
      rw [hleft, hright]
    · have hle1 : k + 1 ≤ n := by omega
      have hbl : below (n + 1) x (k + 1) hk = below n (bond n x) (k + 1) hle1 :=
        below_pred n x (k + 1) hle1 hk
      have hk_low : k ≤ n := Nat.le_trans (Nat.le_succ k) hle1
      have hbr : below (n + 1) x k (Nat.le_trans (Nat.le_succ k) hk) =
          below n (bond n x) k hk_low :=
        below_pred n x k hk_low (Nat.le_trans (Nat.le_succ k) hk)
      rw [hbl, hbr]
      exact ih (bond n x) (mem_bond_of_mem_succ p n x hx) k hle1

theorem climb_idx_cast (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) {d e : ℕ} (h : d = e) :
    (congrArg (fun i => n + i) h) ▸ (climb p n x hx d).1 = (climb p n x hx e).1 := by
  subst h
  rfl

theorem climb_sub_cast (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (d : ℕ) :
    (Nat.add_sub_of_le (Nat.le_add_right n d)) ▸ (climb p n x hx ((n + d) - n)).1 =
      (climb p n x hx d).1 :=
  climb_idx_cast p n x hx (Nat.add_sub_cancel_left n d)

theorem climb_sub_cast_succ (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (d : ℕ) :
    (Nat.add_sub_of_le (Nat.le_add_right n (d + 1))) ▸
        (climb p n x hx ((n + d + 1) - n)).1 =
      (climb p n x hx (d + 1)).1 :=
  climb_sub_cast p n x hx (d + 1)

theorem throughAt_step (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (d : ℕ) :
    bond (n + d) (throughAt p n x hx (n + d + 1)) = throughAt p n x hx (n + d) := by
  rw [throughAt_gt p n x hx (n + d + 1) (Nat.lt_succ_of_le (Nat.le_add_right n d))]
  rw [climb_sub_cast_succ p n x hx d]
  rw [climb_bond]
  cases d with
  | zero =>
    exact (climb_zero p n x hx).trans (throughAt_self p n x hx).symm
  | succ d =>
    rw [throughAt_gt p n x hx (n + (d + 1)) (Nat.lt_succ_of_le (Nat.le_add_right n d))]
    rw [climb_sub_cast p n x hx (d + 1)]

theorem throughAt_compat (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) :
    bond k (throughAt p n x hx (k + 1)) = throughAt p n x hx k := by
  by_cases hk : k + 1 ≤ n
  · have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
    rw [throughAt_le _ _ _ _ _ hk, throughAt_le _ _ _ _ _ hk']
    exact below_bond p n x hx k hk
  · have hle : n ≤ k := by omega
    generalize ddef : k - n = d
    have hd : n + d = k := by
      rw [← ddef]
      exact Nat.add_sub_of_le hle
    clear ddef
    subst hd
    exact throughAt_step p n x hx d

noncomputable def threadThrough (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) : N where
  atStage := throughAt p n x hx
  compat := throughAt_compat p n x hx

theorem threadThrough_proj (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) :
    proj n (threadThrough p n x hx) = x :=
  throughAt_self p n x hx

theorem threadThrough_mem (p : N) (n : ℕ) (x : Stage n)
    (hx : x ∈ (p.atStage (n + 1) : Set (Stage n))) (k : ℕ) :
    proj k (threadThrough p n x hx) ∈ (p.atStage (k + 1) : Set (Stage k)) :=
  throughAt_mem p n x hx k

example : proj 0 (threadThrough fullThread 0 PUnit.unit full_one_mem) = PUnit.unit :=
  threadThrough_proj _ _ _ _

example : threadThrough fullThread 1 ⊥ full_bot_mem ≠ fullThread := by
  intro h
  have := congrArg (proj 1) h
  rw [threadThrough_proj, proj, fullThread] at this
  unfold fullStage at this
  exact stage_one_bot_ne_top this

/-! ## The homeomorphism -/

noncomputable def encodeStage (K : Compacts N) : ∀ n, Stage n
  | 0 => PUnit.unit
  | n + 1 => Compacts.map (proj n) (proj_continuous n) K

theorem encodeStage_compat (K : Compacts N) (n : ℕ) :
    bond n (encodeStage K (n + 1)) = encodeStage K n := by
  cases n with
  | zero => rfl
  | succ n =>
    apply Compacts.ext
    have hfun : bond n ∘ proj (n + 1) = proj n := by
      funext q
      exact q.compat n
    simp only [encodeStage, bond_succ, coe_map]
    rw [← image_comp, hfun]

noncomputable def encode (K : Compacts N) : N where
  atStage := encodeStage K
  compat := encodeStage_compat K

def decodeCarrier (p : N) : Set N :=
  {q | ∀ n, proj n q ∈ (p.atStage (n + 1) : Set (Stage n))}

theorem decodeCarrier_closed (p : N) : IsClosed (decodeCarrier p) := by
  have : decodeCarrier p = ⋂ n, proj n ⁻¹' (p.atStage (n + 1) : Set (Stage n)) := by
    ext q
    simp [decodeCarrier, proj, mem_iInter, mem_preimage]
  rw [this]
  exact isClosed_iInter fun n =>
    (p.atStage (n + 1)).isCompact.isClosed.preimage (proj_continuous n)

noncomputable def decode (p : N) : Compacts N :=
  ⟨decodeCarrier p, (decodeCarrier_closed p).isCompact⟩

theorem decode_encode (K : Compacts N) : decode (encode K) = K := by
  apply Compacts.ext
  ext q
  constructor
  · intro hq
    let t : ℕ → Set N := fun n => (K : Set N) ∩ proj n ⁻¹' {proj n q}
    have htd : ∀ n, t (n + 1) ⊆ t n := by
      intro n r hr
      refine ⟨hr.1, ?_⟩
      have hreq : proj (n + 1) r = proj (n + 1) q := by
        simpa [mem_preimage, mem_singleton_iff] using hr.2
      simp only [proj] at hreq
      simp [mem_preimage, mem_singleton_iff, proj, ← r.compat n, ← q.compat n, hreq]
    have htn : ∀ n, (t n).Nonempty := by
      intro n
      have hqimg : proj n q ∈ proj n '' (K : Set N) := by
        have hq' : proj n q ∈ ((encode K).atStage (n + 1) : Set (Stage n)) := by
          simpa [decode, decodeCarrier] using hq n
        exact hq'
      rcases hqimg with ⟨r, hrK, hrq⟩
      exact ⟨r, hrK, by simpa [mem_preimage, mem_singleton_iff] using hrq⟩
    have htcl : ∀ n, IsClosed (t n) := fun n =>
      K.isCompact.isClosed.inter (isClosed_singleton.preimage (proj_continuous n))
    obtain ⟨r, hr⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
        (htcl 0).isCompact htcl
    have hr' : ∀ n, r ∈ t n := mem_iInter.mp hr
    have hreq : r = q := by
      ext n
      simpa [proj, mem_preimage, mem_singleton_iff] using (hr' n).2
    exact hreq ▸ (hr' 0).1
  · intro hq n
    exact ⟨q, hq, rfl⟩

theorem encode_decode (p : N) : encode (decode p) = p := by
  ext k
  cases k with
  | zero =>
    exact Subsingleton.elim _ _
  | succ n =>
    apply Compacts.ext
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq' : ∀ k, proj k q ∈ (p.atStage (k + 1) : Set (Stage k)) := by
        simpa [decode, decodeCarrier] using hq
      exact hq' n
    · intro hx
      refine ⟨threadThrough p n x hx, ?_, threadThrough_proj p n x hx⟩
      intro k
      simpa [decode, decodeCarrier] using threadThrough_mem p n x hx k

noncomputable def encodeEquiv : Compacts N ≃ N where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem encode_continuous : Continuous encode :=
  continuous_induced_rng.mpr <| continuous_pi fun n =>
    match n with
    | 0 => continuous_const
    | n + 1 => by
      change Continuous fun K => Compacts.map (proj n) (proj_continuous n) K
      exact (proj_continuous n).compacts_map

/-- The limit is homeomorphic to the Vietoris space of its compact subsets. -/
noncomputable def fixedHomeo : N ≃ₜ Compacts N :=
  (Continuous.homeoOfEquivCompactToT2 (f := encodeEquiv) encode_continuous).symm

example : Nonempty (N ≃ₜ Compacts N) := ⟨fixedHomeo⟩

example (n : ℕ) : ¬ Nonempty (Stage n ≃ₜ Compacts (Stage n)) := stage_not_fixed n

end Mettapedia.SetTheory.Hyperuniverse
