import Mettapedia.Logic.HostingStyles.Weighted.FibreSum

/-!
# Weight-preserving maps compose

A first translation splits one source event into `m` middle matches, and a
second splits each middle match into `k` leaves. Along the composite the
fibre multiplicity is `m * k`. Each leg is weight-preserving, and so is the
composite: the fibre sum of the leaves equals the fibre sum of the middle
weights.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Mettapedia.GSLT.Dynamics.JoinAggregation

/-- The `m` by `k` grid of leaves, middle index outermost. -/
def grid (m k : ℕ) : List (Fin m × Fin k) :=
  (List.ofFn fun middle : Fin m => List.ofFn fun leaf : Fin k => (middle, leaf)).flatten

theorem groupSum_flatten {α Y K : Type*} [DecidableEq Y] [AddCommMonoid K]
    (key : α → Y) (weight : α → K) (rows : List (List α)) (y : Y) :
    groupSum key weight rows.flatten y =
      (rows.map fun row => groupSum key weight row y).sum := by
  induction rows with
  | nil => simp [groupSum]
  | cons row rows ih =>
    simp [groupSum_append, ih]

theorem groupSum_selected_row {K : Type*} [CommSemiring K] (m k : ℕ) (w : K)
    (kept : Fin m) :
    groupSum (fun p : Fin m × Fin k => p.1) (fun _ => w)
      (List.ofFn fun leaf : Fin k => (kept, leaf)) kept = (k : K) * w := by
  unfold groupSum
  have filtered :
      List.filter (fun p : Fin m × Fin k => p.1 = kept)
        (List.ofFn fun leaf => (kept, leaf)) = List.ofFn fun leaf => (kept, leaf) := by
    refine List.filter_eq_self.mpr ?_
    intro _ member
    obtain ⟨_, rfl⟩ := List.mem_ofFn.mp member
    exact decide_eq_true rfl
  rw [filtered]
  have mapped :
      (List.ofFn fun leaf : Fin k => (kept, leaf)).map (fun _ => w) =
        List.ofFn fun _ : Fin k => w := by
    rw [List.map_ofFn]
    rfl
  rw [mapped, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem groupSum_other_row {K : Type*} [CommSemiring K] (m k : ℕ) (w : K)
    {kept other : Fin m} (distinct : kept ≠ other) :
    groupSum (fun p : Fin m × Fin k => p.1) (fun _ => w)
      (List.ofFn fun leaf : Fin k => (other, leaf)) kept = 0 := by
  refine groupSum_eq_zero _ ?_
  intro _ member
  obtain ⟨_, rfl⟩ := List.mem_ofFn.mp member
  exact distinct.symm

/-- Each middle match owns `k` leaves, and that fibre sums to `k * w`. -/
theorem leaf_fibre_sum (m k w : ℕ) (middle : Fin m) :
    groupSum (fun p : Fin m × Fin k => p.1) (fun _ => w) (grid m k) middle = k * w := by
  unfold grid
  rw [groupSum_flatten, List.map_ofFn, List.sum_ofFn]
  have each : ∀ other : Fin m,
      groupSum (fun p : Fin m × Fin k => p.1) (fun _ => w)
        (List.ofFn fun leaf => (other, leaf)) middle = if other = middle then k * w else 0 := by
    intro other
    by_cases same : other = middle
    · rw [if_pos same]
      subst same
      exact groupSum_selected_row m k w other
    · rw [if_neg same, groupSum_other_row m k w (Ne.symm same)]
  simp [each, Finset.mem_univ]

theorem grid_length (m k : ℕ) : (grid m k).length = m * k := by
  unfold grid
  simp [List.length_flatten, List.map_ofFn, List.length_ofFn, List.sum_ofFn, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]

/-- **Positive.** The composite multiplicity is the product of the leg
multiplicities. **Negative** for the claim that the composite multiplicity is
the sum: `m * k = m + k` fails at `m = 2`, `k = 3`. -/
theorem multiplicities_multiply (m k : ℕ) (middle : Fin m) :
    (List.ofFn fun _ : Fin m => ()).length = m ∧
      (grid m k).countP (fun p => p.1 = middle) = k ∧
      (grid m k).length = m * k := by
  refine ⟨List.length_ofFn, ?_, grid_length m k⟩
  have counted := groupSum_one (K := ℕ) (fun p : Fin m × Fin k => p.1) (grid m k) middle
  rw [leaf_fibre_sum] at counted
  have : ((grid m k).countP fun p => p.1 = middle) = k * 1 := counted.symm
  simpa using this

theorem multiplicities_do_not_add : (grid 2 3).length ≠ 2 + 3 := by
  rw [grid_length]
  decide

/-- The middle weight of a preserving second leg: `k` leaves of weight `w`. -/
def middleWeight (k w : ℕ) : ℕ := k * w

/-- **The second leg preserves weight.** -/
theorem leaf_leg_weightPreserving (m k w : ℕ) :
    weightPreserving (fun _ : Fin m => middleWeight k w) (fun p : Fin m × Fin k => p.1)
      (fun _ => w) (grid m k) := by
  intro middle
  rw [leaf_fibre_sum]
  rfl

theorem sum_map_const {α : Type} (l : List α) (w : ℕ) :
    ((l.map fun _ => w).sum) = l.length * w := by
  induction l with
  | nil => simp
  | cons _ tail ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
    omega

theorem const_key_sum (m k w : ℕ) :
    groupSum (fun _ : Fin m × Fin k => ()) (fun _ => w) (grid m k) () = (m * k) * w := by
  unfold groupSum
  have filtered :
      List.filter (fun _ : Fin m × Fin k => () = ()) (grid m k) = grid m k := by
    refine List.filter_eq_self.mpr ?_
    intro _ _
    exact decide_eq_true rfl
  rw [filtered, sum_map_const, grid_length, Nat.mul_assoc]

/-- **The first leg preserves weight.** -/
theorem middle_leg_weightPreserving (m k w : ℕ) :
    weightPreserving (fun _ : Unit => (m * k) * w) (fun _ : Fin m => ())
      (fun _ => middleWeight k w) (List.ofFn fun middle : Fin m => middle) := by
  intro _
  unfold groupSum middleWeight
  have filtered :
      List.filter (fun _ : Fin m => () = ()) (List.ofFn fun middle => middle) =
        List.ofFn fun middle => middle := by
    refine List.filter_eq_self.mpr ?_
    intro _ _
    exact decide_eq_true rfl
  rw [filtered]
  have mapped :
      (List.ofFn fun middle : Fin m => middle).map (fun _ => k * w) =
        List.ofFn fun _ : Fin m => k * w := by
    rw [List.map_ofFn]
    rfl
  rw [mapped, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp [Nat.mul_assoc]

/-- **Preserving legs compose.** The leaf fibre sum equals the middle fibre
sum, and both equal the source weight. -/
theorem composite_weightPreserving (m k w : ℕ) :
    weightPreserving (fun _ : Unit => (m * k) * w) (fun _ : Fin m × Fin k => ())
      (fun _ => w) (grid m k) ∧
      groupSum (fun _ : Fin m × Fin k => ()) (fun _ => w) (grid m k) () =
        groupSum (fun _ : Fin m => ()) (fun _ => middleWeight k w)
          (List.ofFn fun middle : Fin m => middle) () := by
  refine ⟨fun _ => (const_key_sum m k w).symm, ?_⟩
  rw [const_key_sum]
  exact middle_leg_weightPreserving m k w ()

end Mettapedia.Logic.HostingStyles.Weighted
