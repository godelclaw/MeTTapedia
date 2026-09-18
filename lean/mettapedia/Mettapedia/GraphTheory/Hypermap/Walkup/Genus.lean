import Mettapedia.GraphTheory.Hypermap.Walkup.Components

/-!
# Deleting a dart never raises the genus

Putting the two counting identities together.  Write `H'` for `walkupE H z`.
The dart count drops by one; the node and face counts drop by one for each
permutation fixing `z`; the edge count and the component count move as
`Hypermap.Walkup.OrbitCounts` and `Hypermap.Walkup.Components` describe.  Since
`Hypermap.even_genus` says the genus formula never truncates, the whole thing
is linear arithmetic once the case values are in hand:

| `z` | edge count | pieces left | genus |
|---|---|---|---|
| barb | `−1` | `0` | unchanged |
| degenerate, not barb | `0` or `−1` | `1` | unchanged |
| non-degenerate, not cross-edge | `−1` | `1` | unchanged |
| non-degenerate, cross-edge | `+1` | `≤ 2` | can **drop** |

The last row is the only one where the genus moves, and it moves down: a cross
edge is a handle, and cutting it is what the induction is for.  So
`genus_walkupE_le` holds always and `genus_walkupE_eq` holds under the
disjunction `Degenerate ∨ ¬ CrossEdge` — which is exactly the source's
hypothesis on `genus_WalkupE_eq`.

That the drop is real, and not an artefact of a too-weak bound, is witnessed in
`Hypermap.SmallExamples`: the genus-one map on three darts has a non-degenerate
cross-edge dart, and Walkup's formula there produces the identity edge
permutation on two darts — a planar map.

`walkupN` and `walkupF` inherit everything through the role-cycling symmetries,
which `Hypermap.Symmetry` already proves genus-invariant.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A degenerate dart that is not a barb is fixed by exactly one of the three
permutations. -/
theorem sum_fix_eq_one_of_degenerate_not_barb (H : Hypermap D) (z : D)
    (hd : Degenerate H z) (hb : ¬ Barb H z) :
    (if H.edge z = z then 1 else 0) + (if H.node z = z then 1 else 0)
      + (if H.face z = z then 1 else 0) = 1 := by
  by_cases he : H.edge z = z
  · by_cases hn : H.node z = z
    · exact absurd ⟨he, hn, face_fix_of_edge_node he hn⟩ hb
    · by_cases hf : H.face z = z
      · exact absurd ⟨he, node_fix_of_edge_face he hf, hf⟩ hb
      · simp [he, hn, hf]
  · by_cases hn : H.node z = z
    · by_cases hf : H.face z = z
      · exact absurd ⟨edge_fix_of_node_face hn hf, hn, hf⟩ hb
      · simp [he, hn, hf]
    · by_cases hf : H.face z = z
      · simp [he, hn, hf]
      · exact absurd hd (by rintro (h | h | h); exacts [he h, hn h, hf h])

/-! ## The genus under a single deletion -/

/-- **A degenerate deletion preserves the genus.** -/
theorem genus_walkupE_eq_of_degenerate (H : Hypermap D) (z : D) (hd : Degenerate H z) :
    genus (walkupE H z) = genus H := by
  have hg := even_genus H
  have hg' := even_genus (walkupE H z)
  rw [eulerRhs_eq_card_add_two_mul_compCount] at hg
  rw [eulerRhs_eq_card_add_two_mul_compCount] at hg'
  have hcard := card_walkupE_succ H z
  have hcomp := compCount_add_zCompCount H z
  have hlhs := eulerLhs_walkupE_of_degenerate H z hd
  by_cases hb : Barb H z
  · have hq := zCompCount_eq_zero_of_barb H z hb
    rw [if_pos hb.1, if_pos hb.2.1, if_pos hb.2.2] at hlhs
    omega
  · have hq1 := zCompCount_le_one_of_degenerate H z hd
    have hq2 := one_le_zCompCount_of_not_barb H z hb
    rw [sum_fix_eq_one_of_degenerate_not_barb H z hd hb] at hlhs
    omega

/-- **A non-cross-edge deletion preserves the genus.** -/
theorem genus_walkupE_eq_of_not_crossEdge (H : Hypermap D) (z : D)
    (hd : ¬ Degenerate H z) (hc : ¬ CrossEdge H z) :
    genus (walkupE H z) = genus H := by
  have hg := even_genus H
  have hg' := even_genus (walkupE H z)
  rw [eulerRhs_eq_card_add_two_mul_compCount] at hg
  rw [eulerRhs_eq_card_add_two_mul_compCount] at hg'
  have hcard := card_walkupE_succ H z
  have hcomp := compCount_add_zCompCount H z
  have hlhs := eulerLhs_walkupE_of_not_crossEdge H z hd hc
  have hq1 := zCompCount_le_one_of_not_crossEdge H z hd hc
  have hb : ¬ Barb H z := fun h => hd (Or.inl h.1)
  have hq2 := one_le_zCompCount_of_not_barb H z hb
  omega

/-- **The Walkup transform preserves the genus** whenever the deleted dart is
degenerate or does not cross its own edge cycle.  This is the source's
`genus_WalkupE_eq`. -/
theorem genus_walkupE_eq (H : Hypermap D) (z : D)
    (h : Degenerate H z ∨ ¬ CrossEdge H z) : genus (walkupE H z) = genus H := by
  rcases h with hd | hc
  · exact genus_walkupE_eq_of_degenerate H z hd
  · by_cases hd : Degenerate H z
    · exact genus_walkupE_eq_of_degenerate H z hd
    · exact genus_walkupE_eq_of_not_crossEdge H z hd hc

/-- **The Walkup transform never raises the genus.**  This is the source's
`le_genus_WalkupE`. -/
theorem genus_walkupE_le (H : Hypermap D) (z : D) : genus (walkupE H z) ≤ genus H := by
  by_cases hd : Degenerate H z
  · exact le_of_eq (genus_walkupE_eq_of_degenerate H z hd)
  · by_cases hc : CrossEdge H z
    · -- the one case where the genus can strictly drop
      have hg := even_genus H
      have hg' := even_genus (walkupE H z)
      rw [eulerRhs_eq_card_add_two_mul_compCount] at hg
      rw [eulerRhs_eq_card_add_two_mul_compCount] at hg'
      have hcard := card_walkupE_succ H z
      have hcomp := compCount_add_zCompCount H z
      have hlhs := eulerLhs_walkupE_of_crossEdge H z hd hc
      have hq := zCompCount_le_two H z
      omega
    · exact le_of_eq (genus_walkupE_eq_of_not_crossEdge H z hd hc)

/-- **Planarity survives the Walkup transform.**  The source's
`planar_WalkupE`. -/
theorem planar_walkupE (H : Hypermap D) (z : D) (hp : Planar H) : Planar (walkupE H z) := by
  rw [planar_iff_genus_eq_zero] at hp ⊢
  have := genus_walkupE_le H z
  omega

/-! ## The two other transforms

`walkupN` and `walkupF` are `walkupE` conjugated by the role-cycling
symmetries, which preserve the genus. -/

theorem genus_walkupN_le (H : Hypermap D) (z : D) : genus (walkupN H z) ≤ genus H := by
  have h := genus_walkupE_le (permN H) z
  rw [genus_permN] at h
  calc genus (walkupN H z) = genus (walkupE (permN H) z) := genus_permF _
    _ ≤ genus H := h

theorem genus_walkupF_le (H : Hypermap D) (z : D) : genus (walkupF H z) ≤ genus H := by
  have h := genus_walkupE_le (permF H) z
  rw [genus_permF] at h
  calc genus (walkupF H z) = genus (walkupE (permF H) z) := genus_permN _
    _ ≤ genus H := h

/-- The source's `planar_WalkupN`. -/
theorem planar_walkupN (H : Hypermap D) (z : D) (hp : Planar H) : Planar (walkupN H z) := by
  rw [planar_iff_genus_eq_zero] at hp ⊢
  have := genus_walkupN_le H z
  omega

/-- The source's `planar_WalkupF`. -/
theorem planar_walkupF (H : Hypermap D) (z : D) (hp : Planar H) : Planar (walkupF H z) := by
  rw [planar_iff_genus_eq_zero] at hp ⊢
  have := genus_walkupF_le H z
  omega

/-! ## Walkup induction

The carrier shrinks by exactly one, so a property of hypermaps can be proved by
strong induction on the dart count, assuming it at every single-dart deletion.
Both directions of the combinatorial Jordan curve theorem run this way; they need
the hypothesis at *every* deletion, not just one, because which dart and which of
the three transforms to use is only decided inside the proof. -/

universe u

/-- **Walkup induction.**  A property of hypermaps that holds whenever it holds on
every punctured carrier holds everywhere.  Well-foundedness is
`card_walkupE_succ`. -/
theorem walkup_induction
    {P : ∀ (E : Type u) [Fintype E] [DecidableEq E], Hypermap E → Prop}
    (hstep : ∀ (E : Type u) [Fintype E] [DecidableEq E] (K : Hypermap E),
      (∀ (y : E) (K' : Hypermap {x : E // x ≠ y}), P {x : E // x ≠ y} K') → P E K)
    {D : Type u} [Fintype D] [DecidableEq D] (H : Hypermap D) : P D H := by
  suffices hmain : ∀ n : ℕ, ∀ (E : Type u) [Fintype E] [DecidableEq E] (K : Hypermap E),
      Fintype.card E ≤ n → P E K by
    exact hmain (Fintype.card D) D H le_rfl
  intro n
  induction n with
  | zero =>
      intro E _ _ K hcard
      refine hstep E K (fun y _ => ?_)
      have hc := card_subtype_ne_succ y
      omega
  | succ n ih =>
      intro E _ _ K hcard
      refine hstep E K (fun y K' => ih {x : E // x ≠ y} K' ?_)
      have hc := card_subtype_ne_succ y
      omega

end Hypermap

end Mettapedia.GraphTheory
