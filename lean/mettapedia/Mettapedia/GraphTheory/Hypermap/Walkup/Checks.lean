import Mettapedia.GraphTheory.Hypermap.Walkup.Genus
import Mettapedia.GraphTheory.Hypermap.SmallExamples

/-!
# The Walkup genus theorems, checked against a map where the genus drops

`genus_walkupE_le` is an inequality and `genus_walkupE_eq` carries a hypothesis.
Both claims are only informative if the inequality can be strict and the
hypothesis cannot be dropped.  This module shows both on the genus-one map
`torusTriple` at the dart `0`, which is non-degenerate and cross-edge:

* the edge count of the transformed map is computed **directly** — Walkup's
  formula there is the identity on two darts, so there are two edge orbits —
  and agrees with the `+1` predicted by the transposition twist;
* the transformed map is planar, so the genus falls from one to zero.

The direct count and the predicted count are obtained independently: the first
from `skipEdgeFun` evaluated by the kernel, the second from
`orbitCount_walkupE_edge_of_crossEdge`.  Their agreement is a check on the
twist theorem, not a restatement of it.
-/

namespace Mettapedia.GraphTheory

open Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace Hypermap

/-- `0` is not fixed by any permutation of the genus-one map. -/
theorem not_degenerate_torusTriple_zero : ¬ Degenerate torusTriple 0 := by
  unfold Degenerate
  decide

/-- `0` and `node 0` share the (single) edge cycle. -/
theorem crossEdge_torusTriple_zero : CrossEdge torusTriple 0 :=
  sameCycle_cyc3 _ _

theorem card_torusTriple_punctured : Fintype.card {x : Fin 3 // x ≠ 0} = 2 := by
  have h := card_subtype_ne_succ (0 : Fin 3)
  simp only [Fintype.card_fin] at h
  omega

/-- **Directly**: the transformed edge permutation is the identity. -/
theorem walkupE_torusTriple_edge : (walkupE torusTriple 0).edge = 1 := by
  refine Equiv.ext fun u => Subtype.ext ?_
  rw [walkupE_edge_apply]
  show skipEdgeFun torusTriple 0 (u : Fin 3) = (u : Fin 3)
  have h : ∀ x : Fin 3, x ≠ 0 → skipEdgeFun torusTriple 0 x = x := by decide
  exact h _ u.2

/-- **Directly**: two edge orbits after the deletion, against one before. -/
theorem orbitCount_walkupE_torusTriple_edge :
    orbitCount (walkupE torusTriple 0).edge = 2 := by
  rw [walkupE_torusTriple_edge, PermSwapDecomposition.orbitCount_one,
    card_torusTriple_punctured]

/-- **Cross-check.**  The twist theorem predicts `orbitCount edge + 1 = 2`, and
that is what the direct computation gives. -/
example : orbitCount (walkupE torusTriple 0).edge = orbitCount torusTriple.edge + 1 := by
  rw [orbitCount_walkupE_torusTriple_edge]
  show 2 = orbitCount cyc3 + 1
  rw [orbitCount_cyc3]

example : orbitCount (walkupE torusTriple 0).edge = orbitCount torusTriple.edge + 1 :=
  orbitCount_walkupE_edge_of_crossEdge torusTriple 0
    not_degenerate_torusTriple_zero crossEdge_torusTriple_zero

/-- The transformed map is connected: its node permutation alone joins the two
surviving darts. -/
theorem compCount_walkupE_torusTriple : compCount (walkupE torusTriple 0) = 1 := by
  have hmem : (walkupE torusTriple 0).node ∈
      [(walkupE torusTriple 0).edge, (walkupE torusTriple 0).node,
        (walkupE torusTriple 0).face] := List.mem_cons_of_mem _ List.mem_cons_self
  have hreach : ∀ u v : {x : Fin 3 // x ≠ 0}, WordReachable
      [(walkupE torusTriple 0).edge, (walkupE torusTriple 0).node,
        (walkupE torusTriple 0).face] u v := by
    intro u v
    have hc : (skipPerm cyc3 0).SameCycle u v :=
      (sameCycle_skipPerm_iff cyc3 0 u v).2 (sameCycle_cyc3 _ _)
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq hc
    have h := wordReachable_pow hmem u n
    rwa [show (walkupE torusTriple 0).node = skipPerm cyc3 0 from rfl, hn] at h
  have h := wordOrbitCount_eq_card_of_completeInvariant
    (L := [(walkupE torusTriple 0).edge, (walkupE torusTriple 0).node,
      (walkupE torusTriple 0).face])
    (fun _ : {x : Fin 3 // x ≠ 0} => ()) (fun u v => ⟨fun _ => rfl, fun _ => hreach u v⟩)
    (fun _ => ⟨⟨1, by decide⟩, rfl⟩)
  show wordOrbitCount _ = 1
  rw [h]
  simp

/-- **The genus really drops**: the Walkup transform of the genus-one map at a
non-degenerate cross-edge dart is planar. -/
theorem genus_walkupE_torusTriple : genus (walkupE torusTriple 0) = 0 := by
  have hg := even_genus (walkupE torusTriple 0)
  rw [eulerRhs_eq_card_add_two_mul_compCount, compCount_walkupE_torusTriple,
    card_torusTriple_punctured] at hg
  have hlhs := eulerLhs_walkupE_of_crossEdge torusTriple 0
    not_degenerate_torusTriple_zero crossEdge_torusTriple_zero
  rw [eulerLhs_torusTriple] at hlhs
  omega

theorem planar_walkupE_torusTriple : Planar (walkupE torusTriple 0) :=
  (planar_iff_genus_eq_zero _).2 genus_walkupE_torusTriple

/-- **`genus_walkupE_le` can be strict**, so it is not secretly an equality. -/
theorem genus_walkupE_torusTriple_lt : genus (walkupE torusTriple 0) < genus torusTriple := by
  rw [genus_walkupE_torusTriple, genus_torusTriple]
  norm_num

/-- **The hypothesis of `genus_walkupE_eq` is load-bearing**: dropping it gives a
false statement, refuted at the genus-one map. -/
theorem not_forall_genus_walkupE_eq :
    ¬ ∀ (H : Hypermap (Fin 3)) (z : Fin 3), genus (walkupE H z) = genus H := by
  intro h
  have := h torusTriple 0
  rw [genus_walkupE_torusTriple, genus_torusTriple] at this
  exact absurd this (by norm_num)

end Hypermap

end Mettapedia.GraphTheory
