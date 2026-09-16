import Mettapedia.GraphTheory.FourColor.HypermapPatch

/-!
# The genus does not see which permutation is called which

The three permutations of a hypermap enter the composite law symmetrically, and
inverting all three is again a hypermap.  This module records the resulting
derived maps and proves that each has the same genus — hence the same
planarity — as the original:

* `Hypermap.permN` and `Hypermap.permF` cycle the three roles;
* `Hypermap.dual` inverts all three and exchanges nodes with faces.

`Hypermap.planar_dual` is the useful one: a map is planar exactly when its dual
is, which is what licenses arguing about a planar map through its faces rather
than its vertices.

All three proofs are the same two observations.  The orbit total `E + N + F` is
a sum, so it does not care about the order of its summands, and a permutation
has the same orbits as its inverse.  The component count does not care either:
it is the orbit count of a *generated* group, so reordering the generators or
replacing them all by their inverses leaves reachability untouched — on a finite
carrier an inverse is a positive power, so no new steps are added.
-/

namespace Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open GoertzelV24MapEulerBound

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Two elementary permutation facts -/

omit [Fintype D] [DecidableEq D] in
theorem apply_inv_apply (σ : Perm D) (x : D) : σ (σ⁻¹ x) = x := by
  rw [← Perm.mul_apply, mul_inv_cancel]
  rfl

omit [DecidableEq D] in
/-- On a finite carrier an inverse step is already a forward walk. -/
theorem wordReachable_inv_step {L : List (Perm D)} {g : Perm D} (hg : g ∈ L) (u : D) :
    WordReachable L u (g⁻¹ u) := by
  have h := wordReachable_of_step hg (g⁻¹ u)
  rwa [apply_inv_apply] at h

omit [DecidableEq D] in
/-- **Inverting every generator preserves the component count.** -/
theorem wordOrbitCount_inv_triple (a b c : Perm D) :
    wordOrbitCount [a⁻¹, b⁻¹, c⁻¹] = wordOrbitCount [a, b, c] := by
  have key : ∀ x y z : Perm D, ∀ u v : D,
      WordReachable [x⁻¹, y⁻¹, z⁻¹] u v → WordReachable [x, y, z] u v := by
    intro x y z u v huv
    refine wordReachable_absorb ?_ huv
    intro g hg w
    rcases List.mem_cons.mp hg with rfl | hg1
    · exact wordReachable_inv_step List.mem_cons_self w
    rcases List.mem_cons.mp hg1 with rfl | hg2
    · exact wordReachable_inv_step (List.mem_cons_of_mem _ List.mem_cons_self) w
    rcases List.mem_cons.mp hg2 with rfl | hg3
    · exact wordReachable_inv_step
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) w
    · simp at hg3
  refine le_antisymm ?_ ?_
  · refine wordOrbitCount_le_of_le (fun u v huv => ?_)
    have h := key a⁻¹ b⁻¹ c⁻¹ u v
    simpa only [inv_inv] using h huv
  · exact wordOrbitCount_le_of_le (fun u v huv => key a b c u v huv)

/-! ## Genus depends only on the two Euler quantities -/

theorem genus_congr {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂] {H₁ : Hypermap D₁} {H₂ : Hypermap D₂}
    (hl : eulerLhs H₁ = eulerLhs H₂) (hr : eulerRhs H₁ = eulerRhs H₂) :
    genus H₁ = genus H₂ := by
  unfold genus
  rw [hl, hr]

/-! ## The composite law, read from the other two starting points -/

theorem face_edge_node (H : Hypermap D) (d : D) : H.face (H.edge (H.node d)) = d :=
  H.node.injective (H.cancel3 (H.node d))

theorem edge_node_face (H : Hypermap D) (d : D) : H.edge (H.node (H.face d)) = d :=
  H.face.injective (face_edge_node H (H.face d))

/-! ## Cycling the roles -/

/-- Relabel `edge, node, face` as `node, face, edge`. -/
def permN (H : Hypermap D) : Hypermap D where
  edge := H.node
  node := H.face
  face := H.edge
  cancel3 := face_edge_node H

/-- Relabel `edge, node, face` as `face, edge, node`. -/
def permF (H : Hypermap D) : Hypermap D where
  edge := H.face
  node := H.edge
  face := H.node
  cancel3 := edge_node_face H

theorem eulerLhs_permN (H : Hypermap D) : eulerLhs (permN H) = eulerLhs H := by
  show orbitCount H.node + orbitCount H.face + orbitCount H.edge =
    orbitCount H.edge + orbitCount H.node + orbitCount H.face
  omega

theorem eulerLhs_permF (H : Hypermap D) : eulerLhs (permF H) = eulerLhs H := by
  show orbitCount H.face + orbitCount H.edge + orbitCount H.node =
    orbitCount H.edge + orbitCount H.node + orbitCount H.face
  omega

theorem compCount_permN (H : Hypermap D) : compCount (permN H) = compCount H := by
  show wordOrbitCount [H.node, H.face, H.edge] = wordOrbitCount [H.edge, H.node, H.face]
  refine wordOrbitCount_eq_of_mem_iff (fun g => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem compCount_permF (H : Hypermap D) : compCount (permF H) = compCount H := by
  show wordOrbitCount [H.face, H.edge, H.node] = wordOrbitCount [H.edge, H.node, H.face]
  refine wordOrbitCount_eq_of_mem_iff (fun g => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem eulerRhs_permN (H : Hypermap D) : eulerRhs (permN H) = eulerRhs H := by
  rw [eulerRhs_eq_card_add_two_mul_compCount, eulerRhs_eq_card_add_two_mul_compCount,
    compCount_permN]

theorem eulerRhs_permF (H : Hypermap D) : eulerRhs (permF H) = eulerRhs H := by
  rw [eulerRhs_eq_card_add_two_mul_compCount, eulerRhs_eq_card_add_two_mul_compCount,
    compCount_permF]

theorem genus_permN (H : Hypermap D) : genus (permN H) = genus H :=
  genus_congr (eulerLhs_permN H) (eulerRhs_permN H)

theorem genus_permF (H : Hypermap D) : genus (permF H) = genus H :=
  genus_congr (eulerLhs_permF H) (eulerRhs_permF H)

theorem planar_permN (H : Hypermap D) : Planar (permN H) ↔ Planar H := by
  rw [planar_iff_genus_eq_zero, planar_iff_genus_eq_zero, genus_permN]

theorem planar_permF (H : Hypermap D) : Planar (permF H) ↔ Planar H := by
  rw [planar_iff_genus_eq_zero, planar_iff_genus_eq_zero, genus_permF]

/-! ## The dual -/

/-- The dual: invert all three permutations and exchange nodes with faces. -/
def dual (H : Hypermap D) : Hypermap D where
  edge := H.edge⁻¹
  node := H.face⁻¹
  face := H.node⁻¹
  cancel3 := by
    intro d
    have h := edge_node_face H (H.face⁻¹ (H.node⁻¹ (H.edge⁻¹ d)))
    simp only [apply_inv_apply] at h
    exact h.symm

theorem eulerLhs_dual (H : Hypermap D) : eulerLhs (dual H) = eulerLhs H := by
  show orbitCount H.edge⁻¹ + orbitCount H.face⁻¹ + orbitCount H.node⁻¹ =
    orbitCount H.edge + orbitCount H.node + orbitCount H.face
  rw [orbitCount_inv, orbitCount_inv, orbitCount_inv]
  omega

theorem compCount_dual (H : Hypermap D) : compCount (dual H) = compCount H := by
  show wordOrbitCount [H.edge⁻¹, H.face⁻¹, H.node⁻¹] = wordOrbitCount [H.edge, H.node, H.face]
  have hswap : wordOrbitCount [H.edge⁻¹, H.face⁻¹, H.node⁻¹] =
      wordOrbitCount [H.edge⁻¹, H.node⁻¹, H.face⁻¹] := by
    refine wordOrbitCount_eq_of_mem_iff (fun g => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  rw [hswap, wordOrbitCount_inv_triple]

theorem eulerRhs_dual (H : Hypermap D) : eulerRhs (dual H) = eulerRhs H := by
  rw [eulerRhs_eq_card_add_two_mul_compCount, eulerRhs_eq_card_add_two_mul_compCount,
    compCount_dual]

/-- **The dual has the same genus.** -/
theorem genus_dual (H : Hypermap D) : genus (dual H) = genus H :=
  genus_congr (eulerLhs_dual H) (eulerRhs_dual H)

/-- **A map is planar exactly when its dual is.** -/
theorem planar_dual (H : Hypermap D) : Planar (dual H) ↔ Planar H := by
  rw [planar_iff_genus_eq_zero, planar_iff_genus_eq_zero, genus_dual]

end Hypermap

end Mettapedia.GraphTheory.FourColor
