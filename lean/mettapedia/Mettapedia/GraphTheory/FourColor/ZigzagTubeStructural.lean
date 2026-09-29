import Mettapedia.GraphTheory.FourColor.ZigzagRingGeometry
import Mettapedia.GraphTheory.FourColor.OpenTangleInternalReplacement

/-!
# Connectedness and bridge-freedom of literal zigzag tubes

The internal graph of one ring is its cycle on alternating input and
output vertices. The cut count agrees with that cycle's edge presentation.
Serial sewing then preserves absence of nontrivial cuts of size at most one.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph
open BoundarySmallCutProfile SmallCutConnectedBridgeless SmallCutReplacementCore
open SerialTangleSmallCutTransfer OpenTangleCutDartSum OpenTangleInternalReplacement

noncomputable section
attribute [local instance] Classical.propDecidable

variable (k : Nat) [NeZero k]

/-- Follow the alternating cycle `d i, e i, d (i+1)`. -/
def vertexNext : Equiv.Perm (Vtx k) where
  toFun
    | .inl i => .inr i
    | .inr i => .inl (i + 1)
  invFun
    | .inl i => .inr (i - 1)
    | .inr i => .inl i
  left_inv := by rintro (i | i) <;> simp
  right_inv := by rintro (i | i) <;> simp

/-- The actual edge-orbit multigraph counts exactly the cuts of the
alternating cycle, without collapsing parallel edges at circumference one. -/
theorem ring_cutSize (s : Vtx k → Bool) :
    cutSize (sideMultigraph (openRing k)) s = cutSize (permutationGraph (vertexNext k)) s := by
  have h := twice_cutSize (openRing k) s
  conv at h =>
    rhs
    simp only [Dart, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
      openRing, asOpen, ring, interiorAlpha, Equiv.coe_fn_mk, flip, interiorVert,
      Bool.not_true, Bool.not_false]
  simp only [Finset.sum_add_distrib] at h
  have ha : (∑ i : Fin k, bit (s (.inr i)) (s (.inl i))) =
      ∑ i : Fin k, bit (s (.inl i)) (s (.inr i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact bit_symm _ _
  have hb : (∑ i : Fin k, bit (s (.inl (i + 1))) (s (.inr i))) =
      ∑ i : Fin k, bit (s (.inr i)) (s (.inl (i + 1))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact bit_symm _ _
  rw [ha, hb] at h
  have he : cutSize (permutationGraph (vertexNext k)) s =
      (∑ i : Fin k, bit (s (.inl i)) (s (.inr i))) +
        ∑ i : Fin k, bit (s (.inr i)) (s (.inl (i + 1))) := by
    simp [cutSize, permutationGraph, vertexNext, bit, Fintype.sum_sum_type]
    congr!
  omega

private theorem ring_constant (s : Vtx k → Bool)
    (hs : cutSize (sideMultigraph (openRing k)) s ≤ 1) :
    ∀ v, s v = s (.inl 0) := by
  rw [ring_cutSize] at hs
  have hedge := permutation_small_cut (vertexNext k) s hs
  have hd (i : Fin k) : s (.inl i) = s (.inl (i + 1)) :=
    (hedge (.inl i)).trans (hedge (.inr i))
  have hroot (i : Fin k) : s (.inl i) = s (.inl 0) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have he : i.castSucc + 1 = i.succ := by apply Fin.ext; simp [Fin.add_def]
      exact (he ▸ hd i.castSucc).symm.trans ih
  rintro (i | i)
  · exact hroot i
  · exact (hedge (.inl i)).symm.trans (hroot i)

theorem ring_no_small_cut : ¬ HasSmallCut (sideMultigraph (openRing k)) := by
  rintro ⟨s, ⟨u, hu⟩, ⟨v, hv⟩, hs⟩
  have h := (ring_constant k s hs u).trans (ring_constant k s hs v).symm
  simp only [hu, hv, Bool.true_eq_false] at h

/-- The actual interior graph of every positive-width ring is connected
and bridgeless. The width-one case retains its parallel edges. -/
theorem ring_connected_bridgeless :
    (sideMultigraph (openRing k)).Connected ∧ (sideMultigraph (openRing k)).Bridgeless :=
  (no_small_cut_iff _).mp (ring_no_small_cut k)

attribute [local instance] tubeVertexFintype tubeInteriorFintype appendRingInteriorFintype

instance tube_vertices_nonempty (n : Nat) : Nonempty (tube k n).V :=
  ⟨(tube k n).data.leftVert 0⟩

omit [NeZero k] in
private theorem hidden_no_small_cut_congr (T U : HiddenTangle (Fin k) (Fin k))
    [Fintype T.I] [DecidableEq T.I] [Fintype U.I] [DecidableEq U.I] (h : T = U) :
    (¬ HasSmallCut (sideMultigraph (asOpen T.data))) ↔
      (¬ HasSmallCut (sideMultigraph (asOpen U.data))) := by
  subst U
  congr!

/-- There are at least two physical edges at each consumed seam. -/
theorem tube_no_small_cut (hk : 2 ≤ k) (n : Nat) :
    ¬ HasSmallCut (sideMultigraph (asOpen (tube k n).data)) := by
  induction n with
  | zero =>
    exact (hidden_no_small_cut_congr k (tube k 0) ⟨Vtx k, Dart k, ring k⟩ rfl).mpr
      (ring_no_small_cut k)
  | succ n ih =>
    apply (hidden_no_small_cut_congr k _ _ (tube_succ k n)).mpr
    convert serial_no_small_cut (tube k n).data (ring k) ih (ring_no_small_cut k)
      (by simpa using hk) using 1
    congr!

/-- Connectedness and bridge-freedom refer to the same literal tubes as
the colouring reconstruction and oriented face-return theorems. -/
theorem tube_connected_bridgeless (hk : 2 ≤ k) (n : Nat) :
    (sideMultigraph (asOpen (tube k n).data)).Connected ∧
      (sideMultigraph (asOpen (tube k n).data)).Bridgeless :=
  (no_small_cut_iff _).mp (tube_no_small_cut k hk n)

open GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge

variable {V I B : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

/-- In any fixed exterior, exchanging two nonempty tubes preserves the
conjunction of connectedness and bridge-freedom. No hypothesis is imposed
on the exterior's own connectedness, port placement, or embedding. -/
theorem tube_replacement_structural (hk : 2 ≤ k) (r s : Nat)
    (outside : OpenTangleData V I B) (m : B ≃ Fin k ⊕ Fin k) :
    ((rotationPrimalGraph
        (outside.composeRotationSystem (asOpen (tube k r).data) m)).Connected ∧
      EdgeBridgeFree (outside.composeRotationSystem (asOpen (tube k r).data) m)) ↔
    ((rotationPrimalGraph
        (outside.composeRotationSystem (asOpen (tube k s).data) m)).Connected ∧
      EdgeBridgeFree (outside.composeRotationSystem (asOpen (tube k s).data) m)) :=
  replacement_structural outside (asOpen (tube k r).data) (asOpen (tube k s).data) m m
    (tube_connected_bridgeless k hk r) (tube_connected_bridgeless k hk s)

end
end Mettapedia.GraphTheory.FourColor.ZigzagRing
