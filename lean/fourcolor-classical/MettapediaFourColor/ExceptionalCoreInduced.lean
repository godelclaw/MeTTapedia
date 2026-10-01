import MettapediaFourColor.FacialPatchInduced
import MettapediaFourColor.MinimalExceptionalEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualFourCycleClassification

/-!
# Inducedness of the exceptional core in the actual minimal dual

The source core has diameter three and each core star is a proper interval
of the prescribed ambient star. Uniform interval and short-path laws rule
out extra ambient core edges. The proof retains the same joint occurrence;
it does not substitute an abstract graph with the same shape.
-/

namespace FourColor.ExceptionalCoreInduced

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections GoertzelV24TwoEdgeCutMinimality
open ExceptionalCore ExceptionalCoreOrientation ExceptionalCoreLocalInjectivity
open ExceptionalOverlap

set_option maxRecDepth 32768

theorem star_strict : ∀ i : Fin 8, (star i).length < coreDegree i := by decide +kernel

theorem star_consecutive_adjacent : ∀ (i : Fin 8) (p q : Fin (star i).length),
    q.val = p.val + 1 → core.Adj (spoke i p) (spoke i q) := by decide +kernel

theorem short_paths : ∀ i j : Fin 8, i ≠ j → core.Adj i j ∨
    (∃ k, core.Adj i k ∧ core.Adj k j) ∨
    ∃ a b, core.Adj i a ∧ core.Adj a b ∧ core.Adj b j := by decide +kernel

section Local

variable {W : Type*} [Finite W] {H : SimpleGraph W}
  [H.LocallyFinite] {rotation : Data H}

theorem joint_reflects_common_neighbor (r : JointReading rotation)
    (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b)
    (k i j : Fin 8) (ki : core.Adj k i) (kj : core.Adj k j)
    (ij : H.Adj (r.core.map i) (r.core.map j)) : core.Adj i j := by
  classical
  obtain ⟨hn, _, hs⟩ := star_specs k
  obtain ⟨p, rfl⟩ := (hs i).mp ki
  obtain ⟨q, rfl⟩ := (hs j).mp kj
  have successor (p q : Fin (star k).length)
      (h : Corner rotation (r.core.map k)
        (r.core.map (spoke k p)) (r.core.map (spoke k q))) : q.val = p.val + 1 := by
    apply FacialPatchInduced.corner_chain_successor rotation cyclic (r.core.map k) hn
      (fun s => r.core.map (spoke k s))
    · intro s
      exact r.core.map.map_adj ((hs _).mpr ⟨s, rfl⟩)
    · intro s h
      exact joint_preserves_turns r tri k _ _ (star_steps k _ _ rfl)
    · rw [r.core.degree]
      exact star_strict k
    · exact h
  rcases facial _ _ _ (r.core.map.map_adj ki) ij (r.core.map.map_adj kj).symm with h | h
  · exact star_consecutive_adjacent k p q (successor p q h)
  · exact (star_consecutive_adjacent k q p (successor q p h)).symm

end Local

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance : (MinimalExceptionalEmbedding.graph original minimal).LocallyFinite :=
  fun _ => Fintype.ofFinite _

theorem four_cycle_chord {a b c d : OrbitFace original.toRotationSystem}
    (ab : (MinimalExceptionalEmbedding.graph original minimal).Adj a b)
    (bc : (MinimalExceptionalEmbedding.graph original minimal).Adj b c)
    (cd : (MinimalExceptionalEmbedding.graph original minimal).Adj c d)
    (da : (MinimalExceptionalEmbedding.graph original minimal).Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) :
    (MinimalExceptionalEmbedding.graph original minimal).Adj a c ∨
      (MinimalExceptionalEmbedding.graph original minimal).Adj b d := by
  classical
  by_cases h : (MinimalExceptionalEmbedding.graph original minimal).Adj a c
  · exact Or.inl h
  right
  apply (ActualDualRotation.dual_adj_iff original.toRotationSystem minimal.facesTwoSided).mpr
  apply GoertzelV24MinimalDualFourCycleClassification.middle_adj_other_of_two_common_neighbors
    original minimal
    ((ActualDualRotation.dual_adj_iff _ _).mp ab)
    ((ActualDualRotation.dual_adj_iff _ _).mp bc)
    ((ActualDualRotation.dual_adj_iff _ _).mp da.symm)
    ((ActualDualRotation.dual_adj_iff _ _).mp cd.symm)
  · exact fun hadj => h ((ActualDualRotation.dual_adj_iff _ _).mpr hadj)
  · exact fun eq => ac (congrArg Subtype.val eq)
  · exact fun eq => bd (congrArg Subtype.val eq.symm)

/-- No additional ambient edge joins two core vertices. -/
theorem joint_induced (r : JointReading (MinimalExceptionalEmbedding.rotation original minimal)) :
    ∀ i j, (MinimalExceptionalEmbedding.graph original minimal).Adj (r.core.map i) (r.core.map j)
      ↔ core.Adj i j := by
  classical
  have reflect := FacialPatchInduced.reflects_of_short_paths r.core.map
    (MinimalExceptionalEmbedding.joint_injective original minimal r)
    (joint_reflects_common_neighbor r (MinimalExceptionalEmbedding.triangular original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal)
      (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal))
    short_paths (fun _ _ _ _ => four_cycle_chord original minimal)
  intro i j
  exact ⟨reflect i j, r.core.map.map_adj⟩

/-- The actual two-occurrence construction now preserves and reflects all
core adjacency. This still makes no claim about the outer ring or repair. -/
theorem source_core_induced
    (x y : ExceptionalPattern.Occurrence (MinimalExceptionalEmbedding.rotation original minimal))
    (aligned : y.vertex 0 = x.vertex 14) :
    ∀ i j, (MinimalExceptionalEmbedding.graph original minimal).Adj
      (coreVertex x i) (coreVertex x j) ↔ core.Adj i j := by
  classical
  exact joint_induced original minimal (jointReading x
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) y aligned)

end
end FourColor.ExceptionalCoreInduced
