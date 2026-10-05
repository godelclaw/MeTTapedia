import MettapediaFourColor.TriangleStripAnchors
import MettapediaFourColor.ActualRuleFanSupply

/-! # A low boundary port exposes an existing diamond

The D0099 source has three degree-five core vertices around boundary port
eight. The two source turns at core vertex twelve retain the flanks of the
same actual edge. Degree five or six at the boundary port therefore supplies
the pentagonal or mixed diamond. Their existing strict reductions exclude
both cases in a graph-backed vertex-minimal counterexample.

This supplies an alternative to recolouring the chosen strip. It does not
assert that every surviving strip has a successful recolouring.
-/

namespace FourColor.StripDiamondAlternative

open SimpleGraph TriangleStripAnchors RulePairDiamond
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The complete source degrees and the two source turns used by the
alternative reduction. The other exterior observations are unrestricted. -/
structure Reading (rotation : Data G) where
  map : input0099.graph →g G
  degree : ∀ i : Fin 19, 11 ≤ i.val →
    G.degree (map i) = (input0099.internalStar i).length
  left : Corner rotation (map 12) (map 11) (map 8)
  right : Corner rotation (map 12) (map 8) (map 15)

/-- Both turns, including the wrap at the end of the row, are in the pinned
source star; the three core degrees are also decoded from that source. -/
theorem source_observations :
    List.IsInfix [11,8,15]
      (input0099.internalStar 12 ++ input0099.internalStar 12) ∧
    (input0099.internalStar 11).length = 5 ∧
    (input0099.internalStar 12).length = 5 ∧
    (input0099.internalStar 15).length = 5 := by decide +kernel

namespace Reading

variable {rotation : Data G} (r : Reading rotation)

def root : G.Dart := ⟨(r.map 12,r.map 8),r.map.map_adj (by decide +kernel)⟩

theorem next_degree : G.degree (rotation.vertexRotation r.root).snd = 5 := by
  obtain ⟨_,_,h⟩ := r.right
  change G.degree (rotation.vertexRotation
    ⟨(r.map 12,r.map 8),r.map.map_adj (by decide +kernel)⟩).snd = 5
  rw [h,r.degree 15 (by decide)]
  exact source_observations.2.2.2

theorem previous_degree : G.degree (rotation.vertexRotation.symm r.root).snd = 5 := by
  obtain ⟨edge,_,h⟩ := r.left
  have back : rotation.vertexRotation.symm r.root = ⟨(r.map 12,r.map 11),edge⟩ := by
    apply rotation.vertexRotation.injective
    rw [Equiv.apply_symm_apply]
    exact h.symm
  rw [back,r.degree 11 (by decide)]
  exact source_observations.2.1

/-- The actual source edge, not merely an isomorphic internal shape,
supplies the appropriate diamond pattern. -/
theorem alternatives (lower : 5 ≤ G.degree (r.map 8))
    (upper : G.degree (r.map 8) ≤ 6) :
    PentagonalAt rotation r.root ∨ MixedAt rotation r.root := by
  have five : G.degree r.root.fst = 5 :=
    (r.degree 12 (by decide)).trans source_observations.2.2.1
  have cases : G.degree (r.map 8) = 5 ∨ G.degree (r.map 8) = 6 := by omega
  rcases cases with h | h
  · exact Or.inl ⟨five,h,r.next_degree,r.previous_degree⟩
  · exact Or.inr ⟨five,h,r.next_degree,r.previous_degree⟩

end Reading

noncomputable section
attribute [local instance] Classical.propDecidable

variable (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Both low-port cases consume the already proved strict reduction and
joint colouring reconstruction. The complete Four Colour theorem is unused. -/
theorem not_low_port
    (s : Reading (ActualRulePairDiamond.rotation original minimal))
    (low : (ActualRulePairDiamond.graph original minimal).degree (s.map 8) ≤ 6) : False := by
  have lower := ActualRuleFanSupply.degree_five original minimal s.root.symm
  rcases s.alternatives lower low with pentagonal | mixed
  · obtain ⟨d,hd⟩ := ActualRulePairDiamond.pentagonal_face_pattern original minimal
      s.root pentagonal
    exact PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
      original d hd minimal
  · obtain ⟨d,hd⟩ := ActualRulePairDiamond.face_pattern original minimal s.root mixed
    exact MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
      original d hd minimal

/-- Any surviving occurrence has a higher-degree boundary port. No flatness
or Kempe-component hypothesis is needed for this geometric exclusion. -/
theorem surviving_degree
    (s : Reading (ActualRulePairDiamond.rotation original minimal)) :
    7 ≤ (ActualRulePairDiamond.graph original minimal).degree (s.map 8) := by
  by_contra h
  exact not_low_port original minimal s (by omega)

end
end FourColor.StripDiamondAlternative
