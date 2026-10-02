import MettapediaFourColor.RuleFanSupply
import MettapediaFourColor.ActualExtendedChainReduction
import MettapediaFourColor.ActualRulePairDiamond

/-!
# Three reconstructions constrain a surviving charge fan

Actual graph-backed vertex minimality supplies all the geometric and
colouring hypotheses of the mixed diamond and both chain reductions.
Thus the common source-rule fan must have a neighbour of degree at least
seven at one of its two unspecified positions. This is a local coverage
law; it does not assert that every flat neighbourhood supplies the rules.
-/

namespace FourColor.ActualRuleFanSupply

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24MinimalFaceSize
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open ActualRulePairDiamond (graph rotation darts degree_dart)
open RuleFanSupply

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- The existing minimum facial length gives the actual dual degree bound. -/
theorem degree_five (d : (graph original minimal).Dart) :
    5 ≤ (graph original minimal).degree d.fst := by
  obtain ⟨e, rfl⟩ := (darts original minimal).surjective d
  rw [degree_dart original minimal e]
  have h := orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample original minimal
    (dartOrbitFace original.toRotationSystem e)
  have simple := orbitFaceBoundarySimple_of_twoSided original.toRotationSystem minimal.facesTwoSided
  rw [simple, orbitFaceDarts_dartOrbitFace_eq_faceOrbit] at h
  exact h

/-- The three alternatives are discharged using genuine smaller-map
colourings and their existing compatible reconstructions. -/
theorem not_low_fan (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (ha : (graph original minimal).degree (firstFree (rotation original minimal) d) ≤ 6)
    (hb : (graph original minimal).degree (secondFree (rotation original minimal) d) ≤ 6) :
    False := by
  have amin := degree_five original minimal
    (ChainFanRecognition.walk (rotation original minimal) d 3).symm
  have bmin := degree_five original minimal
    (ChainFanRecognition.walk (rotation original minimal) d 4).symm
  have center : (graph original minimal).degree
      (start (rotation original minimal) d).fst = 6 := by
    change (graph original minimal).degree
      (ChainFanRecognition.walk (rotation original minimal) d 2).fst = 6
    rw [ChainFanRecognition.walk_fst (rotation original minimal)]
    exact fixed.center
  rcases alternatives (rotation original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal) d fixed ⟨amin, ha⟩ ⟨bmin, hb⟩ with
    diamond | eight | nine
  · obtain ⟨root, hroot⟩ := ActualRulePairDiamond.face_pattern original minimal _ diamond
    exact MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
      original root hroot minimal
  · exact ChainFanRecognition.not_in_minimal original minimal _ center eight
  · exact ActualExtendedChainReduction.not_degree_word original minimal _ center nine

/-- The diamond also rules out the first free degree being five,
independently of the second free degree. -/
theorem first_six (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d) :
    6 ≤ (graph original minimal).degree (firstFree (rotation original minimal) d) := by
  have hmin := degree_five original minimal
    (ChainFanRecognition.walk (rotation original minimal) d 3).symm
  by_contra h
  have five : (graph original minimal).degree (firstFree (rotation original minimal) d) = 5 := by
    change 5 ≤ (graph original minimal).degree (firstFree (rotation original minimal) d) at hmin
    omega
  have pattern := mixed (rotation original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal) d fixed five
  obtain ⟨root, hroot⟩ := ActualRulePairDiamond.face_pattern original minimal _ pattern
  exact MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
    original root hroot minimal

/-- Joint source rules force a higher-degree continuation. The two positions
are fixed by the same root, and no abstract reduction oracle is assumed. -/
theorem surviving_degrees (d : (graph original minimal).Dart)
    (left : RuleMatcher.check (rotation original minimal) 2 d = true)
    (right : RuleMatcher.check (rotation original minimal) 4 d = true)
    (six : (graph original minimal).degree d.fst = 6)
    (shared : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 4 d 2) = 5) :
    6 ≤ (graph original minimal).degree (firstFree (rotation original minimal) d) ∧
      (7 ≤ (graph original minimal).degree (firstFree (rotation original minimal) d) ∨
       7 ≤ (graph original minimal).degree (secondFree (rotation original minimal) d)) := by
  have fixed := fixed_of_checks (rotation original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) d left right six shared
  refine ⟨first_six original minimal d fixed, ?_⟩
  by_contra h
  push Not at h
  exact not_low_fan original minimal d fixed (by omega) (by omega)

/-- The surviving fan supplies a distinct higher-degree centre within
radius two of the receiver, suitable for a subsequent overlapping view. -/
theorem next_center (d : (graph original minimal).Dart)
    (left : RuleMatcher.check (rotation original minimal) 2 d = true)
    (right : RuleMatcher.check (rotation original minimal) 4 d = true)
    (six : (graph original minimal).degree d.fst = 6)
    (shared : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 4 d 2) = 5) :
    ∃ w, w ≠ d.snd ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 2 ∧
      7 ≤ (graph original minimal).degree w := by
  have other (n : ℕ) (hn : 0 < n) (hn' : n < 6) :=
    walk_ne_receiver (rotation original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal) d six n hn hn'
  rcases (surviving_degrees original minimal d left right six shared).2 with ha | hb
  · exact ⟨firstFree (rotation original minimal) d, other 3 (by decide) (by decide),
      walk_near (rotation original minimal) d 3, ha⟩
  · exact ⟨secondFree (rotation original minimal) d, other 4 (by decide) (by decide),
      walk_near (rotation original minimal) d 4, hb⟩

/-- In the low-degree flat domain, the supplied second centre is itself
flat and has degree seven or eight. The flatness and upper bound remain
explicit neighbourhood hypotheses. -/
theorem next_flat_center (d : (graph original minimal).Dart)
    (left : RuleMatcher.check (rotation original minimal) 2 d = true)
    (right : RuleMatcher.check (rotation original minimal) 4 d = true)
    (six : (graph original minimal).degree d.fst = 6)
    (shared : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 4 d 2) = 5)
    (flat : ∀ w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 2,
      NearLinearCharge.finalCharge (rotation original minimal) w = 0)
    (bound : ∀ w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 2,
      (graph original minimal).degree w ≤ 8) :
    ∃ w, w ≠ d.snd ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 2 ∧
      NearLinearCharge.finalCharge (rotation original minimal) w = 0 ∧
      ((graph original minimal).degree w = 7 ∨ (graph original minimal).degree w = 8) := by
  obtain ⟨w, ne, near, high⟩ := next_center original minimal d left right six shared
  have upper := bound w near
  exact ⟨w, ne, near, flat w near, by omega⟩

end
end FourColor.ActualRuleFanSupply
