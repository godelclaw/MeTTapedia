import Mettapedia.GraphTheory.FourColor.SphericalFrozenReduction
import Mettapedia.GraphTheory.FourColor.SphericalMarkedFaceReduction

/-! # One supplied reduction preserving designated faces and frozen support

Names are computed from complete designated faces and frozen edge darts,
closed under edge reversal. The joint-state supplier chooses one physical
candidate on which both the face transport and all colour prescriptions
are preserved. The size bound still depends on designated perimeter.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalFrozenFaceReduction

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24ConnectedEdgeShoreStructuralData
open MarkedCotreeSeam SphericalMarkedFaceReduction

noncomputable section
universe u
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

def namedDarts (rotation : Data G) (holes frozen : Finset G.Dart) : Finset G.Dart :=
  edgeDarts rotation holes ∪ (frozen ∪ frozen.image rotation.toRotationSystem.alpha)

def vertexMarks (rotation : Data G) (holes frozen : Finset G.Dart) : Finset V :=
  (namedDarts rotation holes frozen).image (fun d => d.fst)

omit [G.LocallyFinite] in
theorem namedDarts_alpha (rotation : Data G) (holes frozen : Finset G.Dart)
    {d : G.Dart} (hd : d ∈ namedDarts rotation holes frozen) :
    rotation.toRotationSystem.alpha d ∈ namedDarts rotation holes frozen := by
  rcases Finset.mem_union.mp hd with hd | hd
  · exact Finset.mem_union_left _ (edgeDarts_alpha rotation holes hd)
  · apply Finset.mem_union_right
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_union_left _ (by simpa using he)

/-- One candidate preserves entire designated face cycles and the complete
joint acceptance problem. All marks and boundary names are constructed. -/
theorem exists_orderedMesh_or_replacement (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (holes frozen : Finset G.Dart)
    (hlarge : SphericalFrozenReduction.sizeBound a b (vertexMarks rotation holes frozen).card
      (namedDarts rotation holes frozen).card < Fintype.card V) :
    Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b) ∨
      ∃ w, w ≤ SphericalFrozenReduction.widthBound a b (vertexMarks rotation holes frozen).card
        (namedDarts rotation holes frozen).card ∧
      ∃ pair : SeamPair rotation (vertexMarks rotation holes frozen)
        (Subtype.val : ↥(namedDarts rotation holes frozen) → G.Dart) w,
        Nonempty (BridgelessSphericalCubicMapData pair.candidate) ∧
        Fintype.card ({v : V // majorityDeletedKeep G pair.outer.shore v} ⊕
          {v : V // majorityRetainedKeep G pair.inner.shore v}) < Fintype.card V ∧
        (∀ root ∈ holes, PreservesFace pair root) ∧
        ∃ lift : ↥(namedDarts rotation holes frozen) → pair.candidate.D,
          (∀ m, pair.ambientDart (lift m) = m.val) ∧
          (∀ m, pair.ambientDart (pair.candidate.alpha (lift m)) = rotation.toRotationSystem.alpha m.val) ∧
          ∀ value : ↥(namedDarts rotation holes frozen) → Color,
            FrozenDartTransport.Accepts rotation.toRotationSystem Subtype.val value ↔
              FrozenDartTransport.Accepts pair.candidate lift value := by
  by_cases hm : Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b)
  · exact Or.inl hm
  · have hl : SphericalFrozenReduction.sizeBound a b (vertexMarks rotation holes frozen).card
        (Fintype.card ↥(namedDarts rotation holes frozen)) < Fintype.card V := by
      simpa only [Fintype.card_coe] using hlarge
    obtain ⟨w, hw, pair, hjoint⟩ := SphericalFrozenReduction.exists_joint_seam_of_no_orderedMesh
      rotation ambient htwo a b ha (vertexMarks rotation holes frozen)
      (Subtype.val : ↥(namedDarts rotation holes frozen) → G.Dart) hm hl
    have hmarks : ∀ m : ↥(namedDarts rotation holes frozen), m.val.fst ∈ vertexMarks rotation holes frozen :=
      fun m => Finset.mem_image.mpr ⟨m.val, m.property, rfl⟩
    have hclosed : ∀ m : ↥(namedDarts rotation holes frozen),
        ∃ m' : ↥(namedDarts rotation holes frozen), rotation.toRotationSystem.alpha m.val = m'.val :=
      fun m => ⟨⟨_, namedDarts_alpha rotation holes frozen m.property⟩, rfl⟩
    refine Or.inr ⟨w, ?_, pair, ⟨pair.structuralData ambient htwo⟩,
      pair.candidate_card_lt ambient, ?_, pair.liftedMark hmarks, pair.liftedMark_name hmarks, ?_,
      pair.accepts_iff hjoint hmarks⟩
    · simpa only [Fintype.card_coe] using hw
    · intro root hr
      apply pair.designated_face_survives hmarks hclosed
      intro e he
      exact ⟨⟨e, Finset.mem_union_left _ (faceDarts_mem rotation holes hr he)⟩, rfl⟩
    · intro m
      exact (pair.candidate_alpha_mark hclosed _ m (pair.liftedMark_name hmarks m)).trans
        (congrArg rotation.toRotationSystem.alpha (pair.liftedMark_name hmarks m))

end
end Mettapedia.GraphTheory.FourColor.SphericalFrozenFaceReduction
