import MettapediaFourColor.TwoDiamondCycleReplacement
import MettapediaFourColor.SourceTaitInverse

/-!
# Joint witnesses survive the face-colouring representation change

Every supplied colouring of the smaller cycle replacement has a reference
face-colouring interpretation. Restricting the round trip preserves the
complete exterior and cycle witnesses and their shared seam colours.
This supplies the input representation needed by a planar-remainder Kempe
argument. Exterior closure itself remains a separate obligation.
-/

namespace FourColor.TwoDiamondCycleReplacement

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24TwoEdgeCutMinimality
open OpenTangleClosedWitness

noncomputable section
universe u
variable {V I B : Type u} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (seam : B ≃ Fin 8)

/-- One common face witness preserves the entire exterior observation and
the shared seam, including when the exterior has several components. -/
theorem smaller_joint_face_witness
    (h : BridgelessSphericalCubicMapData (original outside seam))
    (c : (reduced outside seam).EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (hc : (reduced outside seam).IsTaitEdgeColoring c) :
    ∃ k : (reduced outside seam).D → Color,
      ∃ hk : (SourceConstruction.sourceMap (reduced outside seam)).Coloring k,
      ∃ l r, (SourceConstruction.sourceMap (reduced outside seam)).mirror.Coloring k ∧
        IsColor outside l ∧ IsColor cycle r ∧
        (∀ b, l (.inr b) = r (.inr (seam b))) ∧
        (∀ d, SourceConstruction.palette
          (k (composeDartEquiv (.inl d)) +
            k ((reduced outside seam).alpha (composeDartEquiv (.inl d)))) = l d) ∧
        (∀ e, SourceConstruction.taitColoring
          (replacement_class outside seam h).spherical.cubic
          (replacement_class outside seam h).vertexRotationCyclic hk e = c e) := by
  obtain ⟨k, hk, he⟩ := SourceConstruction.tait_round_trip
    (replacement_class outside seam h) c hc
  obtain ⟨l, r, hl, hr, hm, hlread⟩ := restrictOpen outside cycle seam c hc
  refine ⟨k, hk, l, r, (SourceConstruction.reference_mirror_colouring_iff k).mpr hk,
    hl, hr, hm, ?_, he⟩
  intro d
  exact (SourceConstruction.taitColoring_dart
    (replacement_class outside seam h).spherical.cubic
    (replacement_class outside seam h).vertexRotationCyclic hk
    (composeDartEquiv (.inl d))).symm.trans ((he _).trans (hlread d).symm)

end
end FourColor.TwoDiamondCycleReplacement
