import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFactorResidue

/-!
# Finite incoming-profile resolution of the old-prefix factor sum

Every old-prefix fragment contributing to one outgoing source-Cell fragment
is either represented by a genuine incoming finite-profile coordinate or is
the singleton shared-rung residue.  This file chooses that finite resolution
once and rewrites the complete old-prefix factor sum through it.

The resolution is relational: no canonical incoming coordinate is asserted,
and the residue is not promoted to a fictitious profile fragment.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFactorSumEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The complete old-prefix cap sum admits a finite resolution through
incoming profile coordinates and the single local residue value `1`.

`assignment factor = some index` means that the summand is read from that
incoming coordinate.  `none` means that the factor is the shared-rung
residue.  Only contributing factors are constrained. -/
theorem exists_localLayerLeftFactorCapResolution
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    ∃ assignment : aligned.LocalLayerLeftFactor fragment →
        Option aligned.LocalLayerLeftBoundaryIndex,
      (∀ factor, factor ∈ aligned.localLayerLeftFactorFragments fragment →
        match assignment factor with
        | some index =>
            (((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                color hcolor).profile.faceLengthCap index).val) =
              aligned.localLayerLeftFactorPositionCap fragment factor
        | none =>
            aligned.localLayerLeftFactorPositionCap fragment factor = 1) ∧
      aligned.toInterface.localLayerFactorFragmentCapSum
          aligned.toInterface.localLayerLeftPrefixRegion fragment =
        min
          (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
            match assignment factor with
            | some index =>
                ((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                    color hcolor).profile.faceLengthCap index).val
            | none => 1)
          5 := by
  classical
  let assignment : aligned.LocalLayerLeftFactor fragment →
      Option aligned.LocalLayerLeftBoundaryIndex := fun factor =>
    if hcoordinate : ∃ index : aligned.LocalLayerLeftBoundaryIndex,
        (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
            |>.profile.faceLengthCap index).val) =
          aligned.localLayerLeftFactorPositionCap fragment factor then
      some (Classical.choose hcoordinate)
    else
      none
  have hresolve : ∀ factor,
      factor ∈ aligned.localLayerLeftFactorFragments fragment →
        match assignment factor with
        | some index =>
            (((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                color hcolor).profile.faceLengthCap index).val) =
              aligned.localLayerLeftFactorPositionCap fragment factor
        | none =>
            aligned.localLayerLeftFactorPositionCap fragment factor = 1 := by
    intro factor hfactor
    by_cases hcoordinate : ∃ index : aligned.LocalLayerLeftBoundaryIndex,
        (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
            |>.profile.faceLengthCap index).val) =
          aligned.localLayerLeftFactorPositionCap fragment factor
    · simp only [assignment, dif_pos hcoordinate]
      exact Classical.choose_spec hcoordinate
    · have hcases :=
        aligned.exists_localLayerLeftPrefixProfileFaceLengthCap_or_residue_eq_one
          hcubic hrotation color hcolor fragment factor hfactor
      rcases hcases with hprofile | hresidue
      · exact (hcoordinate hprofile).elim
      · simpa only [assignment, dif_neg hcoordinate] using hresidue
  refine ⟨assignment, hresolve, ?_⟩
  change
    min
        (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
          aligned.localLayerLeftFactorPositionCap fragment factor)
        5 =
      min
        (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
          match assignment factor with
          | some index =>
              ((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                  color hcolor).profile.faceLengthCap index).val
          | none => 1)
        5
  congr 1
  apply Finset.sum_congr rfl
  intro factor hfactor
  have hfactorResolve := hresolve factor hfactor
  cases hassignment : assignment factor with
  | none =>
      simpa only [hassignment] using hfactorResolve
  | some index =>
      simp only [hassignment] at hfactorResolve
      exact hfactorResolve.symm

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
