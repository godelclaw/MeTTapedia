import MettapediaFourColor.LocalCoverageAssembly
import MettapediaFourColor.OverlappingPentagonalSectors
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleFacialBond

/-!
# Flat-neighbourhood coverage obligations and an actual reduction consumer

The radius assembly is instantiated on the actual quotient-face dual of a
source cubic map. An outcome is either the existing pentagonal overlap,
with its original seam and joint readings, or a separately named residual
occurrence. Residuals retain their complete support and validity predicate.
They may later be filled by other reduction families or obstructing cycles.

The local supply laws and the identification of `charge` with the source
discharging rules remain obligations. This module does not provide an
inhabitant of `CoverageObligations`, classify all flat cartwheels, identify
dual degree with face length, or remove a classical coverage entry.
-/

namespace FourColor.FlatNeighborhoodCoverage

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation GoertzelV24FaceOrbitIncidence
open GoertzelV24PrimalCycleFacialBond GoertzelV24TwoEdgeCutMinimality
open LocalCoverageAssembly OverlappingPentagonalSectors

noncomputable section

variable {V R : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G)

/-- The actual faces observed by the two views, including both centres.
Repeated readings remain a shared face; they are not independent parameters. -/
def overlapSupport (seam : G.Dart) : Set (OrbitFace rotation.toRotationSystem) :=
  let RS := rotation.toRotationSystem
  {dartOrbitFace RS seam, dartOrbitFace RS (RS.alpha seam),
    dartOrbitFace RS (leftRoot RS seam), dartOrbitFace RS (leftNear RS seam),
    dartOrbitFace RS (leftOuter RS seam), dartOrbitFace RS (rightNear RS seam),
    dartOrbitFace RS (rightOuter RS seam)}

variable (residualSupport : R → Set (OrbitFace rotation.toRotationSystem))
  (residualValid : R → Prop) (charge : OrbitFace rotation.toRotationSystem → ℤ)

/-- Complete supported observations of one alternative, never marginal choices
from two different occurrences. -/
def outcomeSupport : G.Dart ⊕ R → Set (OrbitFace rotation.toRotationSystem) :=
  Sum.elim (overlapSupport rotation) residualSupport

def outcomeValid : G.Dart ⊕ R → Prop :=
  Sum.elim (Readings rotation) residualValid

/-- The three precise local supply obligations. Geometry, charge computation,
source decoding and residual classification must establish these fields. -/
abbrev CoverageObligations :=
  LocalSupply (orbitFaceDualGraph rotation)
    (outcomeSupport rotation residualSupport) (outcomeValid rotation residualValid)
    (fun f => charge f = 0)

variable {rotation residualSupport residualValid charge}

/-- The abstract assembly produces an actual overlap seam and its readings,
or a genuine residual witness, in the same radius-twelve neighbourhood. -/
theorem radius_twelve_outcome
    (laws : CoverageObligations rotation residualSupport residualValid charge)
    (c : OrbitFace rotation.toRotationSystem)
    (hz : OnBall (orbitFaceDualGraph rotation) c 10 (fun f => charge f = 0))
    (hd : OnBall (orbitFaceDualGraph rotation) c 12
      (fun f => (orbitFaceDualGraph rotation).degree f ≤ 8)) :
    Occurs (orbitFaceDualGraph rotation) (overlapSupport rotation) (Readings rotation) c 12 ∨
      Occurs (orbitFaceDualGraph rotation) residualSupport residualValid c 12 := by
  obtain ⟨w, hw, hs⟩ := radius_twelve laws c hz hd
  cases w with
  | inl seam => exact Or.inl ⟨seam, hw, hs⟩
  | inr residual => exact Or.inr ⟨residual, hw, hs⟩

/-- An unresolved coverage branch has a precise residual witness. The overlap
branch is eliminated by actual strict reduction and colouring reconstruction;
no full Four Colour theorem is used to erase it. -/
theorem residual_in_minimal
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (laws : CoverageObligations rotation residualSupport residualValid charge)
    (c : OrbitFace rotation.toRotationSystem)
    (hz : OnBall (orbitFaceDualGraph rotation) c 10 (fun f => charge f = 0))
    (hd : OnBall (orbitFaceDualGraph rotation) c 12
      (fun f => (orbitFaceDualGraph rotation).degree f ≤ 8)) :
    Occurs (orbitFaceDualGraph rotation) residualSupport residualValid c 12 := by
  rcases radius_twelve_outcome laws c hz hd with ⟨seam, readings, _⟩ | residual
  · exact False.elim (OverlappingPentagonalSectors.not_in_minimal rotation seam readings minimal)
  · exact residual

/-- Filling the exceptional-overlap contract feeds the same actual-map
consumer. The lower-degree laws and unresolved residuals stay explicit. -/
theorem residual_in_minimal_from_overlap
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {X : OrbitFace rotation.toRotationSystem → Type*} {mate : ∀ c, X c →
      OrbitFace rotation.toRotationSystem → Prop}
    (low : ∀ c, OnBall (orbitFaceDualGraph rotation) c 2
      (fun f => (orbitFaceDualGraph rotation).degree f ≤ 6) →
      Occurs (orbitFaceDualGraph rotation) (outcomeSupport rotation residualSupport)
        (outcomeValid rotation residualValid) c 2)
    (seven : ∀ c, (orbitFaceDualGraph rotation).degree c = 7 →
      OnBall (orbitFaceDualGraph rotation) c 3 (fun f => charge f = 0) →
      OnBall (orbitFaceDualGraph rotation) c 5
        (fun f => (orbitFaceDualGraph rotation).degree f ≤ 7) →
      Occurs (orbitFaceDualGraph rotation) (outcomeSupport rotation residualSupport)
        (outcomeValid rotation residualValid) c 5)
    (overlap : EightOverlapSupply (orbitFaceDualGraph rotation)
      (outcomeSupport rotation residualSupport) (outcomeValid rotation residualValid)
      (fun f => charge f = 0) X mate)
    (c : OrbitFace rotation.toRotationSystem)
    (hz : OnBall (orbitFaceDualGraph rotation) c 10 (fun f => charge f = 0))
    (hd : OnBall (orbitFaceDualGraph rotation) c 12
      (fun f => (orbitFaceDualGraph rotation).degree f ≤ 8)) :
    Occurs (orbitFaceDualGraph rotation) residualSupport residualValid c 12 :=
  residual_in_minimal minimal (localSupply_of_overlap low seven overlap) c hz hd

/-- Closing the remaining supported residuals would close this flat local
branch. Both the local supply and residual exclusions are explicit arguments. -/
theorem not_in_minimal_of_coverage
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (laws : CoverageObligations rotation residualSupport residualValid charge)
    (c : OrbitFace rotation.toRotationSystem)
    (hz : OnBall (orbitFaceDualGraph rotation) c 10 (fun f => charge f = 0))
    (hd : OnBall (orbitFaceDualGraph rotation) c 12
      (fun f => (orbitFaceDualGraph rotation).degree f ≤ 8))
    (exclude : ∀ w, residualValid w →
      residualSupport w ⊆ closedBall (orbitFaceDualGraph rotation) c 12 → False) : False := by
  obtain ⟨w, hw, hs⟩ := residual_in_minimal minimal laws c hz hd
  exact exclude w hw hs

end
end FourColor.FlatNeighborhoodCoverage
