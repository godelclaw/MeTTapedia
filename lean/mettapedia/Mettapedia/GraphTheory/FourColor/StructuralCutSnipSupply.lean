import Mettapedia.GraphTheory.FourColor.StructuralCutSnipPatch
import Mettapedia.GraphTheory.FourColor.SphericalOrderedContourMesh

/-!
# The route's mesh-or-bond alternative supplies a physical planar patch

When an ordered mesh is absent and the face-dual distance is long enough,
the existing geometric alternative constructs an ordered contour bond. Its
first-return boundary is a nontrivial cycle, so it supplies actual roots for
both snipped sides. The result below packages the constructed bond with the
`Hypermap.Patch` and planarity theorems proved for its physical darts.

This is a cut-and-preservation theorem, not the fixed-mesh exclusion or the
strict, colour-compatible replacement required for the final descent.
-/

namespace Mettapedia.GraphTheory.FourColor.StructuralCutSnipSupply

open Mettapedia.GraphTheory
open SimpleGraphDartRotation
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24FaceOrbitIncidence
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open SphericalContourSeparators
open StructuralCutRLink
open StructuralCutSnipPatch

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

noncomputable section

/-- The no-mesh branch supplies a genuine snip patch whose two pieces are
planar. The roots are extracted from the nonempty first-return border cycle;
they are not extra hypotheses. -/
theorem exists_planar_patch_of_no_orderedMesh
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    (lo a b : ℕ) (ha : 2 ≤ a)
    (hd : lo + a ≤ (orbitFaceDualGraph rotation).dist root far)
    (hno : ¬ Nonempty (OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)) :
    ∃ bond : OrderedContourBond rotation root far lo (lo + a - 1)
        (3 * (orderedLinkageSize a b - 1)),
      ∃ outerD : RetainedDart rotation.toRotationSystem
          (deletedRegionKeep bond.deleted),
        ∃ outerR : RetainedDart rotation.toRotationSystem
            (deletedSideKeep bond.deleted),
          Hypermap.Patch
            (Hypermap.ofRotationSystem rotation.toRotationSystem)
            (diskMap rotation.toRotationSystem bond.deleted outerD)
            (remMap rotation.toRotationSystem bond.deleted outerR)
            (diskEmbed rotation.toRotationSystem bond.deleted)
            (remEmbed rotation.toRotationSystem bond.deleted)
            (diskBorder rotation.toRotationSystem bond.deleted)
            (remBorder rotation.toRotationSystem bond.deleted) ∧
          (Hypermap.Planar
              (diskMap rotation.toRotationSystem bond.deleted outerD) ∧
            Hypermap.Planar
              (remMap rotation.toRotationSystem bond.deleted outerR)) ∧
          (Hypermap.Patch.Bridgeless
              (diskMap rotation.toRotationSystem bond.deleted outerD) ∧
            Hypermap.Patch.Bridgeless
              (remMap rotation.toRotationSystem bond.deleted outerR)) := by
  obtain ⟨bond⟩ :=
    (exists_orderedMesh_or_contour_bond rotation hclass htwo root far
      lo a b ha hd).resolve_left hno
  have hcycle := retainedSuccessor_isCycle_of_orderedContourBond
    rotation hclass htwo root far bond
  obtain ⟨port, _⟩ := hcycle.nonempty_support
  let outerD : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted) := port.1
  let outerR : RetainedDart rotation.toRotationSystem
      (deletedSideKeep bond.deleted) :=
    (complementBoundaryAlphaEquiv rotation.toRotationSystem
      bond.deleted port).1
  exact ⟨bond, outerD, outerR,
    orderedContourBond_patch rotation hclass htwo root far bond outerD outerR,
    orderedContourBond_planar_parts rotation hclass htwo root far bond outerD outerR,
    orderedContourBond_bridgeless_parts rotation hclass htwo root far bond outerD outerR⟩

end

end Mettapedia.GraphTheory.FourColor.StructuralCutSnipSupply
