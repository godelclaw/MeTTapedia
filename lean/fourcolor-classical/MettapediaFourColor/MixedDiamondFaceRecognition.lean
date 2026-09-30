import MettapediaFourColor.MixedDiamondRecognition
import Mettapedia.GraphTheory.FourColor.PartialCubicDartNormalForm
import Mettapedia.GraphTheory.FourColor.SphericalVertexLowerBound

/-!
# Face recognition and joint colouring transport for the mixed diamond

The central pentagon and neighbouring lengths five, six, five construct the
complete thirteen-vertex occurrence under cubic-dual internal-six normal form.
Its exact ordered colouring observation inherits the existing shared profile.

The final context theorem retains physical Kempe closure of the seven-port
exterior as an explicit premise. It is not yet a strict reduction theorem.
-/

namespace FourColor.MixedDiamondPatch.Tangle.FaceRecognition

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation PhysicalForkCodeFaces
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WeightedOrbitFaceCorridor GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideReassembly
open GoertzelV24MinimalFaceSize GoertzelV24PortTangleGluing
open GoertzelV24PhysicalKempeNoncrossingClosure

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance mixedFaceEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance mixedFaceEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart) (hfaces : MixedDiamond.FaceLengths rotation root)
  (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

abbrev cubic := cubic3_of rotation.toRotationSystem h.spherical.cubic h.vertexRotationCyclic

/-- All occurrence fields are constructed from actual face lengths and
normal form, including distinctness and the seven genuine outgoing ports. -/
def recognized : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (Recognition.keep rotation root)
      (Recognition.rootIn rotation root (cubic rotation h) hfaces)) := by
  have htwenty := SphericalVertexLowerBound.twenty_le_card_vertices
    rotation.toRotationSystem h.spherical hminimum
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)
  have hgirth := PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive
    rotation hcubic hinternal.1 (by omega)
  have hv := MixedDiamond.vertex_injective_of_girth rotation root
    (cubic rotation h) hfaces hgirth.1 hgirth.2
  exact Recognition.recognized rotation root (cubic rotation h) hfaces hv hcubic hinternal (by omega)

omit h hminimum hinternal in
/-- Minimality supplies the full ambient normal form, not just cyclic-five
connectivity. It does not supply the local face pattern. -/
def recognized_of_minimality (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    OpenTangleIsomorphism.Iso piece
      (ofVertexSide rotation.toRotationSystem (Recognition.keep rotation root)
        (Recognition.rootIn rotation root
          (cubic rotation minimal.toBridgelessSphericalCubicMapData) hfaces)) :=
  recognized rotation root hfaces minimal.toBridgelessSphericalCubicMapData
    (orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample rotation minimal)
    (cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample rotation minimal)

/-- The physical occurrence uses exactly the reference boundary observation.
Every answer retains a genuine colouring of the entire selected shore. -/
theorem actual_repair :
    KempeBoundarySplit.Repairs
      (OpenTangleKempeRepair.Trace
        (ofVertexSide rotation.toRotationSystem (Recognition.keep rotation root)
          (Recognition.rootIn rotation root (cubic rotation h) hfaces))
        (recognized rotation root hfaces h hminimum hinternal).boundary) 7 := by
  intro et hlen hzero hsum Q hQ hold
  obtain ⟨es, hs, ho⟩ := open_repair et hlen hzero hsum Q hQ hold
  refine ⟨es, ?_, ho⟩
  exact OpenTangleKempeRepair.trace_transport
    (recognized rotation root hfaces h hminimum hinternal) (Equiv.refl _) hs

include hfaces h hminimum hinternal in
/-- The exact correspondence counts all thirteen selected vertices. -/
theorem deleted_card : (Recognition.deleted rotation root).card = 13 := by
  have hc := Fintype.card_congr (recognized rotation root hfaces h hminimum hinternal).vertex
  simp only [Fintype.card_fin] at hc
  simpa [Recognition.keep, deletedSideKeep, deletedRegionKeep, Fintype.card_subtype] using hc.symm

def ports := (recognized rotation root hfaces h hminimum hinternal).boundary.trans
  (complementBoundaryAlphaEquiv rotation.toRotationSystem (Recognition.deleted rotation root)).symm

abbrev outside := ofVertexSide rotation.toRotationSystem
  (deletedRegionKeep (Recognition.deleted rotation root))
  ((ports rotation root hfaces h hminimum hinternal 0).1)

/-- Actual exterior closure remains visible. Once supplied, compatible
whole assignments reconstruct the original map at all seven ports. -/
theorem colorable_of_exterior_closure
    (hclosed : KempeClosed (OpenTangleKempeRepair.Trace
      (outside rotation root hfaces h hminimum hinternal)
      (ports rotation root hfaces h hminimum hinternal)))
    (r : _ → Mettapedia.GraphTheory.FourColor.Color)
    (hr : OpenTangleClosedWitness.IsColor (outside rotation root hfaces h hminimum hinternal) r) :
    RotationSystemTaitColorable rotation.toRotationSystem := by
  let R := recognized rotation root hfaces h hminimum hinternal
  let seam := ports rotation root hfaces h hminimum hinternal
  let O := outside rotation root hfaces h hminimum hinternal
  have ht := OpenTangleKempeRepair.colorable_of_exterior piece O seam open_repair
    (isCubic_vertexSidePortTangle rotation _ _ h.spherical.cubic) hclosed r hr
  have hm : seam.symm.trans R.boundary =
      complementBoundaryAlphaEquiv rotation.toRotationSystem (Recognition.deleted rotation root) := by
    apply Equiv.ext
    intro b
    simp [seam, ports, R]
  have hs := (R.sewn_colorable_iff O seam.symm).mp ht
  rw [hm] at hs
  exact (rotationSystemTaitColorable_complementaryComposite_iff
    rotation.toRotationSystem (Recognition.deleted rotation root) _ _).mp hs

end
end FourColor.MixedDiamondPatch.Tangle.FaceRecognition
