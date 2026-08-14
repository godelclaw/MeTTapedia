import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapAnnularCellulation
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryStubFaceStep

/-!
# Addendum V's one-cap opening enters the closed-web annular tower

The one-cap frontier construction now supplies the exact graph carrier, the
two computed hole orbits, and the spherical Euler presentation.  This module
connects that carrier to `ClosedWebAnnularEmbedding`, the source-facing object
consumed by the corridor, radial-path, and crosscut layers.

The remaining work here is dart-sensitive.  It is not enough that a named
boundary edge occurs in a hole boundary: both orientations of every degree-one
interface edge must lie on the designated hole orbit.  The proof classifies
the two darts over each literal boundary edge and uses the already-computed
stub face step.

This is a conditional C-3-to-C-4 bridge, not the C-4 formation theorem.  Its
arguments still expose the source obligations: retained-side connectedness,
complete retention of the old outer face, the ambient frontier Euler equation,
the cap-collar uniqueness invariant, and the supplied outer-face boundary
datum.  No crosscut pair is constructed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapClosedWebAnnularEmbedding

open SimpleGraphDartRotation
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24FramedAnnularExcess
open GoertzelV24FrontierPentagonCapAnnularCellulation
open GoertzelV24FrontierPentagonCapInnerFace
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24FrontierPentagonCapOpenRegionComparison
open GoertzelV24FrontierPentagonCapOuterFace
open GoertzelV24OpenRegionBoundaryStubFaceStep
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionGraphFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

variable {data : Data G}

private abbrev capOf (walk : FacialPentagonCapBoundaryWalk data) : PentagonCap G :=
  walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap

private abbrev keepCap (walk : FacialPentagonCapBoundaryWalk data) : V → Prop :=
  keep (capOf walk).vertexSupport

private abbrev outerRoot (walk : FacialPentagonCapBoundaryWalk data)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer) :
    Dart data.toRotationSystem (keepCap walk) :=
  FrontierOuterFaceData.openingOuterRoot (capOf walk) houterRetained

local instance retainedVertexFintypeLocal
    (walk : FacialPentagonCapBoundaryWalk data) :
    Fintype (RetainedVertex (keepCap walk)) :=
  GoertzelV24OpenRegionRotation.retainedVertexFintype (keepCap walk)

local instance retainedVertexDecidableEqLocal
    (walk : FacialPentagonCapBoundaryWalk data) :
    DecidableEq (RetainedVertex (keepCap walk)) :=
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq (keepCap walk)

local instance openPrimalGraphDecidableRel
    (walk : FacialPentagonCapBoundaryWalk data)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer) :
    DecidableRel
      (PrimalGraph data.toRotationSystem (keepCap walk)
        (outerRoot walk houterRetained)).Adj :=
  Classical.decRel _

/-- If both darts of one rotation edge have a named face, every dart over
that edge has that face.  This is the exact two-darts-per-edge elimination
used for both opened interfaces. -/
private theorem all_dartsOn_face_of_dart_and_alpha
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (known : RS.D) (face : OrbitFace RS)
    (hknown : dartOrbitFace RS known = face)
    (halpha : dartOrbitFace RS (RS.alpha known) = face)
    (dart : RS.D) (hdart : dart ∈ RS.dartsOn (RS.edgeOf known)) :
    dartOrbitFace RS dart = face := by
  have hknownOn : known ∈ RS.dartsOn (RS.edgeOf known) := by simp
  have hpairs := RS.dartsOn_eq_pair_of_mem hknownOn
  have hcases : dart = known ∨ dart = RS.alpha known := by
    have : dart ∈ ({known, RS.alpha known} : Finset RS.D) := by
      rw [← hpairs]
      exact hdart
    simpa using this
  rcases hcases with rfl | rfl
  · exact hknown
  · exact halpha

private abbrev openedRS
    (walk : FacialPentagonCapBoundaryWalk data)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer) :=
  (graphData data (keepCap walk) (outerRoot walk houterRetained)).toRotationSystem

private abbrev openedBoundary
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
  (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer) :=
  _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison.FrontierBoundaryData.openingPrimalBoundaryData
    data frontier (capOf walk) hinterior hfrontier (outerRoot walk houterRetained)

private abbrev innerStubDart
    (walk : FacialPentagonCapBoundaryWalk data)
  (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer)
    (step : Fin 5) : (openedRS walk houterRetained).D :=
  primalDartEquiv data (keepCap walk) (outerRoot walk houterRetained)
    (Sum.inr (_root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart
      data (capOf walk) step))

/-- The transported inner boundary edge is literally the edge underlying its
fresh cap-stub dart in the graph-backed opening. -/
private theorem openedBoundary_innerBoundaryEdge_eq_edgeOf_innerStubDart
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer)
    (step : Fin 5) :
    (openedBoundary frontier hfrontier walk hinterior houterRetained).innerBoundaryEdge step =
      (openedRS walk houterRetained).edgeOf
        (innerStubDart walk houterRetained step) := by
  have hcapInv :
      (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
        (capOf walk)).symm ((capOf walk).vertex step) =
        Sum.inr
          (GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryPort
            (capOf walk) step) := by
    apply (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
      (capOf walk)).injective
    simp
  have houterInv :
      (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
        (capOf walk)).symm ((capOf walk).spokeOuter step) =
        Sum.inl ⟨(capOf walk).spokeOuter step,
          (capOf walk).spokeOuter_not_mem_vertexSupport step⟩ := by
    apply (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
      (capOf walk)).injective
    simp
  apply Subtype.ext
  simp [openedBoundary, innerStubDart, openedRS, hcapInv, houterInv,
    (capOf walk).spokeEdge_eq step,
    GoertzelV24AnnularBoundaryIsoTransport.transport,
    GoertzelV24AnnularBoundaryIsoTransport.edgeEquiv,
    GoertzelV24AnnularBoundaryIsoTransport.sym2Equiv,
    _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison.PentagonCap.openingGraphIsoOpenPrimalGraph,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.openingGraphIso,
    GoertzelV24DeletedRegionSlitOpenRegionComparison.slitGraphIsoOpenPrimalGraph,
    GoertzelV24DeletedRegionSlitOpenRegionComparison.slitToOpenRegionVertexEquiv,
    GoertzelV24DeletedRegionSlitOpenRegionComparison.portToBoundaryDart,
    GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryPort,
    GoertzelV24FrontierPentagonCapOpening.FrontierBoundaryData.openingBoundaryData,
    GoertzelV24PentagonCapOpening.PentagonCap.openSpokeEmbedding,
    GoertzelV24PentagonCapOpening.PentagonCap.openSpokeEdge,
    GoertzelV24OpenRegionGraphBacking.toPrimalDart,
    _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison.FrontierBoundaryData.openingPrimalBoundaryData]

/-- Both graph darts over a literal fresh cap-stub edge belong to the
computed inner hole.  The second orientation is not inferred from edge
membership: it is transported from the old retained boundary dart joined to
the fresh stub by the opened face permutation. -/
private theorem innerBoundaryEdgeDarts_on_innerHole
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer)
    (step : Fin 5)
    (dart : (openedRS walk houterRetained).D)
    (hdart : dart ∈ (openedRS walk houterRetained).dartsOn
      ((openedBoundary frontier hfrontier walk hinterior
        houterRetained).innerBoundaryEdge step)) :
    dartOrbitFace (openedRS walk houterRetained) dart =
      openingGraphInnerFace walk houterRetained := by
  let boundary :=
    _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart
      data (capOf walk) step
  let known := innerStubDart walk houterRetained step
  have hknown :
      dartOrbitFace (openedRS walk houterRetained) known =
        openingGraphInnerFace walk houterRetained :=
    (openingGraphInnerFace_stub_eq frontier hfrontier walk hinterior
      hrotation hunique houterRetained step).symm
  have hliteralAlpha :
      dartOrbitFace
          (rotationSystem data.toRotationSystem
            (keepCap walk) (outerRoot walk houterRetained))
          ((rotationSystem data.toRotationSystem
            (keepCap walk) (outerRoot walk houterRetained)).alpha
            (Sum.inr boundary)) =
        dartOrbitFace
          (rotationSystem data.toRotationSystem
            (keepCap walk) (outerRoot walk houterRetained))
          (Sum.inr boundary) := by
    rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_stub]
    exact dartOrbitFace_oldBoundary_eq_stub data.toRotationSystem
      (keepCap walk) (outerRoot walk houterRetained) boundary
  have halpha :
      dartOrbitFace (openedRS walk houterRetained)
          ((openedRS walk houterRetained).alpha known) =
        openingGraphInnerFace walk houterRetained := by
    have htransported :
        dartOrbitFace (openedRS walk houterRetained)
            (primalDartEquiv data (keepCap walk)
              (outerRoot walk houterRetained)
              ((rotationSystem data.toRotationSystem
                (keepCap walk) (outerRoot walk houterRetained)).alpha
                (Sum.inr boundary))) =
          dartOrbitFace (openedRS walk houterRetained)
            (primalDartEquiv data (keepCap walk)
              (outerRoot walk houterRetained) (Sum.inr boundary)) := by
      calc
        _ = graphFaceEquiv data (keepCap walk)
              (outerRoot walk houterRetained)
              (dartOrbitFace
                (rotationSystem data.toRotationSystem
                  (keepCap walk) (outerRoot walk houterRetained))
                ((rotationSystem data.toRotationSystem
                  (keepCap walk) (outerRoot walk houterRetained)).alpha
                  (Sum.inr boundary))) :=
            (graphFaceEquiv_dartOrbitFace data (keepCap walk)
              (outerRoot walk houterRetained)
              ((rotationSystem data.toRotationSystem
                (keepCap walk) (outerRoot walk houterRetained)).alpha
                (Sum.inr boundary))).symm
        _ = graphFaceEquiv data (keepCap walk)
              (outerRoot walk houterRetained)
              (dartOrbitFace
                (rotationSystem data.toRotationSystem
                  (keepCap walk) (outerRoot walk houterRetained))
                (Sum.inr boundary)) := congrArg
            (graphFaceEquiv data (keepCap walk) (outerRoot walk houterRetained))
            hliteralAlpha
        _ = _ := graphFaceEquiv_dartOrbitFace data (keepCap walk)
          (outerRoot walk houterRetained) (Sum.inr boundary)
    have halphaKnown :
        (openedRS walk houterRetained).alpha known =
          primalDartEquiv data (keepCap walk) (outerRoot walk houterRetained)
            ((rotationSystem data.toRotationSystem
              (keepCap walk) (outerRoot walk houterRetained)).alpha
              (Sum.inr boundary)) := by
      calc
        _ = known.symm := rfl
        _ = (primalDartEquiv data (keepCap walk)
              (outerRoot walk houterRetained) (Sum.inr boundary)).symm := rfl
        _ = _ := (primalDartEquiv_alpha data (keepCap walk)
          (outerRoot walk houterRetained) (Sum.inr boundary)).symm
    rw [halphaKnown]
    exact htransported.trans hknown
  apply all_dartsOn_face_of_dart_and_alpha
    (openedRS walk houterRetained) known
    (openingGraphInnerFace walk houterRetained) hknown halpha dart
  rw [← openedBoundary_innerBoundaryEdge_eq_edgeOf_innerStubDart
    frontier hfrontier walk hinterior houterRetained step]
  exact hdart

/-- A retained ambient dart over a named old outer edge becomes a graph dart
over the corresponding transported outer boundary edge. -/
private theorem openedBoundary_outerBoundaryEdge_eq_edgeOf_openFaceDart
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (boundary : FrontierOuterFaceData data frontier)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer)
    (outer : Fin outerCount)
    (source : data.toRotationSystem.D)
    (hsource : source ∈ data.toRotationSystem.dartsOn
      (frontier.outerBoundaryEdge outer)) :
    (openedBoundary frontier hfrontier walk hinterior
        houterRetained).outerBoundaryEdge outer =
      (openedRS walk houterRetained).edgeOf
        (primalDartEquiv data (keepCap walk) (outerRoot walk houterRetained)
          (openFaceDart data.toRotationSystem (keepCap walk)
            data.toRotationSystem.outer houterRetained
            (FrontierOuterFaceData.ambientOuterBoundaryPoint
              boundary outer source hsource))) := by
  change G.Dart at source
  have hedge : data.toRotationSystem.edgeOf source =
      frontier.outerBoundaryEdge outer :=
    (data.toRotationSystem.mem_dartsOn).1 hsource
  let point := FrontierOuterFaceData.ambientOuterBoundaryPoint
    boundary outer source hsource
  have hpoint : point.1 = source := rfl
  have hkeepAlpha : keepCap walk
      (data.toRotationSystem.vertOf (data.toRotationSystem.alpha point.1)) :=
    alpha_endpoint_keep_of_faceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer houterRetained point
  have hsourceKeep : keepCap walk source.fst := by
    rw [← hpoint]
    exact houterRetained point.1 point.2
  have htargetKeep : keepCap walk source.snd := by
    rw [hpoint] at hkeepAlpha
    simpa using hkeepAlpha
  have hsourceInv :
      (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
        (capOf walk)).symm source.fst = Sum.inl ⟨source.fst, hsourceKeep⟩ := by
    apply (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
      (capOf walk)).injective
    simp
  have htargetInv :
      (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
        (capOf walk)).symm source.snd = Sum.inl ⟨source.snd, htargetKeep⟩ := by
    apply (GoertzelV24PentagonCapOpeningComparison.PentagonCap.slitToOpenVertexEquiv
      (capOf walk)).injective
    simp
  have halphaOld (hsourceKeep' : keepCap walk source.fst) :
      (rotationSystem data.toRotationSystem (keepCap walk)
        (outerRoot walk houterRetained)).alpha
          (Sum.inl ⟨source, hsourceKeep'⟩) =
        Sum.inl ⟨data.toRotationSystem.alpha source, htargetKeep⟩ := by
    rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
      data.toRotationSystem (keepCap walk) (outerRoot walk houterRetained)
      ⟨source, hsourceKeep'⟩]
  let known := primalDartEquiv data (keepCap walk)
    (outerRoot walk houterRetained)
    (openFaceDart data.toRotationSystem (keepCap walk)
      data.toRotationSystem.outer houterRetained point)
  have hopenDartEq :
      openFaceDart data.toRotationSystem (keepCap walk)
          data.toRotationSystem.outer houterRetained point =
        Sum.inl ⟨source, hsourceKeep⟩ := by
    apply congrArg Sum.inl
    apply Subtype.ext
    exact hpoint
  have hknownFst : known.fst = Sum.inl ⟨source.fst, hsourceKeep⟩ := by
    rfl
  have hknownSnd : known.snd = Sum.inl ⟨source.snd, htargetKeep⟩ := by
    change
      (rotationSystem data.toRotationSystem (keepCap walk)
        (outerRoot walk houterRetained)).vertOf
          ((rotationSystem data.toRotationSystem (keepCap walk)
            (outerRoot walk houterRetained)).alpha
            (openFaceDart data.toRotationSystem (keepCap walk)
              data.toRotationSystem.outer houterRetained point)) = _
    rw [hopenDartEq]
    rw [halphaOld]
    rfl
  have hknownEdge : known.edge =
      s(Sum.inl ⟨source.fst, hsourceKeep⟩,
        Sum.inl ⟨source.snd, htargetKeep⟩) := by
    simp [SimpleGraph.Dart.edge, hknownFst, hknownSnd]
  have hedgeVal : (frontier.outerBoundaryEdge outer).1 = source.edge := by
    exact (congrArg Subtype.val hedge).symm
  change
    (openedBoundary frontier hfrontier walk hinterior
        houterRetained).outerBoundaryEdge outer =
      (openedRS walk houterRetained).edgeOf known
  apply Subtype.ext
  rw [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  change
    ((openedBoundary frontier hfrontier walk hinterior
      houterRetained).outerBoundaryEdge outer).1 = known.edge
  rw [hknownEdge]
  simp only [openedBoundary,
    GoertzelV24AnnularBoundaryIsoTransport.transport,
    GoertzelV24AnnularBoundaryIsoTransport.edgeEquiv,
    GoertzelV24AnnularBoundaryIsoTransport.sym2Equiv,
    _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison.PentagonCap.openingGraphIsoOpenPrimalGraph,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.openingGraphIso,
    GoertzelV24DeletedRegionSlitOpenRegionComparison.slitGraphIsoOpenPrimalGraph,
    GoertzelV24DeletedRegionSlitOpenRegionComparison.slitToOpenRegionVertexEquiv,
    GoertzelV24DeletedRegionSlitOpenRegionComparison.portToBoundaryDart,
    GoertzelV24FrontierPentagonCapOpening.FrontierBoundaryData.openingBoundaryData,
    _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison.FrontierBoundaryData.openingPrimalBoundaryData]
  change Sym2.map _ (frontier.outerBoundaryEdge outer).1 = _
  rw [hedgeVal]
  simp [SimpleGraph.Dart.edge, hsourceInv, htargetInv]

/-- Both graph darts over each old outer-interface edge lie on the completely
retained outer face.  The proof transports both ambient orientations; it does
not infer the opposite face from the unoriented edge alone. -/
private theorem outerBoundaryEdgeDarts_on_outerHole
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (boundary : FrontierOuterFaceData data frontier)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer)
    (outer : Fin outerCount)
    (dart : (openedRS walk houterRetained).D)
    (hdart : dart ∈ (openedRS walk houterRetained).dartsOn
      ((openedBoundary frontier hfrontier walk hinterior
        houterRetained).outerBoundaryEdge outer)) :
    dartOrbitFace (openedRS walk houterRetained) dart =
      FrontierOuterFaceData.openingGraphOuterFace
        (capOf walk) houterRetained := by
  have hcard := data.toRotationSystem.dartsOn_card_two
    (frontier.outerBoundaryEdge outer)
  have hnonempty :
      (data.toRotationSystem.dartsOn
        (frontier.outerBoundaryEdge outer)).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hnonempty with ⟨source, hsource⟩
  change G.Dart at source
  have hsourceAlpha : data.toRotationSystem.alpha source ∈
      data.toRotationSystem.dartsOn (frontier.outerBoundaryEdge outer) :=
    data.toRotationSystem.alpha_mem_dartsOn hsource
  let point := FrontierOuterFaceData.ambientOuterBoundaryPoint
    boundary outer source hsource
  let alphaPoint := FrontierOuterFaceData.ambientOuterBoundaryPoint
    boundary outer (data.toRotationSystem.alpha source) hsourceAlpha
  let known := primalDartEquiv data (keepCap walk)
    (outerRoot walk houterRetained)
    (openFaceDart data.toRotationSystem (keepCap walk)
      data.toRotationSystem.outer houterRetained point)
  have hknown :
      dartOrbitFace (openedRS walk houterRetained) known =
        FrontierOuterFaceData.openingGraphOuterFace
          (capOf walk) houterRetained :=
    FrontierOuterFaceData.openingGraphOuterFace_contains_outerBoundaryDart
      (capOf walk) houterRetained boundary outer source hsource
  have halphaTarget :
      dartOrbitFace (openedRS walk houterRetained)
          (primalDartEquiv data (keepCap walk)
            (outerRoot walk houterRetained)
            (openFaceDart data.toRotationSystem (keepCap walk)
              data.toRotationSystem.outer houterRetained alphaPoint)) =
        FrontierOuterFaceData.openingGraphOuterFace
          (capOf walk) houterRetained :=
    FrontierOuterFaceData.openingGraphOuterFace_contains_outerBoundaryDart
      (capOf walk) houterRetained boundary outer
        (data.toRotationSystem.alpha source) hsourceAlpha
  have hpoint : point.1 = source := rfl
  have halphaPoint : alphaPoint.1 = data.toRotationSystem.alpha source := rfl
  have hsourceKeep : keepCap walk source.fst := by
    rw [← hpoint]
    exact houterRetained point.1 point.2
  have halphaKeep : keepCap walk
      (data.toRotationSystem.vertOf (data.toRotationSystem.alpha source)) := by
    rw [← hpoint]
    exact alpha_endpoint_keep_of_faceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer houterRetained point
  have hopenPointEq :
      openFaceDart data.toRotationSystem (keepCap walk)
          data.toRotationSystem.outer houterRetained point =
        Sum.inl ⟨source, hsourceKeep⟩ := by
    apply congrArg Sum.inl
    apply Subtype.ext
    exact hpoint
  have hopenAlphaPointEq :
      openFaceDart data.toRotationSystem (keepCap walk)
          data.toRotationSystem.outer houterRetained alphaPoint =
        Sum.inl ⟨data.toRotationSystem.alpha source, halphaKeep⟩ := by
    apply congrArg Sum.inl
    apply Subtype.ext
    exact halphaPoint
  have hopenAlpha :
      (rotationSystem data.toRotationSystem (keepCap walk)
        (outerRoot walk houterRetained)).alpha
          (openFaceDart data.toRotationSystem (keepCap walk)
            data.toRotationSystem.outer houterRetained point) =
        openFaceDart data.toRotationSystem (keepCap walk)
          data.toRotationSystem.outer houterRetained alphaPoint := by
    calc
      _ = (rotationSystem data.toRotationSystem (keepCap walk)
            (outerRoot walk houterRetained)).alpha
            (Sum.inl ⟨source, hsourceKeep⟩) := congrArg
              (rotationSystem data.toRotationSystem (keepCap walk)
                (outerRoot walk houterRetained)).alpha hopenPointEq
      _ = Sum.inl ⟨data.toRotationSystem.alpha source, halphaKeep⟩ :=
        GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
          data.toRotationSystem (keepCap walk) (outerRoot walk houterRetained)
          ⟨source, hsourceKeep⟩ halphaKeep
      _ = _ := hopenAlphaPointEq.symm
  have halphaKnown :
      (openedRS walk houterRetained).alpha known =
        primalDartEquiv data (keepCap walk) (outerRoot walk houterRetained)
          (openFaceDart data.toRotationSystem (keepCap walk)
            data.toRotationSystem.outer houterRetained alphaPoint) := by
    calc
      _ = known.symm := rfl
      _ = primalDartEquiv data (keepCap walk) (outerRoot walk houterRetained)
            ((rotationSystem data.toRotationSystem (keepCap walk)
              (outerRoot walk houterRetained)).alpha
              (openFaceDart data.toRotationSystem (keepCap walk)
                data.toRotationSystem.outer houterRetained point)) :=
          (primalDartEquiv_alpha data (keepCap walk)
            (outerRoot walk houterRetained)
            (openFaceDart data.toRotationSystem (keepCap walk)
              data.toRotationSystem.outer houterRetained point)).symm
      _ = _ := congrArg
        (primalDartEquiv data (keepCap walk) (outerRoot walk houterRetained))
        hopenAlpha
  have halpha :
      dartOrbitFace (openedRS walk houterRetained)
          ((openedRS walk houterRetained).alpha known) =
        FrontierOuterFaceData.openingGraphOuterFace
          (capOf walk) houterRetained := by
    rw [halphaKnown]
    exact halphaTarget
  apply all_dartsOn_face_of_dart_and_alpha
    (openedRS walk houterRetained) known
    (FrontierOuterFaceData.openingGraphOuterFace
      (capOf walk) houterRetained) hknown halpha dart
  rw [← openedBoundary_outerBoundaryEdge_eq_edgeOf_openFaceDart
    frontier hfrontier walk hinterior boundary houterRetained
      outer source hsource]
  exact hdart

/-- **Conditional Addendum V formation bridge.** The literal one-cap frontier
opening, its computed hole faces, and its transported ordered interfaces form
the exact `ClosedWebAnnularEmbedding` consumed by the corridor tower.

This theorem packages, but does not construct, the four source-formation
premises listed in `annularCellulation` or the outer-face datum.  In
particular, it is not the C-4 selection theorem and it constructs no separated
crosscut pair. -/
def closedWebAnnularEmbedding
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (boundary : FrontierOuterFaceData data frontier)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer)
    (hretained :
      ((rotationPrimalGraph data.toRotationSystem).induce
        {vertex | keepCap walk vertex}).Connected)
    (hambientEuler :
      (Fintype.card V : Int) - Fintype.card G.edgeSet +
        Fintype.card (OrbitFace data.toRotationSystem) = 2) :
    ClosedWebAnnularEmbedding
      (openedBoundary frontier hfrontier walk hinterior houterRetained) where
  cellulation := annularCellulation frontier hfrontier walk hinterior
    hrotation hunique houterRetained hretained hambientEuler
  outer_dart_on_outerHole :=
    FrontierOuterFaceData.graphData_outer_on_openingGraphOuterFace
      (capOf walk) houterRetained
  innerBoundaryEdgeDarts_on_innerHole := by
    intro inner dart hdart
    exact innerBoundaryEdgeDarts_on_innerHole frontier hfrontier walk
      hinterior hrotation hunique houterRetained inner dart hdart
  outerBoundaryEdgeDarts_on_outerHole := by
    intro outer dart hdart
    exact outerBoundaryEdgeDarts_on_outerHole frontier hfrontier walk
      hinterior boundary houterRetained outer dart hdart

end

end GoertzelV24FrontierPentagonCapClosedWebAnnularEmbedding

end Mettapedia.GraphTheory.FourColor
