import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgelessFaceTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShorePhysicalReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalParallelExclusion

/-!
# Terminating normalization after physical replacement

The physical equal-state splice naturally lives in the category of loopless
rotation multigraphs.  This is already the cap-stable class quantified over by
vertex minimality, so simplicity is not needed for the contradiction.  When a
later consumer does require a simple-graph presentation, however, every
parallel pair can be removed uniformly.

The normalization below is well-founded recursion on the number of vertices.
At a non-simple stage, cubicity turns a parallel pair into explicit digon
data.  The theta branch is Tait colourable and hence impossible; otherwise the
checked digon suppression removes two vertices, preserves the full structural
class, and preserves non-colourability.  Thus the recursion terminates at an
endpoint-simple counterexample.  No list of configurations is involved.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24IteratedDigonNormalization

open GoertzelV24BridgelessFaceTwoSided
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShorePhysicalReplacement
open GoertzelV24MinimalParallelExclusion
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality
open RotationSystem

noncomputable section

universe u

/-- A zero-Tait-count member of the cap-stable class, with injective endpoint
map and no more than `bound` vertices.  Endpoint injectivity is precisely the
condition needed by the canonical simple-graph backing. -/
def EndpointSimpleCounterexampleAtMost (bound : Nat) : Prop :=
  ∃ (V' E' : Type u),
    ∃ (_ : Fintype V') (_ : DecidableEq V')
      (_ : Fintype E') (_ : DecidableEq E'),
    ∃ RS' : RotationSystem.{u, u, u} V' E',
      BridgelessSphericalCubicMapData RS' ∧
        ¬ RotationSystemTaitColorable RS' ∧
        Function.Injective RS'.endpoints ∧
        Fintype.card V' ≤ bound

/-- The strict version returned after normalizing a physical replacement. -/
def EndpointSimpleCounterexampleBelow (bound : Nat) : Prop :=
  ∃ (V' E' : Type u),
    ∃ (_ : Fintype V') (_ : DecidableEq V')
      (_ : Fintype E') (_ : DecidableEq E'),
    ∃ RS' : RotationSystem.{u, u, u} V' E',
      BridgelessSphericalCubicMapData RS' ∧
        ¬ RotationSystemTaitColorable RS' ∧
        Function.Injective RS'.endpoints ∧
        Fintype.card V' < bound

/-- **Terminating parallel-seam normalization.**  Every non-Tait-colourable
loopless connected bridgeless spherical cubic rotation multigraph has an
endpoint-simple descendant with no more vertices.  The recursion performs a
checked digon suppression whenever endpoint injectivity fails. -/
theorem exists_endpointSimpleCounterexampleAtMost_of_counterexample
    {V E : Type u} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E)
    (hclass : BridgelessSphericalCubicMapData RS)
    (hnot : ¬ RotationSystemTaitColorable RS) :
    EndpointSimpleCounterexampleAtMost.{u} (Fintype.card V) := by
  classical
  by_cases hinjective : Function.Injective RS.endpoints
  · exact ⟨V, E, inferInstance, inferInstance, inferInstance, inferInstance,
      RS, hclass, hnot, hinjective, le_rfl⟩
  · obtain ⟨first, second, hendpoints, hne⟩ :=
      Function.not_injective_iff.mp hinjective
    have hparallel : RS.AreParallelEdges first second := ⟨hne, hendpoints⟩
    obtain ⟨D, hD⟩ :=
      RS.exists_wellFormed_digonPatchData_of_areParallelEdges
        hclass.spherical.cubic hparallel
    by_cases htheta : D.vFar hD = D.u
    · exact False.elim (hnot
        (D.taitColorable_of_theta hD hclass.spherical.cubic htheta
          hclass.primalConnected))
    · let suppressed :=
        D.suppressed hD hclass.spherical.cubic hclass.edgeBridgeFree htheta
      have htwoSided : OrbitFacesTwoSided RS :=
        BridgelessSphericalCubicMapData.orbitFacesTwoSided RS hclass
      have hclassSuppressed : BridgelessSphericalCubicMapData suppressed :=
        D.suppressed_bridgelessSphericalCubicMapData
          hD hclass htwoSided htheta
      have hnotSuppressed : ¬ RotationSystemTaitColorable suppressed :=
        D.not_suppressed_taitColorable hD hclass.spherical.cubic
          hclass.edgeBridgeFree htheta hnot
      have hcard : Fintype.card
          (D.twoEdgeCut hD hclass.spherical.cubic
            hclass.edgeBridgeFree htheta).complementData.CapVertex <
          Fintype.card V :=
        D.card_suppressed_vertex_lt hD hclass.spherical.cubic
          hclass.edgeBridgeFree htheta
      obtain ⟨V', E', iV', dV', iE', dE', RS', hclass', hnot',
          hinjective', hle⟩ :=
        exists_endpointSimpleCounterexampleAtMost_of_counterexample
          suppressed hclassSuppressed hnotSuppressed
      exact ⟨V', E', iV', dV', iE', dE', RS', hclass', hnot',
        hinjective', hle.trans hcard.le⟩
termination_by Fintype.card V
decreasing_by
  exact hcard

/-- If the starting counterexample actually contains a parallel pair, its
endpoint-simple normalized descendant is strictly smaller.  This is the exact
checked form of repeated post-splice parallel-seam normalization. -/
theorem exists_endpointSimpleCounterexampleBelow_of_areParallelEdges
    {V E : Type u} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E)
    (hclass : BridgelessSphericalCubicMapData RS)
    (hnot : ¬ RotationSystemTaitColorable RS)
    {first second : E} (hparallel : RS.AreParallelEdges first second) :
    EndpointSimpleCounterexampleBelow.{u} (Fintype.card V) := by
  classical
  obtain ⟨D, hD⟩ :=
    RS.exists_wellFormed_digonPatchData_of_areParallelEdges
      hclass.spherical.cubic hparallel
  by_cases htheta : D.vFar hD = D.u
  · exact False.elim (hnot
      (D.taitColorable_of_theta hD hclass.spherical.cubic htheta
        hclass.primalConnected))
  · let suppressed :=
      D.suppressed hD hclass.spherical.cubic hclass.edgeBridgeFree htheta
    have htwoSided : OrbitFacesTwoSided RS :=
      BridgelessSphericalCubicMapData.orbitFacesTwoSided RS hclass
    have hclassSuppressed : BridgelessSphericalCubicMapData suppressed :=
      D.suppressed_bridgelessSphericalCubicMapData
        hD hclass htwoSided htheta
    have hnotSuppressed : ¬ RotationSystemTaitColorable suppressed :=
      D.not_suppressed_taitColorable hD hclass.spherical.cubic
        hclass.edgeBridgeFree htheta hnot
    have hcard : Fintype.card
        (D.twoEdgeCut hD hclass.spherical.cubic
          hclass.edgeBridgeFree htheta).complementData.CapVertex <
        Fintype.card V :=
      D.card_suppressed_vertex_lt hD hclass.spherical.cubic
        hclass.edgeBridgeFree htheta
    obtain ⟨V', E', iV', dV', iE', dE', RS', hclass', hnot',
        hinjective', hle⟩ :=
      exists_endpointSimpleCounterexampleAtMost_of_counterexample
        suppressed hclassSuppressed hnotSuppressed
    exact ⟨V', E', iV', dV', iE', dE', RS', hclass', hnot',
      hinjective', lt_of_le_of_lt hle hcard⟩

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Any constructive physical replacement has a strictly smaller
endpoint-simple descendant.  This is the representation-normalization field
of M2, separated from the splice because minimality itself already accepts the
literal loopless multigraph. -/
theorem StrictPhysicalReplacementData.exists_endpointSimple_descendant
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    (replacement : StrictPhysicalReplacementData rotation oldShore newShore
      outsideOuter newInnerOuter k oldWidth newWidth) :
    EndpointSimpleCounterexampleBelow.{u} (Fintype.card V) := by
  obtain ⟨V', E', iV', dV', iE', dE', RS', hclass', hnot',
      hinjective', hle⟩ :=
    exists_endpointSimpleCounterexampleAtMost_of_counterexample
      (replacementCandidate rotation oldShore newShore outsideOuter
        newInnerOuter k oldWidth newWidth)
      replacement.structural replacement.notColorable
  exact ⟨V', E', iV', dV', iE', dE', RS', hclass', hnot', hinjective',
    lt_of_le_of_lt hle replacement.vertexCount_lt⟩

/-- **Normalized consumer form of M2.**  Equal canonical states on two
nested connected literal shores, together with strict slab material, produce
a strictly smaller endpoint-simple zero-Tait-count map in the full cap-stable
class.  This theorem composes the physical splice with terminating digon
normalization. -/
theorem exists_strict_endpointSimple_replacement_of_normalizedState_eq
    (rotation : SimpleGraphDartRotation.Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (hfacesTwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    (oldShore newShore : Finset G.edgeSet)
    (hsubset : newShore ⊆ oldShore)
    (hOldConnected : EdgeShoreConnected G oldShore)
    (hOldComplementConnected :
      EdgeShoreConnected G (Finset.univ \ oldShore))
    (hOldMajorityNonempty :
      ∃ vertex, majorityVertexSide G oldShore vertex)
    (hOldComplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G oldShore vertex)
    (hNewConnected : EdgeShoreConnected G newShore)
    (hNewComplementConnected :
      EdgeShoreConnected G (Finset.univ \ newShore))
    (hNewMajorityNonempty :
      ∃ vertex, majorityVertexSide G newShore vertex)
    (hNewComplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G newShore vertex)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (oldInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    (hstate : normalizedState rotation oldShore oldInnerOuter k oldWidth =
      normalizedState rotation newShore newInnerOuter k newWidth)
    (first second : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (hne : first ≠ second)
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
      edge ∈ oldShore \ newShore) :
    EndpointSimpleCounterexampleBelow.{u} (Fintype.card V) := by
  let replacement := strictPhysicalReplacement_of_normalizedState_eq
    rotation ambient hfacesTwoSided hzero oldShore newShore hsubset
    hOldConnected hOldComplementConnected
    hOldMajorityNonempty hOldComplementNonempty
    hNewConnected hNewComplementConnected
    hNewMajorityNonempty hNewComplementNonempty
    outsideOuter oldInnerOuter newInnerOuter
    k oldWidth newWidth hstate first second hne strictVertex hall
  exact StrictPhysicalReplacementData.exists_endpointSimple_descendant
    rotation oldShore newShore outsideOuter newInnerOuter
    k oldWidth newWidth replacement

end

end GoertzelV24IteratedDigonNormalization

end Mettapedia.GraphTheory.FourColor
