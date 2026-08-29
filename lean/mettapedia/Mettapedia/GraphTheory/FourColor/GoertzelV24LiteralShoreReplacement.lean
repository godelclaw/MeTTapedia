import Mettapedia.GraphTheory.FourColor.GoertzelV24IteratedDigonNormalization
import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShoreStateDescent

/-!
# Consumer form of literal-shore replacement

The physical splice is proved at exact equal width, while finite pumping uses
one varying-width state augmented by the shore-cardinality phase.  This file
closes that last consumer boundary: equality of the displayed phased states
on two strictly nested certified shores constructs a strictly smaller
endpoint-simple counterexample.

The proof does not invoke minimality.  It first obtains a cubic star strictly
inside the deleted slab from the equal cardinality phases, unpacks equality
of the dependent finite states to one common literal width, applies the
physical splice, and finally performs terminating digon normalization.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24LiteralShoreReplacement

open GoertzelV24BridgelessFaceTwoSided
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24IteratedDigonNormalization
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24ShoreStateDescent
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24SphereCutMaterial
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- **Literal-shore consumer form of M2.**  Two strictly nested certified
connected shores with equal phased canonical states construct a strictly
smaller endpoint-simple zero-Tait-count map in the same bridgeless spherical
cubic class.  All width transport, strict slab material, physical gluing and
post-splice normalization are performed internally. -/
theorem exists_endpointSimple_replacement_of_cardPhasedState_eq
    (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    {k w : Nat}
    (oldNode newNode : LiteralShoreNode rotation k w)
    (hproper : newNode.shore ⊂ oldNode.shore)
    (heq : oldNode.cardPhasedState = newNode.cardPhasedState) :
    EndpointSimpleCounterexampleBelow.{u} (Fintype.card V) := by
  let incident : V → G.edgeSet → Prop :=
    fun vertex edge => vertex ∈ (edge : Sym2 V)
  have hcubicEdges :
      ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation ambient.spherical.cubic
  have hphase : shoreCardPhase w oldNode.shore =
      shoreCardPhase w newNode.shore :=
    congrArg Prod.fst heq
  have hstate : oldNode.state = newNode.state :=
    congrArg Prod.snd heq
  obtain ⟨strictVertex, -, hall⟩ :=
    exists_strict_slab_vertex_of_cardPhaseRepeat incident w hproper
      (exists_incident_vertex (G := G)) (fun vertex => by
        simpa only [incident, incidentEdgeFinset] using
          (Nat.le_of_eq (hcubicEdges vertex))) newNode.middleBound
      oldNode.middleBound hphase.symm
  obtain ⟨width, oldWidth, newWidth, hnormalized⟩ :=
    boundedNormalizedState_eq_elim rotation oldNode.shore newNode.shore
      oldNode.innerOuter newNode.innerOuter k oldNode.widthBound
      newNode.widthBound hstate
  have hfacesTwoSided : OrbitFacesTwoSided rotation.toRotationSystem :=
    BridgelessSphericalCubicMapData.orbitFacesTwoSided
      rotation.toRotationSystem ambient
  exact exists_strict_endpointSimple_replacement_of_normalizedState_eq
    rotation ambient hfacesTwoSided hzero
    oldNode.shore newNode.shore hproper.1
    oldNode.shoreConnected oldNode.complementConnected
    oldNode.majorityNonempty oldNode.complementNonempty
    newNode.shoreConnected newNode.complementConnected
    newNode.majorityNonempty newNode.complementNonempty
    oldNode.outsideOuter oldNode.innerOuter newNode.innerOuter
    width oldWidth newWidth hnormalized
    oldNode.first oldNode.second oldNode.first_ne_second
    strictVertex (by
      intro edge hedge
      exact hall edge (by
        simpa only [incident, incidentEdgeFinset, Finset.mem_filter,
          Finset.mem_univ, true_and] using hedge))

end

end GoertzelV24LiteralShoreReplacement

end Mettapedia.GraphTheory.FourColor
