import Mettapedia.GraphTheory.FourColor.SphericalContourBondChain
import Mettapedia.GraphTheory.FourColor.GoertzelV24CanonicalHubCyclicity
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedShoreLiteralNode
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# The route's ordered bond is a simple ambient R-link ring

Gonthier's `snip.v` asks for a simple `rlink` cycle.  Its `rlink x y` means
that the face of `edge x` is the face of `y`.  For a connected planar bond in
the present route, the computed first-return permutation already makes each
successive pair satisfy that relation.  This file packages the *actual bond*
as a cyclic sequence of all its boundary darts.  The two-sided-face hypothesis
rules out fixed ports, and the bond's face-uniqueness receipt makes the ring
simple in Gonthier's sense.

The ring is a `Cycle` on boundary darts, not yet a snipped hypermap.  In
particular this theorem does not identify the route's plain hub cap with the
Coq snip disk; `StructuralCutPatchObstruction` shows why that would fail at
three or more ports.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace StructuralCutRLink

open Equiv Equiv.Perm SimpleGraph SimpleGraphDartRotation
open SphericalContourSeparators
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CanonicalHubCyclicity
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24VertexSideOpenTangle
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceOrbitIncidence
open GoertzelV24DeletedRegionRotationSplice

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Coq `geometry.v`'s `rlink`: `y` is on the ambient face containing the
opposite of `x`.  It is not adjacency in the primal graph. -/
def AmbientRLink (RS : RotationSystem V E) (x y : RS.D) : Prop :=
  RS.phi.SameCycle (RS.alpha x) y

/-- Every actual route bond has one exhaustive, face-simple R-link cycle of
boundary darts, with the orientation opposite the deleted-side first return.
The cycle is produced from the exact first-return permutation; no noose or
ring is postulated. -/
theorem orderedContourBond_simpleRLinkCycle
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width) :
    ∃ (ring : Cycle
        (BoundaryDart rotation.toRotationSystem
          (deletedRegionKeep bond.deleted)))
      (hnodup : ring.Nodup),
      (∀ b, b ∈ ring) ∧
      (∀ b (hb : b ∈ ring),
        AmbientRLink rotation.toRotationSystem b.1.1
          (ring.next hnodup b hb).1.1) ∧
      (∀ b c : BoundaryDart rotation.toRotationSystem
          (deletedRegionKeep bond.deleted),
        rotation.toRotationSystem.phi.SameCycle b.1.1 c.1.1 → b = c) ∧
      retainedRegionBoundarySuccessor rotation.toRotationSystem
        (deletedRegionKeep bond.deleted) =
        (deletedRegionBoundarySuccessor rotation.toRotationSystem
          bond.deleted)⁻¹ := by
  let RS := rotation.toRotationSystem
  let keep := deletedRegionKeep bond.deleted
  let σ := retainedRegionBoundarySuccessor RS keep
  have hG : G.Connected := by
    simpa only [RS, rotationPrimalGraph_toRotationSystem_eq]
      using hclass.primalConnected
  obtain ⟨⟨inside, hinside⟩, _⟩ :=
    (SimpleGraph.connected_iff_exists_forall_reachable _).mp bond.connected
  obtain ⟨⟨outside, houtside⟩, _⟩ :=
    (SimpleGraph.connected_iff_exists_forall_reachable _).mp bond.complement_connected
  have hcard : 2 ≤ Fintype.card (BoundaryDart RS keep) :=
    two_le_card_boundaryDart_of_connected_edgeBridgeFree RS
      hclass.primalConnected hclass.edgeBridgeFree keep
      ⟨inside, hinside⟩ ⟨outside, houtside⟩
  have hpair : ∃ first second : BoundaryDart RS keep, first ≠ second := by
    by_contra hnone
    have hsub : Subsingleton (BoundaryDart RS keep) :=
      ⟨by intro x y; by_contra hxy; exact hnone ⟨x, y, hxy⟩⟩
    have hle : Fintype.card (BoundaryDart RS keep) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨first, second, hne⟩ := hpair
  have hhub : (canonicalHubRotation RS keep).IsCycle :=
    canonicalHubRotation_isCycle_of_planarBond rotation bond.deleted
      first.1 hclass.spherical htwo hG hclass.vertexRotationCyclic
      bond.connected bond.complement_connected first second hne
  have hcycle : σ.IsCycle := by
    simpa only [σ, canonicalHubRotation, inv_inv] using hhub.inv
  have hnofix (b : BoundaryDart RS keep) : σ b ≠ b := by
    intro hfixed
    apply htwo b.1.1
    apply Quotient.sound
    have hface := retainedRegionBoundarySuccessor_sameAmbientFace_alpha
      RS keep b
    change RS.phi.SameCycle (RS.alpha b.1.1) (σ b).1.1 at hface
    rw [hfixed] at hface
    exact hface.symm
  let ring : Cycle (BoundaryDart RS keep) := σ.toCycle hcycle
  have hnodup : ring.Nodup := σ.nodup_toCycle hcycle
  refine ⟨ring, hnodup, ?_, ?_, ?_, ?_⟩
  · intro b
    exact (σ.mem_toCycle_iff_support hcycle).2 (hnofix b)
  · intro b hb
    change RS.phi.SameCycle (RS.alpha b.1.1)
      (ring.next hnodup b hb).1.1
    rw [σ.toCycle_next hcycle hb]
    exact retainedRegionBoundarySuccessor_sameAmbientFace_alpha RS keep b
  · intro b c hface
    exact bond.face_unique b c hface
  · exact bond.opposite_order

end

end StructuralCutRLink

end Mettapedia.GraphTheory.FourColor
