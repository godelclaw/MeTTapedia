import Mettapedia.GraphTheory.FourColor.DualTruncateFaceGeometry
import Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource
import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgeTwoSided

/-!
# Geometric consumers of the actual dual-and-truncate face law

Source connectivity lifts through the source vertex rotations and edge
crossings. The complete facial invariant supplies Euler and separates both
sides of every target edge. Together these establish the existing connected,
bridgeless spherical cubic map class for the literal target.
The cyclic-cut colouring supplier consumes this geometry without a source
colour word. Inverse recognition and occurrence coverage remain separate.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateMapGeometry

open DualTruncateColoring DualTruncateFaceGeometry
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24RotationEdgeBridge GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

/-- Distinct facial sides prohibit a bridge even without an Euler assumption.
The existing finite bridge-return law supplies the actual walk argument. -/
theorem edgeBridgeFree_of_facesTwoSided (htwo : OrbitFacesTwoSided RS) :
    EdgeBridgeFree RS := by
  intro d
  by_contra hnot
  let deleted := edgeDeletedPrimalGraph RS (RS.edgeOf d)
  let side : RS.D → Bool := fun x => decide (deleted.Reachable (RS.vertOf d) (RS.vertOf x))
  have hd : side d = true :=
    decide_eq_true (_root_.SimpleGraph.Reachable.rfl)
  have hcycle := GoertzelV24BridgeTwoSided.sameCycle_of_bridge
    RS.phi side d (RS.alpha d) (by
      intro x hxa hside
      have hxd : x ≠ d := fun h => hside (by rw [h])
      have hedge : RS.edgeOf x ≠ RS.edgeOf d := by
        intro h
        exact (RS.edge_fiber_two_cases rfl h).elim hxd hxa
      have hx : deleted.Adj (RS.vertOf x) (RS.vertOf (RS.alpha x)) :=
        ⟨x, hedge, rfl, rfl⟩
      have heq : deleted.Reachable (RS.vertOf d) (RS.vertOf (RS.alpha x)) ↔
          deleted.Reachable (RS.vertOf d) (RS.vertOf x) :=
        ⟨fun h => h.trans hx.reachable.symm, fun h => h.trans hx.reachable⟩
      simp only [side, RS.vert_phi_eq_vert_alpha, heq]) (by
      intro he
      have ht : decide (deleted.Reachable (RS.vertOf d) (RS.vertOf (RS.phi d))) = true :=
        he.trans hd
      have hreach := of_decide_eq_true ht
      exact hnot (by simpa only [RS.vert_phi_eq_vert_alpha] using hreach))
  exact htwo d (Quotient.sound hcycle)

theorem adjacent_alpha (d : RS.D) :
    (rotationPrimalGraph (rotation RS)).Adj d (RS.alpha d) :=
  ⟨(d, 0), rfl, rfl⟩

theorem adjacent_phi (d : RS.D) :
    (rotationPrimalGraph (rotation RS)).Adj d (RS.phi d) :=
  ⟨(d, 1), rfl, rfl⟩

theorem reachable_rho (d : RS.D) :
    (rotationPrimalGraph (rotation RS)).Reachable d (RS.rho d) := by
  have h := (adjacent_alpha RS d).reachable.trans (adjacent_phi RS (RS.alpha d)).reachable
  simpa [RS.alpha_involutive] using h

theorem reachable_rho_pow (n : ℕ) (d : RS.D) :
    (rotationPrimalGraph (rotation RS)).Reachable d ((RS.rho ^ n) d) := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (reachable_rho RS _)

theorem reachable_same_vertex (hrotation : VertexRotationCyclic RS) {d e : RS.D}
    (h : RS.vertOf d = RS.vertOf e) :
    (rotationPrimalGraph (rotation RS)).Reachable d e := by
  obtain ⟨n, hn⟩ := (hrotation d e h).exists_nat_pow_eq
  simpa only [hn] using reachable_rho_pow RS n d

/-- Source primal walks lift to actual target primal walks. -/
theorem primalConnected (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    (rotationPrimalGraph (rotation RS)).Connected := by
  have lift {v w : V} (walk : (rotationPrimalGraph RS).Walk v w) :
      ∀ d e : RS.D, RS.vertOf d = v → RS.vertOf e = w →
        (rotationPrimalGraph (rotation RS)).Reachable d e := by
    induction walk with
    | nil =>
      intro d e hd he
      exact reachable_same_vertex RS hrotation (hd.trans he.symm)
    | @cons v w z hadj tail ih =>
      intro d e hd he
      obtain ⟨x, hx, hxa⟩ := hadj
      exact (reachable_same_vertex RS hrotation (hd.trans hx.symm)).trans
        ((adjacent_alpha RS x).reachable.trans (ih (RS.alpha x) e hxa he))
  exact {
    nonempty := ⟨RS.outer⟩
    preconnected := fun d e => by
      obtain ⟨walk⟩ := hconnected.preconnected (RS.vertOf d) (RS.vertOf e)
      exact lift walk d e rfl rfl }

theorem bridgeFree : EdgeBridgeFree (rotation RS) :=
  edgeBridgeFree_of_facesTwoSided (rotation RS) (facesTwoSided RS)

/-- The actual face law and lifted walks discharge every target map-class
field. Source bridge-freeness is not needed by this construction. -/
theorem mapClass_of (hsphere : OrbitSphericalCubicMapData RS)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    BridgelessSphericalCubicMapData (rotation RS) where
  spherical := DualTruncateFaceGeometry.spherical RS hsphere hrotation
  primalConnected := primalConnected RS hconnected hrotation
  vertexRotationCyclic := DualTruncateConstructionGSLT.rotationCyclic RS
  edgeBridgeFree := bridgeFree RS

theorem mapClass (h : BridgelessSphericalCubicMapData RS) :
    BridgelessSphericalCubicMapData (rotation RS) :=
  mapClass_of RS h.spherical h.primalConnected h.vertexRotationCyclic

/-- Geometry and actual colouring follow from one source domain. -/
theorem coloured_target (h : BridgelessSphericalCubicMapData RS)
    (hregular : (rotationPrimalGraph RS).IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast (rotationPrimalGraph RS) 4)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y) :
    BridgelessSphericalCubicMapData (rotation RS) ∧ RotationSystemTaitColorable (rotation RS) :=
  ⟨mapClass RS h, DualTruncateCyclicSource.tait RS hregular hcyclic h.primalConnected hnot⟩

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

/-- The same source supplies actual spherical geometry and compatible
colouring witnesses throughout every complete faithful GSLT sweep. -/
theorem supported_target (h : BridgelessSphericalCubicMapData RS)
    (hregular : (rotationPrimalGraph RS).IsRegularOfDegree 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast (rotationPrimalGraph RS) 4)
    (hnot : ¬∀ x y : V, x ≠ y → (rotationPrimalGraph RS).Adj x y)
    (order : List RS.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    BridgelessSphericalCubicMapData (rotation RS) ∧
      VertexConstructionGSLT.colouring.Supports
        (route (encodeClosed (cubic RS) (DualTruncateConstructionGSLT.rotationCyclic RS)
          order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  ⟨mapClass RS h,
    DualTruncateCyclicSource.every_complete_sweep RS hregular hcyclic h.primalConnected
      hnot order hn he hcover⟩

end
end Mettapedia.GraphTheory.FourColor.DualTruncateMapGeometry
