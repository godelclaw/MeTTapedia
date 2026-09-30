import Mettapedia.GraphTheory.FourColor.HexagonalTwoRowWiringReduction
import Mettapedia.GraphTheory.FourColor.ZigzagTwoRowShortFaceReturn
import Mettapedia.GraphTheory.FourColor.ZigzagTwoRowExteriorComponents

/-!
# Short end faces recognize the free-wire reduction

The input is a literal embedded two-row slab and five- or six-dart faces
at its end ports. The actual embedding separates the two port blocks;
connectedness makes the exterior port-visible; short faces supply its
opposite return. These facts derive both formerly supplied conditions.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideReassembly
open GoertzelV24CompositeSeamMultigraph GoertzelV24BoundaryEssentialGluing
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceDualConnectedness
open OpenTangleBoundaryConnectivity BoundaryConnectivity ZigzagRing
open OpenTanglePortReplacement

noncomputable section
universe u
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype
set_option backward.isDefEq.respectTransparency false
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {inner : V → Prop} {k : ℕ} [NeZero k]
  (S : SlabOf RS (tube k 1).data inner)

/-- The recognition hypothesis refers to faces of the ambient map. -/
def ShortEndFaces : Prop := ∀ b,
  (RS.faceOrbit (S.outsidePort b).1.1).card = 5 ∨
    (RS.faceOrbit (S.outsidePort b).1.1).card = 6

def wireAmbientDarts : S.wireOriginal.D ≃ RS.D :=
  S.wireOldDarts.trans S.reassemblyDartEquiv

theorem wireAmbientDarts_alpha (d) : S.wireAmbientDarts (S.wireOriginal.alpha d) =
    RS.alpha (S.wireAmbientDarts d) := by
  simp only [wireAmbientDarts, Equiv.trans_apply, wireOldDarts_alpha, reassemblyDartEquiv_alpha]

theorem wireAmbientDarts_rho (hS : S.RotationCompatible) (d) :
    S.wireAmbientDarts (S.wireOriginal.rho d) = RS.rho (S.wireAmbientDarts d) := by
  simp only [wireAmbientDarts, Equiv.trans_apply, wireOldDarts_rho, reassemblyDartEquiv_rho S hS]

theorem wire_return_of_short_end_faces (hS : S.RotationCompatible) (short : S.ShortEndFaces) :
    returnCode S.wireExterior = (boundaryPerm k)⁻¹ := by
  apply ShiftedWiring.Geometry.returnCode_of_short_end_faces
  intro b
  have hc := RotationSystemExactTransport.faceOrbit_card S.wireOriginal RS S.wireAmbientDarts
    S.wireAmbientDarts_alpha (S.wireAmbientDarts_rho hS)
    (ShiftedWiring.Geometry.oldExterior k S.wireExterior (.inr b))
  have hd : S.wireAmbientDarts
      (ShiftedWiring.Geometry.oldExterior k S.wireExterior (.inr b)) = (S.outsidePort b).1.1 := by
    simp only [wireAmbientDarts, ShiftedWiring.Geometry.oldExterior, Equiv.trans_apply,
      wireOldDarts_reassoc, Equiv.sumCongr_apply, Sum.map_inl, reassemblyDartEquiv_left]
    rfl
  rw [hd] at hc
  rw [hc]
  exact short b

private theorem inner_iff_alpha_outside (d : RS.D)
    (hd : S.outsideKeep (RS.vertOf d)) (ha : S.outsideKeep (RS.vertOf (RS.alpha d))) :
    inner (RS.vertOf d) ↔ inner (RS.vertOf (RS.alpha d)) := by
  have step (a : RS.D) (hout : S.outsideKeep (RS.vertOf (RS.alpha a)))
      (hi : inner (RS.vertOf a)) : inner (RS.vertOf (RS.alpha a)) := by
    by_contra hn
    obtain ⟨i, he⟩ := S.boundary_inner ⟨⟨a, hi⟩, hn⟩
    have hm := congrArg RS.alpha he
    rw [RS.alpha_involutive] at hm
    exact S.not_outsideKeep_dart (.inr (.inl i)) (hm ▸ hout)
  refine ⟨step d ha, ?_⟩
  intro hi
  have hh := step (RS.alpha d) (by simpa only [RS.alpha_involutive] using hd) hi
  simpa only [RS.alpha_involutive] using hh

/-- The ambient inner predicate distinguishes the actual exterior shores. -/
def wireShore (v : {v : V // S.outsideKeep v}) : Bool := decide (¬ inner v.1)

theorem wireShore_edge (e : SideEdge S.wireExterior) :
    S.wireShore ((sideMultigraph S.wireExterior).fst e) =
      S.wireShore ((sideMultigraph S.wireExterior).snd e) := by
  let d := e.2.choose
  change decide (¬ inner (RS.vertOf d.1.1)) = decide (¬ inner (RS.vertOf (RS.alpha d.1.1)))
  rw [S.inner_iff_alpha_outside d.1.1 d.1.2 d.2]

theorem wireShore_left (i : Fin k) : S.wireShore (S.wireExterior.boundaryVert (.inl i)) = false := by
  change decide (¬ inner (RS.vertOf (RS.alpha (S.ι (.inr (.inl i)))))) = false
  simp only [S.in_inner i, not_true_eq_false, decide_false]

theorem wireShore_right (i : Fin k) : S.wireShore (S.wireExterior.boundaryVert (.inr i)) = true := by
  change decide (¬ inner (RS.vertOf (RS.alpha (S.ι (.inr (.inr i)))))) = true
  exact decide_eq_true (S.out_not_inner i)

theorem wireExterior_visible (hconn : (rotationPrimalGraph RS).Connected) :
    PortVisible (sideMultigraph S.wireExterior) S.wireExterior.boundaryVert := by
  have hp : ∃ v, ¬ S.outsideKeep v :=
    ⟨RS.vertOf (S.ι (.inr (.inl 0))), S.not_outsideKeep_dart _⟩
  exact visible_reindex S.exterior
    (visible_ofVertexSide RS S.outsideKeep (S.outsidePort (.inl 0)).1 hconn hp)
    S.outsideBoundaryEquiv

/-- Both connected shores are derived from ambient geometry and short faces. -/
def wireTwoShores (hS : S.RotationCompatible) (short : S.ShortEndFaces)
    (hconn : (rotationPrimalGraph RS).Connected) :
    ShiftedWiring.Geometry.TwoShores k S.wireExterior :=
  ShiftedWiring.Geometry.twoShores_of_return k S.wireExterior S.wireShore
    S.wireShore_edge S.wireShore_left S.wireShore_right (S.wireExterior_visible hconn)
    (S.wire_return_of_short_end_faces hS short)

/-- Short ambient end faces suffice for the whole strict reduction. -/
theorem wire_reduction_of_short_end_faces (hk : 3 ≤ k) (hS : S.RotationCompatible)
    (short : S.ShortEndFaces) (h : BridgelessSphericalCubicMapData RS) :
    Fintype.card {v : V // S.outsideKeep v} < Fintype.card V ∧
      BridgelessSphericalCubicMapData (S.wireShortened (S.wireTwoShores hS short h.primalConnected)) ∧
      (RotationSystemTaitColorable (S.wireShortened (S.wireTwoShores hS short h.primalConnected)) →
        RotationSystemTaitColorable RS) :=
  S.wire_reduction hk hS (S.wireTwoShores hS short h.primalConnected)
    (S.wire_return_of_short_end_faces hS short) h

variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Minimality excludes any recognized two-row slab with short end faces. -/
theorem no_two_row_short_end_faces (hk : 3 ≤ k) (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} (S : SlabOf rotation.toRotationSystem (tube k 1).data inner)
    (hS : S.RotationCompatible) (short : S.ShortEndFaces) : False := by
  exact no_two_row_wire_domain hk rotation minimal S hS
    (S.wireTwoShores hS short minimal.toBridgelessSphericalCubicMapData.primalConnected)
    (S.wire_return_of_short_end_faces hS short)

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf
