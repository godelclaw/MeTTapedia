import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceCutTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The cyclic turn from an oriented central edge selects a specified arm
at its base vertex. -/
def orientedEdgeArmTurn (RS : RotationSystem V E)
    (central arm : RS.D) : Bool :=
  decide (RS.rho central = arm)

@[simp] theorem orientedEdgeArmTurn_eq_true_iff
    (RS : RotationSystem V E) (central arm : RS.D) :
    RS.orientedEdgeArmTurn central arm = true ↔
      RS.rho central = arm := by
  simp [orientedEdgeArmTurn]

/-- At a cubic vertex, when the cyclic turn from the central dart does
not select a distinct arm, the arm turns back to the central dart. -/
theorem rho_arm_eq_central_of_orientedEdgeArmTurn_eq_false
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (central arm : RS.D)
    (hbase : RS.vertOf arm = RS.vertOf central)
    (hne : central ≠ arm)
    (hturn : RS.orientedEdgeArmTurn central arm = false) :
    RS.rho arm = central := by
  have hnot : RS.rho central ≠ arm := by
    simpa [orientedEdgeArmTurn] using hturn
  rcases RS.rho_eq_or_rho_eq_of_cubic hcubic hrotation hbase hne with
    hforward | hreverse
  · exact False.elim (hnot hforward)
  · exact hreverse

/-- The two turn bits at opposite ends of an oriented edge. `true` means
that exactly one of the prescribed arms is selected by the local cyclic
turn. -/
def oppositeArmTransferBit (RS : RotationSystem V E)
    (central entryArm exitArm : RS.D) : Bool :=
  Bool.xor
    (RS.orientedEdgeArmTurn central entryArm)
    (RS.orientedEdgeArmTurn (RS.alpha central) exitArm)

@[simp] theorem oppositeArmTransferBit_eq_true_iff
    (RS : RotationSystem V E) (central entryArm exitArm : RS.D) :
    RS.oppositeArmTransferBit central entryArm exitArm = true ↔
      RS.orientedEdgeArmTurn central entryArm ≠
        RS.orientedEdgeArmTurn (RS.alpha central) exitArm := by
  exact Bool.xor_iff_ne

/-- Opposite arms selected by unequal endpoint turns lie on one of the
two explicit two-step face arcs across the central edge. -/
theorem oppositeArm_phi_sq_alpha_pairing_of_transferBit_eq_true
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (central entryArm exitArm : RS.D)
    (hentryBase : RS.vertOf entryArm = RS.vertOf central)
    (hexitBase : RS.vertOf exitArm = RS.vertOf (RS.alpha central))
    (hentryNe : central ≠ entryArm)
    (hexitNe : RS.alpha central ≠ exitArm)
    (htransfer :
      RS.oppositeArmTransferBit central entryArm exitArm = true) :
    RS.phi (RS.phi (RS.alpha entryArm)) = exitArm ∨
      RS.phi (RS.phi (RS.alpha exitArm)) = entryArm := by
  cases hentryTurn : RS.orientedEdgeArmTurn central entryArm with
  | false =>
      cases hexitTurn :
          RS.orientedEdgeArmTurn (RS.alpha central) exitArm with
      | false =>
          simp [oppositeArmTransferBit, hentryTurn, hexitTurn] at htransfer
      | true =>
          left
          have hentryBack : RS.rho entryArm = central :=
            RS.rho_arm_eq_central_of_orientedEdgeArmTurn_eq_false
              hcubic hrotation central entryArm hentryBase hentryNe
              hentryTurn
          have hexitForward : RS.rho (RS.alpha central) = exitArm :=
            (RS.orientedEdgeArmTurn_eq_true_iff
              (RS.alpha central) exitArm).1 hexitTurn
          calc
            RS.phi (RS.phi (RS.alpha entryArm)) = RS.phi central := by
              congr 1
              rw [RotationSystem.phi_apply, RS.alpha_involutive,
                hentryBack]
            _ = exitArm := by
              rw [RotationSystem.phi_apply, hexitForward]
  | true =>
      cases hexitTurn :
          RS.orientedEdgeArmTurn (RS.alpha central) exitArm with
      | false =>
          right
          have hentryForward : RS.rho central = entryArm :=
            (RS.orientedEdgeArmTurn_eq_true_iff central entryArm).1
              hentryTurn
          have hexitBack : RS.rho exitArm = RS.alpha central :=
            RS.rho_arm_eq_central_of_orientedEdgeArmTurn_eq_false
              hcubic hrotation (RS.alpha central) exitArm hexitBase
              hexitNe hexitTurn
          calc
            RS.phi (RS.phi (RS.alpha exitArm)) =
                RS.phi (RS.alpha central) := by
              congr 1
              rw [RotationSystem.phi_apply, RS.alpha_involutive,
                hexitBack]
            _ = entryArm := by
              rw [RotationSystem.phi_apply, RS.alpha_involutive,
                hentryForward]
      | true =>
          simp [oppositeArmTransferBit, hentryTurn, hexitTurn] at htransfer

/-- Exact-cut labels therefore agree on the paired opposite arms whenever
both possible starting arm edges avoid the cut. -/
theorem labels_eq_of_oppositeArms_of_transferBit_eq_true
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {A : Type*} (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (central entryArm exitArm : RS.D)
    (hentryBase : RS.vertOf entryArm = RS.vertOf central)
    (hexitBase : RS.vertOf exitArm = RS.vertOf (RS.alpha central))
    (hentryNe : central ≠ entryArm)
    (hexitNe : RS.alpha central ≠ exitArm)
    (htransfer :
      RS.oppositeArmTransferBit central entryArm exitArm = true)
    (hentryNotCut : ¬cut (RS.edgeOf entryArm))
    (hexitNotCut : ¬cut (RS.edgeOf exitArm)) :
    labels (dartOrbitFace RS entryArm) =
      labels (dartOrbitFace RS exitArm) := by
  rcases RS.oppositeArm_phi_sq_alpha_pairing_of_transferBit_eq_true
      hcubic hrotation central entryArm exitArm hentryBase hexitBase
      hentryNe hexitNe htransfer with hforward | hreverse
  · exact labels_eq_of_phi_sq_alpha_eq_of_not_cut
      RS labels cut hexact entryArm exitArm hforward hentryNotCut
  · exact (labels_eq_of_phi_sq_alpha_eq_of_not_cut
      RS labels cut hexact exitArm entryArm hreverse hexitNotCut).symm

end RotationSystem

end Mettapedia.GraphTheory.FourColor
