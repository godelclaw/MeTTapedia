import Mettapedia.GraphTheory.FourColor.VertexCodeViablePrefix
import Mettapedia.GraphTheory.FourColor.VertexCodeUnboundedMass

/-!
# The accepting predicate for the direct Count system

The prefix test of `VertexCodeViablePrefix` is deliberately not an accepting
test: every closed run fails its extension clause. This file supplies the
separate terminal predicate, executable from the same four coordinates.

A closed run is accepted when its constructed object is connected and
bridgeless, has exact Euler mass four, and carries a proper Tait colouring.
Each clause is identified with the literal property of the constructed object.
Connectivity is what makes the mass clause a planarity test: mass is four times
the component count minus the Euler defect, so at one component, mass four says
exactly that the defect vanishes. Without the connectivity clause, two
components carrying one handle between them would pass.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeTerminalAcceptance

open ExecutableJointTransfer BoundarySmallCutExecutable
open VertexCodeTrace ExecutableVertexCode VertexCodeViablePrefix
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamMultigraph SerialTangleSmallCutTransfer
open GoertzelV24BoundaryEssentialGluing OpenTangleReplacementEuler
open StarAttachmentComponents BoundarySmallCutViability

theorem vertex_nonempty {r : ℕ} (t : Trace r) : Nonempty t.Vertex := by
  induction t with
  | first _ _ => exact ⟨()⟩
  | step _ _ _ _ => exact ⟨.inr ()⟩

/-- Executable terminal acceptance for the direct Count system. -/
def Accepts (t : Trace 0) : Bool :=
  BoundarySmallCutExecutable.accepts (evaluate t).cuts &&
    decide ((evaluate t).mass = 4) &&
    ExecutableVertexCode.accepts t

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every clause is the literal property of the constructed closed object. -/
theorem accepts_exact (t : Trace 0) :
    Accepts t = true ↔
      ((sideMultigraph (asOpen t.realize)).Connected ∧
          (sideMultigraph (asOpen t.realize)).Bridgeless) ∧
        eulerMass (asOpen t.realize) = 4 ∧
        (∃ c, t.realize.IsTaitColoring c) := by
  rw [Accepts, Bool.and_eq_true, Bool.and_eq_true,
    VertexCodeViability.connected_bridgeless_exact,
    ExecutableVertexCode.accepts_exact, decide_eq_true_eq, mass_exact]
  exact and_assoc

/-- A connected multigraph on a nonempty vertex type has one component. -/
theorem card_component_eq_one {V E : Type*} (G : Multigraph V E) [Nonempty V]
    (h : G.Connected) : Nat.card (Component G) = 1 := by
  have hsub : Subsingleton (Component G) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨u, rfl⟩ := Quotient.exists_rep a
    obtain ⟨v, rfl⟩ := Quotient.exists_rep b
    exact Quotient.sound (h u v)
  have hne : Nonempty (Component G) := ⟨Quotient.mk _ (Classical.arbitrary V)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩

/-- At one component the mass clause is exactly vanishing Euler defect, that
is, planarity of the constructed closed object. -/
theorem mass_four_iff_planar (t : Trace 0)
    (hconn : (sideMultigraph (asOpen t.realize)).Connected) :
    eulerMass (asOpen t.realize) = 4 ↔
      VertexAttachmentTransfer.defect t.realize = 0 := by
  haveI : Nonempty t.Vertex := vertex_nonempty t
  have hc := card_component_eq_one (sideMultigraph (asOpen t.realize)) hconn
  unfold VertexAttachmentTransfer.defect
  rw [hc]
  constructor
  · intro h; rw [h]; norm_num
  · intro h; omega

/-- The accepting predicate, read as a statement about the object. -/
theorem accepts_iff_planar_colouring (t : Trace 0) :
    Accepts t = true ↔
      ((sideMultigraph (asOpen t.realize)).Connected ∧
          (sideMultigraph (asOpen t.realize)).Bridgeless) ∧
        VertexAttachmentTransfer.defect t.realize = 0 ∧
        (∃ c, t.realize.IsTaitColoring c) := by
  rw [accepts_exact]
  constructor
  · rintro ⟨⟨hc, hb⟩, hm, hx⟩
    exact ⟨⟨hc, hb⟩, (mass_four_iff_planar t hc).mp hm, hx⟩
  · rintro ⟨⟨hc, hb⟩, hd, hx⟩
    exact ⟨⟨hc, hb⟩, (mass_four_iff_planar t hc).mpr hd, hx⟩

end

section Controls

set_option Elab.async false
set_option maxRecDepth 16000

open VertexCodeChecks

/-- The planar two-vertex three-edge map is accepted. -/
theorem flat_accepted : Accepts (twoStars true) = true := by decide +kernel

/-- Its handled twin has the same colour support and the same cut data, and is
rejected. Colour acceptance alone cannot separate them; the mass clause can. -/
theorem twisted_rejected : Accepts (twoStars false) = false := by decide +kernel

theorem both_colourable :
    ExecutableVertexCode.accepts (twoStars true) = true ∧
      ExecutableVertexCode.accepts (twoStars false) = true :=
  ⟨VertexCodeChecks.flat_colourable, VertexCodeChecks.twisted_colourable⟩

theorem same_cuts :
    (evaluate (twoStars true)).cuts = (evaluate (twoStars false)).cuts :=
  VertexCodeChecks.same_cut_data

/-- Accumulated closed components are rejected: their mass is four per
component, so only a single component can pass. -/
theorem two_components_rejected :
    Accepts (VertexCodeUnboundedMass.family 1) = false := by decide +kernel

end Controls

end Mettapedia.GraphTheory.FourColor.VertexCodeTerminalAcceptance
