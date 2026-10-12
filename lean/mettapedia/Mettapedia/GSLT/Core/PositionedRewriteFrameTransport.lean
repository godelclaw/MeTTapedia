import Mettapedia.GSLT.Core.PositionedRewriteModal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Rule frames and supplied firing instances under closed theory maps

The transported frame retains its complete assignment, assay and instance
objects. Finite-limit preservation earns its actual pullback square. The
chosen pullback's universal property compares supplied instances; composing
with the transported authored action gives the complete event reading.
The outgoing comparison includes the actual program isomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewriteModal.Frame

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory

universe u v
variable {first second : Theory.{u,v}}
variable (mapping : Map first second) {rule : Rule first} (frame : Frame rule)

def transport : Frame (Rule.transport mapping rule) where
  assignments := mapping.closed.functor.obj frame.assignments
  carrier := mapping.closed.functor.obj frame.carrier
  assay := mapping.closed.functor.obj frame.assay
  forget := mapping.closed.functor.map frame.forget
  focus := mapping.closed.functor.map frame.focus
  instantiate := mapping.closed.functor.map frame.instantiate
  hole := mapping.closed.functor.map frame.hole
  plug := mapping.closed.functor.map frame.plug ≫ mapping.program.hom
  square := mapping.closed.functor.map_isPullback frame.square
  source := by
    change mapping.closed.functor.map frame.instantiate ≫
      (mapping.closed.functor.map frame.plug ≫ mapping.program.hom) =
        mapping.closed.functor.map rule.left ≫ mapping.program.hom
    rw [← Category.assoc, ← mapping.closed.functor.map_comp, frame.source]

variable {context : first.closed.Obj}
variable (assignment : context ⟶ frame.assignments) (assay : context ⟶ frame.assay)
variable (compatible : assignment ≫ frame.focus = assay ≫ frame.hole)

include compatible in
theorem transported_match :
    mapping.closed.functor.map assignment ≫ (transport mapping frame).focus =
      mapping.closed.functor.map assay ≫ (transport mapping frame).hole :=
  (mapping.closed.functor.map_comp assignment frame.focus).symm.trans
    ((congrArg mapping.closed.functor.map compatible).trans
      (mapping.closed.functor.map_comp assay frame.hole))

theorem suppliedInstance_transport :
    (transport mapping frame).suppliedInstance (mapping.closed.functor.map assignment)
        (mapping.closed.functor.map assay) (transported_match mapping frame assignment assay compatible) =
      mapping.closed.functor.map (frame.suppliedInstance assignment assay compatible) := by
  apply (transport mapping frame).square.hom_ext
  · have reading := (mapping.closed.functor.map_comp
      (frame.suppliedInstance assignment assay compatible) frame.forget).symm.trans
        (congrArg mapping.closed.functor.map (frame.suppliedInstance_assignment assignment assay compatible))
    exact ((transport mapping frame).suppliedInstance_assignment _ _ _).trans reading.symm
  · have reading := (mapping.closed.functor.map_comp
      (frame.suppliedInstance assignment assay compatible) frame.instantiate).symm.trans
        (congrArg mapping.closed.functor.map (frame.suppliedInstance_assay assignment assay compatible))
    exact ((transport mapping frame).suppliedInstance_assay _ _ _).trans reading.symm

theorem step_transport :
    (transport mapping frame).step (mapping.closed.functor.map assignment)
        (mapping.closed.functor.map assay) (transported_match mapping frame assignment assay compatible) =
      mapping.closed.functor.map (frame.step assignment assay compatible) ≫ mapping.reduction := by
  change (transport mapping frame).suppliedInstance (mapping.closed.functor.map assignment)
    (mapping.closed.functor.map assay) (transported_match mapping frame assignment assay compatible) ≫
      (mapping.closed.functor.map rule.action ≫ mapping.reduction) =
    mapping.closed.functor.map (frame.suppliedInstance assignment assay compatible ≫ rule.action) ≫ mapping.reduction
  rw [suppliedInstance_transport]
  change mapping.closed.functor.map (frame.suppliedInstance assignment assay compatible) ≫
    (mapping.closed.functor.map rule.action ≫ mapping.reduction) = _
  rw [← Category.assoc, ← mapping.closed.functor.map_comp]

theorem step_transport_future {future : first.closed.Obj} (incoming : future ⟶ context) :
    (transport mapping frame).step
        (mapping.closed.functor.map (incoming ≫ assignment))
        (mapping.closed.functor.map (incoming ≫ assay))
        (transported_match mapping frame (incoming ≫ assignment) (incoming ≫ assay)
          (frame.precomposed_match assignment assay compatible incoming)) =
      mapping.closed.functor.map incoming ≫
        (mapping.closed.functor.map (frame.step assignment assay compatible) ≫ mapping.reduction) := by
  rw [step_transport mapping frame (incoming ≫ assignment) (incoming ≫ assay)
    (frame.precomposed_match assignment assay compatible incoming), frame.step_precompose,
    mapping.closed.functor.map_comp, Category.assoc]

def outgoingComparison : mapping.closed.functor.obj (frame.assay ⨯ first.program) ≅
    (transport mapping frame).assay ⨯ second.program :=
  asIso (prodComparison mapping.closed.functor frame.assay first.program) ≪≫
    prod.mapIso (Iso.refl _) mapping.program

theorem outgoingComparison_first :
    (outgoingComparison mapping frame).hom ≫ prod.fst =
      mapping.closed.functor.map (prod.fst : frame.assay ⨯ first.program ⟶ frame.assay) := by
  change (asIso (prodComparison mapping.closed.functor frame.assay first.program) ≪≫
    prod.mapIso (Iso.refl (mapping.closed.functor.obj frame.assay)) mapping.program).hom ≫
    (prod.fst : mapping.closed.functor.obj frame.assay ⨯ second.program ⟶ _) = _
  rw [Iso.trans_hom, asIso_hom, prod.mapIso_hom, Category.assoc, prod.map_fst]
  change prodComparison mapping.closed.functor frame.assay first.program ≫ (prod.fst ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact prodComparison_fst _ _ _

theorem outgoingComparison_second :
    (outgoingComparison mapping frame).hom ≫ prod.snd =
      mapping.closed.functor.map (prod.snd : frame.assay ⨯ first.program ⟶ first.program) ≫ mapping.program.hom := by
  change (asIso (prodComparison mapping.closed.functor frame.assay first.program) ≪≫
    prod.mapIso (Iso.refl (mapping.closed.functor.obj frame.assay)) mapping.program).hom ≫
    (prod.snd : mapping.closed.functor.obj frame.assay ⨯ second.program ⟶ _) = _
  rw [Iso.trans_hom, asIso_hom, prod.mapIso_hom, Category.assoc, prod.map_snd,
    ← Category.assoc, prodComparison_snd]

theorem outgoing_transport :
    mapping.closed.functor.map frame.outgoing ≫ (outgoingComparison mapping frame).hom =
      (transport mapping frame).outgoing := by
  change mapping.closed.functor.map frame.outgoing ≫ (outgoingComparison mapping frame).hom =
    prod.lift (mapping.closed.functor.map frame.instantiate)
      (mapping.closed.functor.map rule.right ≫ mapping.program.hom)
  apply prod.hom_ext
  · rw [Category.assoc, outgoingComparison_first]
    change mapping.closed.functor.map frame.outgoing ≫
      mapping.closed.functor.map (prod.fst : frame.assay ⨯ first.program ⟶ _) = _
    rw [← mapping.closed.functor.map_comp]
    change mapping.closed.functor.map (prod.lift frame.instantiate rule.right ≫ prod.fst) = _
    exact (congrArg mapping.closed.functor.map (prod.lift_fst frame.instantiate rule.right)).trans
      (prod.lift_fst _ _).symm
  · rw [Category.assoc, outgoingComparison_second, ← Category.assoc, ← mapping.closed.functor.map_comp]
    change mapping.closed.functor.map (prod.lift frame.instantiate rule.right ≫ prod.snd) ≫
      mapping.program.hom = _
    exact (congrArg (fun arrow => mapping.closed.functor.map arrow ≫ mapping.program.hom)
      (prod.lift_snd frame.instantiate rule.right)).trans (prod.lift_snd _ _).symm

end Mettapedia.GSLT.Core.PositionedRewriteModal.Frame
