import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedNativeAdmission
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageProgramUniversality

/-!
# The earned comparison retains the program and proposition

A compatible comparison with an independently chosen original program map
supplies the required program square. The independently
constructed local interpretation therefore receives a complete compatible
program-map isomorphism, retaining its proposition reading and the derived
event comparison. Primitive admission is earned rather than supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization Interpretation
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable {target : QuantifiedImplicativeProgramTheory.{k}}
variable (data : OriginComparison (source := source) (selected := selected) (constructors := constructors) target)

def independentNamed : ConjunctiveProgramTheory.Map (namedTheory source selected constructors)
    target.quantified.conjunctive :=
  RelativeClosedNamedQuantifiedModels.namedMap (model data)
    (RelativeClosedNamedQuantifiedMeaning.predicateReadings source target.quantified selected constructors
      data.original.closed.functor target.implication)
    data.original (Iso.refl _)

def programComparison : ProgramReductionTheoryIsoClasses.MapIso data.named.underlying
    (independentNamed data).underlying :=
  RelativeClosedStructuralImageProgramUniversality.comparison (model data)
    data.original (Iso.refl _) data.named.underlying
    (primitiveImages data) (all_old_primitive_admission data)
    (by
      have square := data.restriction.program
      change data.restriction.comparison.hom.app source.program ≫ data.original.program.hom =
        data.named.functor.map (𝟙 _) ≫ data.named.program.hom at square
      rw [data.named.functor.map_id, Category.id_comp] at square
      change data.restriction.comparison.hom.app source.program ≫
        (𝟙 _ ≫ data.original.program.hom) = data.named.program.hom
      rw [Category.id_comp]
      exact square)

theorem proposition_comparison :
    (programComparison data).comparison.hom.app (predicates source selected constructors).proposition ≫
        (independentNamed data).conjunctive.declarations.proposition.hom =
      data.named.conjunctive.declarations.proposition.hom := by
  let reading := CoherentExtension.target_named_object (model data).nativeModel.meanings
    (model data).nativeModel.realization (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit))
  change (entire_named_comparison data).hom.app
      (namedObject (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit))) ≫ eqToHom reading = _
  have primitive := @RelativeClosedStructuralImageCoherent.comparison_object
    source Index Origins selected constructors target.quantified.programTheory.closed.Obj
    inferInstance inferInstance inferInstance inferInstance
    (model data) data.named.functor
    data.named.conjunctive.finite data.named.conjunctive.closed
    (primitiveImages data) (all_old_primitive_admission data)
    (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit))
  change (entire_named_comparison data).hom.app
      (namedObject (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit))) =
    data.named.conjunctive.declarations.proposition.hom ≫ eqToHom reading.symm at primitive
  rw [primitive, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

def namedComparison : ConjunctiveProgramTheory.MapIso data.named (independentNamed data) where
  conjunctive := {
    comparison := (programComparison data).comparison
    proposition := proposition_comparison data }
  program := (programComparison data).program

theorem entire_named_event_square :
    (namedComparison data).comparison.hom.app
        (namedTheory source selected constructors).programTheory.Event ≫
          (independentNamed data).reduction = data.named.reduction :=
  (namedComparison data).reduction_square

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
