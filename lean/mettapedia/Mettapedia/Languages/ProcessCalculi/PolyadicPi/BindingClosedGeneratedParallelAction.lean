import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalClosure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedStructuralLaws
import Mettapedia.CategoryTheory.RelativeClosedCartesianActionPresentation
import Mettapedia.CategoryTheory.InternalCategoryFiniteLimitTransport

/-!
# The complete parallel-edge action in the generated pi guest

Parallel edge closure is the previously independently declared generator.
Two additional typed equations give its entire edge object the unit and
associativity laws of the process monoid action. The old all-arity operations,
communication declarations and complete category survive the finite-limit
and closed inclusion.

These equations concern generated edge classes. Ordered firing occurrences
and execution histories are separate data; they are not identified by this
presentation extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedParallelAction

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory

universe k w z

abbrev Original := BindingClosedGeneratedOperationalModel.Target.{k}
abbrev oldCategory := BindingClosedGeneratedOperationalClosure.category.{k}
abbrev oldOrdinary := BindingClosedGeneratedOperationalClosure.ordinary.{k}

def originalOperations : CartesianMonoidAction.Data Original.{k} where
  edge := oldCategory.edge
  scalar := oldOrdinary.processes
  zero := oldOrdinary.empty
  merge := oldOrdinary.parallel
  act := BindingClosedGeneratedOperationalClosure.parallel

theorem original_scalar_laws : CartesianMonoidAction.ScalarLaws originalOperations.{k} where
  unit := BindingClosedStructuralLaws.parallel_unit
    BindingClosedGeneratedOperationalModel.binding
    BindingClosedGeneratedOperationalModel.structural_schemas (𝟙 oldOrdinary.processes)
  associativity := BindingClosedStructuralLaws.parallel_assoc
    BindingClosedGeneratedOperationalModel.binding
    BindingClosedGeneratedOperationalModel.structural_schemas
    (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)
  commutativity := by
    have whole := BindingClosedStructuralLaws.parallel_comm
      BindingClosedGeneratedOperationalModel.binding
      BindingClosedGeneratedOperationalModel.structural_schemas
      (fst oldOrdinary.processes oldOrdinary.processes) (snd oldOrdinary.processes oldOrdinary.processes)
    change lift (fst oldOrdinary.processes oldOrdinary.processes)
      (snd oldOrdinary.processes oldOrdinary.processes) ≫ oldOrdinary.parallel =
        lift (snd oldOrdinary.processes oldOrdinary.processes)
          (fst oldOrdinary.processes oldOrdinary.processes) ≫ oldOrdinary.parallel at whole
    rw [lift_fst_snd, Category.id_comp] at whole
    exact whole

abbrev originalSignature := BindingClosedGeneratedOperational.signature.{k}
abbrev declaration := CartesianActionPresentation.declaration originalSignature originalOperations.{k}
abbrev signature := CartesianActionPresentation.extended originalSignature originalOperations.{k}
abbrev inclusion := CartesianActionPresentation.inclusion originalSignature originalOperations.{k}
abbrev Guest := Object signature.{k}

def headers : HeaderFormation signature.{k} :=
  CartesianActionPresentation.headers originalSignature originalOperations BindingClosedGeneratedOperational.headers

abbrev theory := CartesianActionPresentation.theory originalSignature originalOperations.{k}
abbrev theoryMap := CartesianActionPresentation.theoryMap originalSignature originalOperations.{k}
abbrev operations := CartesianActionPresentation.operations originalSignature originalOperations.{k}

theorem action_laws : CartesianMonoidAction.Laws operations.{k} :=
  CartesianActionPresentation.action_laws originalSignature originalOperations

theorem scalar_laws : CartesianMonoidAction.ScalarLaws operations.{k} := by
  rw [operations, CartesianActionPresentation.operations, ← CartesianActionPresentation.map_eq_signatureData]
  exact CartesianMonoidAction.map_scalar_laws inclusion.functor originalOperations original_scalar_laws

def category : InternalCategory Guest.{k} :=
  InternalCategoryFiniteLimitTransport.category inclusion.functor oldCategory

def processComparison : operations.{k}.scalar ≅ category.vertex :=
  inclusion.functor.mapIso BindingClosedGeneratedOperationalModel.processComparison

def rightParallel : operations.{k}.scalar ⊗ operations.edge ⟶ operations.edge :=
  lift (snd _ _) (fst _ _) ≫ operations.act

theorem parallel_unit {stage : Guest.{k}} (edge : stage ⟶ operations.edge) :
    CartesianMonoidAction.apply operations edge (CartesianMonoidAction.neutral operations stage) = edge :=
  CartesianMonoidAction.apply_zero operations action_laws edge

theorem parallel_associativity {stage : Guest.{k}} (edge : stage ⟶ operations.edge)
    (first second : stage ⟶ operations.scalar) :
    CartesianMonoidAction.apply operations (CartesianMonoidAction.apply operations edge first) second =
      CartesianMonoidAction.apply operations edge (CartesianMonoidAction.product operations first second) :=
  CartesianMonoidAction.apply_associativity operations action_laws edge first second

theorem parallel_frame_exchange {stage : Guest.{k}} (edge : stage ⟶ operations.edge)
    (first second : stage ⟶ operations.scalar) :
    CartesianMonoidAction.apply operations (CartesianMonoidAction.apply operations edge first) second =
      CartesianMonoidAction.apply operations (CartesianMonoidAction.apply operations edge second) first :=
  CartesianMonoidAction.frame_exchange operations action_laws scalar_laws edge first second

theorem right_parallel_readout {stage : Guest.{k}} (frame : stage ⟶ operations.scalar)
    (edge : stage ⟶ operations.edge) :
    lift frame edge ≫ rightParallel = CartesianMonoidAction.apply operations edge frame := by
  simp only [rightParallel, CartesianMonoidAction.apply, comp_lift_assoc, lift_fst, lift_snd]

theorem parallel_source : operations.{k}.act ≫ category.source =
    lift (fst operations.edge operations.scalar ≫ category.source ≫ processComparison.inv)
      (snd operations.edge operations.scalar) ≫ operations.merge ≫ processComparison.hom := by
  have whole := congrArg inclusion.functor.map BindingClosedGeneratedOperationalClosure.parallel_source
  simp only [inclusion.functor.map_comp, inclusion.functor_lift] at whole
  exact whole

theorem parallel_target : operations.{k}.act ≫ category.target =
    lift (fst operations.edge operations.scalar ≫ category.target ≫ processComparison.inv)
      (snd operations.edge operations.scalar) ≫ operations.merge ≫ processComparison.hom := by
  have whole := congrArg inclusion.functor.map BindingClosedGeneratedOperationalClosure.parallel_target
  simp only [inclusion.functor.map_comp, inclusion.functor_lift] at whole
  exact whole

theorem admission_iff_action {D : Type w} [Category.{z} D]
    [CartesianMonoidalCategory D] [MonoidalClosed D] [_root_.CategoryTheory.Limits.HasFiniteLimits D]
    (meanings : Interpretation.Assignment _ _ D)
    (realized : Interpretation.Realization originalSignature.{k} meanings) :
    Interpretation.Realization signature (EquationExtension.extendAssignment
        (Index := ULift.{k} CartesianActionPresentation.Law) meanings) ↔
      CartesianMonoidAction.Laws
        (CartesianActionPresentation.modelOperations originalSignature originalOperations meanings realized) :=
  CartesianActionPresentation.admission_iff_action originalSignature originalOperations meanings realized

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedParallelAction
