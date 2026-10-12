import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramStructuralAction
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageControls
import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMapControls
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject

/-!
# Structural action with two inputs, a changed program reading and origins

The existing generated constructor sends its supplied children to twice
the first plus four times the second, then one. An independently authored
target constructor exchanges program values zero and one. The complete
structural image square relates the generated name to that independent
target, retaining both child predicates and every changing parameter.
The same independently authored constructor supplies the local square for
the actual quantified program extension, so its complete structural action
uses the program map already carrying the supplied reduction relation.

Distinct authored constructors can have equal image predicates. Explicit
origin/argument receipts remain distinct, so an image alone cannot recover
the origin needed by an occurrence-sensitive consumer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.QuantifiedStructuralActionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory ElementaryTypePredicateReadout
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open InternalPredicateConstructorMaps PositionedModalOutgoingComparison

abbrev native := HigherOrderInternalPredicateQuantifiedObject.operations doctrine
abbrev mapping := InternalPredicateQuantifiedObject.Map.identity native

def programComparison : Nat ≅ Nat := (Equiv.swap (0 : Nat) 1).toIso

def targetConstructor : Nat × Nat ⟶ Nat := TypeCat.ofHom fun pair =>
  Equiv.swap (0 : Nat) 1 (2 * pair.1 + 4 * pair.2 + 1)

theorem local_constructor_square :
    mapping.functor.map RelativeClosedStructuralImageControls.constructor ≫ programComparison.hom =
      (Iso.refl (Nat × Nat)).hom ≫ targetConstructor := by
  ext pair
  rfl

def targetImage : power doctrine (Nat × Nat) ⟶ power doctrine Nat :=
  existsOperation doctrine targetConstructor

theorem complete_independent_image_action :
    RelativeClosedStructuralImageControls.image ≫
        (powerReindexIso native.predicates programComparison).hom = targetImage := by
  rw [RelativeClosedStructuralImageControls.image_complete]
  have earned := complete_independent_square mapping
    RelativeClosedStructuralImageControls.constructor (Iso.refl (Nat × Nat))
    programComparison targetConstructor local_constructor_square
  simp only [comparedPower, InternalPredicateQuantifiedObject.Map.powerComparison_identity,
    Iso.trans_hom, Iso.refl_hom, powerReindexIso, Iso.refl_inv] at earned
  change ((native.existential RelativeClosedStructuralImageControls.constructor).operation ≫
      𝟙 (InternalPredicateFunctionObject.power native.predicates Nat)) ≫
        InternalPredicateQuantifier.precomposition native.predicates programComparison.inv =
    (𝟙 (InternalPredicateFunctionObject.power native.predicates (Nat × Nat)) ≫
      InternalPredicateQuantifier.precomposition native.predicates (𝟙 (Nat × Nat))) ≫
        (native.existential targetConstructor).operation at earned
  simp only [precomposition_identity, Category.comp_id, Category.id_comp] at earned
  exact earned

def output (first second : Nat → Nat) : Subobject (Nat ⊗ Nat) :=
  family doctrine (RelativeClosedStructuralImageControls.inputs first second ≫ targetImage)

theorem complete_family_reading (first second : Nat → Nat) : output first second =
    doctrine.reindex (programComparison.inv ▷ Nat) (RelativeClosedStructuralImageControls.output first second) := by
  unfold output
  rw [← complete_independent_image_action, ← Category.assoc]
  exact precomposition_supplied doctrine programComparison.inv _

theorem output_read (first second : Nat → Nat) (result parameter : Nat) :
    Contains (output first second) (result, parameter) ↔
      result = Equiv.swap (0 : Nat) 1 (2 * first parameter + 4 * second parameter + 1) := by
  rw [complete_family_reading, contains_reindex]
  change Contains (RelativeClosedStructuralImageControls.output first second)
      ((Equiv.swap (0 : Nat) 1).symm result, parameter) ↔ _
  rw [RelativeClosedStructuralImageControls.output_read]
  exact (Equiv.swap (0 : Nat) 1).symm_apply_eq

theorem renamed_image_retains_both_children :
    Contains (output (fun _ => 0) (fun _ => 0)) (0, 0) ∧
      ¬ Contains (output (fun _ => 1) (fun _ => 0)) (0, 0) ∧
        ¬ Contains (output (fun _ => 0) (fun _ => 1)) (0, 0) := by
  refine ⟨(output_read _ _ 0 0).mpr (Equiv.swap_apply_right (0 : Nat) 1).symm, ?_, ?_⟩
  · intro held
    exact (by decide : (0 : Nat) ≠ Equiv.swap (0 : Nat) 1 3) ((output_read _ _ 0 0).mp held)
  · intro held
    exact (by decide : (0 : Nat) ≠ Equiv.swap (0 : Nat) 1 5) ((output_read _ _ 0 0).mp held)

theorem outgoing_program_comparison_is_required :
    targetImage ≠ RelativeClosedStructuralImageControls.image := by
  intro same
  have newMember := renamed_image_retains_both_children.1
  have oldMember : Contains (RelativeClosedStructuralImageControls.output (fun _ => 0) (fun _ => 0)) (0, 0) :=
    (congrArg (fun arrow : power doctrine (Nat × Nat) ⟶ power doctrine Nat =>
      Contains (family doctrine (RelativeClosedStructuralImageControls.inputs (fun _ => 0) (fun _ => 0) ≫ arrow))
        (0, 0)) same).mp newMember
  exact (by decide : (0 : Nat) ≠ 1) ((RelativeClosedStructuralImageControls.output_read _ _ 0 0).mp oldMember)

theorem future_read (result parameter : Nat) :
    Contains (family doctrine
      ((RelativeClosedStructuralImageControls.future ≫
        RelativeClosedStructuralImageControls.inputs id (fun _ => 0)) ≫ targetImage)) (result, parameter) ↔
      result = Equiv.swap (0 : Nat) 1 (2 * (parameter + 1) + 1) := by
  have reading := (congrArg (family doctrine)
    (Category.assoc RelativeClosedStructuralImageControls.future
      (RelativeClosedStructuralImageControls.inputs id (fun _ => 0)) targetImage)).trans
        (family_substitution doctrine RelativeClosedStructuralImageControls.future _)
  rw [reading, contains_reindex]
  change Contains (output id (fun _ => 0)) (result, parameter + 1) ↔ _
  rw [output_read]
  simp only [id_eq, Nat.mul_zero, Nat.add_zero]

theorem actual_future_changes_the_result : Contains (output id (fun _ => 0)) (0, 0) ∧
    ¬ Contains (family doctrine
      ((RelativeClosedStructuralImageControls.future ≫
        RelativeClosedStructuralImageControls.inputs id (fun _ => 0)) ≫ targetImage)) (0, 0) := by
  refine ⟨(output_read id (fun _ => 0) 0 0).mpr (Equiv.swap_apply_right (0 : Nat) 1).symm, ?_⟩
  intro held
  exact (by decide : (0 : Nat) ≠ Equiv.swap (0 : Nat) 1 3) ((future_read 0 0).mp held)

def alternateConstructor : Nat × Nat ⟶ Nat := TypeCat.ofHom fun pair =>
  4 * pair.2 + 2 * pair.1 + 1

theorem independently_authored_constructor_equation :
    RelativeClosedStructuralImageControls.constructor = alternateConstructor := by
  ext pair
  exact congrArg (fun number : Nat => number + 1) (Nat.add_comm (2 * pair.1) (4 * pair.2))

theorem equal_constructor_images_do_not_separate_origins :
    (native.existential RelativeClosedStructuralImageControls.constructor).operation =
      (native.existential alternateConstructor).operation :=
  congrArg (fun arrow : Nat × Nat ⟶ Nat => (native.existential arrow).operation)
    independently_authored_constructor_equation

def constructors : Bool → (Nat × Nat ⟶ Nat)
  | false => RelativeClosedStructuralImageControls.constructor
  | true => alternateConstructor

structure Receipt where
  origin : Bool
  arguments : Nat × Nat
  realizes : constructors origin arguments = (17 : Nat)

def firstReceipt : Receipt := ⟨false, (2, 3), rfl⟩
def secondReceipt : Receipt := ⟨true, (2, 3), rfl⟩

theorem distinct_origins_with_the_same_realized_value : firstReceipt ≠ secondReceipt := by
  intro same
  exact Bool.false_ne_true (congrArg Receipt.origin same)

theorem both_receipts_retain_actual_constructor_arguments :
    constructors firstReceipt.origin firstReceipt.arguments = (17 : Nat) ∧
      constructors secondReceipt.origin secondReceipt.arguments = (17 : Nat) :=
  ⟨firstReceipt.realizes, secondReceipt.realizes⟩

namespace Generated

open RelativeClosedPositionedModalControlData
open RelativeClosedQuantifiedProgramMaps

abbrev supplied := RelativeClosedQuantifiedProgramMapControls.supplied
abbrev operations := RelativeClosedQuantifiedProgramMapControls.nativeOperations
abbrev arguments := upward.obj (Nat × Nat)
abbrev included := RelativeClosedQuantifiedRuleFrames.inclusion theory operations.predicates operations.laws
abbrev generated := RelativeClosedQuantifiedRuleFrames.generatedTheory theory operations.predicates operations.laws

def constructor : arguments ⟶ program :=
  upward.map RelativeClosedStructuralImageControls.constructor

def independentlySuppliedConstructor : arguments ⟶ program := upward.map targetConstructor

def argumentComparison : supplied.extension.functor.obj
    (included.functor.obj arguments) ≅ arguments :=
  supplied.baseComparison.comparison.app arguments

theorem complete_independent_constructor_reading :
    supplied.declarations.functor.map constructor ≫ supplied.program.hom =
      independentlySuppliedConstructor := by
  change upward.map RelativeClosedStructuralImageControls.constructor ≫
    upward.map programComparison.hom = upward.map targetConstructor
  rw [← upward.map_comp]
  exact congrArg upward.map (by ext pair; rfl)

theorem local_generated_constructor_square :
    supplied.extension.functor.map (included.functor.map constructor) ≫
        supplied.extendedProgram.hom = argumentComparison.hom ≫ independentlySuppliedConstructor := by
  change supplied.extension.functor.map (included.functor.map constructor) ≫
      (supplied.baseComparison.comparison.hom.app program ≫ supplied.program.hom) = _
  calc
    _ = (supplied.extension.functor.map (included.functor.map constructor) ≫
        supplied.baseComparison.comparison.hom.app program) ≫ supplied.program.hom :=
      (Category.assoc _ _ _).symm
    _ = (supplied.baseComparison.comparison.hom.app arguments ≫
        supplied.declarations.functor.map constructor) ≫ supplied.program.hom :=
      congrArg (fun arrow => arrow ≫ supplied.program.hom)
        (supplied.baseComparison.comparison.hom.naturality constructor)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun arrow => argumentComparison.hom ≫ arrow) complete_independent_constructor_reading)

theorem complete_generated_structural_image_square :
    supplied.predicateComparison.quantified.functor.map
        ((RelativeClosedQuantified.freeObject
          (RelativeClosedQuantifiedRuleFrames.conjunctive theory operations.predicates operations.laws)).operations.existential
            (included.functor.map constructor)).operation ≫
        (comparedPower supplied.predicateComparison.quantified
          (included.functor.obj program) supplied.extendedProgram).hom =
      (comparedPower supplied.predicateComparison.quantified
          (included.functor.obj arguments) argumentComparison).hom ≫
        (operations.existential independentlySuppliedConstructor).operation :=
  complete_independent_square supplied.predicateComparison.quantified (included.functor.map constructor)
    argumentComparison supplied.extendedProgram independentlySuppliedConstructor local_generated_constructor_square

theorem complete_generated_future_family {first second : generated.closed.Obj}
    (future : first ⟶ second)
    (predicate : second ⟶ InternalPredicateFunctionObject.power
      (RelativeClosedQuantified.freeObject
        (RelativeClosedQuantifiedRuleFrames.conjunctive theory operations.predicates operations.laws)).operations.predicates
          (included.functor.obj arguments)) :
    supplied.predicateComparison.quantified.functor.map ((future ≫ predicate) ≫
        ((RelativeClosedQuantified.freeObject
          (RelativeClosedQuantifiedRuleFrames.conjunctive theory operations.predicates operations.laws)).operations.existential
            (included.functor.map constructor)).operation) ≫
        (comparedPower supplied.predicateComparison.quantified
          (included.functor.obj program) supplied.extendedProgram).hom =
      supplied.predicateComparison.quantified.functor.map future ≫
        ((supplied.predicateComparison.quantified.functor.map predicate ≫
          (comparedPower supplied.predicateComparison.quantified
            (included.functor.obj arguments) argumentComparison).hom) ≫
              (operations.existential independentlySuppliedConstructor).operation) :=
  complete_future_family supplied.predicateComparison.quantified (included.functor.map constructor)
    argumentComparison supplied.extendedProgram independentlySuppliedConstructor
      local_generated_constructor_square future predicate

end Generated

end Mettapedia.GSLT.Core.QuantifiedStructuralActionControls
