import Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated
import Mettapedia.OSLF.NativeTypes.Semantics.Structural.Controls

open Mettapedia.OSLF.Framework

/-!
# Ordered structural decision controls

Both lambda inputs have the authored arrow carrier and abstraction shape.
The generated constructor test accepts only the selected ordered input
predicate. A bound variable with the arrow carrier is rejected as a Lam
argument by the declaration's actual representation requirement.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Structural.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated
open Mettapedia.OSLF.NativeTypes.Semantics.Structural.Controls.Lambda (index binder program)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated term)

theorem empty_equations : generated.plan.equations = [] := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
  rfl

def sortMask (_ : List TypeExpr) (_ : TypeExpr) : ModalHypercube.HSort → Pattern → Bool
  | .star, .bvar _ => false
  | .star, _ => true
  | .box, .bvar _ => true
  | .box, _ => false

def selectedInput (_ : Fin (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration generated index).params.length)
    (input : Pattern) : Bool := input == binder

def constructorTest := localTest generated empty_equations sortMask [] index selectedInput

def otherBinder : Pattern := .lambda none program
def otherProgram : Pattern := .apply "Lam" [otherBinder]

theorem both_arguments_have_the_authored_carrier :
    HasType generated.snapshot.language generated.snapshot.free [] binder (.arrow term term) ∧
    HasType generated.snapshot.language generated.snapshot.free [] otherBinder (.arrow term term) := by
  constructor
  · exact .lambda (.bvar rfl)
  · exact checkHasType_sound (by decide +kernel)

theorem positive_ordered_input : constructorTest.evaluate 0 program = some true := by
  decide +kernel

theorem negative_other_typed_input : constructorTest.evaluate 0 otherProgram = some false := by
  decide +kernel

theorem native_positive_certificate : constructorTest.predicate program :=
  constructorTest.positive 0 program positive_ordered_input

theorem native_negative_certificate : ¬ constructorTest.predicate otherProgram :=
  constructorTest.negative 0 otherProgram negative_other_typed_input

theorem actual_generated_constructor_positive :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (booleanModel generated sortMask []) index
      (booleanInputs generated [] index selectedInput)).meaning program :=
  (test_generated_comparison (booleanModel_equations empty_equations sortMask)
    (localBackend generated [] empty_equations) index (booleanInputs generated [] index selectedInput)
    (booleanInputs_interpreted empty_equations [] index selectedInput)
    (booleanEffective generated sortMask [] index selectedInput) program).mp native_positive_certificate

theorem actual_generated_constructor_negative :
    ¬ (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (booleanModel generated sortMask []) index
      (booleanInputs generated [] index selectedInput)).meaning otherProgram := by
  intro holds
  exact native_negative_certificate
    ((test_generated_comparison (booleanModel_equations empty_equations sortMask)
      (localBackend generated [] empty_equations) index (booleanInputs generated [] index selectedInput)
      (booleanInputs_interpreted empty_equations [] index selectedInput)
      (booleanEffective generated sortMask [] index selectedInput) otherProgram).mpr holds)

def variableTest := localTest generated empty_equations sortMask [.arrow term term] index
  (fun _ _ => true)

theorem arrow_variable_refused_as_binder :
    variableTest.evaluate 0 (.apply "Lam" [.bvar 0]) = some false := by
  decide +kernel

theorem executable_both_sort_domains :
    (booleanModel generated sortMask []).sortDomain term .star program ∧
      (booleanModel generated sortMask [term]).sortDomain term .box (.bvar 0) ∧
      ¬ (booleanModel generated sortMask [term]).sortDomain term .star (.bvar 0) := by
  dsimp only [booleanModel]
  decide +kernel

end Mettapedia.OSLF.NativeTypes.Decision.Structural.Controls
