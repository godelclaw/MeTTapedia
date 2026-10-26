import Mettapedia.Languages.HOLLight.DefinitionModelFamily

/-!
# Interpreting a source type parameter by an inhabited carrier

A model family's carrier equation determines the denotation of a source type
variable. Updating its assignment supplies an explicit equivalence with the
chosen carrier, lifted to the model universe. Other parameter assignments are
retained. No constant or type-operator meaning is inferred from its display name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ModelParameterInterpretation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics DefinitionModelFamily DefinitionAdapters

universe u

def domain (carrier : Type u) (point : carrier) : Domain.{u} :=
  ⟨ULift.{u+1,u} carrier, .up point⟩

noncomputable def assignment (prior : Assignment.{u}) (parameter : Name)
    (carrier : Type u) (point : carrier) : Assignment.{u} := by
  classical
  exact Function.update prior parameter (domain carrier point)

theorem assignment_selected (prior : Assignment.{u}) (parameter : Name)
    (carrier : Type u) (point : carrier) :
    assignment prior parameter carrier point parameter = domain carrier point := by
  classical
  exact Function.update_self ..

theorem assignment_other (prior : Assignment.{u}) (parameter name : Name)
    (carrier : Type u) (point : carrier) (different : name ≠ parameter) :
    assignment prior parameter carrier point name = prior name := by
  classical
  exact Function.update_of_ne different ..

variable {initial context : TheoryContext} {theory : HOL.ClosedTheorySet Symbol}
  (family : Family.{u} initial context theory) (other : OperatorFamilies.{u})
  (prior : Assignment.{u}) (parameter : Name) (carrier : Type u) (point : carrier)

theorem parameter_carrier :
    HOL.Ty.denote.{0,u+1}
      (family.model other (assignment prior parameter carrier point)).Carrier (Ty.var parameter).toHOL =
      ULift.{u+1,u} carrier := by
  rw [Ty.toHOL_of_isAtomic (show (Ty.var parameter).IsAtomic from ⟨rfl,rfl⟩)]
  change (family.model other (assignment prior parameter carrier point)).Carrier _ = _
  rw [family.carrier]
  rw [atomicCarrier, evaluate_var, assignment_selected]
  rfl

noncomputable def parameterEquivalence : carrier ≃
    HOL.Ty.denote.{0,u+1}
      (family.model other (assignment prior parameter carrier point)).Carrier (Ty.var parameter).toHOL :=
  Equiv.ulift.symm.trans (Equiv.cast (parameter_carrier family other prior parameter carrier point).symm)

theorem other_parameter_carrier (name : Name) (different : name ≠ parameter) :
    HOL.Ty.denote.{0,u+1}
      (family.model other (assignment prior parameter carrier point)).Carrier (Ty.var name).toHOL =
      (prior name).Carrier := by
  rw [Ty.toHOL_of_isAtomic (show (Ty.var name).IsAtomic from ⟨rfl,rfl⟩)]
  change (family.model other (assignment prior parameter carrier point)).Carrier _ = _
  rw [family.carrier]
  rw [atomicCarrier, evaluate_var, assignment_other prior parameter name carrier point different]

#print axioms parameter_carrier
#print axioms parameterEquivalence
#print axioms other_parameter_carrier

end Mettapedia.Languages.HOLLight.ModelParameterInterpretation
