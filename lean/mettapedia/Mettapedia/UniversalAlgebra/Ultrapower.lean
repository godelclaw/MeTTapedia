import Mathlib.ModelTheory.Ultraproducts
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mettapedia.UniversalAlgebra.ReducedPower
import Mettapedia.UniversalAlgebra.Mathlib.FirstOrder

/-!
# Ultrapowers as an independent specialization of reduced powers

The model is still constructed through Mathlib's algebraic first-order
ultraproduct. Agreement with the general filter construction is proved on
representatives. Equational transfer needs only properness; stronger first-order
transfer belongs to the ultrafilter interface. Non-diagonal elements remain
observable even when every universal equation agrees with the base model.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Filter FirstOrder

universe u v w

variable {S : Signature.{u}} {Carrier : Type v} {Index : Type w}

namespace Model

/-- The carrier of the ultrapower of `Carrier` along `ultrafilter`. -/
abbrev UltrapowerCarrier (Carrier : Type v) {Index : Type w}
    (ultrafilter : Ultrafilter Index) : Type (max v w) :=
  (ultrafilter : Filter Index).Product (fun _ : Index => Carrier)

/-- The universal-algebra model on an ultrapower, obtained from Mathlib's
pointwise ultraproduct structure on the associated algebraic first-order
language. -/
noncomputable def ultrapower {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (ultrafilter : Ultrafilter Index) :
    Model S (UltrapowerCarrier Carrier ultrafilter) := by
  letI : (index : Index) → S.toFirstOrderLanguage.Structure Carrier :=
    fun _ => model.toFirstOrderStructure
  exact Model.ofFirstOrderStructure inferInstance

/-- A base element viewed as a constant element of an ultrapower. -/
def diagonal {Carrier : Type v} {Index : Type w}
    (ultrafilter : Ultrafilter Index) (value : Carrier) :
    UltrapowerCarrier Carrier ultrafilter :=
  (fun _ : Index => value : Index → Carrier)

/-- Operations in the induced ultrapower model act pointwise on chosen
representatives. -/
theorem ultrapower_interpret {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (ultrafilter : Ultrafilter Index)
    (operation : S.Operation)
    (arguments : Fin (S.arity operation) → Index → Carrier) :
    (model.ultrapower ultrafilter).interpret operation
        (fun position => (arguments position : UltrapowerCarrier Carrier ultrafilter)) =
      (fun index => model.interpret operation (fun position => arguments position index) :
        Index → Carrier) := by
  exact @FirstOrder.Language.Ultraproduct.funMap_cast
    Index (fun _ : Index => Carrier) ultrafilter S.toFirstOrderLanguage
    (fun _ : Index => model.toFirstOrderStructure) (S.arity operation)
    (⟨operation, rfl⟩ : S.toFirstOrderLanguage.Functions (S.arity operation))
    arguments

/-- The two independently constructed models agree on the common quotient carrier. -/
theorem ultrapower_eq_reducedPower {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (ultrafilter : Ultrafilter Index) :
    model.ultrapower ultrafilter = model.reducedPower (ultrafilter : Filter Index) := by
  apply congrArg Model.mk
  funext operation arguments
  refine Quotient.induction_on_pi arguments ?_
  intro representatives
  change (model.ultrapower ultrafilter).interpret operation
      (fun i => (representatives i : UltrapowerCarrier Carrier ultrafilter)) =
    (model.reducedPower (ultrafilter : Filter Index)).interpret operation
      (fun i => (representatives i : ReducedPowerCarrier Carrier (ultrafilter : Filter Index)))
  rw [ultrapower_interpret, reducedPower_interpret]

end Model

/-- Evaluation in an ultrapower is pointwise evaluation of representatives.
This is the term-level fragment of Łoś transfer. -/
theorem Term.evaluate_ultrapower (model : Model S Carrier)
    (ultrafilter : Ultrafilter Index) (valuation : Nat → Index → Carrier) :
    ∀ term : Term S,
      term.evaluate (model.ultrapower ultrafilter)
          (fun i => (valuation i : Model.UltrapowerCarrier Carrier ultrafilter)) =
        (fun index => term.evaluate model (fun i => valuation i index) : Index → Carrier) := by
  intro term
  simpa only [Model.ultrapower_eq_reducedPower] using
    Term.evaluate_reducedPower model (ultrafilter : Filter Index) valuation term
/-- A universally quantified equation holds in a model exactly when it holds in
any constant ultrapower of that model, by the independently proved reduced-power comparison. -/
theorem Equation.holds_ultrapower_iff (model : Model S Carrier)
    (ultrafilter : Ultrafilter Index) (equation : Equation S) :
    equation.Holds (model.ultrapower ultrafilter) ↔ equation.Holds model := by
  simpa only [Model.ultrapower_eq_reducedPower] using
    Equation.holds_reducedPower_iff model (ultrafilter : Filter Index) equation
/-- Satisfaction of a finite occurrence-bearing equation system is invariant
under constant ultrapowers. -/
theorem Model.satisfies_ultrapower_iff (model : Model S Carrier)
    (ultrafilter : Ultrafilter Index) (system : EquationSystem S) :
    (model.ultrapower ultrafilter).Satisfies system ↔ model.Satisfies system := by
  simpa only [Model.ultrapower_eq_reducedPower] using
    Model.satisfies_reducedPower_iff model (ultrafilter : Filter Index) system

namespace UltrapowerBoundary

/-- The class of the identity sequence in the natural-number ultrapower along
the cofinite-extending ultrafilter. -/
noncomputable def growingElement :
    Model.UltrapowerCarrier Nat (Filter.hyperfilter Nat) :=
  (fun index : Nat => index : Nat → Nat)

/-- The identity sequence is not equivalent to any constant sequence.  Thus
equational invariance does not say that the diagonal map exhausts an
ultrapower. -/
theorem growingElement_ne_diagonal (value : Nat) :
    growingElement ≠ Model.diagonal (Filter.hyperfilter Nat) value := by
  intro equalClasses
  have singletonMem : {index : Nat | index = value} ∈ Filter.hyperfilter Nat :=
    Quotient.eq''.mp equalClasses
  exact (Set.finite_singleton value).notMem_hyperfilter
    (by simpa only [Set.ofPred_eq_eq_singleton] using singletonMem)

/-- Negative canary: the diagonal embedding into this ultrapower is not
surjective. -/
theorem diagonal_not_surjective :
    ¬ Function.Surjective
      (Model.diagonal (Filter.hyperfilter Nat) :
        Nat → Model.UltrapowerCarrier Nat (Filter.hyperfilter Nat)) := by
  intro diagonalSurjective
  obtain ⟨value, valueMaps⟩ := diagonalSurjective growingElement
  exact growingElement_ne_diagonal value valueMaps.symm

end UltrapowerBoundary

end Mettapedia.UniversalAlgebra
