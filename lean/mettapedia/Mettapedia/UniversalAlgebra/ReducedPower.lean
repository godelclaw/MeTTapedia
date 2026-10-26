import Mathlib.ModelTheory.Quotients
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Germ.Basic
import Mettapedia.UniversalAlgebra.EquationSystem
import Mettapedia.UniversalAlgebra.Mathlib.FirstOrder

/-!
# Reduced powers of finitary algebras

Finite arity lets pointwise operations descend through eventual equality for
any filter. Universally quantified equations are preserved; a proper filter
also reflects them through constant representatives. Neither construction nor
preservation requires an ultrafilter or an inhabited base carrier.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra
open Filter FirstOrder
universe u v w
variable {S : Signature.{u}} {Carrier : Type v} {Index : Type w}

namespace Model

abbrev ReducedPowerCarrier (Carrier : Type v) (view : Filter Index) : Type (max v w) :=
  view.Product (fun _ : Index => Carrier)

/-- Pointwise algebraic structure, compatible with the supplied filter quotient. -/
@[reducible] private def reducedPowerPrestructure (model : Model S Carrier)
    (view : Filter Index) :
    S.toFirstOrderLanguage.Prestructure (view.productSetoid (fun _ : Index => Carrier)) :=
  { view.productSetoid (fun _ : Index => Carrier) with
    toStructure :=
      { funMap := fun {n} operation arguments index =>
          @FirstOrder.Language.Structure.funMap S.toFirstOrderLanguage Carrier
            model.toFirstOrderStructure n operation (fun position => arguments position index)
        RelMap := fun {_} relation _ => Empty.elim relation }
    fun_equiv := by
      intro n operation first second equal
      filter_upwards [Filter.eventually_all.2 equal] with index pointwise
      exact congrArg _ (funext pointwise)
    rel_equiv := by intro n relation; exact Empty.elim relation }

/-- The algebra on equivalence classes of coordinate sequences. -/
noncomputable def reducedPower (model : Model S Carrier) (view : Filter Index) :
    Model S (ReducedPowerCarrier Carrier view) := by
  letI := reducedPowerPrestructure model view
  exact Model.ofFirstOrderStructure (inferInstanceAs <|
    S.toFirstOrderLanguage.Structure (Quotient (view.productSetoid (fun _ : Index => Carrier))))

def reducedPowerDiagonal (view : Filter Index) (value : Carrier) :
    ReducedPowerCarrier Carrier view := (fun _ : Index => value : Index → Carrier)

theorem reducedPowerDiagonal_injective (view : Filter Index) [NeBot view] :
    Function.Injective (reducedPowerDiagonal view : Carrier → ReducedPowerCarrier Carrier view) := by
  intro first second equal
  exact Filter.eventually_const.mp (Quotient.eq''.mp equal)

/-- Without properness even distinct constants can become equal. -/
theorem reducedPowerDiagonal_bot (first second : Carrier) :
    reducedPowerDiagonal (⊥ : Filter Index) first = reducedPowerDiagonal ⊥ second :=
  Quotient.sound (by
    change ∀ᶠ _ : Index in (⊥ : Filter Index), first = second
    simp)

/-- The quotient operation agrees with pointwise evaluation of the supplied representatives. -/
theorem reducedPower_interpret (model : Model S Carrier) (view : Filter Index)
    (operation : S.Operation) (arguments : Fin (S.arity operation) → Index → Carrier) :
    (model.reducedPower view).interpret operation
        (fun position => (arguments position : ReducedPowerCarrier Carrier view)) =
      (fun index => model.interpret operation (fun position => arguments position index) :
        Index → Carrier) := by
  exact @FirstOrder.Language.funMap_quotient_mk' S.toFirstOrderLanguage (Index → Carrier)
    (view.productSetoid (fun _ : Index => Carrier)) (reducedPowerPrestructure model view)
    (S.arity operation) ⟨operation, rfl⟩ arguments

end Model

/-- Evaluation commutes with the quotient, retaining the supplied coordinate valuation. -/
theorem Term.evaluate_reducedPower (model : Model S Carrier) (view : Filter Index)
    (valuation : Nat → Index → Carrier) (term : Term S) :
    term.evaluate (model.reducedPower view)
        (fun i => (valuation i : Model.ReducedPowerCarrier Carrier view)) =
      (fun index => term.evaluate model (fun i => valuation i index) : Index → Carrier) := by
  induction term with
  | var _ => rfl
  | op operation arguments ih =>
      simp only [Term.evaluate, ih]
      exact Model.reducedPower_interpret model view operation
        (fun position index => (arguments position).evaluate model (fun i => valuation i index))

/-- Preservation does not require properness; the bottom filter is allowed here. -/
theorem Equation.holds_reducedPower (model : Model S Carrier) (view : Filter Index)
    (equation : Equation S) (holds : equation.Holds model) :
    equation.Holds (model.reducedPower view) := by
  intro valuation
  refine Quotient.induction_on_pi valuation ?_
  intro representatives
  change equation.1.evaluate (model.reducedPower view)
      (fun i => (representatives i : Model.ReducedPowerCarrier Carrier view)) =
    equation.2.evaluate (model.reducedPower view)
      (fun i => (representatives i : Model.ReducedPowerCarrier Carrier view))
  rw [Term.evaluate_reducedPower, Term.evaluate_reducedPower]
  exact Quotient.sound (Filter.Eventually.of_forall fun index =>
    holds (fun i => representatives i index))

/-- Proper filters preserve and reflect equational truth, without full first-order transfer. -/
theorem Equation.holds_reducedPower_iff (model : Model S Carrier) (view : Filter Index)
    [NeBot view] (equation : Equation S) :
    equation.Holds (model.reducedPower view) ↔ equation.Holds model := by
  refine ⟨?_, Equation.holds_reducedPower model view equation⟩
  intro holds valuation
  have equal := holds (fun i => Model.reducedPowerDiagonal view (valuation i))
  change equation.1.evaluate (model.reducedPower view)
      (fun i => ((fun _ : Index => valuation i) : Model.ReducedPowerCarrier Carrier view)) =
    equation.2.evaluate (model.reducedPower view)
      (fun i => ((fun _ : Index => valuation i) : Model.ReducedPowerCarrier Carrier view)) at equal
  rw [Term.evaluate_reducedPower, Term.evaluate_reducedPower] at equal
  exact Filter.eventually_const.mp (Quotient.eq''.mp equal)

theorem Model.satisfies_reducedPower_iff (model : Model S Carrier) (view : Filter Index)
    [NeBot view] (system : EquationSystem S) :
    (model.reducedPower view).Satisfies system ↔ model.Satisfies system := by
  simp only [Model.Satisfies, Equation.holds_reducedPower_iff]

end Mettapedia.UniversalAlgebra
