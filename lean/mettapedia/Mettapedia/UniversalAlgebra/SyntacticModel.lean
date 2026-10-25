import Mathlib.CategoryTheory.Types.Basic
import Mettapedia.UniversalAlgebra.SyntacticFunctor

/-!
# Models as evaluation functors on the syntactic category

A model satisfying an equation system evaluates each finite context
as a finite power of its carrier and each syntactic arrow as simultaneous term
evaluation.  The resulting functor preserves the displayed terminal and
binary-product operations by explicit equations.

Finite evaluation uses only the declared context. Empty carriers and nullary
operations are handled by the same substitution and soundness laws.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open CategoryTheory

universe u v w

variable {S : Signature.{u}}

namespace BoundedTermTuple

/-- Evaluate every component of a bounded tuple under a finite valuation. -/
def evaluate {Carrier : Type v} (model : Model S Carrier)
    {input output : Nat} (tuple : BoundedTermTuple S input output) :
    (Fin input → Carrier) → (Fin output → Carrier) :=
  fun valuation position =>
    (tuple.component position).1.evaluateBelow model valuation
      (tuple.component position).2

/-- Pointwise generated consequence gives identical tuple evaluations in
every satisfying model, including empty carriers. -/
theorem evaluate_eq_of_equivalent {Carrier : Type v}
    (model : Model S Carrier) {system : EquationSystem S}
    (satisfies : model.Satisfies system)
    {input output : Nat} {left right : BoundedTermTuple S input output}
    (equivalent : Equivalent system left right) :
    evaluate model left = evaluate model right := by
  funext valuation position
  exact (equivalent position).evaluateBelow_eq model satisfies valuation
    (left.component position).2 (right.component position).2

/-- Evaluation of raw tuple composition is function composition. -/
theorem evaluate_comp {Carrier : Type v}
    (model : Model S Carrier) {first second third : Nat}
    (earlier : BoundedTermTuple S first second)
    (later : BoundedTermTuple S second third) :
    evaluate model (comp earlier later) =
      evaluate model later ∘ evaluate model earlier := by
  funext valuation position
  have argumentBounds (index : Nat) (below : index < second) :
      (substitution earlier index).VariablesBelow first := by
    simpa only [substitution, Term.finSubstitution, below, dite_true] using
      (earlier.component ⟨index, below⟩).2
  change ((later.component position).1.subst (substitution earlier)).evaluateBelow
      model valuation (Term.variablesBelow_subst (later.component position).2
        (substitution earlier) argumentBounds) =
      (later.component position).1.evaluateBelow model
        (evaluate model earlier valuation) (later.component position).2
  rw [Term.evaluateBelow_subst model valuation (substitution earlier) argumentBounds
    (later.component position).1 (later.component position).2]
  congr 1
  funext earlierPosition
  simp only [substitution_apply, evaluate]

/-- Evaluation of the raw identity tuple is the identity function. -/
theorem evaluate_identity {Carrier : Type v} (model : Model S Carrier)
    (size : Nat) :
    evaluate model (identity size) = id := rfl

/-- Evaluation sends raw tuple pairing to pointwise concatenation. -/
theorem evaluate_pair {Carrier : Type v} (model : Model S Carrier)
    {input left right : Nat}
    (first : BoundedTermTuple S input left)
    (second : BoundedTermTuple S input right) :
    evaluate model (pair first second) =
      fun valuation => Fin.addCases
        (evaluate model first valuation)
        (evaluate model second valuation) := by
  funext valuation position
  refine Fin.addCases ?_ ?_ position
  · intro firstPosition
    simp only [evaluate, pair, Fin.addCases_left]
  · intro secondPosition
    simp only [evaluate, pair, Fin.addCases_right]

/-- Finite tuple evaluation commutes with signature interpretation. -/
theorem evaluate_translate {T : Signature.{w}} {Carrier : Type v}
    (symbols : Signature.Interpretation S T) (model : Model T Carrier)
    {input output : Nat} (tuple : BoundedTermTuple S input output) :
    evaluate model (translate symbols tuple) = evaluate (model.reduct symbols) tuple := by
  funext valuation position
  exact Term.evaluateBelow_translate symbols model valuation
    (tuple.component position).1 (tuple.component position).2

end BoundedTermTuple

namespace Model

/-- Evaluate a quotient arrow in a fixed satisfying model. -/
def mapSyntacticHom {Carrier : Type v}
    {system : EquationSystem S} (model : Model S Carrier)
    (satisfies : model.Satisfies system) {input output : Nat} :
    SyntacticCategory.Hom system input output →
      ((Fin input → Carrier) → (Fin output → Carrier)) :=
  Quotient.lift
    (BoundedTermTuple.evaluate model)
    (fun _left _right equivalent =>
      BoundedTermTuple.evaluate_eq_of_equivalent model satisfies equivalent)

@[simp] theorem mapSyntacticHom_mk {Carrier : Type v}
    {system : EquationSystem S} (model : Model S Carrier)
    (satisfies : model.Satisfies system) {input output : Nat}
    (tuple : BoundedTermTuple S input output) :
    model.mapSyntacticHom satisfies (SyntacticCategory.mk system tuple) =
      BoundedTermTuple.evaluate model tuple := rfl

/-- A satisfying model evaluates the syntactic category in finite
powers of its carrier. -/
def syntacticFunctor {Carrier : Type v}
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) :
    SyntacticCategory system ⥤ Type v where
  obj context := Fin (SyntacticCategory.objectSize system context) → Carrier
  map arrow := ↾(model.mapSyntacticHom satisfies arrow)
  map_id _ := congrArg (fun f => ↾f) (BoundedTermTuple.evaluate_identity model _)
  map_comp first second := by
    refine Quotient.inductionOn₂ first second ?_
    intro earlier later
    exact congrArg (fun f => ↾f) (BoundedTermTuple.evaluate_comp model earlier later)

/-- The model functor maps the selected terminal arrow to the unique function
into the empty finite power. -/
theorem syntacticFunctor_map_terminalArrow
    {Carrier : Type v}
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) (input : Nat) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.terminalArrow (S := S) system
          (input := input)) =
      ↾(fun (_valuation : Fin input → Carrier) (position : Fin 0) =>
        Fin.elim0 position) := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext _valuation position
  exact Fin.elim0 position

/-- The model functor maps the selected first projection to restriction along
the first finite-context inclusion. -/
theorem syntacticFunctor_map_firstProjection
    {Carrier : Type v}
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) (left right : Nat) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.firstProjection system left right) =
      ↾(fun (valuation : Fin (left + right) → Carrier)
          (position : Fin left) => valuation (Fin.castAdd right position)) := rfl

/-- The model functor maps the selected second projection to restriction along
the second finite-context inclusion. -/
theorem syntacticFunctor_map_secondProjection
    {Carrier : Type v}
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) (left right : Nat) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.secondProjection system left right) =
      ↾(fun (valuation : Fin (left + right) → Carrier)
          (position : Fin right) => valuation (Fin.natAdd left position)) := rfl

/-- The model functor maps syntactic pairing to pointwise concatenation of the
two evaluated tuples. -/
theorem syntacticFunctor_map_pair
    {Carrier : Type v}
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system)
    {input left right : Nat}
    (first : SyntacticCategory.object system input ⟶
      SyntacticCategory.object system left)
    (second : SyntacticCategory.object system input ⟶
      SyntacticCategory.object system right) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.pair system first second) =
      ↾(fun (valuation : Fin input → Carrier) => Fin.addCases
        ((model.syntacticFunctor system satisfies).map first valuation)
        ((model.syntacticFunctor system satisfies).map second valuation)) := by
  refine Quotient.inductionOn₂ first second ?_
  intro earlier later
  exact congrArg (fun f => ↾f) (BoundedTermTuple.evaluate_pair model earlier later)

/-- Translating syntax and then evaluating agrees with evaluating in the reduct.
The agreement includes object and arrow maps, even for empty carriers. -/
theorem syntacticFunctor_reduct {T : Signature.{w}} {Carrier : Type v}
    {source : EquationSystem S} {target : EquationSystem T}
    (interpretation : EquationSystem.Interpretation source target)
    (model : Model T Carrier) (satisfies : model.Satisfies target) :
    (model.reduct interpretation.symbols).syntacticFunctor source
        (interpretation.reduct_satisfies model satisfies) =
      interpretation.syntacticFunctor ⋙ model.syntacticFunctor target satisfies := by
  apply Functor.toPrefunctor_injective
  refine Prefunctor.ext ?_ ?_
  · intro context
    rfl
  · intro input output arrow
    induction arrow using Quotient.inductionOn with
    | _ tuple =>
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        exact (BoundedTermTuple.evaluate_translate interpretation.symbols model tuple).symm

end Model

namespace FiniteContextControls

/-- A signature with an actual unary operation and no constants. -/
def unarySignature : Signature where
  Operation := Unit
  arity _ := 1

def emptyModel : Model unarySignature Empty where
  interpret _ arguments := arguments ⟨0, Nat.zero_lt_succ 0⟩

def system : EquationSystem unarySignature where
  equations := []

theorem emptyModel_satisfies : emptyModel.Satisfies system := by
  intro equation member
  cases member

theorem empty_context_has_one_valuation :
    Nonempty ((emptyModel.syntacticFunctor system emptyModel_satisfies).obj
      (SyntacticCategory.object system 0)) ∧
    Subsingleton ((emptyModel.syntacticFunctor system emptyModel_satisfies).obj
      (SyntacticCategory.object system 0)) := by
  change Nonempty (Fin 0 → Empty) ∧ Subsingleton (Fin 0 → Empty)
  exact ⟨⟨Fin.elim0⟩, inferInstance⟩

theorem positive_context_has_no_valuation {size : Nat} (positive : 0 < size) :
    IsEmpty ((emptyModel.syntacticFunctor system emptyModel_satisfies).obj
      (SyntacticCategory.object system size)) :=
  ⟨fun valuation => (valuation ⟨0, positive⟩).elim⟩

def nullarySignature : Signature where
  Operation := Unit
  arity _ := 0

theorem no_empty_nullary_model : ¬ Nonempty (Model nullarySignature Empty) := by
  intro existsModel
  exact (Model.nonempty_iff_no_nullary.mp existsModel) () rfl

def successorModel : Model unarySignature Nat where
  interpret _ arguments := arguments ⟨0, Nat.zero_lt_succ 0⟩ + 1

def successorTuple : BoundedTermTuple unarySignature 1 1 where
  component _ := ⟨.op () (fun _ => .var 0), fun _ => Nat.zero_lt_succ 0⟩

theorem two_successor_steps :
    BoundedTermTuple.evaluate successorModel
      (BoundedTermTuple.comp successorTuple successorTuple) (fun _ => 0) 0 = 2 := rfl

/-- A nonidentity interpretation replaces one unary action by two actions. -/
def duplicateUnary : Signature.Interpretation unarySignature unarySignature where
  operation _ := ⟨.op () (fun _ => .op () (fun _ => .var 0)),
    fun _ _ => Nat.zero_lt_succ 0⟩

theorem nonidentity_interpretation_readout :
    BoundedTermTuple.evaluate successorModel
        (BoundedTermTuple.translate duplicateUnary successorTuple) (fun _ => 3) 0 = 5 ∧
      BoundedTermTuple.evaluate (successorModel.reduct duplicateUnary)
        successorTuple (fun _ => 3) 0 = 5 := ⟨rfl, rfl⟩

def zeroModel : Model nullarySignature Nat where
  interpret _ _ := 0

def zeroTerm : Term.Bounded nullarySignature 0 :=
  ⟨.op () (fun position => Fin.elim0 position), fun position => Fin.elim0 position⟩

theorem nullary_evaluation_without_default :
    zeroTerm.1.evaluateBelow zeroModel Fin.elim0 zeroTerm.2 = 0 := rfl

theorem nullary_substitution_ignored (substitution : Nat → Term nullarySignature) :
    zeroTerm.1.subst substitution = zeroTerm.1 := by
  calc
    zeroTerm.1.subst substitution = zeroTerm.1.subst Term.var :=
      Term.subst_eq_of_variablesBelow zeroTerm.2 _ _
        (fun index below => (Nat.not_lt_zero index below).elim)
    _ = zeroTerm.1 := Term.subst_variables _

end FiniteContextControls

end Mettapedia.UniversalAlgebra
