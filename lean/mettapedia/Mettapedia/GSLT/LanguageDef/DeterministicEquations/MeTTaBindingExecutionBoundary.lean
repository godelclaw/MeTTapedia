import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaControlBinders
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaControlCorrespondence
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingMaterialization
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Binding observations at the native-argument boundary

The independent selector permits any emitted atom with the same observation
under the result bindings. Native dispatch, however, consumes syntactic
arguments. The minimal `eval` instruction therefore materializes its atom
under the current frame before invoking the host. The controls below show the
boundary from both sides: a bound scrutinee reaches the host as closed data,
while an unbound one reaches it unresolved and is refused.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings Space)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

/-- Ordinary integer equality, with a distinct result for noninteger operands.
It has no guest-kernel operation or access to a binding frame. -/
def integerEqualityDispatch : GroundedDispatch where
  executable operator := operator = .symbol "=="
  outcome operator arguments result := operator = .symbol "==" ∧
    result = match arguments with
      | [.grounded (.int left), .grounded (.int right)] =>
          .ok [(.symbol (if left = right then "True" else "False"), Bindings.empty)]
      | _ => .incorrectArgument

theorem integer_equality_closed (left right : Int) :
    integerEqualityDispatch.outcome (.symbol "==")
      [.grounded (.int left), .grounded (.int right)]
      (.ok [(.symbol (if left = right then "True" else "False"), Bindings.empty)]) :=
  ⟨rfl, rfl⟩

theorem integer_equality_symbolic_refusal (name : String) (right : Int) :
    integerEqualityDispatch.outcome (.symbol "==")
      [.var name, .grounded (.int right)] .incorrectArgument :=
  ⟨rfl, rfl⟩

/-- The empty frame materializes every atom to itself. -/
theorem empty_frame_materialization (raw : Atom) :
    BindingFrame.Materialization (BindingFrame.historical Bindings.empty) raw raw :=
  ⟨[], .nil _, (Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.apply_empty raw).symm⟩

/-- Negative control: with no binding for the scrutinee, the materialized call
is still open, and the host refuses its unresolved argument. -/
theorem unbound_integer_equality_run (name : String) (right : Int) :
    CoreRunRel Space.empty integerEqualityDispatch []
      (call "eval" [call "==" [.var name, .grounded (.int right)]]) Bindings.empty
      (Atom.notReducible, Bindings.empty) := by
  apply CoreRunRel.instruction
  · simp [call, embeddedInstruction]
  · simp [call, Minimal.IsChain]
  · apply CoreStepRel.eval _ _ _ _ _ (empty_frame_materialization _)
    exact CoreInvocationRel.groundedIncorrectArgument Space.empty (.symbol "==")
      [.var name, .grounded (.int right)] Bindings.empty rfl
      (integer_equality_symbolic_refusal name right)

/-- A frame binding the scrutinee to zero. -/
def zeroFrame : Bindings := ⟨[("fuel", .grounded (.int 0))], []⟩

/-- Positive control: under a frame binding the scrutinee, every materialization
of the emitted call is the closed call, so the host receives data and decides
it. The unresolved spelling never reaches the host through `eval`. -/
theorem materializing_eval_resolves_bound_variable :
    BindingFrame.Materialization (BindingFrame.historical zeroFrame)
        (call "==" [.var "fuel", .grounded (.int 0)])
        (call "==" [.grounded (.int 0), .grounded (.int 0)]) ∧
      (∀ materialized, BindingFrame.Materialization (BindingFrame.historical zeroFrame)
        (call "==" [.var "fuel", .grounded (.int 0)]) materialized →
          materialized = call "==" [.grounded (.int 0), .grounded (.int 0)]) ∧
      integerEqualityDispatch.outcome (.symbol "==")
        [.grounded (.int 0), .grounded (.int 0)] (.ok [(.symbol "True", Bindings.empty)]) := by
  have resolved : BindingFrame.Materialization (BindingFrame.historical zeroFrame)
      (call "==" [.var "fuel", .grounded (.int 0)])
      (call "==" [.grounded (.int 0), .grounded (.int 0)]) := by
    have single := Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.BindingMaterializationRel.single_assignment
      "fuel" (.grounded (.int 0)) (call "==" [.var "fuel", .grounded (.int 0)])
      (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars])
    simpa [zeroFrame, call, Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.apply,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.lookup] using single
  exact ⟨resolved, fun _ other => other.output_eq resolved, by simpa using integer_equality_closed 0 0⟩

/-- The two fuel operations emitted by `withFuel` have the exact closed-call
execution after actual binding materialization. The raw selector observation
is sufficient at this boundary because `evalOp` performs the missing step. -/
theorem materialized_fuel_operations
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) (fuel : Atom) (remaining : Nat)
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation fuel (.grounded (.int remaining))) :
    Metta.Minimal.evalOp environment state continuation
        (encodeModelAtom (call "==" [fuel, .grounded (.int 0)])) runtime =
      Metta.Minimal.evalOp environment state continuation
        (encodeModelAtom (call "==" [.grounded (.int remaining), .grounded (.int 0)])) runtime ∧
    Metta.Minimal.evalOp environment state continuation
        (encodeModelAtom (call "-" [fuel, .grounded (.int 1)])) runtime =
      Metta.Minimal.evalOp environment state continuation
        (encodeModelAtom (call "-" [.grounded (.int remaining), .grounded (.int 1)])) runtime := by
  have invocation (head : String) (argument : Atom) :
      Metta.Minimal.evalOp environment state continuation
          (encodeModelAtom (call head [fuel, argument])) runtime =
        Metta.Minimal.evalOp environment state continuation
          (encodeModelAtom (call head [.grounded (.int remaining), argument])) runtime := by
    apply invariant.evalOp_observation environment state continuation
    intro valuation satisfied
    have same := observed valuation satisfied
    simp only [HEAtomEquationSatisfied] at same
    simp [HEAtomEquationSatisfied, call, encodeModelAtom, encodeModelAtoms,
      applyClassSolution, same]
  exact ⟨invocation "==" _, invocation "-" _⟩

/-- An actual singleton runtime frame removes the alias before equality;
the result holds for every surrounding runtime state and continuation. -/
theorem actual_zero_alias_materializes
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) :
    Metta.Minimal.evalOp environment state continuation
        (encodeModelAtom (call "==" [.var "fuel", .grounded (.int 0)]))
        [.val "fuel" (encodeModelAtom (.grounded (.int 0)))] =
      Metta.Minimal.evalOp environment state continuation
        (encodeModelAtom (call "==" [.grounded (.int 0), .grounded (.int 0)]))
        [.val "fuel" (encodeModelAtom (.grounded (.int 0)))] := by
  apply evalOp_eq_of_instantiate_eq
  simp [call, encodeModelAtom, encodeModelAtoms, encodeModelGround,
    Metta.instantiate, Metta.Bindings.resolveAtom,
    Metta.Bindings.resolve_singleton_val_self_of_not_mem, Metta.Atom.vars]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control
