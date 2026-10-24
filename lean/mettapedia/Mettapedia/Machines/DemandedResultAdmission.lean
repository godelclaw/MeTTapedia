import Mettapedia.GSLT.LanguageDef.DestinationPassingControls

/-!
# Closed arguments do not erase the result observer

An executable counterexample in the existing destination-passing machines.
The only argument is closed. A pure, deterministic pattern primitive reads
two local variables: an unbound head builds a pair as data; `make-wrap`
applies the corresponding constructor. Meeting a demanded result before this
primitive changes its behavior. Computing a private result and then meeting
that demand loses an answer.

The fresh-result control agrees in both machines. These are machine-model
controls, not a verification of the C evaluator or its admission predicates.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DemandedResultAdmission

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-- A deterministic, effect-free dynamic pair-pattern computation. -/
def patternPrimitive : Unit → List (Term sig) → Subst sig × ℕ → Option (Term sig)
  | _, [head, tail], store =>
      let actualHead := store.1.applyTerm head
      let actualTail := store.1.applyTerm tail
      match actualHead with
      | .const "make-wrap" => some (pair (.const "Wrap") actualTail)
      | _ => some (pair actualHead actualTail)
  | _, _, _ => none

abbrev patternStore := substitutionStore (σ := sig) id patternPrimitive noTestUnit

/-- Input, pattern head, pattern tail, and the evaluated pattern. -/
def patternProgram : SProgram L Unit Unit :=
  [((), ⟨4, [.var 0],
    .letPrim (.var 3) () [.var 1, .var 2]
      (.letE (.var 0) (.ret (.var 3))
        (.ret (pair (.var 1) (.var 2))))⟩)]

def closedInput {V : Type} : Term { sig with vars := V } :=
  pair (.const "Wrap") (.const "7")

theorem closedInput_ground {V : Type} :
    (closedInput : Term { sig with vars := V }).isGround := by
  change ∀ i : Fin 2,
    (if i.val = 0 then (.const "Wrap" : Term { sig with vars := V })
      else .const "7").isGround
  intro i
  split <;> trivial

def demandedResult {V : Type} : Term { sig with vars := V } :=
  pair (.const "make-wrap") (.const "7")

def demandedQuery : Code L Unit Unit 1 :=
  .letCall demandedResult () [closedInput] (.ret (.const "accepted"))

def freshQuery : Code L Unit Unit 1 :=
  .letCall (.var 0) () [closedInput] (.ret (.var 0))

def queryFrame : Fin 1 → Term sig := fun i => .var i.val

def runAtReturn (steps : ℕ) (query : Code L Unit Unit 1) :=
  repeats (step (compiled L patternStore (SProgram.normalize L patternProgram))) steps
    (queryState L query queryFrame start)

def runOutputFirst (steps : ℕ) (query : Code L Unit Unit 1) :=
  repeats (step (outputFirst L patternStore (SProgram.normalizeFirst L patternProgram))) steps
    (queryStateOut L query queryFrame start)

def atomView : Term sig → Option String
  | .const name => some name
  | _ => none

def pairView : Term sig → Option (String × String)
  | .app Fn.pair children => do
      let first ← atomView (children ⟨0, by decide⟩)
      let second ← atomView (children ⟨1, by decide⟩)
      pure (first, second)
  | _ => none

/-- Value-first execution rejects the demand; output-first execution accepts.
Both have completed, so this is an answer difference, not merely scheduling. -/
theorem demanded_result_counterexample :
    (runAtReturn 16 demandedQuery).frontier = [] ∧
    (runAtReturn 16 demandedQuery).emitted = [] ∧
    (runOutputFirst 16 demandedQuery).frontier = [] ∧
    (runOutputFirst 16 demandedQuery).emitted.map
      (fun answer => atomView (answer.2.2.1.applyTerm answer.2.1)) =
        [some "accepted"] := by
  unfold runAtReturn runOutputFirst
  rw [show patternStore =
    substitutionStoreByFuel id patternPrimitive noTestUnit 64 from
      (substitutionStoreByFuel_eq id patternPrimitive noTestUnit 64).symm]
  decide

/-- An unconstrained result leaves the local head unbound until its pattern
has run. Both execution disciplines then return the same completed pair. -/
theorem fresh_result_control :
    (runAtReturn 16 freshQuery).frontier = [] ∧
    (runOutputFirst 16 freshQuery).frontier = [] ∧
    (runAtReturn 16 freshQuery).emitted.map
      (fun answer => pairView (answer.2.2.1.applyTerm answer.2.1)) =
        [some ("Wrap", "7")] ∧
    (runOutputFirst 16 freshQuery).emitted.map
      (fun answer => pairView (answer.2.2.1.applyTerm answer.2.1)) =
        [some ("Wrap", "7")] := by
  unfold runAtReturn runOutputFirst
  rw [show patternStore =
    substitutionStoreByFuel id patternPrimitive noTestUnit 64 from
      (substitutionStoreByFuel_eq id patternPrimitive noTestUnit 64).symm]
  decide

/-- An inert pattern constructs syntax without interpreting the head's
current binding. Unification will read those variables when it meets it. -/
def dataPatternPrimitive : Unit → List (Term sig) → Subst sig × ℕ → Option (Term sig)
  | _, [head, tail], _ => some (pair head tail)
  | _, _, _ => none

abbrev dataPatternStore :=
  substitutionStore (σ := sig) id dataPatternPrimitive noTestUnit

/-- Genuine constructor operations satisfy the refinement's mode premise
for every task, rather than merely for one observed execution. -/
theorem data_pattern_moded
    (task : Task Unit (Control L Unit Unit (Subst sig × ℕ))
      (ReturnFrame L Unit Unit)) :
    Moded L (substitutionExact id dataPatternPrimitive noTestUnit) task := by
  apply substitution_moded id dataPatternPrimitive noTestUnit
  intro op args first second supply
  refine ⟨rfl, ?_⟩
  cases args with
  | nil => rfl
  | cons head tail =>
      cases tail with
      | nil => rfl
      | cons second rest => cases rest <;> rfl

/-- On this data-pattern region the established refinement applies: early
destination unification finishes in no more machine steps, preserving the
ordered answers up to consistent store solutions. These are model steps. -/
theorem data_pattern_output_first
    (program : SProgram L Unit Unit) (query : Code L Unit Unit 1) (n : ℕ)
    (done : (repeats
      (step (compiled L dataPatternStore (SProgram.normalize L program))) n
      (queryState L query queryFrame start)).frontier = []) :
    ∃ m ≤ n, (repeats
      (step (outputFirst L dataPatternStore (SProgram.normalizeFirst L program))) m
      (queryStateOut L query queryFrame start)).frontier = [] ∧
      List.Forall₂ (SameAnswer (substitutionExact id dataPatternPrimitive noTestUnit))
        (repeats (step (compiled L dataPatternStore (SProgram.normalize L program))) n
          (queryState L query queryFrame start)).emitted
        (repeats (step (outputFirst L dataPatternStore (SProgram.normalizeFirst L program))) m
          (queryStateOut L query queryFrame start)).emitted := by
  exact outputFirst_terminates (substitutionExact id dataPatternPrimitive noTestUnit)
    (programBindsAhead_normalize program)
    (simulates_query (substitutionExact id dataPatternPrimitive noTestUnit)
      (BindsAhead.refl query) queryFrame start
      (start_wellFormed dataPatternPrimitive noTestUnit))
    (fun _ task _ => data_pattern_moded task) n done

#print axioms demanded_result_counterexample
#print axioms fresh_result_control
#print axioms closedInput_ground
#print axioms data_pattern_moded
#print axioms data_pattern_output_first

end Mettapedia.Machines.DemandedResultAdmission
