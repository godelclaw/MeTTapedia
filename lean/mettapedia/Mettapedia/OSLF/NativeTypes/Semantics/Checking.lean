import Mettapedia.OSLF.NativeTypes.Semantics.Operational
import Mettapedia.OSLF.NativeTypes.Modal.QuerySearch

open Mettapedia.OSLF.Framework

/-!
# Proof-carrying results of executable native questions

The public result keeps the executed frontier, its native question, the
conclusive semantic certificate and all accepted receipt families. Refusal
and exhaustion are data constructors with no invented semantic denial.
Both conclusive polarities are certified by the existing independently
specified equation-aware occurrence semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Checking

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Semantics.Operational GSLTTypeSynthesis

inductive Verdict (statement : Prop) where
  | proof (certificate : statement)
  | refutation (certificate : ¬ statement)
  | unknown
  | refused (connective : Mettapedia.OSLF.NativeTypes.Structural.Connective)
  | illFormed (reason : Mettapedia.OSLF.NativeTypes.Structural.Refusal)
  | refusedPossibility
  | rejectedCube

def Verdict.readout {statement : Prop} : Verdict statement → CheckResult
  | .proof _ => .decided true
  | .refutation _ => .decided false
  | .unknown => .unknown
  | .refused connective => .refused connective
  | .illFormed reason => .illFormed reason
  | .refusedPossibility => .refusedPossibility
  | .rejectedCube => .rejectedCube

theorem Verdict.proof_sound {statement : Prop} {verdict : Verdict statement}
    (positive : verdict.readout = .decided true) : statement := by
  cases verdict <;> simp_all [Verdict.readout]

theorem Verdict.refutation_sound {statement : Prop} {verdict : Verdict statement}
    (negative : verdict.readout = .decided false) : ¬ statement := by
  cases verdict <;> simp_all [Verdict.readout]

structure NativeRun (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (kind : ModalQuery) (test : InvariantTest (generated.request bound carrier source)) where
  execution : QueryRun generated bound carrier source
  verdict : Verdict (questionPredicate kind (generated.request bound carrier source) test
    (generated.request bound carrier source).root)
  answerFamilies : List (AnswerFamily (generated.request bound carrier source) test.accepts)
  counterexampleFamilies : List (AnswerFamily (generated.request bound carrier source)
    (fun target => !test.accepts target))
  verdictReadout : verdict.readout = execution.result
  executedFamilies : answerFamilies = answerOutputs _ execution.state test.accepts
  executedCounterexamples : counterexampleFamilies = answerOutputs _ execution.state
    (fun target => !test.accepts target)

def run (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr) (source : Pattern)
    (kind : ModalQuery) (test : InvariantTest (generated.request bound carrier source)) (budget : Nat) :
    NativeRun generated bound carrier source kind test :=
  let execution := generated.searchModal bound carrier source kind test budget
  let verdict : Verdict (questionPredicate kind (generated.request bound carrier source) test
      (generated.request bound carrier source).root) :=
    match result : execution.result with
    | .decided true => .proof ((generated_search_answer_is_native_membership result).mp rfl)
    | .decided false => .refutation (fun holds =>
        Bool.false_ne_true ((generated_search_answer_is_native_membership result).mpr holds))
    | .unknown => .unknown
    | .refused connective => .refused connective
    | .illFormed reason => .illFormed reason
    | .refusedPossibility => .refusedPossibility
    | .rejectedCube => .rejectedCube
  {execution := execution, verdict := verdict,
    answerFamilies := answerOutputs _ execution.state test.accepts,
    counterexampleFamilies := answerOutputs _ execution.state (fun target => !test.accepts target),
    verdictReadout := by
      dsimp only [verdict]
      split <;> simp_all only [Verdict.readout],
    executedFamilies := rfl,
    executedCounterexamples := rfl}

theorem run_readout (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (kind : ModalQuery) (test : InvariantTest (generated.request bound carrier source))
    (budget : Nat) :
    (run generated bound carrier source kind test budget).verdict.readout =
      (generated.searchModal bound carrier source kind test budget).result :=
  (run generated bound carrier source kind test budget).verdictReadout

theorem run_retains_actual_receipts (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (kind : ModalQuery) (test : InvariantTest (generated.request bound carrier source))
    (budget : Nat) :
    (run generated bound carrier source kind test budget).answerFamilies.map (fun output => output.1.val) =
      ((generated.searchModal bound carrier source kind test budget).state.answers.filter
        (fun answer => test.accepts answer.val.target)).map Subtype.val :=
  retained_origins_and_multiplicity _ _ _

/-- The negative readout does not discard its discriminating executions.
Counterexamples retain the same ordered physical receipts as the frontier. -/
theorem run_retains_counterexample_receipts (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (kind : ModalQuery) (test : InvariantTest (generated.request bound carrier source))
    (budget : Nat) :
    (run generated bound carrier source kind test budget).counterexampleFamilies.map (fun output => output.1.val) =
      ((generated.searchModal bound carrier source kind test budget).state.answers.filter
        (fun answer => !test.accepts answer.val.target)).map Subtype.val :=
  retained_origins_and_multiplicity _ _ _

theorem counterexample_native_readout {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr}
    {source : Pattern} {test : InvariantTest (generated.request bound carrier source)}
    (counterexample : AnswerFamily (generated.request bound carrier source) (fun target => !test.accepts target)) :
    counterexample.1.val.Valid (generated.request bound carrier source).plan
      (generated.request bound carrier source).bound (generated.request bound carrier source).expected
      (generated.request bound carrier source).root ∧ test.accepts counterexample.1.val.target = false := by
  refine ⟨counterexample.1.property, ?_⟩
  have denied : (!test.accepts counterexample.1.val.target) = true := counterexample.2.down
  cases observed : test.accepts counterexample.1.val.target with
  | false => rfl
  | true => simp [observed] at denied

/-- An actual counterexample family refutes the outgoing universal native
question, without requiring exhaustive enumeration of other successors. -/
theorem counterexample_refutes_outgoing_native {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr}
    {source : Pattern} {test : InvariantTest (generated.request bound carrier source)}
    (counterexample : AnswerFamily (generated.request bound carrier source) (fun target => !test.accepts target)) :
    ¬ questionPredicate .outgoingUniversal (generated.request bound carrier source) test
      (generated.request bound carrier source).root := by
  intro universal
  have accepted := universal _ (GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _ counterexample.1.property)
  have denied := (counterexample_native_readout counterexample).2
  exact Bool.false_ne_true (denied.symm.trans accepted)

theorem run_positive_native {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr}
    {source : Pattern} {kind : ModalQuery} {test : InvariantTest (generated.request bound carrier source)}
    {budget : Nat} (positive : (run generated bound carrier source kind test budget).verdict.readout = .decided true) :
    (gsltOSLF (theory generated bound carrier)).satisfies
      (generated.request bound carrier source).root
      (questionType kind (generated.request bound carrier source) test).pred :=
  Verdict.proof_sound positive

theorem run_negative_native {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr}
    {source : Pattern} {kind : ModalQuery} {test : InvariantTest (generated.request bound carrier source)}
    {budget : Nat} (negative : (run generated bound carrier source kind test budget).verdict.readout = .decided false) :
    ¬ (gsltOSLF (theory generated bound carrier)).satisfies
      (generated.request bound carrier source).root
      (questionType kind (generated.request bound carrier source) test).pred :=
  Verdict.refutation_sound negative

/-- Proof erasure leaves the original executable readout unchanged, including
unknown and refusal. Adding native evidence does not strengthen a budget. -/
theorem run_unknown_iff (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (source : Pattern) (kind : ModalQuery) (test : InvariantTest (generated.request bound carrier source))
    (budget : Nat) :
    (run generated bound carrier source kind test budget).verdict.readout = .unknown ↔
      (generated.searchModal bound carrier source kind test budget).result = .unknown := by
  rw [run_readout]

end Mettapedia.OSLF.NativeTypes.Semantics.Checking
