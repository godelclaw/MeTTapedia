import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

/-!
# Generated control in the independent minimal MeTTa semantics

The emitter uses explicit sequencing and first-match selection. These laws
retain the current binding materialization, saved caller and live syntax of
entered frames. The raw ordered scan theorem applies when its pending scan
syntax is fixed by materialization; empty entry bindings establish that
condition. General chain and unification laws retain materialization explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings ResultPair)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

variable {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
  {typing : EvalTypeService} {caller : Option Atom}

/-- The existing function-body boundary after one raw instruction result.
The bindings materialize that result before deciding whether to continue. -/
def BodyCompletion (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (raw result : ResultPair) (typing : EvalTypeService := publishedTypeService)
    (caller : Option Atom := none) : Prop :=
  ∃ materialized, BindingMaterializationRel raw.2 raw.1 materialized ∧
    ((embeddedInstruction materialized = false ∧ result = (materialized, raw.2)) ∨
      (embeddedInstruction materialized = true ∧
        CoreFunctionBodyRel space dispatch live materialized raw.2 result
          (typing := typing) (caller := caller)))

/-- One actual run followed by its materialization boundary completes a body. -/
theorem body_of_run {atom : Atom} {incoming : Bindings} {middle result : ResultPair}
    (execution : CoreRunRel space dispatch live atom incoming middle
      (typing := typing) (caller := caller))
    (continuation : BodyCompletion space dispatch live middle result typing caller) :
    CoreFunctionBodyRel space dispatch live atom incoming result
      (typing := typing) (caller := caller) := by
  obtain ⟨materialized, binding, terminal | resumes⟩ := continuation
  · obtain ⟨terminal, rfl⟩ := terminal
    exact .terminal space atom incoming middle materialized execution binding terminal
  · exact .resume space atom incoming middle materialized result execution binding resumes.1 resumes.2

/-- Exact body decomposition keeps the binding boundary between execution and
continuation. It does not silently execute an unmaterialized result. -/
theorem body_decompose {atom : Atom} {incoming : Bindings} {result : ResultPair} :
    CoreFunctionBodyRel space dispatch live atom incoming result
      (typing := typing) (caller := caller) ↔
    ∃ middle : ResultPair, CoreRunRel space dispatch live atom incoming middle
      (typing := typing) (caller := caller) ∧
      BodyCompletion space dispatch live middle result typing caller := by
  constructor
  · intro execution
    generalize resultEq : BindingFrame.historicalResult result = framed at execution
    cases execution with
    | terminal _ _ _ middle materialized execution binding terminal =>
        have historical := execution.preserves_historical rfl
        refine ⟨BindingFrame.rawResult middle, ?_, materialized,
          binding.of_historical historical, Or.inl ⟨terminal, ?_⟩⟩
        · simpa only [historical.result] using execution
        · have rawEq := congrArg BindingFrame.rawResult resultEq
          rw [BindingFrame.raw_historicalResult] at rawEq
          exact rawEq
    | resume _ _ _ middle materialized _ execution binding embedded continuation =>
        have historical := execution.preserves_historical rfl
        refine ⟨BindingFrame.rawResult middle, ?_, materialized,
          binding.of_historical historical, Or.inr ⟨embedded, ?_⟩⟩
        · simpa only [historical.result] using execution
        · rw [← resultEq] at continuation
          have historicalEq : middle.2 = BindingFrame.historical middle.2.bindings := historical
          rw [historicalEq] at continuation
          exact continuation
  · rintro ⟨middle, execution, continuation⟩
    exact body_of_run execution continuation

/-- A noninstruction whose materializations remain terminal returns the
materialized atom, retaining its complete incoming binding frame. -/
theorem body_terminal_iff {atom : Atom} {incoming : Bindings} {result : ResultPair}
    (terminal : embeddedInstruction atom = false)
    (remainsTerminal : ∀ normalized, BindingMaterializationRel incoming atom normalized →
      embeddedInstruction normalized = false) :
    CoreFunctionBodyRel space dispatch live atom incoming result
      (typing := typing) (caller := caller) ↔
      ∃ normalized, BindingMaterializationRel incoming atom normalized ∧
        result = (normalized, incoming) := by
  rw [body_decompose]
  constructor
  · rintro ⟨middle, execution, normalized, binding, done | resumes⟩
    · have same := (core_run_data_exact terminal).mp execution
      have rawSame : middle = (atom, incoming) := by
        have rawEq := congrArg BindingFrame.rawResult same
        rw [BindingFrame.raw_historicalResult] at rawEq
        exact rawEq
      subst middle
      exact ⟨normalized, binding, done.2⟩
    · have same := (core_run_data_exact terminal).mp execution
      have rawSame : middle = (atom, incoming) := by
        have rawEq := congrArg BindingFrame.rawResult same
        rw [BindingFrame.raw_historicalResult] at rawEq
        exact rawEq
      subst middle
      have contradiction := remainsTerminal normalized binding
      rw [contradiction] at resumes
      cases resumes.1
  · rintro ⟨normalized, binding, rfl⟩
    exact ⟨(atom, incoming), .data space atom incoming terminal,
      normalized, binding, Or.inl ⟨remainsTerminal normalized binding, rfl⟩⟩

/-- A literal return marker survives materialization, while its payload may
resolve variables in the current binding frame. -/
theorem body_returned_iff (atom : Atom) (incoming : Bindings) (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (returned atom) incoming result
      (typing := typing) (caller := caller) ↔
      ∃ value, BindingMaterializationRel incoming atom value ∧
        result = (returned value, incoming) := by
  constructor
  · intro execution
    obtain ⟨value, materialized, same⟩ := function_return_body_exact.mp execution
    exact ⟨value, materialized, BindingFrame.historicalResult_injective same⟩
  · rintro ⟨value, materialized, rfl⟩
    exact function_return_body_exact.mpr ⟨value, materialized, rfl⟩

/-- Entering a function protects its actual body and records its caller. -/
theorem function_returns {body atom : Atom} {incoming output : Bindings}
    (shape : ∃ items, body = .expression items)
    (execution : CoreFunctionBodyRel space dispatch (call "function" [body] :: live) body incoming
      (returned atom, output) (typing := typing) (caller := some (call "function" [body]))) :
    CoreRunRel space dispatch live (call "function" [body]) incoming (atom, output)
      (typing := typing) (caller := caller) := by
  apply CoreRunRel.instruction
  · simp [call, embeddedInstruction]
  · simp [call, Minimal.IsChain]
  · exact .functionReturn space body atom incoming output shape execution

/-- Sequencing retains its saved syntax, materializes the selected result,
substitutes that result once, and continues in the outer caller. -/
theorem body_chain_iff (source : Atom) (name : String) (template : Atom)
    (incoming : Bindings) (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (call "chain" [source, .var name, template])
      incoming result (typing := typing) (caller := caller) ↔
      ∃ value, ∃ output : Bindings, ∃ normalized,
        CoreRunRel space dispatch (call "chain" [source, .var name, template] :: live)
          source incoming (value, output) (typing := typing)
          (caller := some (call "chain" [source, .var name, template])) ∧
        BindingMaterializationRel output value normalized ∧
        CoreFunctionBodyRel space dispatch live (substituteName name normalized template)
          output result (typing := typing) (caller := caller) := by
  rw [body_decompose]
  constructor
  · rintro ⟨middle, execution, continuation⟩
    generalize middleEq : BindingFrame.historicalResult middle = framed at execution
    cases execution with
    | data _ _ _ terminal => simp [call, embeddedInstruction] at terminal
    | instruction _ _ _ _ _ nonchain => simp [call, Minimal.IsChain] at nonchain
    | chain _ _ _ _ _ _ step rest =>
        generalize sourceCode : call "chain" [source, .var name, template] = code at step
        cases step <;> simp_all [call]
        rename_i source' name' template' raw normalized _ binding run
        have historical := run.preserves_historical rfl
        refine ⟨raw.1, raw.2.bindings, ?_, normalized,
          binding.of_historical historical, ?_⟩
        · have paired := historical.result
          change (raw.1, BindingFrame.historical raw.2.bindings) = raw at paired
          rw [← paired] at run
          exact run
        · have historicalEq : raw.2 = BindingFrame.historical raw.2.bindings := historical
          rw [historicalEq, ← middleEq] at rest
          exact body_of_run (middle := middle) rest continuation
  · rintro ⟨value, output, normalized, execution, materialized, continuation⟩
    obtain ⟨middle, run, rest⟩ := body_decompose.mp continuation
    refine ⟨middle, ?_, rest⟩
    apply CoreRunRel.chain
    · exact ⟨_, rfl⟩
    · exact .chain space source name template incoming (value, output) normalized execution materialized
    · exact run

/-- Exact raw unification retains the selected output readout. Constraint
equivalence alone does not determine the returned syntax. -/
theorem run_unify_iff (target pattern yes no : Atom) (incoming : Bindings)
    (result : ResultPair) :
    CoreRunRel space dispatch live (call "unify" [target, pattern, yes, no]) incoming
      result (typing := typing) (caller := caller) ↔
      (UnifyCandidateRel target pattern incoming result.2 ∧
        BindingMaterializationRel result.2 yes result.1) ∨
      (UnifyNoMatchRel target pattern incoming ∧ result = (no, incoming)) := by
  change CoreRunRel space dispatch live
    (.expression [.symbol "unify", target, pattern, yes, no])
      (BindingFrame.historical incoming) (BindingFrame.historicalResult result)
        (typing := typing) (caller := caller) ↔ _
  rw [unify_run_exact]
  constructor
  · rintro (⟨candidate, _, materialized⟩ | ⟨missing, same⟩)
    · exact Or.inl ⟨candidate, materialized⟩
    · exact Or.inr ⟨missing, BindingFrame.historicalResult_injective same⟩
  · rintro (⟨candidate, materialized⟩ | ⟨missing, rfl⟩)
    · exact Or.inl ⟨candidate, .historical _ _, materialized⟩
    · exact Or.inr ⟨missing, rfl⟩

/-- The function continuation runs after the exact primitive readout. The
failure arm retains both raw fallback syntax and the incoming frame. -/
theorem body_unify_iff (target pattern yes no : Atom) (incoming : Bindings)
    (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (call "unify" [target, pattern, yes, no])
      incoming result (typing := typing) (caller := caller) ↔
      (∃ emitted output, UnifyCandidateRel target pattern incoming output ∧
        BindingMaterializationRel output yes emitted ∧
        BodyCompletion space dispatch live (emitted, output) result typing caller) ∨
      (UnifyNoMatchRel target pattern incoming ∧
        BodyCompletion space dispatch live (no, incoming) result typing caller) := by
  rw [body_decompose]
  constructor
  · rintro ⟨middle, execution, continuation⟩
    rcases (run_unify_iff target pattern yes no incoming middle).mp execution with
      ⟨selected, materialized⟩ | ⟨missing, rfl⟩
    · exact Or.inl ⟨middle.1, middle.2, selected, materialized, continuation⟩
    · exact Or.inr ⟨missing, continuation⟩
  · rintro (⟨emitted, output, selected, materialized, continuation⟩ | ⟨missing, continuation⟩)
    · exact ⟨_, (run_unify_iff target pattern yes no incoming (emitted, output)).mpr
        (Or.inl ⟨selected, materialized⟩), continuation⟩
    · exact ⟨_, (run_unify_iff target pattern yes no incoming (no, incoming)).mpr
        (Or.inr ⟨missing, rfl⟩), continuation⟩

/-- For syntax fixed by the actual binding theory, the completion boundary is
exactly the existing body relation. This is a local syntax condition. -/
theorem body_completion_fixed_iff (atom : Atom) (incoming : Bindings) (result : ResultPair)
    (fixed : ∀ normalized, BindingMaterializationRel incoming atom normalized ↔ normalized = atom) :
    BodyCompletion space dispatch live (atom, incoming) result typing caller ↔
      CoreFunctionBodyRel space dispatch live atom incoming result
        (typing := typing) (caller := caller) := by
  constructor
  · rintro ⟨normalized, materialized, terminal | resumes⟩
    · have same := (fixed normalized).mp materialized
      subst normalized
      obtain ⟨terminal, rfl⟩ := terminal
      exact .terminal space atom incoming (atom, incoming) atom
        (.data space atom incoming terminal) materialized terminal
    · have same := (fixed normalized).mp materialized
      subst normalized
      exact resumes.2
  · intro body
    by_cases terminal : embeddedInstruction atom = false
    · obtain ⟨middle, execution, continuation⟩ := body_decompose.mp body
      have same := (core_run_data_exact terminal).mp execution
      have rawSame : middle = (atom, incoming) := by
        have rawEq := congrArg BindingFrame.rawResult same
        rw [BindingFrame.raw_historicalResult] at rawEq
        exact rawEq
      subst middle
      exact continuation
    · exact ⟨atom, (fixed atom).mpr rfl,
        Or.inr ⟨Bool.eq_true_of_not_eq_false terminal, body⟩⟩

/-- A physical first viable branch occurrence, including its exact selected
readout. The prefix retains duplicate rows and proves each earlier refusal. -/
def SelectedBranchReadout (target : Atom) (incoming : Bindings)
    (branches : List (Atom × Atom)) (emitted : Atom) (output : Bindings) : Prop :=
  ∃ before pattern body after,
    branches = before ++ (pattern, body) :: after ∧
    (∀ row ∈ before, UnifyNoMatchRel target row.1 incoming) ∧
    UnifyCandidateRel target pattern incoming output ∧
    BindingMaterializationRel output body emitted

@[simp] theorem selectedBranchReadout_nil (target : Atom) (incoming : Bindings)
    (emitted : Atom) (output : Bindings) :
    ¬SelectedBranchReadout target incoming [] emitted output := by
  rintro ⟨before, pattern, body, after, same, _⟩
  have sizes := congrArg List.length same
  simp only [List.length_nil, List.length_append, List.length_cons] at sizes
  omega

theorem selectedBranchReadout_cons (target pattern body : Atom)
    (incoming : Bindings) (rest : List (Atom × Atom)) (emitted : Atom) (output : Bindings) :
    SelectedBranchReadout target incoming ((pattern, body) :: rest) emitted output ↔
      (UnifyCandidateRel target pattern incoming output ∧
        BindingMaterializationRel output body emitted) ∨
      (UnifyNoMatchRel target pattern incoming ∧
        SelectedBranchReadout target incoming rest emitted output) := by
  constructor
  · rintro ⟨before, selectedPattern, selectedBody, after, same, earlier, matched, materialized⟩
    cases before with
    | nil =>
        simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        exact Or.inl ⟨matched, materialized⟩
    | cons row before =>
        simp only [List.cons_append, List.cons.injEq] at same
        obtain ⟨rfl, same⟩ := same
        exact Or.inr ⟨earlier _ List.mem_cons_self,
          before, selectedPattern, selectedBody, after, same,
          fun row member => earlier row (List.mem_cons_of_mem _ member), matched, materialized⟩
  · rintro (⟨matched, materialized⟩ | ⟨missing, before, selectedPattern, selectedBody,
      after, same, earlier, matched, materialized⟩)
    · exact ⟨[], pattern, body, rest, rfl, by simp, matched, materialized⟩
    · refine ⟨(pattern, body) :: before, selectedPattern, selectedBody, after,
        by simp only [List.cons_append, same], ?_, matched, materialized⟩
      intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact missing
      · exact earlier row member

/-- The generated scan follows the first viable physical row. Its exact
materialization and complete continuation remain visible at the endpoint. -/
theorem body_select_iff (target : Atom) (branches : List (Atom × Atom)) (otherwise : Atom)
    (incoming : Bindings) (result : ResultPair)
    (fixed : ∀ rest, rest.IsSuffix branches → ∀ normalized,
      BindingMaterializationRel incoming (selectBranches target rest otherwise) normalized ↔
        normalized = selectBranches target rest otherwise) :
    CoreFunctionBodyRel space dispatch live (selectBranches target branches otherwise)
      incoming result (typing := typing) (caller := caller) ↔
      ((∀ row ∈ branches, UnifyNoMatchRel target row.1 incoming) ∧
        CoreFunctionBodyRel space dispatch live otherwise incoming result
          (typing := typing) (caller := caller)) ∨
      ∃ emitted output, SelectedBranchReadout target incoming branches emitted output ∧
        BodyCompletion space dispatch live (emitted, output) result typing caller := by
  induction branches with
  | nil => simp only [selectBranches, List.foldr_nil, List.not_mem_nil, false_implies,
      implies_true, true_and, selectedBranchReadout_nil, false_and, exists_false, or_false]
  | cons row rest ih =>
      rcases row with ⟨pattern, body⟩
      have restSuffix : rest.IsSuffix ((pattern, body) :: rest) := ⟨[(pattern, body)], rfl⟩
      have tailFixed := fixed rest restSuffix
      have ih := ih (fun tail suffix => fixed tail (suffix.trans restSuffix))
      simp only [selectBranches, List.foldr_cons, body_unify_iff]
      constructor
      · rintro (⟨emitted, output, selected, materialized, execution⟩ | ⟨refused, execution⟩)
        · exact Or.inr ⟨emitted, output,
            (selectedBranchReadout_cons _ _ _ _ _ _ _).mpr (Or.inl ⟨selected, materialized⟩),
            execution⟩
        · have body := (body_completion_fixed_iff _ _ _ tailFixed).mp execution
          rcases ih.mp body with ⟨none, run⟩ | ⟨chosen, frame, scan, run⟩
          · refine Or.inl ⟨?_, run⟩
            intro row member
            rcases List.mem_cons.mp member with rfl | member
            · exact refused
            · exact none row member
          · exact Or.inr ⟨chosen, frame,
              (selectedBranchReadout_cons _ _ _ _ _ _ _).mpr (Or.inr ⟨refused, scan⟩), run⟩
      · rintro (⟨none, run⟩ | ⟨chosen, frame, scan, run⟩)
        · exact Or.inr ⟨none _ List.mem_cons_self,
            (body_completion_fixed_iff _ _ _ tailFixed).mpr (ih.mpr
              (Or.inl ⟨fun row member => none row (List.mem_cons_of_mem _ member), run⟩))⟩
        · rcases (selectedBranchReadout_cons _ _ _ _ _ _ _).mp scan with
            ⟨matched, materialized⟩ | ⟨refused, rest⟩
          · exact Or.inl ⟨chosen, frame, matched, materialized, run⟩
          · exact Or.inr ⟨refused,
              (body_completion_fixed_iff _ _ _ tailFixed).mpr
                (ih.mpr (Or.inr ⟨chosen, frame, rest, run⟩))⟩

/-- Entering a generated branch scan with empty bindings establishes every
required pending-syntax fixedness check, without restricting its patterns. -/
theorem empty_bindings_fix_scan (target : Atom) (branches : List (Atom × Atom))
    (otherwise : Atom) :
    ∀ rest, rest.IsSuffix branches → ∀ normalized,
      BindingMaterializationRel Bindings.empty (selectBranches target rest otherwise) normalized ↔
        normalized = selectBranches target rest otherwise := by
  intro rest _ normalized
  exact BindingMaterializationRel.empty_iff _ _

/-- Once a row is viable, materializing or executing its result cannot retry
later rows. No fixedness restriction is needed for this first-row law. -/
theorem body_first_viable_iff (target pattern body : Atom) (rest : List (Atom × Atom))
    (otherwise : Atom) (incoming : Bindings) (result : ResultPair)
    (viable : ∃ output, UnifyCandidateRel target pattern incoming output) :
    CoreFunctionBodyRel space dispatch live
      (selectBranches target ((pattern, body) :: rest) otherwise)
      incoming result (typing := typing) (caller := caller) ↔
      ∃ emitted output, UnifyCandidateRel target pattern incoming output ∧
        BindingMaterializationRel output body emitted ∧
        BodyCompletion space dispatch live (emitted, output) result typing caller := by
  simp only [selectBranches, List.foldr_cons, body_unify_iff]
  constructor
  · rintro (selected | ⟨refused, _⟩)
    · exact selected
    · obtain ⟨output, candidate⟩ := viable
      exact False.elim (refused output candidate)
  · exact Or.inl

/-- Returned expressions remain data after their bindings are materialized,
even when their head names an ordinary recursive call. -/
theorem returns_callable_data (head : String) (arguments : List Atom) (incoming : Bindings)
    (normalized : Atom)
    (materialized : BindingMaterializationRel incoming (call head arguments) normalized) :
    CoreRunRel space dispatch live
      (call "function" [returned (call head arguments)]) incoming
      (normalized, incoming) (typing := typing) (caller := caller) := by
  apply function_returns ⟨_, rfl⟩
  exact (body_returned_iff _ _ _).mpr ⟨normalized, materialized, rfl⟩

/-- A selected materialized value is reused at the chain and return boundaries
without interpreting it as an ordinary call or replaying its producer. -/
theorem sequence_returned_data (head : String) (arguments : List Atom) (name : String)
    (incoming : Bindings) (normalized : Atom)
    (materialized : BindingMaterializationRel incoming (call head arguments) normalized) :
    CoreFunctionBodyRel space dispatch live
      (call "chain" [call "function" [returned (call head arguments)], .var name,
        returned (.var name)]) incoming
      (returned normalized, incoming) (typing := typing) (caller := caller) := by
  apply (body_chain_iff _ _ _ incoming (returned normalized, incoming)).mpr
  refine ⟨normalized, incoming, normalized,
    returns_callable_data head arguments incoming normalized materialized,
    materialization_reapply materialized, ?_⟩
  simp [returned, call, substituteName]
  exact function_return_body_exact.mpr ⟨normalized, materialization_reapply materialized, rfl⟩

/-- Absence of a literal return head cannot be repaired by binding its operands
or by treating callable-looking data as an instruction. -/
theorem bare_data_is_not_a_return (head : String) (arguments : List Atom)
    (incoming output : Bindings) (value : Atom)
    (data : embeddedInstruction (call head arguments) = false)
    (notReturn : head ≠ "return") :
    ¬ CoreFunctionBodyRel space dispatch live (call head arguments) incoming
      (returned value, output) (typing := typing) (caller := caller) := by
  have staysTerminal : ∀ normalized,
      BindingMaterializationRel incoming (call head arguments) normalized →
        embeddedInstruction normalized = false := by
    rintro normalized ⟨presentation, _, rfl⟩
    simpa [call, TypeSubst.apply, embeddedInstruction] using data
  intro body
  obtain ⟨normalized, ⟨presentation, _, same⟩, paired⟩ :=
    (body_terminal_iff (result := (returned value, output)) data staysTerminal).mp body
  have atomSame := congrArg Prod.fst paired
  change returned value = normalized at atomSame
  rw [← atomSame] at same
  simp [returned, call, TypeSubst.apply, Ne.symm notReturn] at same

/-! ## Materialization boundary controls -/

/-- Empty entry bindings prove the complete raw-scan correspondence, including
open patterns; this is the intended initially unbound generated dispatcher. -/
theorem empty_entry_scan_correspondence (target : Atom) (branches : List (Atom × Atom))
    (otherwise : Atom) (result : ResultPair) :
    CoreFunctionBodyRel space dispatch live (selectBranches target branches otherwise)
      Bindings.empty result (typing := typing) (caller := caller) ↔
      ((∀ row ∈ branches, UnifyNoMatchRel target row.1 Bindings.empty) ∧
        CoreFunctionBodyRel space dispatch live otherwise Bindings.empty result
          (typing := typing) (caller := caller)) ∨
      ∃ emitted output, SelectedBranchReadout target Bindings.empty branches emitted output ∧
        BodyCompletion space dispatch live (emitted, output) result typing caller :=
  body_select_iff target branches otherwise Bindings.empty result
    (empty_bindings_fix_scan target branches otherwise)

/-- A pending fallback can become a return expression under nonempty bindings.
Consequently raw pending syntax is not automatically fixed. -/
theorem bound_fallback_changes_pending_syntax :
    let bindings : Bindings := ⟨[("pending", returned (.symbol "done"))], []⟩
    let raw := selectBranches (.symbol "target") [] (.var "pending")
    BindingMaterializationRel bindings raw (returned (.symbol "done")) ∧
      returned (.symbol "done") ≠ raw := by
  dsimp only [selectBranches, List.foldr_nil]
  constructor
  · simpa [returned, call, TypeSubst.apply, TypeSubst.lookup] using
      BindingMaterializationRel.single_assignment "pending" (returned (.symbol "done"))
        (.var "pending") (by simp [returned, call, TypeSubst.typeVars, TypeSubst.typeVarsList])
  · intro impossible
    cases impossible

/-- The old raw-terminal result fails even for one assignment and a return
payload. The actual body returns the resolved payload in the same frame. -/
theorem bound_return_payload_is_materialized :
    let bindings : Bindings := ⟨[("payload", .symbol "value")], []⟩
    CoreFunctionBodyRel space dispatch live (returned (.var "payload")) bindings
      (returned (.symbol "value"), bindings) (typing := typing) (caller := caller) ∧
      (returned (.symbol "value"), bindings) ≠ (returned (.var "payload"), bindings) := by
  intro bindings
  constructor
  · apply (body_returned_iff _ _ (returned (.symbol "value"), bindings)).mpr
    refine ⟨.symbol "value", ?_, rfl⟩
    simpa [bindings, TypeSubst.apply, TypeSubst.lookup] using
      BindingMaterializationRel.single_assignment "payload" (.symbol "value")
        (.var "payload") (by simp [TypeSubst.typeVars])
  · simp [returned, call]


namespace UnifyReadoutControls

open Mettapedia.Languages.MeTTa.HE
open Spec.Match.Merge

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.UnifyReadoutControls

private theorem exact_materialization :
    BindingMaterializationRel outputBindings template observed := by
  simpa [outputBindings, template, observed, Bindings.assign, Bindings.empty,
    Bindings.isBound, Bindings.lookup, TypeSubst.apply, TypeSubst.lookup] using
    BindingMaterializationRel.single_assignment "x" (.symbol "B") template
      (by simp [TypeSubst.typeVars])

/-- The previous constraint-only step permits unread syntax; the exact raw
execution law excludes it even though the output bindings are satisfiable. -/
theorem coarse_step_does_not_imply_exact_run (service : Spec.Eval.GroundedDispatch) :
    UnifyStep (.var "x") (.symbol "B") template (.symbol "Fail")
      Bindings.empty template outputBindings ∧
    ¬CoreRunRel space service live
      (call "unify" [.var "x", .symbol "B", template, .symbol "Fail"])
      Bindings.empty (template, outputBindings) (typing := typing) (caller := caller) := by
  constructor
  · exact .success ⟨actual_candidate, fun _ _ => rfl⟩
  · intro run
    rcases (run_unify_iff (.var "x") (.symbol "B") template (.symbol "Fail")
      Bindings.empty (template, outputBindings)).mp run with ⟨_, read⟩ | ⟨missing, _⟩
    · have wrong := BindingMaterializationRel.output_eq read exact_materialization
      simp [template, observed] at wrong
    · exact missing _ actual_candidate

def repeatedBranches : List (Atom × Atom) :=
  [(.symbol "A", .symbol "miss"), (.symbol "A", .symbol "miss"),
    (.var "x", template), (.var "x", .symbol "late")]

private theorem refused : UnifyNoMatchRel (.symbol "B") (.symbol "A") Bindings.empty := by
  rintro output ⟨matched, matching, _⟩
  exact symbol_mismatch_not_match (by decide) matched matching

private theorem selected : UnifyCandidateRel (.symbol "B") (.var "x") Bindings.empty outputBindings := by
  have loop : Spec.Match.Merge.SemanticLoopFree outputBindings :=
    Spec.Match.Merge.semanticLoopFree_single_assignment (by intro occurs; cases occurs)
  refine ⟨outputBindings, .nonVarVar rfl loop, ?_⟩
  apply Spec.Match.Merge.MergeRel.logicalMerge
    (.mk (by simp [Spec.Match.Merge.constraints, Bindings.empty]) .nil)
  exact ⟨fun _ => .symbol "B", by
    simp [outputBindings, Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
      Spec.Type.RuntimeRefinement.applyTypeValuation, Bindings.assign,
      Bindings.empty, Bindings.isBound, Bindings.lookup]⟩

/-- Two equal refused rows remain two physical prefix occurrences before
the selected third row; the later viable row cannot take its place. -/
theorem duplicate_prefix_selected_third :
    SelectedBranchReadout (.symbol "B") Bindings.empty repeatedBranches observed outputBindings ∧
      repeatedBranches[0]? = repeatedBranches[1]? ∧
      repeatedBranches[2]? = some (.var "x", template) := by
  refine ⟨?_, rfl, rfl⟩
  refine ⟨[(.symbol "A", .symbol "miss"), (.symbol "A", .symbol "miss")],
    .var "x", template, [(.var "x", .symbol "late")], rfl, ?_, selected, exact_materialization⟩
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst row
  exact refused

theorem duplicate_prefix_does_not_select_later :
    ¬SelectedBranchReadout (.symbol "B") Bindings.empty repeatedBranches
      (.symbol "late") outputBindings := by
  intro read
  change SelectedBranchReadout _ _ ((_ , _) :: (_ , _) :: (_ , _) :: (_ , _) :: []) _ _ at read
  rcases (selectedBranchReadout_cons _ _ _ _ _ _ _).mp read with
    ⟨matched, _⟩ | ⟨_, tail⟩
  · exact refused _ matched
  rcases (selectedBranchReadout_cons _ _ _ _ _ _ _).mp tail with
    ⟨matched, _⟩ | ⟨_, tail⟩
  · exact refused _ matched
  rcases (selectedBranchReadout_cons _ _ _ _ _ _ _).mp tail with
    ⟨_, materialized⟩ | ⟨missing, _⟩
  · have wrong := BindingMaterializationRel.output_eq materialized exact_materialization
    cases wrong
  · exact missing _ selected

/-- The generated program reaches the selected readout and stops as data,
using exactly the same physical scan witness. -/
theorem duplicate_prefix_actual_body (service : Spec.Eval.GroundedDispatch) :
    CoreFunctionBodyRel space service live
      (selectBranches (.symbol "B") repeatedBranches (.symbol "fallback"))
      Bindings.empty (observed, outputBindings) (typing := typing) (caller := caller) := by
  apply (empty_entry_scan_correspondence (.symbol "B") repeatedBranches
    (.symbol "fallback") (observed, outputBindings)).mpr
  exact Or.inr ⟨observed, outputBindings, duplicate_prefix_selected_third.1,
    observed, materialization_reapply exact_materialization, Or.inl ⟨rfl, rfl⟩⟩

end UnifyReadoutControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control
