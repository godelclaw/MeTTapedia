import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.OSLF.NativeTypes.Semantics.Families

/-!
# PeTTa execution as an OSLF-generating GSLT

The operational rules in `DeclarativeSpec`, including effects and I/O, form
the GSLT in `Eval`, and OSLF modalities are generated from that graph. The
type of configurations reachable in one step is exactly the transition
judgment and, by adequacy, the executable step function.
Printed output only grows and input is consumed in order along every
transition. The selected-rewrite view, a GSLT built from the `CoreDecl` relation over
`Pattern`, is in `PatternRewrite.OperationalGSLT`; relating the two needs a
fragment simulation, not a renaming.
-/


namespace Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Eval
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities

def system (program : Program) := gsltOSLF (theory program)

/-- The generated modality directly classifies the declarative transitions. -/
theorem next_configuration_type_iff_transition
    (program : Program) (source target : Configuration) :
    (system program).satisfies (S := ()) source
      (exactTargetNativeType (theory program) target).pred ↔
        DeclarativeSpec.Transition program source target :=
  satisfies_exactTargetNativeType_iff_step (theory program) source target

theorem next_configuration_type (program : Program) (source target : Configuration) :
    (system program).satisfies (S := ()) source
      (exactTargetNativeType (theory program) target).pred ↔
        step program source = some target :=
  (next_configuration_type_iff_transition program source target).trans
    (step_iff_transition program source target).symm

theorem output_extends (program : Program) (source target : Configuration)
    (transition : step program source = some target) :
    ∃ added, target.output = source.output ++ added := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals simp only [step] at transition
      all_goals
        repeat' first
          | contradiction
          | split at transition
          | solve
              | cases transition
                simp_all

theorem input_is_consumed_in_order (program : Program) (source target : Configuration)
    (transition : step program source = some target) :
    ∃ consumed, source.input = consumed ++ target.input := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals simp only [step] at transition
      all_goals
        repeat' first
          | contradiction
          | split at transition
          | solve
              | cases transition
                simp_all
                all_goals first | exact ⟨[], rfl⟩ | exact ⟨[_], rfl⟩

def Printed (history : List Atom) (configuration : Configuration) : Prop :=
  ∃ suffix, configuration.output = history ++ suffix

theorem printed_preserved (program : Program) (history : List Atom) :
    Printed history ≤ derivedForwardBox (gsltSpan (theory program)) (Printed history) := by
  intro source observed edge atSource
  obtain ⟨suffix, before⟩ := observed
  obtain ⟨added, after⟩ := output_extends program edge.source edge.target
    (transition_step edge.step)
  change edge.source = source at atSource
  subst source
  refine ⟨suffix ++ added, ?_⟩
  change edge.target.output = history ++ (suffix ++ added)
  rw [after, before, List.append_assoc]

theorem printed_step_image (program : Program) (history : List Atom) :
    derivedImage (gsltSpan (theory program)) (Printed history) ≤ Printed history :=
  (preserved_iff_derivedImage_le (gsltSpan (theory program)) (Printed history)).mp
    (printed_preserved program history)

/-- Finiteness is preserved by the actual judgment-generated GSLT. -/
theorem finite_cells_preserved (program : SpaceSemantics.Program) :
    (fun configuration : Configuration => NamedSpaces.Store.FiniteCells configuration.state) ≤
      derivedForwardBox (gsltSpan (theory program))
        (fun configuration => NamedSpaces.Store.FiniteCells configuration.state) := by
  intro source finite edge atSource
  change edge.source = source at atSource
  subst source
  exact DeclarativeSpec.transition_finite_cells finite edge.step

theorem empty_tail_preserved (program : SpaceSemantics.Program) :
    (fun configuration : Configuration => NamedSpaces.Store.EmptyTail configuration.state []) ≤
      derivedForwardBox (gsltSpan (theory program))
        (fun configuration => NamedSpaces.Store.EmptyTail configuration.state []) := by
  intro source vacant edge atSource
  change edge.source = source at atSource
  subst source
  exact DeclarativeSpec.transition_empty_tail vacant edge.step


/-! ## Retained output of a pure, terminating singleton computation -/

/-- Native membership is stated directly by the executable target machine.
The returned value is unconstrained; the state and I/O observations must be
unchanged. This is stronger than a cardinality bound on answers. -/
def pureSingletonPredicate (program : Program) : EquationPredicate (theory program) :=
  ⟨fun configuration => ∃ value fuel,
      run program fuel configuration = .complete configuration.state [value]
        configuration.input configuration.output,
   by intro first second same; cases same; rfl⟩

/-- The dependent family retains the actual returned value and its independent
operational derivation. Lists inside that value retain every occurrence. -/
def pureSingletonOutput (program : Program) :
    Mettapedia.OSLF.NativeTypes.Semantics.Families.NativeOutput (theory program) where
  predicate := pureSingletonPredicate program
  Family configuration := {value : Atom // DeclarativeSpec.Runs program configuration
    (.complete configuration.state [value] configuration.input configuration.output)}
  supportExact configuration := by
    constructor
    · rintro ⟨⟨value, derives⟩⟩
      obtain ⟨fuel, computed⟩ := (completed_run_iff_derivation program configuration _ _ _ _).mpr derives
      exact ⟨value, fuel, computed⟩
    · rintro ⟨value, fuel, computed⟩
      exact ⟨⟨value, (completed_run_iff_derivation program configuration _ _ _ _).mp ⟨fuel, computed⟩⟩⟩

/-- A retained pure output determines every completed execution, including
all observations. Determinacy rules out a second effectful completion. -/
theorem pureSingleton_all_completed (program : Program) (configuration : Configuration)
    (witness : (pureSingletonOutput program).Family configuration)
    (after : Effects.State) (answers input output : List Atom)
    (completed : ∃ fuel, run program fuel configuration = .complete after answers input output) :
    after = configuration.state ∧ answers = [witness.val] ∧
      input = configuration.input ∧ output = configuration.output := by
  obtain ⟨firstFuel, first⟩ := (completed_run_iff_derivation program configuration _ _ _ _).mpr witness.property
  obtain ⟨secondFuel, second⟩ := completed
  obtain ⟨stateEq, answersEq, inputEq, outputEq⟩ :=
    completed_result_unique program firstFuel secondFuel configuration _ _ _ _ _ _ _ _ first second
  exact ⟨stateEq.symm, answersEq.symm, inputEq.symm, outputEq.symm⟩

theorem pureSingleton_family_subsingleton (program : Program) (configuration : Configuration) :
    Subsingleton ((pureSingletonOutput program).Family configuration) := by
  constructor
  intro first second
  apply Subtype.ext
  have same := pureSingleton_all_completed program configuration first
    configuration.state [second.val] configuration.input configuration.output
    ((completed_run_iff_derivation program configuration _ _ _ _).mpr second.property)
  exact (List.singleton_inj.mp same.2.1).symm

/-- The compositional execution proof earns the native certificate; the
certificate is not supplied by a compiler annotation or a source readback. -/
def pureSingleton_of_returns (program : Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (state : Effects.State) (expression value : Atom)
    (returned : PureReturns program bindings state expression state value) :
    (pureSingletonOutput program).Family { state := state, control := .evaluate bindings expression } :=
  ⟨value, (pure_returns_derivation_iff program bindings state state expression value returned state [value] [] []).mpr
    ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Consumers recover the actual pure execution obligation from the native
certificate, while retaining its returned value. -/
theorem pureSingleton_returns (program : Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (state : Effects.State) (expression : Atom)
    (witness : (pureSingletonOutput program).Family
      { state := state, control := .evaluate bindings expression }) :
    PureReturns program bindings state expression state witness.val :=
  (completed_run_iff_path program _ state [witness.val] [] []).mp
    ((completed_run_iff_derivation program _ state [witness.val] [] []).mpr witness.property)

/-- An actual print cannot inhabit the unchanged-I/O native output, even
though its ordinary result is a singleton boolean. -/
theorem println_not_pureSingleton (program : Program)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (state : Effects.State)
    (name : String) (value : Atom)
    (demanded : argumentIsRaw program "println!" 0 = false)
    (captured : Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (.var name) = value) :
    ¬ (pureSingletonPredicate program)
      { state := state, control := .evaluate bindings (.expression [.symbol "println!", .var name]) } := by
  intro supported
  obtain ⟨witness⟩ := (pureSingletonOutput program).supportExact _ |>.mpr supported
  have printed := Eval.InputOutput.println_variable_io_returns program bindings state name value [] [] demanded captured
  have observed := pureSingleton_all_completed program _ witness state [Effects.boolean true] [] [value]
    (path_has_sufficient_fuel program _ state [Effects.boolean true] [] [value] printed)
  have impossible : [value] = [] := observed.2.2.2
  simp at impossible

/-! ## Physical occurrences in an operationally observed output list -/

/-- An observer reads a list from the returned target value. Membership is
stated by actual execution and the observer, independently of any source
validity predicate. The observer may reject values outside its wire format. -/
def orderedOutputPredicate {α : Type*} (program : Program)
    (read : Atom → List α → Prop) : EquationPredicate (theory program) :=
  ⟨fun configuration => ∃ (value : Atom) (values : List α) (index : Nat) (payload : α) (fuel : Nat),
      run program fuel configuration = .complete configuration.state [value]
        configuration.input configuration.output ∧
      read value values ∧ values[index]? = some payload,
   by intro first second same; cases same; rfl⟩

/-- Physical indices distinguish equal payloads at different positions.
Execution derivations and evaluator budgets are propositions, so they do
not manufacture additional receipt identities. -/
def orderedOutput {α : Type*} (program : Program)
    (read : Atom → List α → Prop) :
    Mettapedia.OSLF.NativeTypes.Semantics.Families.NativeOutput (theory program) where
  predicate := orderedOutputPredicate program read
  Family configuration := {occurrence : Nat × α // ∃ value values,
    DeclarativeSpec.Runs program configuration
      (.complete configuration.state [value] configuration.input configuration.output) ∧
    read value values ∧ values[occurrence.1]? = some occurrence.2}
  supportExact configuration := by
    constructor
    · rintro ⟨⟨⟨index, payload⟩, value, values, completed, observed, present⟩⟩
      obtain ⟨fuel, computed⟩ := (completed_run_iff_derivation program configuration _ _ _ _).mpr completed
      exact ⟨value, values, index, payload, fuel, computed, observed, present⟩
    · rintro ⟨value, values, index, payload, fuel, computed, observed, present⟩
      exact ⟨⟨⟨index, payload⟩, value, values,
        (completed_run_iff_derivation program configuration _ _ _ _).mp ⟨fuel, computed⟩,
        observed, present⟩⟩

/-- Exact execution and a functional target observer identify every retained
output occurrence. This compares data identities, not evaluation witnesses. -/
def orderedOutputEquiv {α : Type*} (program : Program)
    (read : Atom → List α → Prop)
    (functional : ∀ value first second, read value first → read value second → first = second)
    (configuration : Configuration)
    (witness : (pureSingletonOutput program).Family configuration)
    (values : List α) (observed : read witness.val values) :
    {occurrence : Nat × α // values[occurrence.1]? = some occurrence.2} ≃
      (orderedOutput program read).Family configuration where
  toFun occurrence := ⟨occurrence.val, witness.val, values, witness.property, observed, occurrence.property⟩
  invFun occurrence := ⟨occurrence.val, by
    obtain ⟨value, results, completed, readout, present⟩ := occurrence.property
    have same := pureSingleton_all_completed program configuration witness
      configuration.state [value] configuration.input configuration.output
      ((completed_run_iff_derivation program configuration _ _ _ _).mpr completed)
    have valueEq : value = witness.val := List.singleton_inj.mp same.2.1
    have resultEq : results = values := functional witness.val results values (valueEq ▸ readout) observed
    simpa only [resultEq] using present⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem orderedOutputEquiv_preserves_occurrence {α : Type*} (program : Program)
    (read : Atom → List α → Prop)
    (functional : ∀ value first second, read value first → read value second → first = second)
    (configuration : Configuration)
    (witness : (pureSingletonOutput program).Family configuration)
    (values : List α) (observed : read witness.val values)
    (occurrence : {occurrence : Nat × α // values[occurrence.1]? = some occurrence.2}) :
    (orderedOutputEquiv program read functional configuration witness values observed occurrence).val =
      occurrence.val := rfl

/-- Universal questions range over every physical result position. Their
transport uses exact output coverage; a single successful result is insufficient. -/
theorem orderedOutput_forall_iff {α : Type*} (program : Program)
    (read : Atom → List α → Prop)
    (functional : ∀ value first second, read value first → read value second → first = second)
    (configuration : Configuration)
    (witness : (pureSingletonOutput program).Family configuration)
    (values : List α) (observed : read witness.val values) (property : Nat → α → Prop) :
    (∀ occurrence : (orderedOutput program read).Family configuration,
      property occurrence.val.1 occurrence.val.2) ↔
      ∀ index payload, values[index]? = some payload → property index payload := by
  let comparison := orderedOutputEquiv program read functional configuration witness values observed
  constructor
  · intro universal index payload present
    exact universal (comparison ⟨⟨index, payload⟩, present⟩)
  · intro universal occurrence
    obtain ⟨original, rfl⟩ := comparison.surjective occurrence
    exact universal original.val.1 original.val.2 original.property

namespace OrderedOutputControls

private def readExpression (value : Atom) (values : List Atom) : Prop := value = .expression values

private theorem readExpression_functional (value : Atom) (first second : List Atom)
    (firstRead : readExpression value first) (secondRead : readExpression value second) : first = second :=
  Atom.expression.inj (firstRead.symm.trans secondRead)

private def quotedConfiguration (state : Effects.State) (values : List Atom) : Configuration :=
  {state, control := .evaluate [] (.expression [.symbol "quote", .expression values])}

private def quotedWitness (program : Program) (state : Effects.State) (values : List Atom) :
    (pureSingletonOutput program).Family (quotedConfiguration state values) :=
  pureSingleton_of_returns program [] state _ _ (by
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using
      quote_returns program [] state (.expression values))

private def quotedOccurrence (program : Program) (state : Effects.State)
    (values : List Atom) (index : Nat) (value : Atom) (present : values[index]? = some value) :
    (orderedOutput program readExpression).Family (quotedConfiguration state values) :=
  orderedOutputEquiv program readExpression readExpression_functional _
    (quotedWitness program state values) values rfl ⟨⟨index, value⟩, present⟩

/-- Actual quotation of equal payloads retains two distinct native witnesses. -/
theorem equal_payloads_distinct_occurrences (program : Program) (state : Effects.State) (value : Atom) :
    quotedOccurrence program state [value, value] 0 value rfl ≠
      quotedOccurrence program state [value, value] 1 value rfl := by
  intro same
  have impossible : (0 : Nat) = 1 := congrArg (fun occurrence => occurrence.val.1) same
  exact Nat.zero_ne_one impossible

/-- An actual returned empty list has no output-occurrence native member. -/
theorem empty_output_has_no_occurrence (program : Program) (state : Effects.State) :
    ¬ (orderedOutput program readExpression).predicate (quotedConfiguration state []) := by
  intro supported
  obtain ⟨occurrence⟩ := (orderedOutput program readExpression).supportExact _ |>.mpr supported
  have original := (orderedOutputEquiv program readExpression readExpression_functional _
    (quotedWitness program state []) [] rfl).symm occurrence
  have impossible := original.property
  simp at impossible

end OrderedOutputControls

end Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
