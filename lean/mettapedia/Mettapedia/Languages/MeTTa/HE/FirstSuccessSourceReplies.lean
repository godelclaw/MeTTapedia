import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlMachine
import Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-!
# Constructed source replies at the independent HE boundary

Type lookup and raw evaluation use the actual existing source functions.
Their replies are proved against the independent type/evaluator judgments,
including the complete result list rather than just answer support. The
separate applicability component retains raw type-checking path multiplicity.

The source applicability and matching helpers are fuel-indexed. General
correspondence for non-raw applicability and casting remains separate from
these replies, as do native binding substitution and domain refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type

theorem getAtomTypes_nonempty (space : Space) (value : Atom) :
    getAtomTypes space value ≠ [] := by
  have guard : ∀ types : List Atom,
      (if types.isEmpty then [Atom.undefinedType] else types) ≠ [] := by
    intro types
    cases types <;> simp
  exact guard _

/-- The whole source-ordered type list has an independent lookup derivation.
No theorem about a merely selected member is used as its substitute. -/
theorem source_types (space : Space) (value : Atom) :
    StorageTypesRel space value (getAtomTypes space value) := by
  obtain ⟨type, member⟩ := List.exists_mem_of_ne_nil (getAtomTypes space value)
    (getAtomTypes_nonempty space value)
  obtain ⟨types, related, _⟩ :=
    (Conformance.typeOfRel_iff_mem_getAtomTypes space value type).mpr member
  rw [Conformance.typesOfRel_eq_getAtomTypes related]
  exact related

theorem source_types_iff (space : Space) (value : Atom) (types : List Atom) :
    getAtomTypes space value = types ↔ StorageTypesRel space value types := by
  constructor
  · rintro rfl
    exact source_types space value
  · exact Conformance.typesOfRel_eq_getAtomTypes

/-- The actual configuration-scoped type query realizes the independent
lookup contract for every inherited scope retained by that configuration. -/
theorem scoped_source_types (state : RecursiveTasks.Configuration) (scope : List String)
    (bindings : Bindings) (subject expected : Atom)
    (retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state) :
    scopedTypeLookup scope state.space bindings subject expected
      (FirstSuccessRecursiveExecution.invocationTypes state bindings subject expected) :=
  EquationFreshening.getAtomTypesScoped_scopedTypeLookup _ _ _ _ _
    (source_types state.space subject) retained

/-- One scope-fixed naming convention leaves the complete cast input
unchanged, including aliases and variables nested inside binding values. -/
theorem invocation_scope_fixed (scope : List String) (subject expected : Atom)
    (bindings : Bindings) (names : String → String)
    (fixed : ∀ name ∈ invocationTypeScope scope [] subject expected bindings, names name = name) :
    Spec.Type.RuntimeRefinement.renameTypeVars names subject = subject ∧
      Spec.Type.RuntimeRefinement.renameTypeVars names expected = expected ∧
      Spec.Bindings.ScopeObservation.renameBindings names bindings = bindings := by
  have publicFixed : ∀ name, Steps.QueryVisibleName [expected] subject bindings name → names name = name := by
    intro name visible
    apply fixed name
    rw [EquationScope.queryVisible_support_iff] at visible
    simp only [invocationTypeScope,List.nil_append,Spec.Type.Presentation.TypeSubst.typeVarsList,
      List.append_nil,List.mem_append]
    rcases visible with queried | ⟨atom,member,occurs⟩ | constrained
    · exact Or.inl (Or.inr (Or.inl (Steps.atomOccurs_iff_mem_typeVars _ _ |>.mp queried)))
    · obtain rfl := List.mem_singleton.mp member
      exact Or.inl (Or.inr (Or.inr (Steps.atomOccurs_iff_mem_typeVars _ _ |>.mp occurs)))
    · exact Or.inr constrained
  obtain ⟨subjectFixed,bindingsFixed⟩ := EquationScope.caller_fixed names publicFixed
  refine ⟨subjectFixed,?_,bindingsFixed⟩
  calc
    _ = Spec.Type.RuntimeRefinement.renameTypeVars id expected :=
      Spec.Type.Presentation.ScopeObservation.renameTypeVars_congr_on_typeVars expected (fun name member =>
        fixed name (by simp [invocationTypeScope,Spec.Type.Presentation.TypeSubst.typeVarsList,member]))
    _ = expected := Spec.Type.Presentation.ScopeObservation.renameTypeVars_id expected

/-- Every legal source choice of fresh type names aligns with the actual
worker query by one caller-fixed permutation over the entire ordered family.
This starts at the actual retained configuration, rather than quantifying one
literal result list independently of its saved callers and answer prefix. -/
theorem scoped_source_types_complete (state : RecursiveTasks.Configuration) (scope : List String)
    (bindings : Bindings) (subject expected : Atom) (types : List Atom)
    (retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state)
    (source : scopedTypeLookup scope state.space bindings subject expected types) :
    ∃ names : Equiv.Perm String,
      (∀ name ∈ invocationTypeScope scope [] subject expected bindings, names name = name) ∧
      FirstSuccessRecursiveExecution.invocationTypes state bindings subject expected =
        types.map (Spec.Type.RuntimeRefinement.renameTypeVars names) := by
  obtain ⟨literal,queried,sourceInstances⟩ := source
  obtain ⟨nativeLiteral,nativeQueried,nativeInstances⟩ :=
    scoped_source_types state scope bindings subject expected retained
  have same := queried.unique nativeQueried
  rw [same] at sourceInstances
  exact Spec.Type.Presentation.ScopeObservation.argumentAlphaVariants_public_fixed_permutation
    sourceInstances nativeInstances

/-- Saved callers and answer prefixes may change the chosen private names.
For the same context and cast input their actual queries still agree under
one permutation fixing the declared input scope. -/
theorem scoped_queries_retained_equiv (first second : RecursiveTasks.Configuration)
    (scope : List String) (bindings : Bindings) (subject expected : Atom)
    (sameSpace : first.space = second.space)
    (firstRetained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames first)
    (secondRetained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames second) :
    ∃ names : Equiv.Perm String,
      (∀ name ∈ invocationTypeScope scope [] subject expected bindings, names name = name) ∧
      FirstSuccessRecursiveExecution.invocationTypes second bindings subject expected =
        (FirstSuccessRecursiveExecution.invocationTypes first bindings subject expected).map
          (Spec.Type.RuntimeRefinement.renameTypeVars names) := by
  apply scoped_source_types_complete second scope bindings subject expected _ secondRetained
  simpa only [sameSpace] using scoped_source_types first scope bindings subject expected firstRetained

private theorem cast_match_rename_iff (names : Equiv.Perm String) (expected actual : Atom)
    (bindings output : Bindings)
    (expectedFixed : Spec.Type.RuntimeRefinement.renameTypeVars names expected = expected)
    (bindingsFixed : Spec.Bindings.ScopeObservation.renameBindings names bindings = bindings) :
    TypeMatchRel expected (Spec.Type.RuntimeRefinement.renameTypeVars names actual) bindings output ↔
      TypeMatchRel expected actual bindings (Spec.Bindings.ScopeObservation.renameBindings names.symm output) := by
  have roundtrip : Spec.Bindings.ScopeObservation.renameBindings names
      (Spec.Bindings.ScopeObservation.renameBindings names.symm output) = output := by
    simpa only [Equiv.symm_symm] using
      Spec.Bindings.ScopeObservation.renameBindings_perm_inverse names.symm output
  simpa only [expectedFixed,bindingsFixed,roundtrip] using TypeMatchRel.rename_iff names expected actual bindings
      (Spec.Bindings.ScopeObservation.renameBindings names.symm output)

/-- A completed cast using the actual worker query is a source cast with
that chosen fresh family. Only the local lookup contract changes. -/
theorem scoped_cast_worker_to_source (state : RecursiveTasks.Configuration) (scope : List String)
    (bindings : Bindings) (subject expected : Atom) (results : ResultSet)
    (retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state)
    (source : TypeCastBatchRel state.space subject expected bindings results
      (lookup := fun frame atom demand types =>
        FirstSuccessRecursiveExecution.invocationTypes state frame atom demand = types)) :
    TypeCastBatchRel state.space subject expected bindings results
      (lookup := scopedTypeLookup scope state.space) := by
  apply source.change_lookup
  intro types queried
  rw [←queried]
  exact scoped_source_types state scope bindings subject expected retained

/-- Every completed scoped source cast aligns with the actual query at its
retained configuration. One permutation transports the complete result batch,
including reached bindings and all error occurrences; caller inputs are fixed.
This is the lookup/cast boundary, not yet execution of the worker's matcher. -/
theorem scoped_cast_source_to_worker (state : RecursiveTasks.Configuration) (scope : List String)
    (bindings : Bindings) (subject expected : Atom) (results : ResultSet)
    (retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state)
    (source : TypeCastBatchRel state.space subject expected bindings results
      (lookup := scopedTypeLookup scope state.space)) :
    ∃ names : Equiv.Perm String,
      (∀ name ∈ invocationTypeScope scope [] subject expected bindings, names name = name) ∧
      TypeCastBatchRel state.space subject expected bindings (Renaming.results names results)
        (lookup := fun frame atom demand types =>
          FirstSuccessRecursiveExecution.invocationTypes state frame atom demand = types) := by
  cases source with
  | @success _ _ types earlier later actual output queried selected rejected matched =>
      obtain ⟨names,fixed,typesEqual⟩ := scoped_source_types_complete state scope bindings subject expected
        types retained queried
      obtain ⟨subjectFixed,expectedFixed,bindingsFixed⟩ :=
        invocation_scope_fixed scope subject expected bindings names fixed
      have matchedNext : TypeMatchRel expected (Spec.Type.RuntimeRefinement.renameTypeVars names actual)
          bindings (Spec.Bindings.ScopeObservation.renameBindings names output) := by
        simpa only [expectedFixed,bindingsFixed] using TypeMatchRel.rename names matched
      have rejectedNext : ∀ prior ∈ earlier.map (Spec.Type.RuntimeRefinement.renameTypeVars names),
          ∀ candidate, ¬TypeMatchRel expected prior bindings candidate := by
        intro prior member candidate accepted
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact rejected original present _
          ((cast_match_rename_iff names expected original bindings candidate expectedFixed bindingsFixed).mp accepted)
      refine ⟨names,fixed,?_⟩
      have mappedOrder : types.map (Spec.Type.RuntimeRefinement.renameTypeVars names) =
          earlier.map (Spec.Type.RuntimeRefinement.renameTypeVars names) ++
            Spec.Type.RuntimeRefinement.renameTypeVars names actual ::
              later.map (Spec.Type.RuntimeRefinement.renameTypeVars names) := by
        simpa only [List.map_append,List.map_cons] using
          congrArg (List.map (Spec.Type.RuntimeRefinement.renameTypeVars names)) selected
      have casted := TypeCastBatchRel.success (space := state.space) (atom := subject)
        (expectedType := expected) (bindings := bindings)
        (lookup := fun frame atom demand types =>
          FirstSuccessRecursiveExecution.invocationTypes state frame atom demand = types)
        typesEqual mappedOrder rejectedNext matchedNext
      simpa only [Renaming.results,Renaming.result,List.map_cons,List.map_nil,subjectFixed] using casted
  | @failure _ _ types queried rejected =>
      obtain ⟨names,fixed,typesEqual⟩ := scoped_source_types_complete state scope bindings subject expected
        types retained queried
      obtain ⟨subjectFixed,expectedFixed,bindingsFixed⟩ :=
        invocation_scope_fixed scope subject expected bindings names fixed
      have rejectedNext : ∀ actual ∈ types.map (Spec.Type.RuntimeRefinement.renameTypeVars names),
          ∀ candidate, ¬TypeMatchRel expected actual bindings candidate := by
        intro actual member candidate accepted
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact rejected original present _
          ((cast_match_rename_iff names expected original bindings candidate expectedFixed bindingsFixed).mp accepted)
      refine ⟨names,fixed,?_⟩
      have casted := TypeCastBatchRel.failure (space := state.space) (atom := subject)
        (expectedType := expected) (bindings := bindings)
        (lookup := fun frame atom demand types =>
          FirstSuccessRecursiveExecution.invocationTypes state frame atom demand = types)
        typesEqual rejectedNext
      simpa only [Renaming.results,Renaming.result,List.map_map,Function.comp_def,
        renamed_badType,subjectFixed,expectedFixed,bindingsFixed] using casted

/-- Replenishing depths preserves the same aligned type instance and complete
cast batch. The permutation is selected once, before the future grants. -/
theorem scoped_cast_source_to_worker_deepen (state : RecursiveTasks.Configuration) (scope : List String)
    (bindings : Bindings) (subject expected : Atom) (results : ResultSet)
    (retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state)
    (source : TypeCastBatchRel state.space subject expected bindings results
      (lookup := scopedTypeLookup scope state.space)) :
    ∃ names : Equiv.Perm String,
      (∀ name ∈ invocationTypeScope scope [] subject expected bindings, names name = name) ∧
      ∀ extra, TypeCastBatchRel (state.deepen extra).space subject expected bindings
        (Renaming.results names results)
        (lookup := fun frame atom demand types =>
          FirstSuccessRecursiveExecution.invocationTypes (state.deepen extra) frame atom demand = types) := by
  obtain ⟨names,fixed,casted⟩ := scoped_cast_source_to_worker state scope bindings subject expected results retained source
  refine ⟨names,fixed,fun extra => ?_⟩
  simpa only [RecursiveTasks.Configuration.deepen_space,
    FirstSuccessRecursiveExecution.invocationTypes_deepen] using casted

/-- The aligned complete batch preserves the caller's constraint observer
on every occurrence, not only the selected atom. Private spellings travel
together; repeated answers and diagnostics remain separate list entries. -/
theorem scoped_cast_observed (state : RecursiveTasks.Configuration) (scope : List String)
    (bindings : Bindings) (subject expected : Atom) (results : ResultSet)
    (retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state)
    (source : TypeCastBatchRel state.space subject expected bindings results
      (lookup := scopedTypeLookup scope state.space)) :
    ∃ actualResults, TypeCastBatchRel state.space subject expected bindings actualResults
        (lookup := fun frame atom demand types =>
          FirstSuccessRecursiveExecution.invocationTypes state frame atom demand = types) ∧
      ∃ names : Equiv.Perm String,
        (∀ name ∈ invocationTypeScope scope [] subject expected bindings, names name = name) ∧
        List.Forall₂ (fun original actual =>
          actual.1 = Spec.Type.RuntimeRefinement.renameTypeVars names original.1 ∧
          actual.2 = Spec.Bindings.ScopeObservation.renameBindings names original.2 ∧
          Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
            (invocationTypeScope scope [] subject expected bindings) original.2 actual.2)
          results actualResults := by
  obtain ⟨names,fixed,casted⟩ := scoped_cast_source_to_worker state scope bindings subject expected results retained source
  refine ⟨_,casted,names,fixed,?_⟩
  clear source casted
  induction results with
  | nil => exact .nil
  | cons result rest remaining =>
      exact .cons ⟨rfl,rfl,
        Spec.Bindings.ScopeObservation.BindingTheoryEquivAt.of_renameBindings
          _ result.2 names fixed⟩ remaining

/-- Atom demand has exactly one semantic result for arbitrary syntax,
bindings, nesting, quotation and error-shaped data. -/
theorem raw_result_unique
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {value : Atom} {bindings : BindingFrame} {result : FrameResult}
    (evaluated : EvalAtomRawRel space dispatch live (typing := typing)
      value Atom.atomType bindings result) : result = (value, bindings) := by
  cases evaluated with
  | emptyOrError => rfl
  | typePass => rfl
  | cast _ _ _ _ _ _ _ doesNotPass _ _ => exact (doesNotPass (Or.inl rfl)).elim
  | interpretSuccess _ _ _ _ _ _ _ doesNotPass _ _ _ => exact (doesNotPass (Or.inl rfl)).elim
  | interpretError _ _ _ _ _ _ _ doesNotPass _ _ _ => exact (doesNotPass (Or.inl rfl)).elim

theorem source_raw_reply_iff
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (result : ResultPair) :
    result ∈ evalAtom space source value Atom.atomType bindings (fuel + 1) ↔
      EvalAtomRawRel space semantic live (typing := typing)
        value Atom.atomType bindings result := by
  rw [evalAtom_raw_positive]
  simp only [List.mem_singleton]
  constructor
  · rintro rfl
    exact RetainedArgumentSpecification.atom_demand_raw space semantic live typing value bindings
  · intro evaluated
    exact BindingFrame.historicalResult_injective (raw_result_unique evaluated)

/-- Concrete source output constructs every reply witness in occurrence
order; the complete reply is a singleton rather than a support quotient. -/
theorem source_raw_reply
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (value : Atom) (bindings : Bindings)
    (fuel : Nat) :
    evalAtom space source value Atom.atomType bindings (fuel + 1) = [(value, bindings)] ∧
      EvalAtomRawRel space semantic live (typing := typing)
        value Atom.atomType bindings (value, bindings) :=
  ⟨evalAtom_raw_positive space source value bindings fuel,
    RetainedArgumentSpecification.atom_demand_raw space semantic live typing value bindings⟩

theorem raw_arguments_unique
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {values : List Atom} {bindings : BindingFrame} {result : FrameResult}
    (evaluated : InterpretArgsRel space dispatch live (typing := typing)
      values (List.replicate values.length Atom.atomType) bindings result) :
    result = (argumentPacket values, bindings) := by
  induction values generalizing live bindings result with
  | nil => cases evaluated; rfl
  | cons value values ih =>
      cases evaluated with
      | headChangedError _ _ _ _ _ head evaluated _ changed =>
          have returned := raw_result_unique evaluated
          cases returned
          exact (changed rfl).elim
      | tailError _ _ _ _ _ head tail evaluated _ remaining notPacket =>
          have returned := raw_result_unique evaluated
          cases returned
          have tailReturned := ih remaining
          cases tailReturned
          exact (notPacket values rfl).elim
      | success _ _ _ _ _ head tail evaluated _ remaining _ =>
          have returned := raw_result_unique evaluated
          cases returned
          have tailReturned := ih remaining
          cases tailReturned
          simp only [argumentValues_packet]

theorem source_raw_arguments_iff
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (values : List Atom) (bindings : Bindings)
    (fuel : Nat) (enough : values.length < fuel) (result : ResultPair) :
    result ∈ interpretArgs space source values (List.replicate values.length Atom.atomType)
      bindings fuel ↔
      InterpretArgsRel space semantic live (typing := typing)
        values (List.replicate values.length Atom.atomType) bindings result := by
  rw [interpretArgs_raw space source values bindings fuel enough]
  simp only [List.mem_singleton]
  constructor
  · rintro rfl
    simpa only [List.map_map, Function.comp_def, List.map_id', BindingFrame.historicalResult_pair] using
      RetainedArgumentSpecification.history_to_arguments
        (RetainedArgumentSpecification.raw_history space semantic live typing values bindings)
  · intro evaluated
    exact BindingFrame.historicalResult_injective (raw_arguments_unique evaluated)

/-- One raw source callback is delivered to its exact currently pending
endpoint. Semantic truth is constructed separately from serial acceptance. -/
theorem deliver_source_raw
    (configuration : NativeArgumentControl.Configuration) (argument : TypedApplyState)
    (prepared : NativeArgumentControl.Prepared) (rest : List NativeArgumentControl.Frame)
    (ticket : Nat) (pending : configuration.frames =
      .waiting (.evaluate argument prepared) ticket :: rest)
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (fuel charge : Nat)
    (raw : prepared.domain = Atom.atomType) :
    ∃ after, NativeArgumentControl.DeliveryRel configuration
      ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
        .evaluated (evalAtom space source prepared.bound prepared.domain argument.env (fuel + 1)),
        charge⟩ after ∧
      EvalAtomRawRel space semantic live (typing := typing)
        prepared.bound prepared.domain argument.env (prepared.bound, argument.env) := by
  rw [raw, evalAtom_raw_positive]
  refine ⟨NativeArgumentControl.replied configuration rest
    ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
      .evaluated [(prepared.bound, argument.env)], charge⟩
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared
      [(prepared.bound, argument.env)]) prepared], ?_, ?_⟩
  · apply (NativeArgumentControl.deliver_iff _ _ _).mp
    exact NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      [(prepared.bound, argument.env)] charge pending
  · exact RetainedArgumentSpecification.atom_demand_raw space semantic live typing
      prepared.bound argument.env

namespace ScopedControls

open Spec.Type.RuntimeRefinement Spec.Type.Presentation
open Spec.Type.Presentation.Exact Spec.Bindings.ScopeObservation Spec.Match.Merge

private def caller : Bindings :=
  ⟨[("kept",.var "representative"),("scheme",.symbol "Number")],[("linked","representative")]⟩
private def context : Space := Space.ofList [.expression [.symbol ":",.symbol "datum",.var "scheme"]]
private def state : RecursiveTasks.Configuration :=
  {RecursiveTasks.Configuration.initial context (.atom (.symbol "datum") (.var "wanted") caller 0 [.var "caller"]) with
    stack := [.prepend [(.var "saved",caller)]], emitted := [(.var "published",caller)]}
private def scope : List String := ["caller","saved","published"]

private theorem retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state := by decide +kernel

private theorem query : scopedTypeLookup scope context caller (.symbol "datum") (.var "wanted") [.var "chosen"] := by
  refine ⟨[.var "scheme"],?_,.cons ?_ (.nil _)⟩
  · simpa only [show getAtomTypes context (.symbol "datum") = [.var "scheme"] by decide +kernel] using
      source_types context (.symbol "datum")
  · refine ⟨Equiv.swap "scheme" "chosen",Equiv.injective _,?_,?_⟩
    · simp
    · intro name member
      obtain rfl := List.mem_singleton.mp member
      decide +kernel

private theorem matched : TypeMatchRel (.var "wanted") (.var "chosen") caller
    (caller.addEquality "wanted" "chosen") := by
  refine .structural (by intro same; cases same) (by intro same; cases same)
    (by intro same; cases same) (by intro same; cases same)
    (.varVar _ _ (semanticLoopFree_of_assignments_nil rfl)) ?_
  refine .mk (order := [.equality "wanted" "chosen"]) ?_
    (.equality (.consistent (values := []) (by decide +kernel) trivial) .nil)
  decide +kernel

private theorem casted : TypeCastBatchRel context (.symbol "datum") (.var "wanted") caller
    [(.symbol "datum",caller.addEquality "wanted" "chosen")]
    (lookup := scopedTypeLookup scope context) :=
  .success (earlierTypes := []) (laterTypes := []) query rfl (by simp) matched

/-- The caller has a bare alias, an equality and an existing assignment of
the raw schematic spelling. Saved and already published variable names are
protected, even when the retained evaluator has no remaining depth. -/
theorem changed_alias_cast_survives_every_grant :
    ∃ names : Equiv.Perm String,
      (∀ name ∈ invocationTypeScope scope [] (.symbol "datum") (.var "wanted") caller, names name = name) ∧
      ∀ extra, TypeCastBatchRel (state.deepen extra).space (.symbol "datum") (.var "wanted") caller
        (Renaming.results names [(.symbol "datum",caller.addEquality "wanted" "chosen")])
        (lookup := fun frame atom demand types =>
          FirstSuccessRecursiveExecution.invocationTypes (state.deepen extra) frame atom demand = types) :=
  scoped_cast_source_to_worker_deepen state scope caller _ _ _ retained casted

theorem cast_really_changes_constraints : caller.addEquality "wanted" "chosen" ≠ caller := by decide +kernel

private def duplicateContext : Space := Space.ofList
  [.expression [.symbol ":",.symbol "datum",.symbol "A"],
   .expression [.symbol ":",.symbol "datum",.symbol "A"]]
private def duplicateState : RecursiveTasks.Configuration :=
  RecursiveTasks.Configuration.initial duplicateContext (.atom (.symbol "datum") (.symbol "B") caller 0 [])

private theorem duplicate_query : FirstSuccessRecursiveExecution.invocationTypes duplicateState caller
    (.symbol "datum") (.symbol "B") = [.symbol "A",.symbol "A"] := by decide +kernel

private theorem rejected (output : Bindings) : ¬TypeMatchRel (.symbol "B") (.symbol "A") caller output := by
  intro matched
  obtain ⟨_,structural,_⟩ := matched.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide)
  exact symbol_mismatch_not_match (by decide) _ structural

theorem duplicate_failures_complete : TypeCastBatchRel duplicateContext (.symbol "datum") (.symbol "B") caller
    [(mkError (.symbol "datum") (.badType (.symbol "B") (.symbol "A")),caller),
     (mkError (.symbol "datum") (.badType (.symbol "B") (.symbol "A")),caller)]
    (lookup := fun frame atom demand types =>
      FirstSuccessRecursiveExecution.invocationTypes duplicateState frame atom demand = types) := by
  apply TypeCastBatchRel.failure (types := [.symbol "A",.symbol "A"]) duplicate_query
  intro actual member output
  obtain rfl : actual = .symbol "A" := by simpa using member
  exact rejected output

/-- A completed failing query cannot drop an occurrence of a duplicate type
annotation. This inverts every completed batch, not only the control above. -/
theorem duplicate_failures_cannot_drop_occurrence {results : ResultSet}
    (completed : TypeCastBatchRel duplicateContext (.symbol "datum") (.symbol "B") caller results
      (lookup := fun frame atom demand types =>
        FirstSuccessRecursiveExecution.invocationTypes duplicateState frame atom demand = types)) :
    results.length = 2 := by
  cases completed with
  | @success _ _ types earlier later actual output queried selected _ matched =>
      have member : actual ∈ types := by rw [selected]; simp
      rw [←queried,duplicate_query] at member
      obtain rfl : actual = .symbol "A" := by simpa using member
      exact (rejected output matched).elim
  | failure queried _ => simp only [List.length_map,←queried,duplicate_query]; rfl

/-- Pointwise alpha similarity cannot license merging two private variable
identities. A coherent permutation preserves the whole family's equality
pattern, including correlations across its occurrences. -/
theorem coherent_family_cannot_merge_distinct (left right common : String) (different : left ≠ right) :
    ¬∃ names : Equiv.Perm String,
      [.var common,.var common] = ([.var left,.var right] : List Atom).map (renameTypeVars names) := by
  rintro ⟨names,equal⟩
  simp only [List.map_cons,List.map_nil,renameTypeVars] at equal
  have first := Atom.var.inj (List.cons.inj equal).1
  have second := Atom.var.inj (List.cons.inj (List.cons.inj equal).2).1
  exact different (names.injective (first.symm.trans second))

end ScopedControls

/-! ## Primitive `matchTypes` Cardinality, Coverage Unfolding, and Ordered `typeCastLoop` Fold -/

/-- Principal-result cardinality of `matchTypes`: every call returns at most one
binding record (either `[]` or `[out]`), unconditionally across all syntax and fuel. -/
theorem matchTypes_length_le_one (expected actual : Atom) (b : Bindings) (depth : Nat) :
    (matchTypes expected actual b depth).length ≤ 1 := by
  unfold matchTypes
  split
  · simp
  · have hAtoms := matchAtoms_length_le_one expected actual depth
    generalize matchAtoms expected actual depth = matched at hAtoms
    cases matched with
    | nil => simp
    | cons mb rest =>
        cases rest with
        | nil =>
            simpa using mergeBindings_length_le_one b mb depth
        | cons _ _ =>
            simp at hAtoms

/-- Any member `out ∈ matchTypes expected actual b depth` is its unique element. -/
theorem matchTypes_eq_singleton_of_mem {expected actual : Atom} {b out : Bindings} {depth : Nat}
    (mem : out ∈ matchTypes expected actual b depth) :
    matchTypes expected actual b depth = [out] := by
  have hLen := matchTypes_length_le_one expected actual b depth
  generalize matchTypes expected actual b depth = mtch at mem hLen
  cases mtch with
  | nil => cases mem
  | cons hd tl =>
      cases tl with
      | nil =>
          simp only [List.mem_singleton] at mem
          rw [mem]
      | cons _ _ =>
          simp at hLen

/-- Every `matchTypes` evaluation is either `[]` or a singleton `[out]`. -/
theorem matchTypes_eq_nil_or_singleton (expected actual : Atom) (b : Bindings) (depth : Nat) :
    matchTypes expected actual b depth = [] ∨
      ∃ out, matchTypes expected actual b depth = [out] := by
  cases h : matchTypes expected actual b depth with
  | nil => exact Or.inl rfl
  | cons hd tl =>
      have hMem : hd ∈ matchTypes expected actual b depth := by
        rw [h]
        exact List.mem_cons_self
      exact Or.inr ⟨hd, h ▸ matchTypes_eq_singleton_of_mem hMem⟩

/-- Outside the two wildcard types (`%Undefined%` and `Atom`), `matchTypesCovered`
unfolds into atom-match coverage plus merge coverage on every atom-match output. -/
theorem matchTypesCovered_nonWildcard_iff
    {expected actual : Atom} (b : Bindings) (depth : Nat)
    (notUndefLeft : expected ≠ Atom.undefinedType)
    (notAtomLeft : expected ≠ Atom.atomType)
    (notUndefRight : actual ≠ Atom.undefinedType)
    (notAtomRight : actual ≠ Atom.atomType) :
    matchTypesCovered expected actual b depth = true ↔
      matchCovered depth (.atoms expected actual) = true ∧
        ∀ mb ∈ matchAtoms expected actual depth,
          matchCovered depth (.merge b mb) = true := by
  have hGate :
      (expected == Atom.undefinedType || expected == Atom.atomType ||
       actual == Atom.undefinedType || actual == Atom.atomType) = false := by
    simp [notUndefLeft, notAtomLeft, notUndefRight, notAtomRight]
  unfold matchTypesCovered MatchDepth.queryCovered MatchDepth.typesQuery
  rw [if_neg (by simp [hGate])]
  simp [Mettapedia.Machines.ReadOnlyQuery.run,
    Mettapedia.Machines.ReadOnlyQuery.run_flatTraverse_reads, evalMatch]

/-- One-step coverage unfolding of `TypeCheckDepth.castLoopQuery` on `t :: rest`:
coverage holds if and only if `matchTypesCovered expectedType t b depth = true` and,
when `matchTypes expectedType t b depth` is empty, the remaining suffix query is covered. -/
theorem castLoopQuery_covered_cons_iff
    (t : Atom) (rest : List Atom) (atom expectedType : Atom)
    (b : Bindings) (depth : Nat) (noMatch : List Atom) :
    MatchDepth.queryCovered depth
      (TypeCheckDepth.castLoopQuery (t :: rest) atom expectedType b noMatch) = true ↔
      matchTypesCovered expectedType t b depth = true ∧
        (if (matchTypes expectedType t b depth).isEmpty then
          MatchDepth.queryCovered depth
            (TypeCheckDepth.castLoopQuery rest atom expectedType b (noMatch ++ [t])) = true
         else True) := by
  rw [TypeCheckDepth.castLoopQuery]
  unfold matchTypesCovered MatchDepth.queryCovered
  rw [Mettapedia.Machines.ReadOnlyQuery.run_bind, List.all_append, Bool.and_eq_true,
    MatchDepth.run_typesQuery]
  constructor
  · rintro ⟨hHead, hTail⟩
    refine ⟨hHead, ?_⟩
    split
    · rename_i hEmpty
      simp only [hEmpty, ↓reduceIte] at hTail
      exact hTail
    · trivial
  · rintro ⟨hHead, hTail⟩
    refine ⟨hHead, ?_⟩
    split at hTail
    · rename_i hEmpty
      simp only [hEmpty, ↓reduceIte]
      exact hTail
    · rename_i hNotEmpty
      simp [hNotEmpty, Mettapedia.Machines.ReadOnlyQuery.run]

/-- Pointwise `List.Forall₂` on diagnostic error maps when `rel b b` holds. -/
private theorem forall2_error_map_refl
    {rel : Bindings → Bindings → Prop} {b : Bindings} (hRefl : rel b b)
    (atom expectedType : Atom) (types : List Atom) :
    List.Forall₂ (fun w s : ResultPair => w.1 = s.1 ∧ rel w.2 s.2)
      (types.map fun actual => (mkError atom (.badType expectedType actual), b))
      (types.map fun actual => (mkError atom (.badType expectedType actual), b)) := by
  induction types with
  | nil => exact .nil
  | cons actual rest ih => exact .cons ⟨rfl, hRefl⟩ ih

/-- Ordered Cast-Fold Law (`typeCastLoop_to_typeCastBatch_related`):
Inducts over the remaining candidate list `types` with accumulated rejected prefix `noMatch`
(`allTypes = noMatch ++ types`), using `matchTypes_eq_nil_or_singleton` (principal-result
cardinality) and `castLoopQuery_covered_cons_iff` (coverage unfolding) to construct a
complete `TypeCastBatchRel` batch `sourceResults` aligned with `typeCast.typeCastLoop`
via `List.Forall₂`, preserving first-success selection, all earlier rejected candidates,
and every duplicate failure occurrence. -/
theorem typeCastLoop_to_typeCastBatch_related
    (space : Space) (atom expectedType : Atom) (b : Bindings) (depth : Nat)
    (sourceLookup : TypeLookupRel)
    (matching : Atom → Atom → Bindings → Bindings → Prop)
    (rel : Bindings → Bindings → Prop)
    (pred : Bindings → Prop)
    (hRefl : rel b b)
    (hPredIn : pred b)
    (allTypes types noMatch : List Atom)
    (hLookup : sourceLookup b atom expectedType allTypes)
    (hSplit : allTypes = noMatch ++ types)
    (hCov : MatchDepth.queryCovered depth
      (TypeCheckDepth.castLoopQuery types atom expectedType b noMatch) = true)
    (hEarlier : ∀ earlier ∈ noMatch, ∀ candidate, ¬matching expectedType earlier b candidate)
    (hReject : ∀ actual ∈ types,
      matchTypesCovered expectedType actual b depth = true →
      matchTypes expectedType actual b depth = [] →
      ∀ candidate, ¬matching expectedType actual b candidate)
    (hAccept : ∀ actual ∈ types, ∀ out ∈ matchTypes expectedType actual b depth,
      matchTypesCovered expectedType actual b depth = true →
      (atom, out) ∈ typeCast.typeCastLoop types atom expectedType b depth noMatch →
      ∃ sourceOut, matching expectedType actual b sourceOut ∧
        rel out sourceOut ∧ pred sourceOut) :
    ∃ sourceResults : ResultSet,
      TypeCastBatchRel space atom expectedType b sourceResults
        (lookup := sourceLookup) (matching := matching) ∧
      List.Forall₂ (fun w s : ResultPair => w.1 = s.1 ∧ rel w.2 s.2)
        (typeCast.typeCastLoop types atom expectedType b depth noMatch)
        sourceResults ∧
      (∀ r ∈ sourceResults, pred r.2) := by
  induction types generalizing noMatch with
  | nil =>
      have hAllEq : allTypes = noMatch := by simpa using hSplit
      subst hAllEq
      refine ⟨allTypes.map fun actual => (mkError atom (.badType expectedType actual), b),
        TypeCastBatchRel.failure hLookup hEarlier,
        forall2_error_map_refl hRefl atom expectedType allTypes, ?_⟩
      intro r hMem
      obtain ⟨actual, _, rfl⟩ := List.mem_map.mp hMem
      exact hPredIn
  | cons actual laterTypes ih =>
      obtain ⟨hHeadCov, hTailCov⟩ :=
        (castLoopQuery_covered_cons_iff actual laterTypes atom expectedType b depth noMatch).mp hCov
      rcases matchTypes_eq_nil_or_singleton expectedType actual b depth with hEmpty | ⟨out, hSingle⟩
      · have hTailCov' :
            MatchDepth.queryCovered depth
              (TypeCheckDepth.castLoopQuery laterTypes atom expectedType b (noMatch ++ [actual])) = true := by
          simpa [hEmpty] using hTailCov
        have hLoopEq :
            typeCast.typeCastLoop (actual :: laterTypes) atom expectedType b depth noMatch =
              typeCast.typeCastLoop laterTypes atom expectedType b depth (noMatch ++ [actual]) := by
          simp [typeCast.typeCastLoop, hEmpty]
        have hActualRej : ∀ candidate, ¬matching expectedType actual b candidate :=
          hReject actual List.mem_cons_self hHeadCov hEmpty
        have hEarlier' :
            ∀ earlier ∈ noMatch ++ [actual], ∀ candidate, ¬matching expectedType earlier b candidate := by
          intro earlier hMem
          rcases List.mem_append.mp hMem with hOld | hSingleMem
          · exact hEarlier earlier hOld
          · obtain rfl := List.mem_singleton.mp hSingleMem
            exact hActualRej
        have hSplit' : allTypes = (noMatch ++ [actual]) ++ laterTypes := by
          simpa [List.append_assoc] using hSplit
        have hReject' :
            ∀ next ∈ laterTypes,
              matchTypesCovered expectedType next b depth = true →
              matchTypes expectedType next b depth = [] →
              ∀ candidate, ¬matching expectedType next b candidate :=
          fun next hMem => hReject next (List.mem_cons_of_mem actual hMem)
        have hAccept' :
            ∀ next ∈ laterTypes, ∀ out ∈ matchTypes expectedType next b depth,
              matchTypesCovered expectedType next b depth = true →
              (atom, out) ∈ typeCast.typeCastLoop laterTypes atom expectedType b depth (noMatch ++ [actual]) →
              ∃ sourceOut, matching expectedType next b sourceOut ∧
                rel out sourceOut ∧ pred sourceOut := by
          intro next hMem out hOutMem hNextCov hPairMem
          apply hAccept next (List.mem_cons_of_mem actual hMem) out hOutMem hNextCov
          rwa [hLoopEq]
        rw [hLoopEq]
        exact ih (noMatch ++ [actual]) hSplit' hTailCov' hEarlier' hReject' hAccept'
      · have hOutMem : out ∈ matchTypes expectedType actual b depth := by
          rw [hSingle]
          exact List.mem_cons_self
        have hLoopEq :
            typeCast.typeCastLoop (actual :: laterTypes) atom expectedType b depth noMatch =
              [(atom, out)] := by
          simp [typeCast.typeCastLoop, hSingle]
        have hPairMem :
            (atom, out) ∈ typeCast.typeCastLoop (actual :: laterTypes) atom expectedType b depth noMatch := by
          rw [hLoopEq]
          exact List.mem_cons_self
        obtain ⟨sourceOut, hMatch, hRel, hPred⟩ :=
          hAccept actual List.mem_cons_self out hOutMem hHeadCov hPairMem
        refine ⟨[(atom, sourceOut)],
          TypeCastBatchRel.success hLookup hSplit hEarlier hMatch,
          by rw [hLoopEq]; exact .cons ⟨rfl, hRel⟩ .nil, ?_⟩
        intro r hMem
        obtain rfl := List.mem_singleton.mp hMem
        exact hPred

/-- Top-level `typeCast` specialization of `typeCastLoop_to_typeCastBatch_related`:
constructs a complete `TypeCastBatchRel` derivation for `typeCast atom expectedType space b depth lookup`
from `typeCastCovered atom expectedType space b depth lookup = true` and the local comparison
obligations on `lookup b atom expectedType`. -/
theorem typeCast_to_typeCastBatch_related
    (space : Space) (atom expectedType : Atom) (b : Bindings) (depth : Nat)
    (lookup : TypeLookup)
    (sourceLookup : TypeLookupRel)
    (matching : Atom → Atom → Bindings → Bindings → Prop)
    (rel : Bindings → Bindings → Prop)
    (pred : Bindings → Prop)
    (hRefl : rel b b)
    (hPredIn : pred b)
    (hLookup : sourceLookup b atom expectedType (lookup b atom expectedType))
    (hCov : typeCastCovered atom expectedType space b depth lookup = true)
    (hReject : ∀ actual ∈ lookup b atom expectedType,
      matchTypesCovered expectedType actual b depth = true →
      matchTypes expectedType actual b depth = [] →
      ∀ candidate, ¬matching expectedType actual b candidate)
    (hAccept : ∀ actual ∈ lookup b atom expectedType,
      ∀ out ∈ matchTypes expectedType actual b depth,
      matchTypesCovered expectedType actual b depth = true →
      (atom, out) ∈ typeCast atom expectedType space b depth lookup →
      ∃ sourceOut, matching expectedType actual b sourceOut ∧
        rel out sourceOut ∧ pred sourceOut) :
    ∃ sourceResults : ResultSet,
      TypeCastBatchRel space atom expectedType b sourceResults
        (lookup := sourceLookup) (matching := matching) ∧
      List.Forall₂ (fun w s : ResultPair => w.1 = s.1 ∧ rel w.2 s.2)
        (typeCast atom expectedType space b depth lookup)
        sourceResults ∧
      (∀ r ∈ sourceResults, pred r.2) := by
  exact typeCastLoop_to_typeCastBatch_related space atom expectedType b depth
    sourceLookup matching rel pred hRefl hPredIn
    (lookup b atom expectedType) (lookup b atom expectedType) []
    hLookup rfl hCov (by intro _ h; cases h) hReject hAccept

/-- Policy-generic generalization of `scoped_cast_worker_to_source`: a completed cast
using the actual worker query `invocationTypes state` is a source cast under
`scopedTypeLookup scope state.space` for any `matching` policy. -/
theorem scoped_cast_worker_to_source_matching
    (state : RecursiveTasks.Configuration) (scope : List String)
    (bindings : Bindings) (subject expected : Atom) (results : ResultSet)
    (matching : Atom → Atom → Bindings → Bindings → Prop)
    (retained : ∀ name ∈ scope, name ∈ RecursiveScope.configurationNames state)
    (source : TypeCastBatchRel state.space subject expected bindings results
      (lookup := fun frame atom demand types =>
        FirstSuccessRecursiveExecution.invocationTypes state frame atom demand = types)
      (matching := matching)) :
    TypeCastBatchRel state.space subject expected bindings results
      (lookup := scopedTypeLookup scope state.space)
      (matching := matching) := by
  apply source.change_lookup
  intro types queried
  rw [← queried]
  exact scoped_source_types state scope bindings subject expected retained

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies
