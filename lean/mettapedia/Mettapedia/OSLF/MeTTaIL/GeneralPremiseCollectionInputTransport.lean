import Mettapedia.OSLF.MeTTaIL.GeneralPremiseNullaryTransport
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.OSLF.MeTTaIL.StructuralDescentDepth

/-!
# Canonical transport of typed provider queries

Mixed input/output queries transport through their actual scoped operations.
Checked object input templates preserve canonical reads; ordinary output
matching on canonical provider values preserves its complete allocation trace,
including nested sets. Provider-row occurrences and final captures are retained.
The whole-variable input results remain specializations. Query semantics is
unchanged; quantified and child-step premises need additional transport laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching CanonicalBags

/-! ## Mode-parametric provider queries -/

/-- Inputs use the general checked object-template reader. Outputs use the
ordinary traced matcher on the already canonical provider value, with no
restriction on the schema's collection nesting or rest variables. -/
def checkCanonicalQueryArguments (context : Context) : Nat → List Pattern → List RelationArgMode → Bool
  | _, [], [] => true
  | index, schema :: schemas, .input :: modes =>
      checkCanonicalRead context.rule context.spec (context.site index) [] 0 schema &&
        checkCanonicalQueryArguments context (index + 1) schemas modes
  | index, _ :: schemas, .output :: modes =>
      checkCanonicalQueryArguments context (index + 1) schemas modes
  | _, _, _ => false

theorem Interpreted.TracedArgumentsHold.canonical_transport {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins)
    (increasing : IncreasingSpines context.rule context.spec)
    (checked : checkCanonicalQueryArguments context index schemas modes = true)
    (canonical : ∀ value ∈ values, canon value = value) :
    GeneralPremise.TracedArgumentsHold context index (canonAssignment initial) schemas values modes
      (canonAssignment final) origins := by
  induction held with
  | nil => exact .nil
  | @input index initial final schema value schemas values modes origins projected tail ih =>
    simp only [checkCanonicalQueryArguments, Bool.and_eq_true] at checked
    exact .input
      (instantiateWith?_canonical_result Substitution.instantiateBVar context.rule context.spec
        context.bound.length (context.site index) [] 0 _ _ _ checked.1 projected
        (canonical _ List.mem_cons_self))
      (ih checked.2 (fun value member => canonical value (List.mem_cons_of_mem _ member)))
  | output matched tail ih =>
    exact .output (traced_matches_canonical_subject increasing matched (canonical _ List.mem_cons_self))
      (ih checked (fun value member => canonical value (List.mem_cons_of_mem _ member)))

def CanonicalQueryGuard (provider : ProviderSnapshot) (context : Context) (premise : Premise) : Prop :=
  ∃ relation arguments signature, premise = .relationQuery relation arguments ∧
    signature? provider relation arguments.length = some signature ∧
      checkCanonicalQueryArguments context 0 arguments signature.modes = true

def checkCanonicalQueryGuard (provider : ProviderSnapshot) (context : Context) : Premise → Bool
  | .relationQuery relation arguments =>
      (signature? provider relation arguments.length).any fun signature =>
        checkCanonicalQueryArguments context 0 arguments signature.modes
  | _ => false

theorem checkCanonicalQueryGuard_iff (provider : ProviderSnapshot) (context : Context) (premise : Premise) :
    checkCanonicalQueryGuard provider context premise = true ↔ CanonicalQueryGuard provider context premise := by
  cases premise with
  | relationQuery relation arguments =>
    simp only [checkCanonicalQueryGuard, Option.any_eq_true]
    constructor
    · rintro ⟨signature, declared, checked⟩
      exact ⟨relation, arguments, signature, rfl, declared, checked⟩
    · rintro ⟨relation', arguments', signature, same, declared, checked⟩
      cases same
      exact ⟨signature, declared, checked⟩
  | _ => simp [checkCanonicalQueryGuard, CanonicalQueryGuard]

def CanonicalQueryGuards (provider : ProviderSnapshot) : Context → List Premise → Prop
  | _, [] => True
  | context, premise :: premises =>
      CanonicalQueryGuard provider context premise ∧ CanonicalQueryGuards provider context.next premises

def checkCanonicalQueryGuards (provider : ProviderSnapshot) : Context → List Premise → Bool
  | _, [] => true
  | context, premise :: premises =>
      checkCanonicalQueryGuard provider context premise && checkCanonicalQueryGuards provider context.next premises

theorem checkCanonicalQueryGuards_iff (provider : ProviderSnapshot) (context : Context) (premises : List Premise) :
    checkCanonicalQueryGuards provider context premises = true ↔ CanonicalQueryGuards provider context premises := by
  induction premises generalizing context with
  | nil => simp [checkCanonicalQueryGuards, CanonicalQueryGuards]
  | cons premise premises ih =>
    simp only [checkCanonicalQueryGuards, Bool.and_eq_true, checkCanonicalQueryGuard_iff, ih, CanonicalQueryGuards]

/-- Whole-variable input occurrences, each with its actual empty scoped spine. -/
def CollectionInputs (context : Context) : Nat → List Pattern → Prop
  | _, [] => True
  | index, .fvar name :: arguments =>
      arguments? context.rule context.spec name (context.site index) [] = some [] ∧
        CollectionInputs context (index + 1) arguments
  | _, _ :: _ => False
termination_by structural _ arguments => arguments

/-- Provider rows use the same canonical representatives as captured inputs.
Repeated rows remain distinct occurrences in the provider list. -/
def CanonicalProviderRows (provider : ProviderSnapshot) : Prop :=
  ∀ row ∈ provider.rows, ∀ value ∈ row.values, canon value = value

def checkCollectionInputs (context : Context) : Nat → List Pattern → Bool
  | _, [] => true
  | index, .fvar name :: arguments =>
      arguments? context.rule context.spec name (context.site index) [] == some [] &&
        checkCollectionInputs context (index + 1) arguments
  | _, _ :: _ => false
termination_by structural _ arguments => arguments

theorem checkCollectionInputs_iff (context : Context) (index : Nat) (arguments : List Pattern) :
    checkCollectionInputs context index arguments = true ↔ CollectionInputs context index arguments := by
  induction arguments generalizing index with
  | nil => simp [checkCollectionInputs, CollectionInputs]
  | cons argument arguments ih =>
    cases argument <;> simp [checkCollectionInputs, CollectionInputs, ih]

def checkCanonicalProviderRows (provider : ProviderSnapshot) : Bool :=
  provider.rows.all fun row => row.values.all fun value => canon value == value

theorem checkCanonicalProviderRows_iff (provider : ProviderSnapshot) :
    checkCanonicalProviderRows provider = true ↔ CanonicalProviderRows provider := by
  simp only [checkCanonicalProviderRows, List.all_eq_true, beq_iff_eq, CanonicalProviderRows]

theorem Interpreted.TracedQuery.canonical_transport {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins)
    (increasing : IncreasingSpines context.rule context.spec)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (checked : ∀ signature, signature? environment.provider relation arguments.length = some signature →
      checkCanonicalQueryArguments context 0 arguments signature.modes = true) :
    GeneralPremise.TracedQuery environment context relation arguments (canonAssignment initial) rowIndex
      (canonAssignment final) origins := by
  cases held with
  | row selected declared typed arguments finalTyped =>
    exact .row selected declared typed
      (arguments.canonical_transport increasing (checked _ declared)
        (rows _ (List.mem_of_getElem? selected))) (typedAssignment_canon finalTyped)
  | dynamicRow registered _ _ _ _ _ _ _ => rw [finite] at registered; cases registered

theorem Interpreted.PremiseHolds.canonical_query_transport {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : GeneralPremise.PremiseHolds environment context premise initial final event)
    (increasing : IncreasingSpines context.rule context.spec)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CanonicalQueryGuard environment.provider context premise) :
    GeneralPremise.PremiseHolds environment context premise (canonAssignment initial) (canonAssignment final) event := by
  obtain ⟨relation, arguments, signature, rfl, declared, checked⟩ := guarded
  cases held with
  | query query =>
    exact .query (query.canonical_transport increasing finite rows (fun actual found => by
      have same := Option.some.inj (declared.symm.trans found)
      simpa only [← same] using checked))

theorem Interpreted.PremisesHold.canonical_query_transport {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {history : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (increasing : IncreasingSpines context.rule context.spec)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CanonicalQueryGuards environment.provider context premises) :
    GeneralPremise.PremisesHold environment context premises (canonAssignment initial) (canonAssignment final) history := by
  cases held with
  | nil => exact .nil
  | cons head tail =>
    exact .cons (head.canonical_query_transport increasing finite rows guarded.1)
      (tail.canonical_query_transport increasing finite rows guarded.2)
termination_by premises.length
decreasing_by all_goals simp_all [List.length_cons]

theorem Interpreted.PremisesHold.canonical_query_history_depth {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {history : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (guarded : CanonicalQueryGuards environment.provider context premises) :
    StructuralDescent.eventsDepth history = 0 := by
  cases held with
  | nil => simp only [StructuralDescent.eventsDepth]
  | cons head tail =>
    obtain ⟨relation, arguments, signature, same, _, _⟩ := guarded.1
    subst same
    have rest := tail.canonical_query_history_depth guarded.2
    cases head with
    | query _ => simp only [StructuralDescent.eventsDepth, StructuralDescent.eventDepth, rest, Nat.max_self]
termination_by premises.length
decreasing_by all_goals simp_all [List.length_cons]

/-- A local query declaration with input modes and whole-capture projections. -/
def CollectionInputGuard (provider : ProviderSnapshot) (context : Context) (premise : Premise) : Prop :=
  ∃ relation arguments signature, premise = .relationQuery relation arguments ∧
    signature? provider relation arguments.length = some signature ∧
    signature.modes = List.replicate arguments.length .input ∧ CollectionInputs context 0 arguments

def checkCollectionInputGuard (provider : ProviderSnapshot) (context : Context) : Premise → Bool
  | .relationQuery relation arguments =>
      checkCollectionInputs context 0 arguments &&
        (signature? provider relation arguments.length).any fun signature =>
          decide (signature.modes = List.replicate arguments.length .input)
  | _ => false

theorem checkCollectionInputGuard_iff (provider : ProviderSnapshot) (context : Context) (premise : Premise) :
    checkCollectionInputGuard provider context premise = true ↔ CollectionInputGuard provider context premise := by
  cases premise with
  | relationQuery relation arguments =>
    simp only [checkCollectionInputGuard, Bool.and_eq_true, checkCollectionInputs_iff,
      Option.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨inputs, signature, declared, modes⟩
      exact ⟨relation, arguments, signature, rfl, declared, modes, inputs⟩
    · rintro ⟨relation', arguments', signature, same, declared, modes, inputs⟩
      cases same
      exact ⟨inputs, signature, declared, modes⟩
  | _ => simp [checkCollectionInputGuard, CollectionInputGuard]

def CollectionInputGuards (provider : ProviderSnapshot) : Context → List Premise → Prop
  | _, [] => True
  | context, premise :: premises =>
      CollectionInputGuard provider context premise ∧ CollectionInputGuards provider context.next premises
termination_by structural _ premises => premises

def checkCollectionInputGuards (provider : ProviderSnapshot) : Context → List Premise → Bool
  | _, [] => true
  | context, premise :: premises =>
      checkCollectionInputGuard provider context premise && checkCollectionInputGuards provider context.next premises
termination_by structural _ premises => premises

theorem checkCollectionInputGuards_iff (provider : ProviderSnapshot) (context : Context) (premises : List Premise) :
    checkCollectionInputGuards provider context premises = true ↔ CollectionInputGuards provider context premises := by
  induction premises generalizing context with
  | nil => simp [checkCollectionInputGuards, CollectionInputGuards]
  | cons premise premises ih =>
    simp only [checkCollectionInputGuards, Bool.and_eq_true, checkCollectionInputGuard_iff,
      ih, CollectionInputGuards]

theorem instantiateValue?_root_canon {value : ContextualValue} {ambient : Nat} {actual : Pattern}
    (projected : instantiateValue? value ambient 0 [] = some actual) :
    instantiateValue? (canonValue value) ambient 0 [] = some (canon actual) := by
  obtain ⟨other, read, _⟩ := instantiateValue?_same
    (show ValueSame value (canonValue value) from
      ⟨rfl, rfl, (canon_idempotent value.body).symm⟩) ambient 0 [] actual projected
  have before := (ConditionalEquationExecution.instantiate_root_readout value ambient actual projected).2
  have after := (ConditionalEquationExecution.instantiate_root_readout (canonValue value) ambient other read).2
  simpa only [before, after, canonValue] using read

theorem instantiateAt?_input_canon {context : Context} {assignment : Assignment}
    {index : Nat} {name : String} {actual : Pattern}
    (spine : arguments? context.rule context.spec name (context.site index) [] = some [])
    (projected : instantiateAt? context.rule context.spec context.bound.length (context.site index) []
      0 assignment (.fvar name) = some actual) :
    instantiateAt? context.rule context.spec context.bound.length (context.site index) []
      0 (canonAssignment assignment) (.fvar name) = some (canon actual) := by
  simp only [instantiateAt?, instantiateWith?, spine, Option.bind_eq_bind,
    Option.bind_some, Option.bind_eq_some_iff] at projected ⊢
  obtain ⟨value, found, read⟩ := projected
  exact ⟨canonValue value, by rw [lookup_canonAssignment, found]; rfl,
    instantiateValue?_root_canon read⟩

/-! ## Lexically scoped quantified validation

Rearranging a finite carrier changes validation positions and can remove
duplicate set elements. The result below transports actual body witnesses
and records where each retained validation came from; it does not assert
equality of presentation-dependent raw histories.
-/

theorem removeParameter_canon (assignment : Assignment) (parameter : String) :
    canonAssignment (removeParameter parameter assignment) =
      removeParameter parameter (canonAssignment assignment) := by
  induction assignment with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨key, value⟩
    simp only [canonAssignment] at ih
    by_cases same : key = parameter <;> simp [removeParameter, canonAssignment, same, ih]

theorem bindParameter_canon (assignment : Assignment) (parameter : String) (value : ContextualValue) :
    canonAssignment (bindParameter parameter value assignment) =
      bindParameter parameter (canonValue value) (canonAssignment assignment) := by
  simp only [bindParameter, canonAssignment, List.map_cons]
  exact congrArg ((parameter, canonValue value) :: ·) (removeParameter_canon assignment parameter)

theorem finiteCollection?_canon {ambient : Nat} {assignment : Assignment} {name : String}
    {kind : CollType} {elements : List Pattern}
    (read : finiteCollection? ambient assignment name = some (kind, elements)) :
    finiteCollection? ambient (canonAssignment assignment) name =
      some (kind, arrange kind (elements.map canon)) := by
  simp only [finiteCollection?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read ⊢
  obtain ⟨value, found, actual, projected, collection⟩ := read
  have shape : actual = .collection kind elements none := by
    cases actual <;> simp only [concreteCollection?] at collection <;> try cases collection
    rename_i actualKind actualElements rest
    cases rest with
    | some _ => cases collection
    | none => cases Option.some.inj collection; rfl
  subst actual
  refine ⟨canonValue value, ?_, .collection kind (arrange kind (elements.map canon)) none, ?_, rfl⟩
  · rw [lookup_canonAssignment, found]; rfl
  · simpa only [canon_collection] using instantiateValue?_root_canon projected

/-- Every element's validation is an actual retained body event, with its
original ordinal. This holds for every premise form, including child steps
and nested quantifiers. -/
theorem Interpreted.QuantifiedElements.body_witnesses {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {history : List (Nat × Pattern × List Event)}
    (held : GeneralPremise.QuantifiedElements environment context parameter body index elements initial final history) :
    ∀ element ∈ elements, ∃ ordinal completed event,
      (ordinal, element, [event]) ∈ history ∧
      TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial) ∧
      GeneralPremise.PremiseHolds environment context.quantified body
        (bindParameter parameter (localValue context.bound element) initial) completed event := by
  induction elements generalizing index history with
  | nil => simp
  | cons element elements ih =>
    cases held with
    | @cons _ _ _ _ _ _ _ middle _ event _ typed head tail =>
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨index, middle, event, List.mem_cons_self, typed, head⟩
      · obtain ⟨ordinal, completed, nextEvent, present, typed, valid⟩ := ih tail item member
        exact ⟨ordinal, completed, nextEvent, List.mem_cons_of_mem _ present, typed, valid⟩

/-- Build the real quantified relation from independently valid bodies.
The extra predicate keeps an arbitrary citation condition on every chosen
event; the construction cannot insert evidence without a body witness. -/
theorem Interpreted.QuantifiedElements.history_of_body_witnesses
    {environment : Environment} {context : Context} {parameter : String} {body : Premise}
    {initial : Assignment} (elements : List Pattern) (index : Nat)
    (citation : Pattern → Event → Prop)
    (validates : ∀ element ∈ elements, ∃ completed event,
      TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial) ∧
      GeneralPremise.PremiseHolds environment context.quantified body
        (bindParameter parameter (localValue context.bound element) initial) completed event ∧
      citation element event) :
    ∃ history, GeneralPremise.QuantifiedElements environment context parameter body index elements initial initial history ∧
      ∀ entry ∈ history, ∃ event, entry.2.2 = [event] ∧ citation entry.2.1 event := by
  induction elements generalizing index with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons element elements ih =>
    obtain ⟨completed, event, typed, valid, cited⟩ := validates element List.mem_cons_self
    obtain ⟨history, tail, citations⟩ := ih (index + 1)
      (fun item member => validates item (List.mem_cons_of_mem _ member))
    refine ⟨(index, element, [event]) :: history, .cons typed valid tail, ?_⟩
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨event, rfl, cited⟩
    · exact citations entry member

/-- Canonical carrier validation uses only original query events. Sorting
or set contraction changes ordinals, while original provider citations and
ordinary output allocation traces remain available in the chosen events. -/
theorem Interpreted.QuantifiedElements.canonical_query_validation
    {environment : Environment} {context : Context} {parameter : String} {body : Premise}
    {index : Nat} {elements : List Pattern} {initial final : Assignment}
    {history : List (Nat × Pattern × List Event)}
    (held : GeneralPremise.QuantifiedElements environment context parameter body index elements initial final history)
    (increasing : IncreasingSpines context.rule context.spec)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CanonicalQueryGuard environment.provider context.quantified body) (kind : CollType) :
    ∃ canonicalHistory,
      GeneralPremise.QuantifiedElements environment context parameter body index (arrange kind (elements.map canon))
        (canonAssignment initial) (canonAssignment final) canonicalHistory ∧
      ∀ entry ∈ canonicalHistory, ∃ event ordinal original,
        entry.2.2 = [event] ∧ (ordinal, original, [event]) ∈ history ∧ canon original = entry.2.1 := by
  rw [held.final_eq_initial]
  obtain ⟨canonicalHistory, valid, citations⟩ := Interpreted.QuantifiedElements.history_of_body_witnesses
    (arrange kind (elements.map canon)) index
    (fun element event => ∃ ordinal original, (ordinal, original, [event]) ∈ history ∧ canon original = element)
    (by
      intro element present
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp ((arrange_mem element).mp present)
      obtain ⟨ordinal, completed, event, cited, typed, valid⟩ := held.body_witnesses original member
      have typedCanonical := typedAssignment_canon typed
      have validCanonical := valid.canonical_query_transport increasing finite rows guarded
      rw [bindParameter_canon] at typedCanonical validCanonical
      exact ⟨canonAssignment completed, event, typedCanonical, validCanonical, ordinal, original, cited, rfl⟩)
  refine ⟨canonicalHistory, valid, ?_⟩
  intro entry member
  obtain ⟨event, same, ordinal, original, present, canonical⟩ := citations entry member
  exact ⟨event, ordinal, original, same, present, canonical⟩

theorem Interpreted.PremiseHolds.canonical_quantified_query_transport
    {environment : Environment} {context : Context} {collection parameter : String} {body : Premise}
    {kind : CollType} {elements : List Pattern} {initial final : Assignment}
    {history : List (Nat × Pattern × List Event)}
    (read : finiteCollection? context.bound.length initial collection = some (kind, elements))
    (held : GeneralPremise.QuantifiedElements environment context parameter body 0 elements initial final history)
    (increasing : IncreasingSpines context.rule context.spec)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CanonicalQueryGuard environment.provider context.quantified body) :
    ∃ canonicalHistory,
      GeneralPremise.PremiseHolds environment context (.forAll collection parameter body)
        (canonAssignment initial) (canonAssignment final)
        (.quantified context.premiseIndex context.quantifierDepth kind canonicalHistory) ∧
      ∀ entry ∈ canonicalHistory, ∃ event ordinal original,
        entry.2.2 = [event] ∧ (ordinal, original, [event]) ∈ history ∧ canon original = entry.2.1 := by
  obtain ⟨canonicalHistory, validated, origins⟩ :=
    held.canonical_query_validation increasing finite rows guarded kind
  exact ⟨canonicalHistory, .quantified (finiteCollection?_canon read) validated, origins⟩

#print axioms Interpreted.QuantifiedElements.body_witnesses
#print axioms Interpreted.QuantifiedElements.history_of_body_witnesses
#print axioms Interpreted.QuantifiedElements.canonical_query_validation
#print axioms Interpreted.PremiseHolds.canonical_quantified_query_transport

/-- Input guards preserve their assignment and every argument's origin.
Canonicalizing captures neither creates provider occurrences nor replays a
different validation trace. -/
theorem Interpreted.TracedArgumentsHold.collection_inputs_canon {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins)
    (inputs : CollectionInputs context index schemas)
    (inputModes : modes = List.replicate schemas.length .input)
    (canonical : ∀ value ∈ values, canon value = value) :
    final = initial ∧ GeneralPremise.TracedArgumentsHold context index (canonAssignment initial) schemas values modes
      (canonAssignment final) origins := by
  induction held with
  | nil => exact ⟨rfl, .nil⟩
  | @input index initial final schema value schemas values modes origins projected tail ih =>
    have modes : modes = List.replicate schemas.length .input := (List.cons.inj inputModes).2
    cases schema with
    | fvar name =>
      obtain ⟨same, transported⟩ := ih inputs.2 modes
        (fun v member => canonical v (List.mem_cons_of_mem _ member))
      refine ⟨same, .input ?_ transported⟩
      simpa only [canonical value List.mem_cons_self] using instantiateAt?_input_canon inputs.1 projected
    | _ => cases inputs
  | output _ _ _ => cases (List.cons.inj inputModes).1

/-- Static provider inputs retain the original row index under capture
normalization. Dynamic providers need their own equality contract. -/
theorem Interpreted.TracedQuery.collection_inputs_canon {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedQuery environment context relation arguments initial rowIndex final origins)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (inputs : CollectionInputs context 0 arguments)
    (inputModes : ∀ signature, signature? environment.provider relation arguments.length = some signature →
      signature.modes = List.replicate arguments.length .input) :
    final = initial ∧ GeneralPremise.TracedQuery environment context relation arguments (canonAssignment initial)
      rowIndex (canonAssignment final) origins := by
  cases held with
  | row selected declared typed arguments finalTyped =>
    obtain ⟨same, transported⟩ := arguments.collection_inputs_canon inputs (inputModes _ declared)
      (rows _ (List.mem_of_getElem? selected))
    exact ⟨same, .row selected declared typed transported (typedAssignment_canon finalTyped)⟩
  | dynamicRow registered _ _ _ _ _ _ _ =>
    rw [finite] at registered
    cases registered

theorem Interpreted.PremiseHolds.collection_inputs_canon {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : GeneralPremise.PremiseHolds environment context premise initial final event)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CollectionInputGuard environment.provider context premise) :
    final = initial ∧ GeneralPremise.PremiseHolds environment context premise (canonAssignment initial)
      (canonAssignment final) event := by
  obtain ⟨relation, arguments, signature, rfl, declared, modes, inputs⟩ := guarded
  cases held with
  | query query =>
    obtain ⟨same, transported⟩ := query.collection_inputs_canon finite rows inputs (fun actual found => by
      have sameSignature := Option.some.inj (declared.symm.trans found)
      simpa only [← sameSignature] using modes)
    exact ⟨same, .query transported⟩

/-- The entire retained premise history survives, with the original provider
indices and no new bindings. Collection-valued inputs use the same theorem as
scalar inputs; no provider-row normalization is silently performed. -/
theorem Interpreted.PremisesHold.collection_inputs_canon {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {history : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (finite : environment.provider.dynamicRelations = [])
    (rows : CanonicalProviderRows environment.provider)
    (guarded : CollectionInputGuards environment.provider context premises) :
    final = initial ∧ GeneralPremise.PremisesHold environment context premises (canonAssignment initial)
      (canonAssignment final) history := by
  cases held with
  | nil => exact ⟨rfl, .nil⟩
  | cons head tail =>
    obtain ⟨middleEq, head'⟩ := head.collection_inputs_canon finite rows guarded.1
    obtain ⟨finalEq, tail'⟩ := tail.collection_inputs_canon finite rows guarded.2
    exact ⟨finalEq.trans middleEq, .cons head' tail'⟩
termination_by premises.length
decreasing_by all_goals simp_all [List.length_cons]

theorem Interpreted.PremisesHold.collection_inputs_history_depth {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {history : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (guarded : CollectionInputGuards environment.provider context premises) :
    StructuralDescent.eventsDepth history = 0 := by
  cases held with
  | nil => simp only [StructuralDescent.eventsDepth]
  | cons head tail =>
    obtain ⟨relation, arguments, signature, same, declared, modes, inputs⟩ := guarded.1
    subst same
    have rest := tail.collection_inputs_history_depth guarded.2
    cases head with
    | query _ => simp only [StructuralDescent.eventsDepth, StructuralDescent.eventDepth, rest, Nat.max_self]
termination_by premises.length
decreasing_by all_goals simp_all [List.length_cons]

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
