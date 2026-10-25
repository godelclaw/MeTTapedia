import Mettapedia.OSLF.MeTTaIL.ScopedCollectionReplay
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionCanonical
import Mettapedia.OSLF.MeTTaIL.StructuralDescentFiniteServices
import Mettapedia.OSLF.MeTTaIL.GeneralEquationMatcherWork

/-!
# Collection matching as ordinary matching at an equivalent presentation

The collection matcher does not introduce a new source transition judgment.
Every successful unordered match supplies an explicit presentation of the
source collection on which the ordinary scoped matcher succeeds.  For sets,
that presentation may repeat a selected member; for bags, it preserves the
full multiplicity.

This is the forward compatibility boundary needed by a shared executor.  The
reverse boundary, which transports an ordinary match from an arbitrary
equivalent presentation back to the finite collection matcher, is separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection

theorem presents_trans {kind : CollType} {first second third : List Pattern}
    (left : Presents kind first second) (right : Presents kind second third) :
    Presents kind first third := by
  cases kind with
  | vec => exact left.trans right
  | hashBag => exact left.trans right
  | hashSet => intro item; exact (left item).trans (right item)

theorem presents_arrange (kind : CollType) (items : List Pattern) :
    Presents kind items (arrange kind items) := by
  cases kind with
  | vec => rfl
  | hashBag => exact (PatternLexOrder.sortLex_perm items).symm
  | hashSet => intro item; exact (arrange_mem item).symm

theorem presents_append_arrange {kind : CollType} {source selected residual : List Pattern}
    (presented : Presents kind source (selected ++ residual)) :
    Presents kind source (selected ++ arrange kind residual) := by
  apply presents_trans presented
  simpa only [List.append_nil] using
    (Presents.surround (kind := kind) selected [] (presents_arrange kind residual))

theorem collection_equivalent_of_presents {kind : CollType} (unordered : kind ≠ .vec)
    {left right : List Pattern} (same : Presents kind left right) :
    Relation.EqvGen BagStep (.collection kind left none) (.collection kind right none) := by
  cases kind with
  | vec => exact False.elim (unordered rfl)
  | hashBag => exact .rel _ _ (.permute (by decide) same)
  | hashSet => exact .rel _ _ (.members same)

/-- Ordered element matching followed by the collection rest operation is an
ordinary unordered match against the selected row followed by the canonical
residual. -/
theorem bag_of_arguments_finished
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial middle final : Assignment} {schemas selected residual : List Pattern}
    {rest : Option String} {kind : CollType}
    (rows : GeneralScopedMatch.Arguments rule spec ambient site path depth
      initial index schemas selected middle)
    (finished : ScopedCollectionMatching.Finished rule spec ambient site path depth
      (index + schemas.length) kind rest middle (arrange kind residual) final) :
    GeneralScopedMatch.Bag rule spec ambient site path depth initial index
      schemas rest kind (selected ++ arrange kind residual) final := by
  cases rows with
  | nil =>
      simp only [List.length_nil, Nat.add_zero] at finished
      generalize arrangedEq : arrange kind residual = arranged at finished ⊢
      cases finished with
      | empty => exact .nil
      | captured captured => exact .rest captured
  | cons head tail =>
      have continued := bag_of_arguments_finished (residual := residual) (rest := rest)
        (final := final) tail (by
          convert finished using 1
          simp only [List.length_cons]
          omega)
      simpa only [List.cons_append, List.eraseIdx_zero] using
        (GeneralScopedMatch.Bag.cons (selected := 0) (within := by simp) head continued)
termination_by schemas

/-- Conservativity on canonical carriers: every consumptive unordered match
accepted by the original matcher is a match of the collection backend. -/
theorem collection_of_bag_on_fixed
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType} (unordered : kind ≠ .vec)
    (fixed : arrange kind targets = targets)
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial
      index schemas rest kind targets final) :
    ScopedCollectionMatching.Matches rule spec ambient site path depth index
      initial schemas rest kind targets final := by
  cases matched with
  | nil =>
      refine ⟨[], [], initial, Presents.refl _ _, .nil, ?_⟩
      have empty : arrange kind [] = [] := by cases kind <;> rfl
      simpa only [List.length_nil, Nat.add_zero, empty] using
        (ScopedCollectionMatching.Finished.empty (rule := rule) (spec := spec)
          (ambient := ambient) (site := site) (path := path) (depth := depth)
          (index := index) (kind := kind) (initial := initial))
  | @rest _ _ _ _ _ _ targets _ captured =>
      refine ⟨[], targets, initial, ?_, .nil, ?_⟩
      · simpa only [List.nil_append] using Presents.refl kind targets
      · exact .captured (by simpa [fixed] using captured)
  | cons selected within head tail =>
      have residualFixed : arrange kind (targets.eraseIdx selected) =
          targets.eraseIdx selected :=
        ScopedCollectionMachine.arrange_sublist_fixed kind fixed
          (List.eraseIdx_sublist targets selected)
      obtain ⟨selectedTail, residual, last, tailPresents, tailRows, tailFinished⟩ :=
        collection_of_bag_on_fixed unordered residualFixed tail
      refine ⟨targets[selected] :: selectedTail, residual, last, ?_,
        .cons head tailRows, ?_⟩
      · have split := List.getElem_cons_eraseIdx_perm within
        have first : Presents kind targets (targets[selected] :: targets.eraseIdx selected) := by
          cases kind with
          | vec => exact False.elim (unordered rfl)
          | hashBag => exact split.symm
          | hashSet => exact fun item => split.mem_iff.symm
        have second := presents_cons tailPresents targets[selected]
        exact presents_trans first (by simpa only [List.cons_append] using second)
      · convert tailFinished using 1
        simp only [List.length_cons]
        omega
termination_by schemas

theorem collection_matches_of_ordinary_on_fixed
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType} (unordered : kind ≠ .vec)
    (fixed : arrange kind targets = targets)
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial
      (.collection kind schemas rest) (.collection kind targets none) final) :
    ScopedCollectionMatching.Matches rule spec ambient site path depth 0 initial
      schemas rest kind targets final := by
  cases matched with
  | bag _ bag => exact collection_of_bag_on_fixed unordered fixed bag
  | vector _ => exact False.elim (unordered rfl)
  | vectorRest _ _ => exact False.elim (unordered rfl)

/-- The replacement is conservative on the old matcher's canonical fragment:
every old assignment is still enumerated by the collection backend. -/
theorem ordinary_match_mem_collection_run
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial final : Assignment) (schemas : List Pattern) (rest : Option String)
    {kind : CollType} (unordered : kind ≠ .vec) {targets : List Pattern}
    (fixed : arrange kind targets = targets)
    (member : final ∈ matchAt rule spec ambient site path depth initial
      (.collection kind schemas rest) (.collection kind targets none)) :
    final ∈ ScopedCollectionMatching.run rule spec ambient site path depth 0
      initial schemas rest kind targets := by
  apply (ScopedCollectionMatching.run_exact rule spec ambient site path depth 0
    initial final schemas rest unordered ?_).mpr
  · exact collection_matches_of_ordinary_on_fixed unordered fixed
      (GeneralScopedMatch.matchAt_sound member)
  · intro setKind
    have canonical := canonical_set_distinct targets
    rw [setKind] at fixed
    rwa [fixed] at canonical

/-- A semantic collection match is an ordinary scoped match on a concrete
presentation equal under the collection kind's declared equality. -/
theorem matches_has_ordinary_presentation
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType} (unordered : kind ≠ .vec)
    (matched : ScopedCollectionMatching.Matches rule spec ambient site path depth
      0 initial schemas rest kind targets final) :
    ∃ presented, Presents kind targets presented ∧
      GeneralScopedMatch.Matches rule spec ambient site path depth initial
        (.collection kind schemas rest) (.collection kind presented none) final := by
  obtain ⟨selected, residual, middle, presents, rows, finished⟩ := matched
  let presented := selected ++ arrange kind residual
  refine ⟨presented, presents_append_arrange presents, .bag unordered ?_⟩
  exact bag_of_arguments_finished rows finished

theorem matches_has_ordinary_equivalent_presentation
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType} (unordered : kind ≠ .vec)
    (matched : ScopedCollectionMatching.Matches rule spec ambient site path depth
      0 initial schemas rest kind targets final) :
    ∃ presented,
      Relation.EqvGen BagStep (.collection kind targets none)
        (.collection kind presented none) ∧
      GeneralScopedMatch.Matches rule spec ambient site path depth initial
        (.collection kind schemas rest) (.collection kind presented none) final := by
  obtain ⟨presented, same, ordinary⟩ :=
    matches_has_ordinary_presentation unordered matched
  exact ⟨presented, collection_equivalent_of_presents unordered same, ordinary⟩

/-- Executable compatibility: every assignment returned by the finite
collection matcher is returned by the ordinary matcher at an explicit
equivalent presentation. -/
theorem run_has_ordinary_presentation
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial final : Assignment) (schemas : List Pattern) (rest : Option String)
    {kind : CollType} (unordered : kind ≠ .vec) {targets : List Pattern}
    (distinct : kind = .hashSet → targets.Nodup)
    (member : final ∈ ScopedCollectionMatching.run rule spec ambient site path depth
      0 initial schemas rest kind targets) :
    ∃ presented, Presents kind targets presented ∧
      final ∈ matchAt rule spec ambient site path depth initial
        (.collection kind schemas rest) (.collection kind presented none) := by
  have matched := (ScopedCollectionMatching.run_exact rule spec ambient site path depth
    0 initial final schemas rest unordered distinct).mp member
  obtain ⟨presented, same, ordinary⟩ :=
    matches_has_ordinary_presentation unordered matched
  exact ⟨presented, same, ordinary.complete⟩

/-- The deterministic ordinary presentation used by the backend adapter. -/
def ordinaryTarget (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) : Pattern :=
  .collection request.kind
    (receipt.allocation.values ++ arrange request.kind receipt.allocation.residual) none

/-- A checked producer receipt has the independent collection-matching
meaning. The arranged-carrier premise is exactly the invariant established by
the compiler before starting a collection batch. -/
theorem valid_allocation_presents
    {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (unordered : request.kind ≠ .vec)
    (fixed : arrange request.kind request.targets = request.targets)
    (valid : ScopedCollectionMachine.Valid request receipt) :
    Presents request.kind request.targets
      (receipt.allocation.values ++ receipt.allocation.residual) := by
  obtain ⟨decisionLength, replayed, accepted⟩ := valid
  have allocated : receipt.allocation ∈ request.allocations := by
    have recovered := CollectionSelection.replay_complete replayed
    simpa only [ScopedCollectionMachine.Request.allocations, decisionLength,
      CollectionSelection.Allocation.erase] using recovered
  obtain ⟨middle, tracedRows, finished⟩ :=
    (ScopedCollectionMachine.allocation_accepts_iff request receipt.allocation
      receipt.matching).mp accepted
  have rows := tracedRows.matching
  have rowLength : request.schemas.length = receipt.allocation.values.length :=
    (ScopedCollectionMatching.rows_iff_arguments request.rule request.spec
      request.ambient request.site request.path request.depth request.index
      request.initial middle request.schemas receipt.allocation.values).mpr rows |>.length
  have erased : receipt.allocation.erase ∈
      kindAllocations request.kind request.schemas.length request.targets := by
    rw [kindAllocations, ← tracedAllocations_erase]
    exact List.mem_map.mpr ⟨receipt.allocation, allocated, rfl⟩
  have distinct : request.kind = .hashSet → request.targets.Nodup := by
    intro setKind
    have canonical := canonical_set_distinct request.targets
    rw [setKind] at fixed
    rwa [fixed] at canonical
  apply (allocations_present_exact unordered distinct).mp
  refine ⟨receipt.allocation.residual, ?_, Presents.refl _ _⟩
  simpa only [rowLength, CollectionSelection.Allocation.erase] using erased

theorem valid_has_collection_meaning
    {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (unordered : request.kind ≠ .vec)
    (fixed : arrange request.kind request.targets = request.targets)
    (valid : ScopedCollectionMachine.Valid request receipt) :
    ScopedCollectionMatching.Matches request.rule request.spec request.ambient
      request.site request.path request.depth request.index request.initial
      request.schemas request.rest request.kind request.targets
      receipt.matching.assignment := by
  obtain ⟨middle, tracedRows, finished⟩ :=
    (ScopedCollectionMachine.allocation_accepts_iff request receipt.allocation
      receipt.matching).mp valid.2.2
  exact ⟨receipt.allocation.values, receipt.allocation.residual, middle,
    valid_allocation_presents unordered fixed valid, tracedRows.matching, finished⟩

theorem valid_ordinary_target_equivalent
    {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (unordered : request.kind ≠ .vec)
    (fixed : arrange request.kind request.targets = request.targets)
    (valid : ScopedCollectionMachine.Valid request receipt) :
    Relation.EqvGen BagStep (.collection request.kind request.targets none)
      (ordinaryTarget request receipt) := by
  apply collection_equivalent_of_presents unordered
  exact presents_append_arrange (valid_allocation_presents unordered fixed valid)

/-- A checked collection firing is an ordinary scoped match at a model-equal
presentation, with the same assignment and authored reduct. -/
theorem firing_has_ordinary_equivalent_presentation
    {request : ScopedCollectionMachine.Request}
    {firing : ScopedCollectionMachine.FiringReceipt}
    (rootIndex : request.index = 0)
    (unordered : request.kind ≠ .vec)
    (fixed : arrange request.kind request.targets = request.targets)
    (valid : ScopedCollectionMachine.FiringValid request firing) :
    ∃ presented trace,
      Relation.EqvGen BagStep (.collection request.kind request.targets none)
        (.collection request.kind presented none) ∧
      GeneralScopedMatchMachine.TracedMatches request.rule request.spec request.ambient
        request.site request.path request.depth request.initial
        (.collection request.kind request.schemas request.rest)
        (.collection request.kind presented none) trace firing.source.matching.assignment ∧
      reduct? request.rule request.spec request.ambient firing.source.matching.assignment =
        some firing.target := by
  have meaning := valid_has_collection_meaning unordered fixed valid.1
  rw [rootIndex] at meaning
  obtain ⟨presented, equivalent, ordinary⟩ :=
    matches_has_ordinary_equivalent_presentation unordered meaning
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace ordinary
  exact ⟨presented, trace, equivalent, traced, valid.2⟩

def ordinaryRequest (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) : GeneralScopedMatchMachine.Request :=
  { request.machine with target := ordinaryTarget request receipt }

/-- Re-run only the ordinary scoped checker on the explicit presentation. This
is an adapter, not a second collection search: allocation has already selected
the presentation, and the filter retains exactly the collection receipt's
assignment. -/
def ordinaryAnswers (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    List {answer : GeneralScopedMatchMachine.Answer //
      answer.Valid (ordinaryRequest request receipt)} :=
  (StructuralDescent.FiniteServices.Matcher.answers (ordinaryRequest request receipt)).filter
    fun answer => answer.val.assignment == receipt.matching.assignment

/-- The two complete matching strategies used by the semantic finite service
and the emitted complete machine reach the identical final state. -/
theorem finishMatcher_start_eq_finiteState (request : GeneralScopedMatchMachine.Request) :
    GeneralEquationJobExecution.finishMatcher request
        (GeneralScopedMatchMachine.start request) =
      StructuralDescent.FiniteServices.Matcher.state request := by
  unfold StructuralDescent.FiniteServices.Matcher.state
  apply GeneralEquationJobExecution.finishMatcher_eq_run_of_enough
  exact Nat.le_refl _

/-- Erasing proof fields from `ordinaryAnswers` gives exactly the complete
machine's ordered, trace-retaining filtered frontier. -/
def ordinaryAnswerValues (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    List GeneralScopedMatchMachine.Answer :=
  (ordinaryAnswers request receipt).map Subtype.val

theorem finiteAnswerValues (request : GeneralScopedMatchMachine.Request) :
    (StructuralDescent.FiniteServices.Matcher.answers request).map Subtype.val =
      (StructuralDescent.FiniteServices.Matcher.state request).answers := by
  unfold StructuralDescent.FiniteServices.Matcher.answers
  rw [List.map_map]
  simp [Function.comp_def]

theorem ordinaryAnswerValues_eq (request : ScopedCollectionMachine.Request)
    (receipt : ScopedCollectionMachine.Receipt) :
    ordinaryAnswerValues request receipt =
      (GeneralEquationJobExecution.finishMatcher (ordinaryRequest request receipt)
        (GeneralScopedMatchMachine.start (ordinaryRequest request receipt))).answers.filter
          fun answer => answer.assignment == receipt.matching.assignment := by
  rw [finishMatcher_start_eq_finiteState]
  unfold ordinaryAnswerValues ordinaryAnswers
  change List.map Subtype.val
      (List.filter ((fun answer : GeneralScopedMatchMachine.Answer =>
        answer.assignment == receipt.matching.assignment) ∘ Subtype.val)
        (StructuralDescent.FiniteServices.Matcher.answers
          (ordinaryRequest request receipt))) = _
  rw [← List.filter_map, finiteAnswerValues]

/-- A checked collection receipt always has an ordinary checked answer at the
deterministic equivalent presentation. This gives the generic premise machine
the exact matcher payload it already consumes. -/
theorem ordinaryAnswers_complete
    {request : ScopedCollectionMachine.Request}
    {receipt : ScopedCollectionMachine.Receipt}
    (rootIndex : request.index = 0)
    (unordered : request.kind ≠ .vec)
    (valid : ScopedCollectionMachine.Valid request receipt) :
    ∃ answer ∈ ordinaryAnswers request receipt,
      answer.val.assignment = receipt.matching.assignment := by
  obtain ⟨middle, tracedRows, finished⟩ :=
    (ScopedCollectionMachine.allocation_accepts_iff request receipt.allocation
      receipt.matching).mp valid.2.2
  have rows := tracedRows.matching
  have ordinary : GeneralScopedMatch.Matches request.rule request.spec request.ambient
      request.site request.path request.depth request.initial
      (.collection request.kind request.schemas request.rest)
      (ordinaryTarget request receipt) receipt.matching.assignment := by
    apply GeneralScopedMatch.Matches.bag unordered
    rw [rootIndex] at rows finished
    exact bag_of_arguments_finished rows finished
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace ordinary
  let wanted : GeneralScopedMatchMachine.Answer :=
    { assignment := receipt.matching.assignment, trace := trace }
  have wantedValid : wanted.Valid (ordinaryRequest request receipt) := by
    simpa only [wanted, GeneralScopedMatchMachine.Answer.Valid, ordinaryRequest,
      ScopedCollectionMachine.Request.machine, ordinaryTarget] using traced
  obtain ⟨answer, member, same⟩ :=
    StructuralDescent.FiniteServices.Matcher.answers_complete
      (ordinaryRequest request receipt) wanted wantedValid
  refine ⟨answer, List.mem_filter.mpr ⟨member, ?_⟩, ?_⟩
  · simp only [beq_iff_eq, same, wanted]
  · simp only [same, wanted]

end Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
