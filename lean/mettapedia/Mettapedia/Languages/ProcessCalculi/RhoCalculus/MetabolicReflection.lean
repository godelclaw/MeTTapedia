import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicInitialConfiguration

/-!
# Operational reflection for closed metabolic phases

In a live phase the only matching pair is the owner and stack message.
In a nonempty reclaimed phase it is the exposed cell and pop request.
Spent records never become eligible metabolic messages. The independent
COMM path therefore determines every public successor up to rho equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Canonical CanonicalBag CanonicalReaction CanonicalReactionOccurrences CanonicalStepperCompleteness
open LanguageDefGSLT LanguageDefRewriteSystem ResourcePredation

universe u
variable {Head : Type u}

private def inputChannelOf : Pattern → Option Pattern
  | .apply "PInput" [channel, _] => some channel
  | _ => none

private def outputChannelOf : Pattern → Option Pattern
  | .apply "POutput" [channel, _] => some channel
  | _ => none

private theorem parallel_member (parts : List RhoProcess)
    (atomic : ∀ process ∈ parts, ∀ nested,
      canonicalize process.1 ≠ .collection .hashBag nested none)
    {pattern : Pattern} (member : pattern ∈ (fromProcess (parallel parts)).1) :
    ∃ process ∈ parts, pattern = canonicalize process.1 := by
  rw [parallel, fromProcess_ofList_inventory] at member
  have listMember : pattern ∈ bagContents ((parts.map Subtype.val).map canonicalize) := by simpa using member
  obtain ⟨inSplice, _⟩ := List.mem_filter.mp listMember
  obtain ⟨original, inOriginal, inOriginalSplice⟩ := List.mem_flatMap.mp inSplice
  obtain ⟨part, inParts, originalEq⟩ := List.mem_map.mp inOriginal
  obtain ⟨process, inProcesses, partEq⟩ := List.mem_map.mp inParts
  subst part
  subst original
  have singleton := bagSplice_eq_singleton_of_not_bag (atomic process inProcesses)
  rw [singleton] at inOriginalSplice
  exact ⟨process, inProcesses, List.mem_singleton.mp inOriginalSplice⟩

private theorem live_atomic (encoding : Encoding Head) (stack : Stack Head) (count : Nat) (record : List Head) :
    ∀ process ∈ [messageProcess encoding stack, ownerProcess count] ++ record.map (burnedProcess encoding),
      ∀ nested, canonicalize process.1 ≠ .collection .hashBag nested none := by
  intro process member nested
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | inRecord
  · simp [messageProcess, closedProcess, message, output, canonicalize]
  · cases count <;> simp [ownerProcess, closedProcess, owner, zero, input, canonicalize]
  · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
    simp [burnedProcess, closedProcess, burned, output, canonicalize]

private theorem reclaimed_atomic (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) :
    ∀ process ∈ [payloadProcess encoding (.cell head tail), triggerProcess, ownerProcess count] ++
      record.map (burnedProcess encoding),
      ∀ nested, canonicalize process.1 ≠ .collection .hashBag nested none := by
  intro process member nested
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | inRecord
  · simp [payloadProcess, closedProcess, payload, input, canonicalize]
  · simp [triggerProcess, closedProcess, trigger, output, canonicalize]
  · cases count <;> simp [ownerProcess, closedProcess, owner, zero, input, canonicalize]
  · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
    simp [burnedProcess, closedProcess, burned, output, canonicalize]

private theorem rule_input_mem {source : Bag} (rule : GroundComm) (residue : Bag)
    (sourceEqual : source = append rule.redex residue) : input rule.inputChannel rule.body ∈ source.1 := by
  rw [sourceEqual]
  exact Multiset.mem_add.mpr (Or.inl (by simp [GroundComm.redex]))

private theorem rule_output_mem {source : Bag} (rule : GroundComm) (residue : Bag)
    (sourceEqual : source = append rule.redex residue) : output rule.outputChannel rule.payload ∈ source.1 := by
  rw [sourceEqual]
  exact Multiset.mem_add.mpr (Or.inl (by simp [GroundComm.redex]))

private theorem live_rule_pair (encoding : Encoding Head) (stack : Stack Head) (count : Nat) (record : List Head)
    (rule : GroundComm) (residue : Bag)
    (sourceEqual : fromProcess (live encoding stack (count + 1) record) = append rule.redex residue) :
    input rule.inputChannel rule.body = canonicalize (owner (count + 1)) ∧
      output rule.outputChannel rule.payload = canonicalize (message encoding stack) := by
  obtain ⟨process, member, inputShape⟩ := parallel_member _ (live_atomic encoding stack (count + 1) record)
    (rule_input_mem rule residue sourceEqual)
  have inputShape : input rule.inputChannel rule.body = canonicalize (owner (count + 1)) := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl) | inRecord
    · have impossible := congrArg inputChannelOf inputShape
      change some rule.inputChannel = none at impossible
      cases impossible
    · exact inputShape
    · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
      have impossible := congrArg inputChannelOf inputShape
      change some rule.inputChannel = none at impossible
      cases impossible
  have inputChannel : rule.inputChannel = metabolic := by
    have names := congrArg inputChannelOf inputShape
    change some rule.inputChannel = some metabolic at names
    exact Option.some.inj names
  refine ⟨inputShape, ?_⟩
  obtain ⟨process, member, outputShape⟩ := parallel_member _ (live_atomic encoding stack (count + 1) record)
    (rule_output_mem rule residue sourceEqual)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | inRecord
  · exact outputShape
  · have impossible := congrArg outputChannelOf outputShape
    change some rule.outputChannel = none at impossible
    cases impossible
  · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
    have outputChannel : rule.outputChannel = spent := by
      have names := congrArg outputChannelOf outputShape
      change some rule.outputChannel = some spent at names
      exact Option.some.inj names
    exact False.elim (names_distinct.2.1 (by simpa [inputChannel, outputChannel] using rule.channels))

private theorem reclaimed_output (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) (rule : GroundComm) (residue : Bag)
    (sourceEqual : fromProcess (reclaimed encoding (.cell head tail) count record) = append rule.redex residue) :
    (rule.outputChannel = pop ∧ output rule.outputChannel rule.payload = canonicalize trigger) ∨
      rule.outputChannel = spent := by
  obtain ⟨process, member, outputShape⟩ := parallel_member _ (reclaimed_atomic encoding head tail count record)
    (rule_output_mem rule residue sourceEqual)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | inRecord
  · have impossible := congrArg outputChannelOf outputShape
    change some rule.outputChannel = none at impossible
    cases impossible
  · refine Or.inl ⟨?_, outputShape⟩
    have names := congrArg outputChannelOf outputShape
    change some rule.outputChannel = some pop at names
    exact Option.some.inj names
  · have impossible := congrArg outputChannelOf outputShape
    cases count <;> change some rule.outputChannel = none at impossible <;> cases impossible
  · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
    apply Or.inr
    have names := congrArg outputChannelOf outputShape
    change some rule.outputChannel = some spent at names
    exact Option.some.inj names

private theorem reclaimed_rule_pair (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) (rule : GroundComm) (residue : Bag)
    (sourceEqual : fromProcess (reclaimed encoding (.cell head tail) count record) = append rule.redex residue) :
    input rule.inputChannel rule.body = canonicalize (payload encoding (.cell head tail)) ∧
      output rule.outputChannel rule.payload = canonicalize trigger := by
  have outputOptions := reclaimed_output encoding head tail count record rule residue sourceEqual
  obtain ⟨process, member, inputShape⟩ := parallel_member _ (reclaimed_atomic encoding head tail count record)
    (rule_input_mem rule residue sourceEqual)
  have inputShape : input rule.inputChannel rule.body = canonicalize (payload encoding (.cell head tail)) := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl) | inRecord
    · exact inputShape
    · have impossible := congrArg inputChannelOf inputShape
      change some rule.inputChannel = none at impossible
      cases impossible
    · cases count with
      | zero =>
          have impossible := congrArg inputChannelOf inputShape
          change some rule.inputChannel = none at impossible
          cases impossible
      | succ count =>
          have inputChannel : rule.inputChannel = metabolic := by
            have names := congrArg inputChannelOf inputShape
            change some rule.inputChannel = some metabolic at names
            exact Option.some.inj names
          rcases outputOptions with ⟨outputChannel, _⟩ | outputChannel
          · exact False.elim (names_distinct.1 (by simpa [inputChannel, outputChannel] using rule.channels))
          · exact False.elim (names_distinct.2.1 (by simpa [inputChannel, outputChannel] using rule.channels))
    · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
      have impossible := congrArg inputChannelOf inputShape
      change some rule.inputChannel = none at impossible
      cases impossible
  refine ⟨inputShape, ?_⟩
  have inputChannel : rule.inputChannel = pop := by
    have names := congrArg inputChannelOf inputShape
    change some rule.inputChannel = some pop at names
    exact Option.some.inj names
  rcases outputOptions with ⟨_, outputShape⟩ | outputChannel
  · exact outputShape
  · exact False.elim (names_distinct.2.2.1 (by simpa [inputChannel, outputChannel] using rule.channels))

private theorem successor_inventory_unique {source first second : RhoProcess} {receiver resource : Pattern}
    (unique : ∀ (rule : GroundComm) (residue : Bag), fromProcess source = append rule.redex residue →
      input rule.inputChannel rule.body = receiver ∧ output rule.outputChannel rule.payload = resource)
    (firstStep : rhoLanguageDefGSLT.Step source first) (secondStep : rhoLanguageDefGSLT.Step source second) :
    fromProcess first = fromProcess second := by
  obtain ⟨firstRule, firstResidue, firstSource, firstTarget⟩ := public_reaction firstStep
  obtain ⟨secondRule, secondResidue, secondSource, secondTarget⟩ := public_reaction secondStep
  have firstPair := unique firstRule firstResidue firstSource
  have secondPair := unique secondRule secondResidue secondSource
  have rules : firstRule = secondRule := groundComm_ext
    (firstPair.1.trans secondPair.1.symm) (firstPair.2.trans secondPair.2.symm)
  subst secondRule
  have residues : firstResidue = secondResidue := by
    apply Subtype.ext
    exact add_left_cancel
      (congrArg Subtype.val (firstSource.symm.trans secondSource))
  subst secondResidue
  exact firstTarget.trans secondTarget.symm

theorem live_step_reflects (encoding : Encoding Head) (stack : Stack Head) (count : Nat) (record : List Head)
    {target : RhoProcess} (actual : rhoLanguageDefGSLT.Step (live encoding stack (count + 1) record) target) :
    fromProcess target = fromProcess (reclaimed encoding stack count record) :=
  successor_inventory_unique (live_rule_pair encoding stack count record) actual
    (reclaim_step encoding stack count record)

theorem reclaimed_step_reflects (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) {target : RhoProcess}
    (actual : rhoLanguageDefGSLT.Step (reclaimed encoding (.cell head tail) count record) target) :
    fromProcess target = fromProcess (live encoding tail count (head :: record)) :=
  successor_inventory_unique (reclaimed_rule_pair encoding head tail count record) actual
    (pop_step encoding head tail count record)

theorem live_occurrence_step_reflects (encoding : Encoding Head) (stack : Stack Head)
    (count : Nat) (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding stack (count + 1) record))
    (firing : ResourcePredation.Firing source) :
    inventory firing.target = fromProcess (reclaimed encoding stack count record) := by
  have actual : rhoLanguageDefGSLT.Step (live encoding stack (count + 1) record) (readout firing.target) := by
    apply (publicStep_iff _ _).mpr
    rw [← sourceInventory]
    have independent := (publicStep_iff _ _).mp firing.public_step
    simpa [readout, fromProcess_toProcess] using independent
  have target := live_step_reflects encoding stack count record actual
  simpa [readout, fromProcess_toProcess] using target

theorem reclaimed_occurrence_step_reflects (encoding : Encoding Head) (head : Head) (tail : Stack Head)
    (count : Nat) (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (reclaimed encoding (.cell head tail) count record))
    (firing : ResourcePredation.Firing source) :
    inventory firing.target = fromProcess (live encoding tail count (head :: record)) := by
  have actual : rhoLanguageDefGSLT.Step (reclaimed encoding (.cell head tail) count record) (readout firing.target) := by
    apply (publicStep_iff _ _).mpr
    rw [← sourceInventory]
    have independent := (publicStep_iff _ _).mp firing.public_step
    simpa [readout, fromProcess_toProcess] using independent
  have target := reclaimed_step_reflects encoding head tail count record actual
  simpa [readout, fromProcess_toProcess] using target

private theorem firing_step_at (source : Configuration) (process : RhoProcess)
    (sourceInventory : inventory source = fromProcess process) (firing : ResourcePredation.Firing source) :
    rhoLanguageDefGSLT.Step process (readout firing.target) := by
  apply (publicStep_iff _ _).mpr
  rw [← sourceInventory]
  have independent := (publicStep_iff _ _).mp firing.public_step
  simpa [readout, fromProcess_toProcess] using independent

theorem exhausted_live_has_no_step (encoding : Encoding Head) (stack : Stack Head)
    (record : List Head) {target : RhoProcess}
    (actual : rhoLanguageDefGSLT.Step (live encoding stack 0 record) target) : False := by
  obtain ⟨rule, residue, sourceEqual, _⟩ := public_reaction actual
  obtain ⟨process, member, inputShape⟩ := parallel_member _ (live_atomic encoding stack 0 record)
    (rule_input_mem rule residue sourceEqual)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | inRecord
  · have impossible := congrArg inputChannelOf inputShape
    change some rule.inputChannel = none at impossible
    cases impossible
  · have impossible := congrArg inputChannelOf inputShape
    change some rule.inputChannel = none at impossible
    cases impossible
  · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
    have impossible := congrArg inputChannelOf inputShape
    change some rule.inputChannel = none at impossible
    cases impossible

theorem exhausted_live_has_no_firing (encoding : Encoding Head) (stack : Stack Head)
    (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding stack 0 record)) :
    ∀ _ : ResourcePredation.Firing source, False := by
  intro firing
  exact exhausted_live_has_no_step encoding stack record
    (firing_step_at source _ sourceInventory firing)

private theorem empty_reclaimed_atomic (encoding : Encoding Head) (count : Nat) (record : List Head) :
    ∀ process ∈ [payloadProcess encoding .empty, triggerProcess, ownerProcess count] ++
      record.map (burnedProcess encoding),
      ∀ nested, canonicalize process.1 ≠ .collection .hashBag nested none := by
  intro process member nested
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | inRecord
  · simp [payloadProcess, closedProcess, payload, zero, canonicalize]
  · simp [triggerProcess, closedProcess, trigger, output, canonicalize]
  · cases count <;> simp [ownerProcess, closedProcess, owner, zero, input, canonicalize]
  · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
    simp [burnedProcess, closedProcess, burned, output, canonicalize]

theorem empty_reclaimed_any_fuel_has_no_step (encoding : Encoding Head)
    (count : Nat) (record : List Head) {target : RhoProcess}
    (actual : rhoLanguageDefGSLT.Step (reclaimed encoding .empty count record) target) : False := by
  obtain ⟨rule, residue, sourceEqual, _⟩ := public_reaction actual
  obtain ⟨process, member, inputShape⟩ := parallel_member _ (empty_reclaimed_atomic encoding count record)
    (rule_input_mem rule residue sourceEqual)
  have inputChannel : rule.inputChannel = metabolic := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl) | inRecord
    · have impossible := congrArg inputChannelOf inputShape
      change some rule.inputChannel = none at impossible
      cases impossible
    · have impossible := congrArg inputChannelOf inputShape
      change some rule.inputChannel = none at impossible
      cases impossible
    · cases count with
      | zero =>
          have impossible := congrArg inputChannelOf inputShape
          change some rule.inputChannel = none at impossible
          cases impossible
      | succ count =>
          have names := congrArg inputChannelOf inputShape
          change some rule.inputChannel = some metabolic at names
          exact Option.some.inj names
    · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
      have impossible := congrArg inputChannelOf inputShape
      change some rule.inputChannel = none at impossible
      cases impossible
  obtain ⟨process, member, outputShape⟩ := parallel_member _ (empty_reclaimed_atomic encoding count record)
    (rule_output_mem rule residue sourceEqual)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | inRecord
  · have impossible := congrArg outputChannelOf outputShape
    change some rule.outputChannel = none at impossible
    cases impossible
  · have outputChannel : rule.outputChannel = pop := by
      have names := congrArg outputChannelOf outputShape
      change some rule.outputChannel = some pop at names
      exact Option.some.inj names
    exact names_distinct.1 (by simpa [inputChannel, outputChannel] using rule.channels)
  · have impossible := congrArg outputChannelOf outputShape
    cases count <;> change some rule.outputChannel = none at impossible <;> cases impossible
  · obtain ⟨head, _, rfl⟩ := List.mem_map.mp inRecord
    have outputChannel : rule.outputChannel = spent := by
      have names := congrArg outputChannelOf outputShape
      change some rule.outputChannel = some spent at names
      exact Option.some.inj names
    exact names_distinct.2.1 (by simpa [inputChannel, outputChannel] using rule.channels)

theorem empty_reclaimed_any_fuel_has_no_firing (encoding : Encoding Head)
    (count : Nat) (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (reclaimed encoding .empty count record)) :
    ∀ _ : ResourcePredation.Firing source, False := by
  intro firing
  exact empty_reclaimed_any_fuel_has_no_step encoding count record
    (firing_step_at source _ sourceInventory firing)

theorem exhausted_live_public_quiet (encoding : Encoding Head) (stack : Stack Head)
    (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding stack 0 record))
    {target : RhoProcess} (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) target) :
    target = readout source :=
  public_history_quiet_of_no_firing
    (exhausted_live_has_no_firing encoding stack record source sourceInventory) history

theorem empty_reclaimed_any_fuel_public_quiet (encoding : Encoding Head)
    (count : Nat) (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (reclaimed encoding .empty count record))
    {target : RhoProcess} (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) target) :
    target = readout source :=
  public_history_quiet_of_no_firing
    (empty_reclaimed_any_fuel_has_no_firing encoding count record source sourceInventory) history

/-- Empty stacks can be reclaimed, but no following debit can complete. -/
theorem empty_stack_second_firing_impossible (encoding : Encoding Head)
    (count : Nat) (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding .empty (count + 1) record))
    (first : ResourcePredation.Firing source) (second : ResourcePredation.Firing first.target) : False :=
  empty_reclaimed_any_fuel_has_no_firing encoding count record first.target
    (live_occurrence_step_reflects encoding .empty count record source sourceInventory first) second

/-- Every actual finite execution consumes the supplied finite controller.
The bound covers arbitrary occurrence choices and equation representatives. -/
theorem live_execution_length_bound (encoding : Encoding Head) (count : Nat) (stack : Stack Head)
    (record : List Head) (source target : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding stack count record))
    (execution : ResourceClaimHistory.Execution source target) : execution.length ≤ 2 * count := by
  induction count generalizing stack record source target with
  | zero =>
      cases execution with
      | done => simp [ResourceClaimHistory.Execution.length]
      | next firing rest =>
          exact False.elim (exhausted_live_has_no_firing encoding stack record source sourceInventory firing)
  | succ count ih =>
      cases execution with
      | done => simp [ResourceClaimHistory.Execution.length]
      | next firing rest =>
          have intermediate := live_occurrence_step_reflects encoding stack count record source sourceInventory firing
          cases stack with
          | empty =>
              cases rest with
              | done => simp [ResourceClaimHistory.Execution.length]; omega
              | next second remainder =>
                  exact False.elim
                    (empty_reclaimed_any_fuel_has_no_firing encoding count record firing.target intermediate second)
          | cell head tail =>
              cases rest with
              | done => simp [ResourceClaimHistory.Execution.length]; omega
              | next second remainder =>
                  have remaining := reclaimed_occurrence_step_reflects encoding head tail count record
                    firing.target intermediate second
                  have bound := ih tail (head :: record) second.target target remaining remainder
                  simpa only [ResourceClaimHistory.Execution.length] using (by omega :
                    1 + (1 + remainder.length) ≤ 2 * (count + 1))

theorem public_execution_bounded (encoding : Encoding Head) (count : Nat) (stack : Stack Head)
    (record : List Head) (source : Configuration)
    (sourceInventory : inventory source = fromProcess (live encoding stack count record))
    {target : RhoProcess} (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) target) :
    ∃ final, ∃ execution : ResourceClaimHistory.Execution source final,
      inventory final = fromProcess target ∧ execution.length ≤ 2 * count := by
  obtain ⟨final, execution, endpoint⟩ := ResourceClaimHistory.public_execution_lifts source history
  exact ⟨final, execution, endpoint,
    live_execution_length_bound encoding count stack record source final sourceInventory execution⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic
