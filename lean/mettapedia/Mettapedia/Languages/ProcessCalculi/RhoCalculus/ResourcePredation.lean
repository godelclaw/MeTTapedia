import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences
import Mathlib.Data.List.OfFn

/-!
# Resource occurrences and contextual receipt in closed rho

Occurrence keys distinguish equal messages. Origins distinguish the surrounding
context from the protected computation. COMM consumes two selected occurrences;
its continuation inherits the receiver's origin, and newly exposed primes receive
fresh keys. Forgetting this bookkeeping gives the complete, equation-saturated
closed COMM semantics. A resource receipt is an actual firing, not a test of image
membership or of the possession of a channel name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-- Origin records receiver/activation lineage. It does not record who authored
arbitrary quoted code transported as an output payload. -/
inductive Origin where
  | computation
  | context
  deriving DecidableEq

structure Occurrence where
  key : Nat
  origin : Origin
  term : { pattern : Pattern // IsPrime pattern }

/-- Allocation state is monotone across execution, including empty reacta. -/
structure Configuration where
  occurrences : List Occurrence
  nextKey : Nat
  reserved : ∀ occurrence ∈ occurrences, occurrence.key < nextKey

private theorem key_le_sum {occurrences : List Occurrence} {occurrence : Occurrence}
    (membership : occurrence ∈ occurrences) :
    occurrence.key ≤ (occurrences.map Occurrence.key).sum := by
  induction occurrences with
  | nil => simp at membership
  | cons head tail ih =>
      rcases List.mem_cons.mp membership with rfl | membership
      · simp only [List.map_cons, List.sum_cons]
        omega
      · have smaller := ih membership
        simp only [List.map_cons, List.sum_cons]
        omega

/-- The initial reservation lies above all initially supplied keys. -/
def Configuration.ofList (occurrences : List Occurrence) : Configuration where
  occurrences := occurrences
  nextKey := (occurrences.map Occurrence.key).sum + 1
  reserved := by
    intro occurrence membership
    have bound := key_le_sum membership
    omega

/-- Parallel assembly reserves both allocation ranges. Distinct initial keys
are checked separately when a designated occurrence is supplied. -/
def Configuration.join (first second : Configuration) : Configuration where
  occurrences := first.occurrences ++ second.occurrences
  nextKey := max first.nextKey second.nextKey
  reserved := by
    intro occurrence member
    rcases List.mem_append.mp member with left | right
    · exact lt_of_lt_of_le (first.reserved occurrence left) (le_max_left _ _)
    · exact lt_of_lt_of_le (second.reserved occurrence right) (le_max_right _ _)

/-- An origin projection retains allocation history and all selected occurrences. -/
def Configuration.selectOrigin (configuration : Configuration) (origin : Origin) : Configuration where
  occurrences := configuration.occurrences.filter (fun occurrence => occurrence.origin == origin)
  nextKey := configuration.nextKey
  reserved := by
    intro occurrence member
    exact configuration.reserved occurrence (List.mem_of_mem_filter member)

def patterns (configuration : Configuration) : List Pattern :=
  configuration.occurrences.map fun occurrence => occurrence.term.1

def inventory (configuration : Configuration) : Bag :=
  ⟨(patterns configuration : Multiset Pattern), fun pattern membership => by
    obtain ⟨occurrence, _, rfl⟩ := List.mem_map.mp (by simpa [patterns] using membership)
    exact occurrence.term.2⟩

def readout (configuration : Configuration) : RhoProcess :=
  toProcess (inventory configuration)

theorem patterns_prime (configuration : Configuration) :
    ∀ pattern ∈ patterns configuration, IsPrime pattern := by
  intro pattern member
  obtain ⟨occurrence, _, rfl⟩ := List.mem_map.mp member
  exact occurrence.term.2

/-- The retained inventory agrees with a separately formed parallel presentation. -/
theorem inventory_of_patterns (configuration : Configuration) :
    inventory configuration = fromProcess (ofList (patterns configuration)
      (fun pattern member => (patterns_prime configuration pattern member).1)) := by
  apply Subtype.ext
  exact (fromProcess_ofList_primes _ (patterns_prime configuration)).symm

/-- The two initial actors partition the whole operational inventory. -/
theorem inventory_origin_partition (configuration : Configuration) :
    inventory configuration = append
      (inventory (configuration.selectOrigin .computation))
      (inventory (configuration.selectOrigin .context)) := by
  apply Subtype.ext
  change (configuration.occurrences.map (fun occurrence => occurrence.term.1) : Multiset Pattern) =
    (((configuration.occurrences.filter (fun occurrence => occurrence.origin == .computation)).map
      (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern) +
    (((configuration.occurrences.filter (fun occurrence => occurrence.origin == .context)).map
      (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern)
  have partition : ∀ occurrences : List Occurrence,
      (occurrences.map (fun occurrence => occurrence.term.1) : Multiset Pattern) =
        (((occurrences.filter (fun occurrence => occurrence.origin == .computation)).map
          (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern) +
        (((occurrences.filter (fun occurrence => occurrence.origin == .context)).map
          (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern) := by
    intro occurrences
    induction occurrences with
    | nil => simp
    | cons head tail ih =>
        cases head with
        | mk key origin term =>
            cases origin with
            | computation =>
                change term.1 ::ₘ (tail.map (fun occurrence => occurrence.term.1) : Multiset Pattern) =
                  (term.1 ::ₘ (((tail.filter (fun occurrence => occurrence.origin == .computation)).map
                    (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern)) +
                  (((tail.filter (fun occurrence => occurrence.origin == .context)).map
                    (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern)
                rw [Multiset.cons_add, ih]
            | context =>
                change term.1 ::ₘ (tail.map (fun occurrence => occurrence.term.1) : Multiset Pattern) =
                  (((tail.filter (fun occurrence => occurrence.origin == .computation)).map
                    (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern) +
                  (term.1 ::ₘ (((tail.filter (fun occurrence => occurrence.origin == .context)).map
                    (fun occurrence => occurrence.term.1) : List Pattern) : Multiset Pattern))
                rw [Multiset.add_cons, ih]
  exact partition _

def Distinct (configuration : Configuration) : Prop :=
  (configuration.occurrences.map Occurrence.key).Nodup

def fresh (configuration : Configuration) : Nat := configuration.nextKey

theorem key_lt_fresh {configuration : Configuration} {occurrence : Occurrence}
    (membership : occurrence ∈ configuration.occurrences) : occurrence.key < fresh configuration :=
  configuration.reserved occurrence membership

/-- Selection is by occurrence position before and after removal of the input. -/
structure Firing (source : Configuration) where
  inputIndex : Fin source.occurrences.length
  outputIndex : Fin (source.occurrences.eraseIdx inputIndex.val).length
  rule : GroundComm
  inputAt : (source.occurrences[inputIndex.val]).term.1 = input rule.inputChannel rule.body
  outputAt : ((source.occurrences.eraseIdx inputIndex.val)[outputIndex.val]).term.1 =
    output rule.outputChannel rule.payload

namespace Firing

variable {source : Configuration}

def receiver (firing : Firing source) : Occurrence := source.occurrences[firing.inputIndex.val]

def resource (firing : Firing source) : Occurrence :=
  (source.occurrences.eraseIdx firing.inputIndex.val)[firing.outputIndex.val]

def tail (firing : Firing source) : Configuration where
  occurrences := (source.occurrences.eraseIdx firing.inputIndex.val).eraseIdx firing.outputIndex.val
  nextKey := source.nextKey
  reserved := by
    intro occurrence membership
    exact source.reserved occurrence
      (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx membership))

/-- The actual substituted continuation is decomposed into all of its primes. -/
def spawned (firing : Firing source) : List Occurrence :=
  List.ofFn fun position : Fin (ordered firing.rule.reactum.1).length =>
    { key := fresh source + position.val
      origin := firing.receiver.origin
      term := ⟨(ordered firing.rule.reactum.1)[position.val],
        ordered_prime firing.rule.reactum (List.getElem_mem position.isLt)⟩ }

def target (firing : Firing source) : Configuration where
  occurrences := firing.spawned ++ firing.tail.occurrences
  nextKey := source.nextKey + firing.spawned.length
  reserved := by
    intro occurrence membership
    rcases List.mem_append.mp membership with spawned | remaining
    · obtain ⟨position, rfl⟩ := List.mem_ofFn.mp spawned
      change source.nextKey + position.val <
        source.nextKey + firing.spawned.length
      simp only [Firing.spawned, List.length_ofFn]
      omega
    · have bound := firing.tail.reserved occurrence remaining
      change occurrence.key < source.nextKey at bound
      omega

theorem selection_perm (firing : Firing source) :
    List.Perm source.occurrences (firing.receiver :: firing.resource :: firing.tail.occurrences) :=
  ((List.getElem_cons_eraseIdx_perm firing.outputIndex.isLt).cons _ |>.trans
    (List.getElem_cons_eraseIdx_perm firing.inputIndex.isLt)).symm

theorem source_readout (firing : Firing source) :
    inventory source = append firing.rule.redex (inventory firing.tail) := by
  apply Subtype.ext
  have permutation := firing.selection_perm.map (fun occurrence => occurrence.term.1)
  have equal := Multiset.coe_eq_coe.mpr permutation
  simpa [inventory, patterns, receiver, resource, firing.inputAt, firing.outputAt,
    append, GroundComm.redex] using equal

@[simp]
theorem spawned_patterns (firing : Firing source) :
    (firing.spawned.map fun occurrence => occurrence.term.1) = ordered firing.rule.reactum.1 := by
  simp only [spawned, List.map_ofFn]
  exact List.ofFn_getElem

theorem target_readout (firing : Firing source) :
    inventory firing.target = append firing.rule.reactum (inventory firing.tail) := by
  apply Subtype.ext
  change ((firing.spawned ++ firing.tail.occurrences).map
    (fun occurrence => occurrence.term.1) : Multiset Pattern) = _
  rw [List.map_append]
  change (((firing.spawned.map fun occurrence => occurrence.term.1) ++ patterns firing.tail) : Multiset Pattern) = _
  rw [spawned_patterns, ← Multiset.coe_add, ordered_multiset]
  rfl

/-- The bookkeeping receipt executes in the independent public rho semantics. -/
theorem public_step (firing : Firing source) :
    rhoLanguageDefGSLT.Step (readout source) (readout firing.target) := by
  apply reaction_public
  exact ⟨firing.rule, inventory firing.tail,
    firing.source_readout, firing.target_readout⟩

theorem spawned_origin (firing : Firing source) {occurrence : Occurrence}
    (membership : occurrence ∈ firing.spawned) :
    occurrence.origin = firing.receiver.origin := by
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp membership
  rfl

theorem spawned_fresh (firing : Firing source) {occurrence : Occurrence}
    (membership : occurrence ∈ firing.spawned) : fresh source ≤ occurrence.key := by
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp membership
  change fresh source ≤ fresh source + position.val
  omega

theorem tail_mem_source (firing : Firing source) {occurrence : Occurrence}
    (membership : occurrence ∈ firing.tail.occurrences) : occurrence ∈ source.occurrences :=
  List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx membership)

/-- Equal payloads do not allow the consumed key to survive as another occurrence. -/
theorem resource_key_removed (firing : Firing source) (distinct : Distinct source) :
    ∀ occurrence ∈ firing.target.occurrences, occurrence.key ≠ firing.resource.key := by
  intro occurrence membership equal
  rcases List.mem_append.mp membership with spawned | remaining
  · have lower := firing.spawned_fresh spawned
    have upper := key_lt_fresh (List.mem_of_mem_eraseIdx
      (List.getElem_mem firing.outputIndex.isLt))
    change firing.resource.key < fresh source at upper
    omega
  · have unique := firing.selection_perm.map Occurrence.key |>.nodup_iff.mp distinct
    have tailUnique : firing.resource.key ∉ firing.tail.occurrences.map Occurrence.key := by
      exact (List.nodup_cons.mp (List.nodup_cons.mp unique).2).1
    exact tailUnique (List.mem_map.mpr ⟨occurrence, remaining, equal⟩)

/-- Fresh keys and retained old keys remain distinct after an actual firing. -/
theorem distinct_target (firing : Firing source) (distinct : Distinct source) :
    Distinct firing.target := by
  have tailDistinct : (firing.tail.occurrences.map Occurrence.key).Nodup := by
    have unique := firing.selection_perm.map Occurrence.key |>.nodup_iff.mp distinct
    exact (List.nodup_cons.mp (List.nodup_cons.mp unique).2).2
  have spawnedDistinct : (firing.spawned.map Occurrence.key).Nodup := by
    simp only [spawned, List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro first second equal
    apply Fin.ext
    change fresh source + first.val = fresh source + second.val at equal
    omega
  change ((firing.spawned ++ firing.tail.occurrences).map Occurrence.key).Nodup
  rw [List.map_append, List.nodup_append]
  refine ⟨spawnedDistinct, tailDistinct, ?_⟩
  intro firstKey left secondKey right equal
  obtain ⟨newOccurrence, newMember, newKey⟩ := List.mem_map.mp left
  obtain ⟨oldOccurrence, oldMember, oldKey⟩ := List.mem_map.mp right
  have lower := firing.spawned_fresh newMember
  have upper := key_lt_fresh (firing.tail_mem_source oldMember)
  omega

end Firing

/-- Finite annotated executions; each edge has its own actual COMM receipt. -/
def Step (source target : Configuration) : Prop :=
  ∃ firing : Firing source, firing.target = target

abbrev History := Relation.ReflTransGen Step

/-- Every public closed step has an occurrence selection in this inventory.
This uses completeness of the independently authored COMM family, including
all equation transports; no scheduler or selected execution is assumed. -/
theorem publicStep_lifts {source : Configuration} {target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step (readout source) target) :
    ∃ firing : Firing source, inventory firing.target = fromProcess target := by
  obtain ⟨rule, residue, sourceEqual, targetEqual⟩ := public_reaction step
  rw [readout, fromProcess_toProcess] at sourceEqual
  have permutation : List.Perm (patterns source)
      (input rule.inputChannel rule.body :: output rule.outputChannel rule.payload ::
        ordered residue.1) := by
    apply Multiset.coe_eq_coe.mp
    change (inventory source).1 = _
    rw [sourceEqual]
    change ([input rule.inputChannel rule.body, output rule.outputChannel rule.payload] :
      Multiset Pattern) + residue.1 = _
    calc
      _ = ([input rule.inputChannel rule.body, output rule.outputChannel rule.payload] :
          Multiset Pattern) + (ordered residue.1 : Multiset Pattern) :=
        congrArg (fun rest =>
          ([input rule.inputChannel rule.body, output rule.outputChannel rule.payload] :
            Multiset Pattern) + rest) (ordered_multiset residue.1).symm
      _ = _ := Multiset.coe_add _ _
  obtain ⟨i, iBound, j, jBound, inputAt, outputAt, tailPermutation⟩ :=
    locate_pair permutation
  have iSource : i < source.occurrences.length := by simpa [patterns] using iBound
  have jSource : j < (source.occurrences.eraseIdx i).length := by
    simpa [patterns, List.eraseIdx_map] using jBound
  have inputShape : (source.occurrences[i]).term.1 = input rule.inputChannel rule.body := by
    simpa [patterns] using inputAt
  have outputShape : ((source.occurrences.eraseIdx i)[j]).term.1 =
      output rule.outputChannel rule.payload := by
    simpa [patterns, List.eraseIdx_map] using outputAt
  let firing : Firing source := ⟨⟨i, iSource⟩, ⟨j, jSource⟩, rule, inputShape, outputShape⟩
  have residueEqual : inventory firing.tail = residue := by
    apply Subtype.ext
    rw [← ordered_multiset residue.1]
    apply Multiset.coe_eq_coe.mpr
    simpa [inventory, patterns, Firing.tail, firing, List.eraseIdx_map] using tailPermutation
  refine ⟨firing, ?_⟩
  rw [firing.target_readout, residueEqual]
  exact targetEqual.symm

/-- Every finite annotated history is an actual closed rho execution. -/
theorem History.public {source target : Configuration} (history : History source target) :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) (readout target) := by
  induction history with
  | refl => exact .refl
  | tail history step ih =>
      obtain ⟨firing, rfl⟩ := step
      exact ih.tail firing.public_step

/-- Every finite public execution can retain occurrence and origin receipts.
The target presentation is compared by its independently canonical inventory. -/
theorem public_history_lifts (initial : Configuration) {target : RhoProcess}
    (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout initial) target) :
    ∃ final, History initial final ∧ inventory final = fromProcess target := by
  induction history with
  | refl => exact ⟨initial, .refl, (fromProcess_toProcess _).symm⟩
  | @tail middle target history step ih =>
      obtain ⟨current, receiptHistory, currentEqual⟩ := ih
      have currentStep : rhoLanguageDefGSLT.Step (readout current) target := by
        apply (CanonicalReaction.publicStep_iff _ _).mpr
        rw [readout, fromProcess_toProcess, currentEqual]
        exact (CanonicalReaction.publicStep_iff _ _).mp step
      obtain ⟨firing, finalEqual⟩ := publicStep_lifts currentStep
      exact ⟨firing.target, receiptHistory.tail ⟨firing, rfl⟩, finalEqual⟩

/-- Persistent occurrence identity is preserved throughout the supplied history. -/
theorem History.distinct {source target : Configuration} (history : History source target)
    (distinct : Distinct source) : Distinct target := by
  induction history with
  | refl => exact distinct
  | tail history step ih =>
      obtain ⟨firing, rfl⟩ := step
      exact firing.distinct_target ih

/-- A resource designation is an initially present, uniquely keyed output
owned by the computation. It is independent of future contextual behavior. -/
def ProtectedResource (resourceKey : Nat) (initial : Configuration) : Prop :=
  Distinct initial ∧ ∃ occurrence ∈ initial.occurrences,
    occurrence.key = resourceKey ∧ occurrence.origin = .computation ∧
      ∃ channel payload, occurrence.term.1 = output channel payload

/-- A computation-owned output is received by a context-origin input. -/
def HarvestAt {source : Configuration} (resourceKey : Nat) (firing : Firing source) : Prop :=
  firing.resource.key = resourceKey ∧ firing.resource.origin = .computation ∧
    firing.receiver.origin = .context

def CanHarvest (resourceKey : Nat) (initial : Configuration) : Prop :=
  ProtectedResource resourceKey initial ∧
    ∃ current, History initial current ∧
      ∃ firing : Firing current, HarvestAt resourceKey firing

/-- Matching and the initial resource designation are supplied independently
before the actual operational receipt is constructed. -/
theorem matching_occurrences_harvest (source : Configuration)
    (distinct : Distinct source)
    (inputIndex : Fin source.occurrences.length)
    (outputIndex : Fin (source.occurrences.eraseIdx inputIndex.val).length)
    (rule : GroundComm)
    (inputAt : (source.occurrences[inputIndex.val]).term.1 = input rule.inputChannel rule.body)
    (outputAt : ((source.occurrences.eraseIdx inputIndex.val)[outputIndex.val]).term.1 =
      output rule.outputChannel rule.payload)
    (computationResource : ((source.occurrences.eraseIdx inputIndex.val)[outputIndex.val]).origin =
      .computation)
    (contextReceiver : (source.occurrences[inputIndex.val]).origin = .context) :
    ∃ firing : Firing source,
      HarvestAt ((source.occurrences.eraseIdx inputIndex.val)[outputIndex.val]).key firing ∧
      rhoLanguageDefGSLT.Step (readout source) (readout firing.target) ∧
      CanHarvest ((source.occurrences.eraseIdx inputIndex.val)[outputIndex.val]).key source := by
  let firing : Firing source := ⟨inputIndex, outputIndex, rule, inputAt, outputAt⟩
  have resource : ProtectedResource firing.resource.key source :=
    ⟨distinct, firing.resource,
      List.mem_of_mem_eraseIdx (List.getElem_mem outputIndex.isLt),
      rfl, computationResource, rule.outputChannel, rule.payload, outputAt⟩
  have harvesting : HarvestAt firing.resource.key firing :=
    ⟨rfl, computationResource, contextReceiver⟩
  exact ⟨firing, harvesting, firing.public_step, resource, source, .refl, firing, harvesting⟩

/-- Empty reacta never roll back the allocation reservation. -/
theorem Firing.nextKey_mono {source : Configuration} (firing : Firing source) :
    source.nextKey ≤ firing.target.nextKey := by
  change source.nextKey ≤ source.nextKey + firing.spawned.length
  omega

theorem History.nextKey_mono {source target : Configuration}
    (history : History source target) : source.nextKey ≤ target.nextKey := by
  induction history with
  | refl => rfl
  | tail history step ih =>
      obtain ⟨firing, rfl⟩ := step
      exact ih.trans firing.nextKey_mono

/-- Every old key in a target retains its complete original occurrence. -/
theorem Firing.old_occurrence_mem_source {source : Configuration} (firing : Firing source)
    {occurrence : Occurrence} (old : occurrence.key < source.nextKey)
    (membership : occurrence ∈ firing.target.occurrences) : occurrence ∈ source.occurrences := by
  rcases List.mem_append.mp membership with new | retained
  · have lower := firing.spawned_fresh new
    exact False.elim (by unfold fresh at lower; omega)
  · exact firing.tail_mem_source retained

theorem History.old_occurrence_mem_source {source target : Configuration}
    (history : History source target) {occurrence : Occurrence}
    (old : occurrence.key < source.nextKey) (membership : occurrence ∈ target.occurrences) :
    occurrence ∈ source.occurrences := by
  induction history with
  | refl => exact membership
  | tail history step ih =>
      obtain ⟨firing, rfl⟩ := step
      have currentBound : occurrence.key < _ :=
        lt_of_lt_of_le old (History.nextKey_mono history)
      exact ih (firing.old_occurrence_mem_source currentBound membership)

/-- A consumed resource cannot reappear under its old key anywhere later. -/
theorem Firing.consumed_key_never_reappears {source : Configuration}
    (firing : Firing source) (distinct : Distinct source)
    {future : Configuration} (history : History firing.target future) :
    ∀ occurrence ∈ future.occurrences, occurrence.key ≠ firing.resource.key := by
  intro occurrence membership equal
  have initialBound := source.reserved firing.resource
    (List.mem_of_mem_eraseIdx (List.getElem_mem firing.outputIndex.isLt))
  have old : occurrence.key < firing.target.nextKey := by
    rw [equal]
    exact lt_of_lt_of_le initialBound firing.nextKey_mono
  exact firing.resource_key_removed distinct occurrence
    (History.old_occurrence_mem_source history old membership) equal

/-- Independent shape invariant of the output-only context profile. -/
def ContextOutputs (configuration : Configuration) : Prop :=
  ∀ occurrence ∈ configuration.occurrences, occurrence.origin = .context →
    ∃ channel payload, occurrence.term.1 = output channel payload

theorem Firing.receiver_not_context {source : Configuration} (firing : Firing source)
    (outputs : ContextOutputs source) : firing.receiver.origin ≠ .context := by
  intro context
  obtain ⟨channel, payload, shape⟩ := outputs firing.receiver
    (List.getElem_mem firing.inputIndex.isLt) context
  have impossible := firing.inputAt.symm.trans shape
  simp [input, output] at impossible

theorem Firing.contextOutputs_target {source : Configuration} (firing : Firing source)
    (outputs : ContextOutputs source) : ContextOutputs firing.target := by
  intro occurrence membership context
  rcases List.mem_append.mp membership with spawned | remaining
  · exact False.elim (firing.receiver_not_context outputs
      ((firing.spawned_origin spawned).symm.trans context))
  · exact outputs occurrence (firing.tail_mem_source remaining) context

theorem History.contextOutputs {source target : Configuration}
    (history : History source target) (outputs : ContextOutputs source) :
    ContextOutputs target := by
  induction history with
  | refl => exact outputs
  | tail history step ih =>
      obtain ⟨firing, rfl⟩ := step
      exact firing.contextOutputs_target ih

/-- Protection allows legitimate computation-origin spending throughout the path. -/
theorem contextOutputs_never_harvest {source : Configuration}
    (outputs : ContextOutputs source) (key : Nat) : ¬ CanHarvest key source := by
  rintro ⟨_, current, history, firing, _, _, context⟩
  exact firing.receiver_not_context (history.contextOutputs outputs) context

/-- A closed quiescent system admits no contextual receipt at any finite time. -/
theorem never_harvest_of_no_firing {source : Configuration}
    (quiescent : ∀ _ : Firing source, False) (key : Nat) :
    ¬ CanHarvest key source := by
  have quietHistory : ∀ {target}, History source target → target = source := by
    intro target history
    induction history with
    | refl => rfl
    | tail history step ih =>
        subst ih
        obtain ⟨firing, _⟩ := step
        exact False.elim (quiescent firing)
  rintro ⟨_, current, history, firing, _⟩
  have equal := quietHistory history
  subst current
  exact quiescent firing

/-- Quiescence holds for the whole public semantics, including equations. -/
theorem public_history_quiet_of_no_firing {source : Configuration}
    (quiescent : ∀ _ : Firing source, False) {target : RhoProcess}
    (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) target) :
    target = readout source := by
  induction history with
  | refl => rfl
  | tail history step ih =>
      rw [ih] at step
      obtain ⟨firing, _⟩ := publicStep_lifts step
      exact False.elim (quiescent firing)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation
