import Mettapedia.Logic.Derivation
import Init.Data.Array.Lemmas

/-!
# Shared finite derivation graphs

Nodes cite earlier cache positions rather than expanding their proof trees.
The premise list retains order and repeated occurrences. Origins accompany
the graph but do not authorize an inference. The rule witness is checked
against the actual cited premises and the claimed conclusion.

The logical soundness theorem uses the existing `RuleWitness` and `Derives`.
It applies to any finite graph and does not depend on exported theorem names.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DerivationGraph

universe u v w

variable {J : Type u} {W : Type v} {Origin : Type w}

structure Node (J : Type u) (W : Type v) (Origin : Type w) where
  conclusion : J
  witness : W
  parents : List Nat
  origin : Origin

/-- Every reference is resolved in the already checked cache. -/
def lookupPremises (cache : Array J) : List Nat → Option (List J)
  | [] => some []
  | index :: rest => do
      let premise ← cache[index]?
      let premises ← lookupPremises cache rest
      pure (premise :: premises)

/-- Successful lookup retains one entry for every premise occurrence. -/
theorem lookupPremises_length (cache : Array J) {indices : List Nat} {premises : List J}
    (accepted : lookupPremises cache indices = some premises) :
    premises.length = indices.length := by
  induction indices generalizing premises with
  | nil => cases Option.some.inj accepted; rfl
  | cons index rest ih =>
      cases head : cache[index]? with
      | none => simp [lookupPremises, head] at accepted
      | some premise =>
          cases tail : lookupPremises cache rest with
          | none => simp [lookupPremises, head, tail] at accepted
          | some earlier =>
              have equal : premise :: earlier = premises := by
                simpa [lookupPremises, head, tail] using accepted
              subst premises
              simp only [List.length_cons, ih tail]

/-- Each selected premise is a previously stored judgment. -/
theorem lookupPremises_mem (cache : Array J) {indices : List Nat} {premises : List J}
    (accepted : lookupPremises cache indices = some premises) :
    ∀ premise ∈ premises, premise ∈ cache := by
  induction indices generalizing premises with
  | nil =>
      cases Option.some.inj accepted
      intro premise member
      cases member
  | cons index rest ih =>
      cases head : cache[index]? with
      | none => simp [lookupPremises, head] at accepted
      | some premise =>
          cases tail : lookupPremises cache rest with
          | none => simp [lookupPremises, head, tail] at accepted
          | some earlier =>
              have equal : premise :: earlier = premises := by
                simpa [lookupPremises, head, tail] using accepted
              subst premises
              intro judgment member
              rcases List.mem_cons.mp member with rfl | member
              · exact Array.mem_of_getElem? head
              · exact ih tail judgment member

def Node.replay {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (cache : Array J) (node : Node J interface.W Origin) : Option (Array J) := do
  let premises ← lookupPremises cache node.parents
  if interface.isInstance node.witness premises node.conclusion then
    some (cache.push node.conclusion)
  else none

/-- Exact replay records both the ordered references and the rule check.
This also permits a richer surrounding judgment, such as a theory context,
to reuse graph admission without a second graph checker. -/
theorem Node.replay_eq_some_iff {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (cache result : Array J)
    (node : Node J interface.W Origin) :
    node.replay interface cache = some result ↔
      ∃ premises, lookupPremises cache node.parents = some premises ∧
        interface.isInstance node.witness premises node.conclusion = true ∧
        result = cache.push node.conclusion := by
  unfold replay
  cases found : lookupPremises cache node.parents with
  | none => simp
  | some earlier =>
      constructor
      · intro checked
        change (if interface.isInstance node.witness earlier node.conclusion then
          some (cache.push node.conclusion) else none) = some result at checked
        split at checked
        · rename_i valid
          exact ⟨earlier, rfl, valid, (Option.some.inj checked).symm⟩
        · cases checked
      · rintro ⟨premises, selected, valid, shape⟩
        have equal : earlier = premises := Option.some.inj selected
        subst premises
        rw [shape]
        change (if interface.isInstance node.witness earlier node.conclusion then
          some (cache.push node.conclusion) else none) = some (cache.push node.conclusion)
        rw [if_pos valid]

theorem Node.replay_sound {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    {cache result : Array J} {node : Node J interface.W Origin}
    (earlier : ∀ judgment ∈ cache, Derives rules judgment)
    (accepted : node.replay interface cache = some result) :
    ∀ judgment ∈ result, Derives rules judgment := by
  cases premisesFound : lookupPremises cache node.parents with
  | none => simp [replay, premisesFound] at accepted
  | some premises =>
      by_cases valid : interface.isInstance node.witness premises node.conclusion = true
      · have equal : cache.push node.conclusion = result := by
          simpa [replay, premisesFound, valid] using accepted
        subst result
        intro judgment member
        rcases Array.mem_push.mp member with member | rfl
        · exact earlier judgment member
        · exact Derives.node premises node.conclusion
            (interface.sound node.witness premises node.conclusion valid)
            (fun premise member => earlier premise
              (lookupPremises_mem cache premisesFound premise member))
      · simp [replay, premisesFound, valid] at accepted

/-- The cache grows once for each accepted node, with no proof-tree expansion. -/
def replayFrom {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules) :
    Array J → List (Node J interface.W Origin) → Option (Array J)
  | cache, [] => some cache
  | cache, node :: rest => do
      let next ← node.replay interface cache
      replayFrom interface next rest

theorem replayFrom_sound {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache result : Array J}
    {nodes : List (Node J interface.W Origin)}
    (earlier : ∀ judgment ∈ cache, Derives rules judgment)
    (accepted : replayFrom interface cache nodes = some result) :
    ∀ judgment ∈ result, Derives rules judgment := by
  induction nodes generalizing cache with
  | nil =>
      cases Option.some.inj accepted
      exact earlier
  | cons node rest ih =>
      cases first : node.replay interface cache with
      | none => simp [replayFrom, first] at accepted
      | some next =>
          apply ih (node.replay_sound interface earlier first)
          simpa [replayFrom, first] using accepted

def replay {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (nodes : List (Node J interface.W Origin)) : Option (Array J) :=
  replayFrom interface #[] nodes

theorem Node.replay_eq_push {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache result : Array J}
    {node : Node J interface.W Origin}
    (accepted : node.replay interface cache = some result) :
    result = cache.push node.conclusion := by
  unfold replay at accepted
  cases found : lookupPremises cache node.parents with
  | none => simp [found] at accepted
  | some premises =>
      by_cases valid : interface.isInstance node.witness premises node.conclusion = true
      · simpa [found, valid] using accepted.symm
      · simp [found, valid] at accepted

/-- Appending checked nodes cannot change any earlier premise address. -/
theorem replayFrom_preserves_lookup {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache result : Array J}
    {nodes : List (Node J interface.W Origin)}
    (accepted : replayFrom interface cache nodes = some result)
    {index : Nat} {judgment : J} (found : cache[index]? = some judgment) :
    result[index]? = some judgment := by
  induction nodes generalizing cache with
  | nil => cases Option.some.inj accepted; exact found
  | cons node rest ih =>
      cases first : node.replay interface cache with
      | none => simp [replayFrom, first] at accepted
      | some next =>
          have remaining : replayFrom interface next rest = some result := by
            simpa [replayFrom, first] using accepted
          apply ih remaining
          rw [node.replay_eq_push interface first]
          have inside : index < cache.size := (Array.getElem?_eq_some_iff.mp found).1
          rw [Array.getElem?_push, if_neg (Nat.ne_of_lt inside)]
          exact found

theorem replayFrom_append {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache middle result : Array J}
    {first later : List (Node J interface.W Origin)}
    (initial : replayFrom interface cache first = some middle)
    (remaining : replayFrom interface middle later = some result) :
    replayFrom interface cache (first ++ later) = some result := by
  induction first generalizing cache with
  | nil => cases Option.some.inj initial; exact remaining
  | cons node rest ih =>
      cases first : node.replay interface cache with
      | none => simp [replayFrom, first] at initial
      | some next =>
          have suffix : replayFrom interface next rest = some middle := by
            simpa [replayFrom, first] using initial
          simpa [replayFrom, first] using ih suffix

private def Buildable {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (Origin : Type w) (judgment : J) : Prop :=
  ∀ cache, ∃ (nodes : List (Node J interface.W Origin)) (result : Array J) (index : Nat),
    replayFrom interface cache nodes = some result ∧ result[index]? = some judgment

private theorem buildPremises {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (premises : List J)
    (available : ∀ judgment ∈ premises, Buildable interface Origin judgment)
    (cache : Array J) :
    ∃ (nodes : List (Node J interface.W Origin)) (result : Array J) (indices : List Nat),
      replayFrom interface cache nodes = some result ∧
        lookupPremises result indices = some premises := by
  induction premises generalizing cache with
  | nil => exact ⟨[], cache, [], rfl, rfl⟩
  | cons premise rest ih =>
      obtain ⟨first, middle, index, checked, found⟩ := available premise (by simp) cache
      obtain ⟨later, result, indices, checkedLater, foundLater⟩ :=
        ih (fun judgment member => available judgment (by simp [member])) middle
      refine ⟨first ++ later, result, index :: indices,
        replayFrom_append interface checked checkedLater, ?_⟩
      simp [lookupPremises, replayFrom_preserves_lookup interface checkedLater found, foundLater]

/-- Every finite derivation has a checked, backward-referencing graph.
The existence proof chooses source rule witnesses, rather than assuming an
exporter's correctness. A receiving replay can still retain a more shared graph. -/
theorem exists_replay_of_derives {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (origin : Origin)
    {judgment : J} (derivation : Derives rules judgment) :
    ∃ (nodes : List (Node J interface.W Origin)) (cache : Array J) (index : Nat),
      replay interface nodes = some cache ∧ cache[index]? = some judgment := by
  have buildable : Buildable interface Origin judgment := by
    apply Derives.least (Buildable interface Origin) _ derivation
    intro premises conclusion rule earlier cache
    obtain ⟨witness, accepted⟩ := interface.complete premises conclusion rule
    obtain ⟨nodes, result, indices, checked, found⟩ := buildPremises interface premises earlier cache
    let node : Node J interface.W Origin := ⟨conclusion, witness, indices, origin⟩
    have last : node.replay interface result = some (result.push conclusion) := by
      simp [Node.replay, node, found, accepted]
    refine ⟨nodes ++ [node], result.push conclusion, result.size,
      replayFrom_append interface checked ?_, Array.getElem?_push_size⟩
    simp [replayFrom, last]
  exact buildable #[]

theorem replay_sound {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {nodes : List (Node J interface.W Origin)}
    {cache : Array J} (accepted : replay interface nodes = some cache) :
    ∀ judgment ∈ cache, Derives rules judgment :=
  replayFrom_sound interface (fun _ member => by simp at member) accepted

/-- A received root is validated by its proof graph and actual conclusion;
its source label is not consulted. -/
theorem root_sound {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {nodes : List (Node J interface.W Origin)}
    {cache : Array J} {root : Nat} {conclusion : J}
    (accepted : replay interface nodes = some cache)
    (rootFound : cache[root]? = some conclusion) : Derives rules conclusion :=
  replay_sound interface accepted conclusion (Array.mem_of_getElem? rootFound)

theorem derives_iff_checked_graph {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (origin : Origin) (judgment : J) :
    Derives rules judgment ↔
      ∃ (nodes : List (Node J interface.W Origin)) (cache : Array J) (index : Nat),
        replay interface nodes = some cache ∧ cache[index]? = some judgment :=
  ⟨exists_replay_of_derives interface origin,
    fun ⟨_, _, _, accepted, found⟩ => root_sound interface accepted found⟩

/-- Repeated references are retained as two premise occurrences. -/
theorem repeated_reference {cache : Array J} {index : Nat} {judgment : J}
    (found : cache[index]? = some judgment) :
    lookupPremises cache [index, index] = some [judgment, judgment] := by
  simp [lookupPremises, found]

/-- A forward reference cannot be satisfied by any node after the current one. -/
theorem out_of_bounds_refused (cache : Array J) (index : Nat)
    (outside : cache.size ≤ index) (rest : List Nat) :
    lookupPremises cache (index :: rest) = none := by
  simp [lookupPremises, Array.getElem?_eq_none outside]


/-- Relocate parent addresses without changing the rule, result or occurrence origin. -/
def Node.relocate (address : Nat → Nat) (node : Node J W Origin) : Node J W Origin :=
  { node with parents := node.parents.map address }

/-- Full positional lookup agreement includes refusal of absent addresses. -/
def LookupAgreement (source target : Array J) (address : Nat → Nat) : Prop :=
  ∀ index, target[address index]? = source[index]?

/-- Relocating the physical parent list preserves its exact ordered lookup result. -/
theorem lookupPremises_relocate {source target : Array J} {address : Nat → Nat}
    (agreement : LookupAgreement source target address) (parents : List Nat) :
    lookupPremises target (parents.map address) = lookupPremises source parents := by
  induction parents with
  | nil => rfl
  | cons parent rest ih => simp [lookupPremises, agreement parent, ih]

/-- Every successful premise address is earlier than the current cache end. -/
theorem lookupPremises_indices_lt {cache : Array J} {indices : List Nat} {premises : List J}
    (found : lookupPremises cache indices = some premises) :
    ∀ index ∈ indices, index < cache.size := by
  induction indices generalizing premises with
  | nil => simp
  | cons index rest ih =>
      cases head : cache[index]? with
      | none => simp [lookupPremises, head] at found
      | some premise =>
          cases tail : lookupPremises cache rest with
          | none => simp [lookupPremises, head, tail] at found
          | some earlier =>
              intro selected member
              rcases List.mem_cons.mp member with rfl | member
              · exact (Array.getElem?_eq_some_iff.mp head).1
              · exact ih tail selected member

/-- An absent parent anywhere in the list refuses the entire premise vector. -/
theorem lookupPremises_none_of_future {cache : Array J} {indices : List Nat} {index : Nat}
    (member : index ∈ indices) (future : cache.size ≤ index) :
    lookupPremises cache indices = none := by
  cases found : lookupPremises cache indices with
  | none => rfl
  | some premises =>
      have earlier := lookupPremises_indices_lt found index member
      omega

/-- A node cannot be authorized by a parent that is stored only later. -/
theorem Node.future_reference_refused {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (cache : Array J)
    (node : Node J interface.W Origin) {index : Nat}
    (member : index ∈ node.parents) (future : cache.size ≤ index) :
    node.replay interface cache = none := by
  simp [Node.replay, lookupPremises_none_of_future member future]

/-- Each accepted node adds one physical conclusion. -/
theorem replayFrom_size {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache result : Array J}
    {nodes : List (Node J interface.W Origin)}
    (accepted : replayFrom interface cache nodes = some result) :
    result.size = cache.size + nodes.length := by
  induction nodes generalizing cache with
  | nil => cases Option.some.inj accepted; simp
  | cons node rest ih =>
      cases first : node.replay interface cache with
      | none => simp [replayFrom, first] at accepted
      | some next =>
          have remaining : replayFrom interface next rest = some result := by
            simpa [replayFrom, first] using accepted
          have counted := ih remaining
          rw [Node.replay_eq_push interface first, Array.size_push] at counted
          simp only [List.length_cons]
          omega

/-- The completed cache retains its prefix and every physical node conclusion. -/
theorem replayFrom_toList {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache result : Array J}
    {nodes : List (Node J interface.W Origin)}
    (accepted : replayFrom interface cache nodes = some result) :
    result.toList = cache.toList ++ nodes.map Node.conclusion := by
  induction nodes generalizing cache with
  | nil => cases Option.some.inj accepted; simp
  | cons node rest ih =>
      cases first : node.replay interface cache with
      | none => simp [replayFrom, first] at accepted
      | some next =>
          have remaining : replayFrom interface next rest = some result := by
            simpa [replayFrom, first] using accepted
          rw [ih remaining, Node.replay_eq_push interface first]
          simp

/-- Appending one corresponding conclusion preserves complete address agreement.
Future local addresses are shifted to the future of the target cache as well. -/
theorem LookupAgreement.push {source target : Array J} {address : Nat → Nat}
    (agreement : LookupAgreement source target address)
    (future : ∀ offset, address (source.size + offset) = target.size + offset)
    (conclusion : J) : LookupAgreement (source.push conclusion) (target.push conclusion) address := by
  intro index
  by_cases newest : index = source.size
  · subst index
    have last := future 0
    simp only [Nat.add_zero] at last
    simp [last]
  · by_cases previous : index < source.size
    · have sourcePresent : ∃ judgment, source[index]? = some judgment := by
        exact ⟨source[index], Array.getElem?_eq_getElem previous⟩
      obtain ⟨judgment, found⟩ := sourcePresent
      have targetFound := (agreement index).trans found
      have targetInside : address index < target.size := (Array.getElem?_eq_some_iff.mp targetFound).1
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt targetInside)]
      rw [Array.getElem?_push, if_neg newest]
      exact agreement index
    · have later : source.size < index := by omega
      have shifted := future (index - source.size)
      have restored : source.size + (index - source.size) = index := by omega
      rw [restored] at shifted
      have targetLater : target.size < address index := by omega
      rw [Array.getElem?_push, if_neg (Nat.ne_of_gt targetLater)]
      rw [Array.getElem?_push, if_neg newest]
      exact agreement index

/-- The remaining local address tail starts after the newly appended node. -/
theorem futureAddresses_push {source target : Array J} {address : Nat → Nat}
    (future : ∀ offset, address (source.size + offset) = target.size + offset)
    (conclusion : J) :
    ∀ offset, address ((source.push conclusion).size + offset) =
      (target.push conclusion).size + offset := by
  intro offset
  have next := future (offset + 1)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

/-- A relocated node executes exactly the same rule witness against the same
premise occurrences. -/
theorem Node.replay_relocate {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {source target result : Array J}
    {address : Nat → Nat} (agreement : LookupAgreement source target address)
    {node : Node J interface.W Origin}
    (accepted : node.replay interface source = some result) :
    (node.relocate address).replay interface target = some (target.push node.conclusion) := by
  obtain ⟨premises, found, admitted, _⟩ := (Node.replay_eq_some_iff interface _ _ _).mp accepted
  apply (Node.replay_eq_some_iff interface _ _ _).mpr
  refine ⟨premises, ?_, admitted, rfl⟩
  simpa only [Node.relocate, lookupPremises_relocate agreement] using found

/-- A refused local node remains refused under full positional relocation. -/
theorem Node.replay_relocate_none {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {source target : Array J}
    {address : Nat → Nat} (agreement : LookupAgreement source target address)
    (node : Node J interface.W Origin) :
    (node.relocate address).replay interface target = none ↔
      node.replay interface source = none := by
  simp only [Node.replay, Node.relocate, lookupPremises_relocate agreement]
  cases lookupPremises source node.parents with
  | none => simp
  | some premises =>
      by_cases accepted : interface.isInstance node.witness premises node.conclusion = true
      · simp [accepted]
      · simp [accepted]

/-- A checked local graph is spliced into a larger checked cache without
expanding any previously stored proof. Exact address agreement survives. -/
theorem replayFrom_relocate {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {source target sourceResult : Array J}
    {address : Nat → Nat} (agreement : LookupAgreement source target address)
    (future : ∀ offset, address (source.size + offset) = target.size + offset)
    {nodes : List (Node J interface.W Origin)}
    (accepted : replayFrom interface source nodes = some sourceResult) :
    ∃ targetResult, replayFrom interface target (nodes.map (Node.relocate address)) = some targetResult ∧
      LookupAgreement sourceResult targetResult address := by
  induction nodes generalizing source target with
  | nil => cases Option.some.inj accepted; exact ⟨target, rfl, agreement⟩
  | cons node rest ih =>
      cases first : node.replay interface source with
      | none => simp [replayFrom, first] at accepted
      | some next =>
          have remaining : replayFrom interface next rest = some sourceResult := by
            simpa [replayFrom, first] using accepted
          have nextEq := Node.replay_eq_push interface first
          subst next
          have actual := Node.replay_relocate interface agreement first
          obtain ⟨targetResult, checked, finalAgreement⟩ := ih
            (agreement.push future node.conclusion) (futureAddresses_push future node.conclusion) remaining
          refine ⟨targetResult, ?_, finalAgreement⟩
          simpa [replayFrom, actual] using checked

/-- A block's refusal is reflected as well as preserved, including absent
parents and malformed rule witnesses. -/
theorem replayFrom_relocate_none_iff {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {source target : Array J}
    {address : Nat → Nat} (agreement : LookupAgreement source target address)
    (future : ∀ offset, address (source.size + offset) = target.size + offset)
    (nodes : List (Node J interface.W Origin)) :
    replayFrom interface target (nodes.map (Node.relocate address)) = none ↔
      replayFrom interface source nodes = none := by
  induction nodes generalizing source target with
  | nil => simp [replayFrom]
  | cons node rest ih =>
      cases first : node.replay interface source with
      | none =>
          have refused := (Node.replay_relocate_none interface agreement node).mpr first
          simp [replayFrom, first, refused]
      | some next =>
          have nextEq := Node.replay_eq_push interface first
          subst next
          have actual := Node.replay_relocate interface agreement first
          simpa [replayFrom, actual, first] using
            ih (agreement.push future node.conclusion) (futureAddresses_push future node.conclusion)


/-- Successful premise selection agrees at every retained occurrence. -/
theorem lookupPremises_at {cache : Array J} {roots : List Nat}
    {premises : List J} (found : lookupPremises cache roots = some premises)
    (index : Nat) (inside : index < roots.length) :
    cache[roots[index]]? = premises[index]? := by
  induction roots generalizing premises index with
  | nil => simp at inside
  | cons root rest ih =>
      cases head : cache[root]? with
      | none => simp [lookupPremises, head] at found
      | some premise =>
          cases tail : lookupPremises cache rest with
          | none => simp [lookupPremises, head, tail] at found
          | some later =>
              have same : premise :: later = premises := by
                simpa [lookupPremises, head, tail] using found
              subst premises
              cases index with
              | zero => simpa using head
              | succ index => simpa using ih tail index (by simpa using inside)

/-- A checked extension preserves every ordered premise-vector lookup. -/
theorem lookupPremises_preserved {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules)
    {actual result : Array J} {nodes : List (Node J interface.W Origin)}
    (accepted : replayFrom interface actual nodes = some result)
    {indices : List Nat} {premises : List J}
    (found : lookupPremises actual indices = some premises) :
    lookupPremises result indices = some premises := by
  induction indices generalizing premises with
  | nil => cases Option.some.inj found; rfl
  | cons index rest ih =>
      cases head : actual[index]? with
      | none => simp [lookupPremises, head] at found
      | some premise =>
          cases tail : lookupPremises actual rest with
          | none => simp [lookupPremises, head, tail] at found
          | some later =>
              have same : premise :: later = premises := by
                simpa [lookupPremises, head, tail] using found
              subst premises
              have preserved := replayFrom_preserves_lookup interface accepted head
              simp [lookupPremises, preserved, ih tail]

/-- Premise lookup distributes over ordered concatenation. -/
theorem lookupPremises_append (actual : Array J) (left right : List Nat) :
    lookupPremises actual (left ++ right) = (do
      let earlier ← lookupPremises actual left
      let later ← lookupPremises actual right
      pure (earlier ++ later)) := by
  induction left with
  | nil => simp [lookupPremises]
  | cons head rest ih =>
      simp only [List.cons_append, lookupPremises, ih]
      cases actual[head]? <;> cases lookupPremises actual rest <;>
        cases lookupPremises actual right <;> rfl



/-- Every parent of an accepted graph is a real physical position in the
completed cache. This also bounds numeric reference encodings. -/
theorem replayFrom_parents_lt_result {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache result : Array J}
    {nodes : List (Node J interface.W Origin)}
    (accepted : replayFrom interface cache nodes = some result) :
    ∀ node ∈ nodes, ∀ index ∈ node.parents, index < result.size := by
  induction nodes generalizing cache with
  | nil => simp
  | cons node rest ih =>
      cases first : node.replay interface cache with
      | none => simp [replayFrom, first] at accepted
      | some next =>
          have later : replayFrom interface next rest = some result := by
            simpa [replayFrom, first] using accepted
          have growth : result.size = next.size + rest.length :=
            replayFrom_size interface (cache := next) (nodes := rest) later
          have nextSize : next.size = cache.size + 1 := by
            rw [Node.replay_eq_push interface first, Array.size_push]
          obtain ⟨premises, selected, _, _⟩ := (Node.replay_eq_some_iff interface _ _ _).mp first
          intro selectedNode member index cited
          rcases List.mem_cons.mp member with same | member
          · subst selectedNode
            have earlier := lookupPremises_indices_lt selected index cited
            omega
          · exact ih later selectedNode member index cited

end Mettapedia.Logic.DerivationGraph
