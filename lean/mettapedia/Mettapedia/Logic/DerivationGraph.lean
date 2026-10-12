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

end Mettapedia.Logic.DerivationGraph
