import Mettapedia.Logic.DerivationGraph
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Schedule independence of derivation-graph checking

A derivation graph is checked by a sequential replay. Each node reads only its
ordered premise occurrences in the cache and contributes one value. This module
proves that the order of independent nodes is irrelevant.

* `replayWith` replays a graph with any local step that reads only the node's
  premise values. Judgment checking (`replayWith_judgmentStep`) is one instance;
  proof-relevant unfolding into the free multicategory is another
  (`RuleMulticategoryGraphs`).
* `replayWith_iff_local` characterizes sequential acceptance by local
  constraints on the final cache: backward references, and each node's step
  applied to its looked-up premises.
* `replayWith_permute`, `replayWith_permute_reflect`, `replayWith_permute_iff`:
  reordering the nodes by any permutation that keeps every premise before its
  consumer, relocating references accordingly, preserves acceptance (in both
  directions when the original order is topological) and moves each node's
  value with it.
  `replayWith_permute_refused`: a reordering that places a premise after its
  consumer is refused.
* The work account is schedule invariant: the number of local steps and the
  number of premise lookups do not depend on the order
  (`permute_length`, `permute_lookups`).

This answers, for the shared checking loop, the requirement that acceptance
and its resource account be independent of the checking schedule. It concerns
linear extensions of one dependency graph; it does not identify graphs that
differ in sharing.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DerivationGraph

universe u v w x

variable {J : Type u} {W : Type v} {Origin : Type w} {α : Type x}

/-- Replay with a local step that reads only the node and its ordered premise
values. -/
def replayWith (step : Node J W Origin → List α → Option α) :
    Array α → List (Node J W Origin) → Option (Array α)
  | cache, [] => some cache
  | cache, node :: rest =>
      match lookupPremises cache node.parents with
      | none => none
      | some premises =>
          match step node premises with
          | none => none
          | some value => replayWith step (cache.push value) rest

/-- The judgment-checking step of a rule-witness interface. -/
def judgmentStep {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (node : Node J interface.W Origin) (premises : List J) : Option J :=
  if interface.isInstance node.witness premises node.conclusion then some node.conclusion else none

/-- Ordinary graph replay is replay with the judgment-checking step. -/
theorem replayWith_judgmentStep {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (cache : Array J) (nodes : List (Node J interface.W Origin)) :
    replayWith (judgmentStep interface) cache nodes = replayFrom interface cache nodes := by
  induction nodes generalizing cache with
  | nil => rfl
  | cons node rest ih =>
      simp only [replayWith, replayFrom, Node.replay, judgmentStep]
      cases lookupPremises cache node.parents with
      | none => rfl
      | some premises =>
          by_cases accepted : interface.isInstance node.witness premises node.conclusion = true
          · simp [accepted, ih]
          · simp [accepted]

/-- Replay interprets concatenation as composition of partial cache maps. -/
theorem replayWith_append (step : Node J W Origin → List α → Option α) (cache : Array α)
    (first later : List (Node J W Origin)) :
    replayWith step cache (first ++ later) =
      (replayWith step cache first).bind fun middle => replayWith step middle later := by
  induction first generalizing cache with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.cons_append, replayWith]
      cases found : lookupPremises cache node.parents with
      | none => rfl
      | some premises =>
          simp only []
          cases computed : step node premises with
          | none => rfl
          | some value => exact ih _

/-- **Relocation.** A block replayed from one cache replays, with references
relocated, from any cache that agrees at every relocated position, provided
the step ignores physical positions. Agreement extends to the results. -/
theorem replayWith_relocate (step : Node J W Origin → List α → Option α)
    (stable : ∀ (node : Node J W Origin) (address : Nat → Nat),
      step (node.relocate address) = step node)
    {source target sourceResult : Array α} {address : Nat → Nat}
    (agreement : LookupAgreement source target address)
    (future : ∀ offset, address (source.size + offset) = target.size + offset)
    {nodes : List (Node J W Origin)}
    (accepted : replayWith step source nodes = some sourceResult) :
    ∃ targetResult, replayWith step target (nodes.map (Node.relocate address)) = some targetResult ∧
      LookupAgreement sourceResult targetResult address := by
  induction nodes generalizing source target with
  | nil => cases Option.some.inj accepted; exact ⟨target, rfl, agreement⟩
  | cons node rest ih =>
      simp only [replayWith] at accepted
      cases found : lookupPremises source node.parents with
      | none => rw [found] at accepted; cases accepted
      | some premises =>
          simp only [found] at accepted
          cases computed : step node premises with
          | none => simp only [computed] at accepted; cases accepted
          | some value =>
              simp only [computed] at accepted
              obtain ⟨targetResult, replayed, finalAgreement⟩ :=
                ih (agreement.push future value) (futureAddresses_push future value) accepted
              refine ⟨targetResult, ?_, finalAgreement⟩
              simp only [List.map_cons, replayWith]
              have relocatedFound : lookupPremises target (node.relocate address).parents =
                  some premises := by
                simp only [Node.relocate]
                rw [lookupPremises_relocate agreement]
                exact found
              simp only [relocatedFound, stable, computed]
              exact replayed

/-! ## Local characterization of sequential replay -/

/-- Lookups agree on two caches that agree at every cited position. -/
theorem lookupPremises_congr {α : Type x} {first second : Array α} :
    ∀ {indices : List Nat}, (∀ j ∈ indices, first[j]? = second[j]?) →
      lookupPremises first indices = lookupPremises second indices
  | [], _ => rfl
  | j :: rest, agree => by
      simp only [lookupPremises]
      rw [agree j (List.mem_cons_self), lookupPremises_congr fun k member =>
        agree k (List.mem_cons_of_mem _ member)]

/-- Local acceptance of one node at one position of a final cache. -/
def LocalAt (step : Node J W Origin → List α → Option α) (cache : Array α)
    (position : Nat) (node : Node J W Origin) : Prop :=
  (∀ j ∈ node.parents, j < position) ∧
    ∃ premises, lookupPremises cache node.parents = some premises ∧
      step node premises = cache[position]?

/-- **Sequential replay is local.** Replay from a prefix accepts exactly when the
final cache extends the prefix, has one value per node, and every node is
locally accepted at its own position with backward references. -/
theorem replayWith_iff_local (step : Node J W Origin → List α → Option α) :
    ∀ (prefix_ : Array α) (nodes : List (Node J W Origin)) (cache : Array α),
      replayWith step prefix_ nodes = some cache ↔
        cache.size = prefix_.size + nodes.length ∧
          (∀ i < prefix_.size, cache[i]? = prefix_[i]?) ∧
          ∀ k (hk : k < nodes.length), LocalAt step cache (prefix_.size + k) nodes[k]
  | prefix_, [], cache => by
      constructor
      · intro accepted
        cases Option.some.inj accepted
        exact ⟨by simp, fun _ _ => rfl, fun k hk => absurd hk (by simp)⟩
      · rintro ⟨size, agree, -⟩
        have equal : prefix_ = cache := by
          apply Array.ext
          · simpa using size.symm
          · intro i hi hi'
            have := agree i hi
            rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi'] at this
            exact (Option.some.inj this).symm
        subst equal
        rfl
  | prefix_, node :: rest, cache => by
      constructor
      · intro accepted
        simp only [replayWith] at accepted
        cases found : lookupPremises prefix_ node.parents with
        | none => simp [found] at accepted
        | some premises =>
            cases computed : step node premises with
            | none => simp [found, computed] at accepted
            | some value =>
                simp only [found, computed] at accepted
                obtain ⟨size, agree, later⟩ :=
                  (replayWith_iff_local step (prefix_.push value) rest cache).mp accepted
                have below : ∀ j ∈ node.parents, j < prefix_.size :=
                  lookupPremises_indices_lt found
                have agreePrefix : ∀ i < prefix_.size, cache[i]? = prefix_[i]? := by
                  intro i hi
                  rw [agree i (by simp; omega), Array.getElem?_push, if_neg (by omega)]
                refine ⟨by simp at size ⊢; omega, agreePrefix, ?_⟩
                intro k hk
                cases k with
                | zero =>
                    refine ⟨fun j member => by simpa using below j member, premises, ?_, ?_⟩
                    · rw [← found]
                      exact lookupPremises_congr fun j member => agreePrefix j (below j member)
                    · simp only [List.getElem_cons_zero, Nat.add_zero]
                      rw [computed, agree prefix_.size (by simp), Array.getElem?_push_size]
                | succ k =>
                    obtain ⟨backward, premises', found', computed'⟩ :=
                      later k (by simpa using hk)
                    refine ⟨fun j member => ?_, premises', found', ?_⟩
                    · have := backward j member
                      simp at this
                      omega
                    · simp only [List.getElem_cons_succ]
                      rw [computed']
                      congr 1
                      simp
                      omega
      · rintro ⟨size, agree, local_⟩
        obtain ⟨backward, premises, found, computed⟩ := local_ 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at backward found computed
        have foundPrefix : lookupPremises prefix_ node.parents = some premises := by
          rw [← found]
          exact (lookupPremises_congr fun j member => agree j (backward j member)).symm
        have sizeLt : prefix_.size < cache.size := by simp at size; omega
        have valueEq : cache[prefix_.size]? = some cache[prefix_.size] :=
          Array.getElem?_eq_getElem sizeLt
        simp only [replayWith, foundPrefix]
        rw [computed, valueEq]
        apply (replayWith_iff_local step (prefix_.push cache[prefix_.size]) rest cache).mpr
        refine ⟨by simp at size ⊢; omega, ?_, ?_⟩
        · intro i hi
          by_cases last : i = prefix_.size
          · subst last
            rw [valueEq, Array.getElem?_push_size]
          · rw [Array.getElem?_push, if_neg last]
            exact agree i (by simp at hi; omega)
        · intro k hk
          obtain ⟨backward', premises', found', computed'⟩ := local_ (k + 1) (by simp; omega)
          refine ⟨fun j member => ?_, premises', found', ?_⟩
          · have := backward' j member
            simp
            omega
          · simp only [List.getElem_cons_succ] at computed'
            rw [computed']
            congr 1
            simp
            omega

/-! ## Reordering -/

/-- Physical position map of a permutation of node positions. -/
def positionMap {n : Nat} (π : Equiv.Perm (Fin n)) (j : Nat) : Nat :=
  if h : j < n then (π ⟨j, h⟩ : Nat) else j

/-- Reorder a graph: the node at old position `i` moves to `π i`, and every
premise reference is relocated with it. -/
def permute (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length)) :
    List (Node J W Origin) :=
  List.ofFn fun k => (nodes.get (π.symm k)).relocate (positionMap π)

@[simp] theorem permute_length (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length)) :
    (permute nodes π).length = nodes.length := by
  simp [permute]

theorem permute_getElem (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length))
    (k : Nat) (hk : k < (permute nodes π).length) :
    (permute nodes π)[k] =
      (nodes.get (π.symm ⟨k, by simpa using hk⟩)).relocate (positionMap π) := by
  simp [permute]

/-- A reordering respects the graph when every premise stays before its consumer. -/
def Respects (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length)) : Prop :=
  ∀ (i : Fin nodes.length) (j : Nat) (hj : j < nodes.length),
    j ∈ (nodes.get i).parents → π ⟨j, hj⟩ < π i

/-- The values of a cache, moved to their new positions. -/
def permuteCache {n : Nat} (π : Equiv.Perm (Fin n)) (cache : Array α) (sized : cache.size = n) :
    Array α :=
  Array.ofFn fun k : Fin n => cache[(π.symm k : Nat)]'(by rw [sized]; exact (π.symm k).isLt)

theorem permuteCache_getElem? {n : Nat} (π : Equiv.Perm (Fin n)) (cache : Array α)
    (sized : cache.size = n) (i : Fin n) :
    (permuteCache π cache sized)[(π i : Nat)]? = cache[(i : Nat)]? := by
  have inside : (i : Nat) < cache.size := by rw [sized]; exact i.isLt
  simp [permuteCache, Array.getElem?_eq_getElem inside]

theorem permuteCache_size {n : Nat} (π : Equiv.Perm (Fin n)) (cache : Array α)
    (sized : cache.size = n) : (permuteCache π cache sized).size = n := by
  simp [permuteCache]

/-- Reordered lookups read the same values as the original lookups. -/
theorem lookup_relocated {n : Nat} (π : Equiv.Perm (Fin n)) (cache : Array α)
    (sized : cache.size = n) (parents : List Nat) (inside : ∀ j ∈ parents, j < n) :
    lookupPremises (permuteCache π cache sized) (parents.map (positionMap π)) =
      lookupPremises cache parents := by
  induction parents with
  | nil => rfl
  | cons j rest ih =>
      have hj : j < n := inside j List.mem_cons_self
      have mapped : positionMap π j = (π ⟨j, hj⟩ : Nat) := by simp [positionMap, hj]
      simp only [List.map_cons, lookupPremises, mapped]
      rw [permuteCache_getElem? π cache sized ⟨j, hj⟩,
        ih fun k member => inside k (List.mem_cons_of_mem _ member)]

/-- **Schedule independence.** If the local step ignores physical reference
positions, a reordering that respects the graph accepts exactly when the
original does, and every node keeps its value at its new position. -/
theorem replayWith_permute (step : Node J W Origin → List α → Option α)
    (stable : ∀ (node : Node J W Origin) (address : Nat → Nat),
      step (node.relocate address) = step node)
    (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length))
    (respects : Respects nodes π) {cache : Array α}
    (accepted : replayWith step #[] nodes = some cache) :
    ∃ cache', replayWith step #[] (permute nodes π) = some cache' ∧
      ∀ i : Fin nodes.length, cache'[(π i : Nat)]? = cache[(i : Nat)]? := by
  obtain ⟨size, -, local_⟩ := (replayWith_iff_local step #[] nodes cache).mp accepted
  have sized : cache.size = nodes.length := by simpa using size
  refine ⟨permuteCache π cache sized, ?_, permuteCache_getElem? π cache sized⟩
  apply (replayWith_iff_local step #[] (permute nodes π) _).mpr
  refine ⟨by simp [permuteCache_size], fun i hi => absurd hi (by simp), ?_⟩
  intro k hk
  have hk' : k < nodes.length := by simpa using hk
  set i := π.symm ⟨k, hk'⟩ with hi
  have back : π i = ⟨k, hk'⟩ := by simp [hi]
  obtain ⟨backward, premises, found, computed⟩ := local_ i i.isLt
  simp only [Array.size_empty, Nat.zero_add] at backward found computed ⊢
  have nodeEq : (permute nodes π)[k] = (nodes.get i).relocate (positionMap π) :=
    permute_getElem nodes π k hk
  rw [nodeEq]
  have insideParents : ∀ j ∈ (nodes.get i).parents, j < nodes.length := fun j member =>
    lt_trans (backward j (by simpa using member)) i.isLt
  refine ⟨?_, premises, ?_, ?_⟩
  · intro j member
    simp only [Node.relocate, List.mem_map] at member
    obtain ⟨j₀, member₀, rfl⟩ := member
    have hj₀ : j₀ < nodes.length := insideParents j₀ member₀
    have ordered := respects i j₀ hj₀ member₀
    rw [back] at ordered
    have := Fin.lt_def.mp ordered
    simpa [positionMap, hj₀] using this
  · simp only [Node.relocate]
    rw [lookup_relocated π cache sized _ insideParents]
    simpa using found
  · rw [stable]
    have position : cache[(i : Nat)]? = (permuteCache π cache sized)[k]? := by
      rw [← permuteCache_getElem? π cache sized i, back]
    simpa [position] using computed

/-- Lookups along a reference map agree when the two caches agree at every
cited position. -/
theorem lookupPremises_map_congr {first second : Array α} (address : Nat → Nat) :
    ∀ {parents : List Nat}, (∀ j ∈ parents, second[address j]? = first[j]?) →
      lookupPremises second (parents.map address) = lookupPremises first parents
  | [], _ => rfl
  | j :: rest, agree => by
      simp only [List.map_cons, lookupPremises]
      rw [agree j List.mem_cons_self, lookupPremises_map_congr address fun k member =>
        agree k (List.mem_cons_of_mem _ member)]

/-- Every premise reference points to an earlier node. -/
def Backward (nodes : List (Node J W Origin)) : Prop :=
  ∀ (i : Fin nodes.length), ∀ j ∈ (nodes.get i).parents, j < i

/-- **Reflection.** If both orders keep premises before consumers, acceptance of
the reordered graph gives acceptance of the original, with the same values. -/
theorem replayWith_permute_reflect (step : Node J W Origin → List α → Option α)
    (stable : ∀ (node : Node J W Origin) (address : Nat → Nat),
      step (node.relocate address) = step node)
    (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length))
    (backward : Backward nodes) {cache' : Array α}
    (accepted : replayWith step #[] (permute nodes π) = some cache') :
    ∃ cache, replayWith step #[] nodes = some cache ∧
      ∀ i : Fin nodes.length, cache'[(π i : Nat)]? = cache[(i : Nat)]? := by
  obtain ⟨size, -, local_⟩ := (replayWith_iff_local step #[] (permute nodes π) cache').mp accepted
  have sized : cache'.size = nodes.length := by simpa using size
  let cache := permuteCache π.symm cache' sized
  have values : ∀ i : Fin nodes.length, cache[(i : Nat)]? = cache'[(π i : Nat)]? := by
    intro i
    have := permuteCache_getElem? π.symm cache' sized (π i)
    simpa using this
  refine ⟨cache, ?_, fun i => (values i).symm⟩
  apply (replayWith_iff_local step #[] nodes cache).mpr
  refine ⟨by simp [cache, permuteCache_size], fun i hi => absurd hi (by simp), ?_⟩
  intro k hk
  let i : Fin nodes.length := ⟨k, hk⟩
  have hk' : (π i : Nat) < (permute nodes π).length := by simp
  obtain ⟨-, premises, found, computed⟩ := local_ (π i) hk'
  have nodeEq := permute_getElem nodes π (π i) hk'
  have parentEq : π.symm ⟨(π i : Nat), by simp⟩ = i := by simp
  rw [nodeEq, parentEq] at found computed
  have insideParents : ∀ j ∈ (nodes.get i).parents, j < nodes.length := fun j member =>
    lt_trans (backward i j member) i.isLt
  refine ⟨fun j member => by simpa using backward i j member, premises, ?_, ?_⟩
  · rw [← found]
    simp only [Node.relocate]
    symm
    apply lookupPremises_map_congr
    intro j member
    have hj : j < nodes.length := insideParents j member
    rw [show positionMap π j = (π ⟨j, hj⟩ : Nat) by simp [positionMap, hj]]
    exact (values ⟨j, hj⟩).symm
  · rw [stable] at computed
    have getEq : nodes[k] = nodes.get i := rfl
    have valueEq : cache[k]? = cache'[(π i : Nat)]? := values i
    simp only [Array.size_empty, Nat.zero_add] at computed ⊢
    rw [getEq, computed, valueEq]

/-- **Schedule independence, both directions.** For two topological orders of
one graph, acceptance coincides and each node keeps its value. -/
theorem replayWith_permute_iff (step : Node J W Origin → List α → Option α)
    (stable : ∀ (node : Node J W Origin) (address : Nat → Nat),
      step (node.relocate address) = step node)
    (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length))
    (backward : Backward nodes) (respects : Respects nodes π) :
    (∃ cache, replayWith step #[] nodes = some cache) ↔
      ∃ cache', replayWith step #[] (permute nodes π) = some cache' := by
  constructor
  · rintro ⟨cache, accepted⟩
    obtain ⟨cache', replayed, -⟩ := replayWith_permute step stable nodes π respects accepted
    exact ⟨cache', replayed⟩
  · rintro ⟨cache', accepted⟩
    obtain ⟨cache, replayed, -⟩ := replayWith_permute_reflect step stable nodes π backward accepted
    exact ⟨cache, replayed⟩

/-- Positions compose: undoing a reordering restores every reference. -/
theorem positionMap_symm {n : Nat} (π : Equiv.Perm (Fin n)) (j : Nat) (hj : j < n) :
    positionMap π.symm (positionMap π j) = j := by
  have inside : (π ⟨j, hj⟩ : Nat) < n := (π ⟨j, hj⟩).isLt
  simp [positionMap, hj, inside]

/-- A reordering that places some premise after its consumer is refused,
even though the original graph is accepted. -/
theorem replayWith_permute_refused (step : Node J W Origin → List α → Option α)
    (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length))
    (i : Fin nodes.length) (j : Nat) (hj : j < nodes.length) (member : j ∈ (nodes.get i).parents)
    (late : π i ≤ π ⟨j, hj⟩) :
    replayWith step #[] (permute nodes π) = none := by
  cases replayed : replayWith step #[] (permute nodes π) with
  | none => rfl
  | some cache' =>
      obtain ⟨-, -, local_⟩ := (replayWith_iff_local step #[] (permute nodes π) cache').mp replayed
      have hk : (π i : Nat) < (permute nodes π).length := by simp
      obtain ⟨backward, -⟩ := local_ (π i) hk
      have nodeEq := permute_getElem nodes π (π i) hk
      have parentEq : π.symm ⟨(π i : Nat), by simp⟩ = i := by simp
      rw [nodeEq, parentEq] at backward
      have cited : positionMap π j ∈ ((nodes.get i).relocate (positionMap π)).parents := by
        simp only [Node.relocate]
        exact List.mem_map_of_mem member
      have := backward _ cited
      simp only [positionMap, hj, dif_pos, Array.size_empty, Nat.zero_add] at this
      have := Fin.lt_def.mpr this
      exact absurd late (not_le.mpr this)

/-- The number of local steps is schedule invariant. -/
theorem permute_steps (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length)) :
    (permute nodes π).length = nodes.length := permute_length nodes π

/-- The number of premise lookups is schedule invariant. -/
theorem permute_lookups (nodes : List (Node J W Origin)) (π : Equiv.Perm (Fin nodes.length)) :
    ((permute nodes π).map fun node => node.parents.length).sum =
      (nodes.map fun node => node.parents.length).sum := by
  have reorder : (List.ofFn fun k => (nodes.get (π.symm k)).parents.length).Perm
      (List.ofFn fun k => (nodes.get k).parents.length) :=
    Equiv.Perm.ofFn_comp_perm π.symm (fun k => (nodes.get k).parents.length)
  have left : (permute nodes π).map (fun node => node.parents.length) =
      List.ofFn fun k => (nodes.get (π.symm k)).parents.length := by
    simp [permute, Node.relocate, List.map_ofFn, Function.comp_def]
  have right : List.ofFn (fun k => (nodes.get k).parents.length) =
      nodes.map (fun node => node.parents.length) := by
    conv_rhs => rw [← List.ofFn_get nodes]
    rw [List.map_ofFn]
    rfl
  rw [left, ← right]
  exact reorder.sum_eq

/-- Judgment replay is schedule independent. -/
theorem replay_permute {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (nodes : List (Node J interface.W Origin)) (π : Equiv.Perm (Fin nodes.length))
    (respects : Respects nodes π) {cache : Array J}
    (accepted : replay interface nodes = some cache) :
    ∃ cache', replay interface (permute nodes π) = some cache' ∧
      ∀ i : Fin nodes.length, cache'[(π i : Nat)]? = cache[(i : Nat)]? := by
  unfold replay at accepted ⊢
  rw [← replayWith_judgmentStep] at accepted ⊢
  exact replayWith_permute (judgmentStep interface) (fun _ _ => rfl) nodes π respects accepted

end Mettapedia.Logic.DerivationGraph
