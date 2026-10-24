import Mettapedia.Machines.ConstructorSummary
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mathlib.Data.List.Rotate

/-!
# Demand-computed summaries of immutable constructor DAGs

Nodes have finite lists of lower-ranked children. The rank is a termination
witness, not a fixed bound on language terms or an allocation discipline.
The executable evaluator consults a cache, recursively demands children on a
miss, and installs the newly combined summary. The algebra may depend on a
node's allocation label; in particular it need not be an unlocated bit fold.

Cached metadata and physical edges are separate. An absent summary is not
evidence of absent variables, references, effects, or collector roots.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DemandSummary

universe u v w

structure Graph (Label : Type u) where
  label : Nat → Label
  children : (i : Nat) → List (Fin i)

abbrev Cache (Summary : Type v) := Nat → Option Summary

structure Result (Value : Type w) (Summary : Type v) where
  value : Value
  cache : Cache Summary
  computed : List Nat

variable {Label : Type u} {Summary : Type v} {Value : Type w}

def eager (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) : Summary :=
  combine (g.label i) ((g.children i).map fun child => eager g combine child.val)
termination_by i

def sequence {A : Type w} (xs : List A)
    (step : A → Cache Summary → Result Summary Summary)
    (cache : Cache Summary) : Result (List Summary) Summary :=
  match xs with
  | [] => ⟨[], cache, []⟩
  | x :: xs =>
      let first := step x cache
      let rest := sequence xs step first.cache
      ⟨first.value :: rest.value, rest.cache, first.computed ++ rest.computed⟩

def demand (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) : Result Summary Summary :=
  match cache i with
  | some value => ⟨value, cache, []⟩
  | none =>
      let children := sequence (g.children i)
        (fun child c => demand g combine child.val c) cache
      let value := combine (g.label i) children.value
      ⟨value, Function.update children.cache i (some value), children.computed ++ [i]⟩
termination_by i

def Sound (g : Graph Label) (combine : Label → List Summary → Summary)
    (cache : Cache Summary) : Prop :=
  ∀ i value, cache i = some value → value = eager g combine i

def Extends (before after : Cache Summary) : Prop :=
  ∀ i value, before i = some value → after i = some value

theorem Extends.refl (cache : Cache Summary) : Extends cache cache := by
  intro i value h
  exact h

theorem Extends.trans {a b c : Cache Summary}
    (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  intro i value h
  exact bc i value (ab i value h)

theorem Extends.none_of_none {a b : Cache Summary} (ab : Extends a b)
    {i : Nat} (absent : b i = none) : a i = none := by
  cases h : a i with
  | none => rfl
  | some value => simpa [absent] using ab i value h

theorem Extends.some_of_some {a b : Cache Summary} (ab : Extends a b)
    {i : Nat} (present : (a i).isSome = true) : (b i).isSome = true := by
  cases h : a i with
  | none => simp [h] at present
  | some value => simp [ab i value h]

/-- Construction accounting. Request/edge accounting is supplied separately by
`demandRequests_eq` and `demandRequests_le_uncached_edges`. -/
structure Valid (g : Graph Label) (combine : Label → List Summary → Summary)
    (before : Cache Summary) (result : Result Value Summary)
    (expected : Value) (bound : Nat) : Prop where
  value_eq : result.value = expected
  sound : Sound g combine result.cache
  preserves : Extends before result.cache
  fresh : ∀ i ∈ result.computed, before i = none
  stored : ∀ i ∈ result.computed, (result.cache i).isSome = true
  nodup : result.computed.Nodup
  bounded : ∀ i ∈ result.computed, i < bound

theorem sequence_valid {A : Type w} (g : Graph Label)
    (combine : Label → List Summary → Summary) (expected : A → Summary)
    (step : A → Cache Summary → Result Summary Summary) (bound : Nat)
    (xs : List A)
    (each : ∀ x ∈ xs, ∀ cache, Sound g combine cache →
      Valid g combine cache (step x cache) (expected x) bound)
    (cache : Cache Summary) (sound : Sound g combine cache) :
    Valid g combine cache (sequence xs step cache) (xs.map expected) bound := by
  induction xs generalizing cache with
  | nil =>
      exact ⟨rfl, sound, Extends.refl _, by simp [sequence],
        by simp [sequence], by simp [sequence], by simp [sequence]⟩
  | cons x xs ih =>
      have first := each x (by simp) cache sound
      have rest := ih (fun y hy => each y (by simp [hy])) _ first.sound
      refine ⟨?_, rest.sound, first.preserves.trans rest.preserves, ?_, ?_, ?_, ?_⟩
      · simp only [sequence, List.map_cons]
        rw [first.value_eq, rest.value_eq]
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact first.fresh i hi
        · exact first.preserves.none_of_none (rest.fresh i hi)
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact rest.preserves.some_of_some (first.stored i hi)
        · exact rest.stored i hi
      · apply List.nodup_append.mpr
        refine ⟨first.nodup, rest.nodup, ?_⟩
        intro i hi j hj same
        subst j
        have present := first.stored i hi
        simp [rest.fresh i hj] at present
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact first.bounded i hi
        · exact rest.bounded i hi

theorem demand_valid (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) (sound : Sound g combine cache) :
    Valid g combine cache (demand g combine i cache) (eager g combine i) (i + 1) := by
  induction i using Nat.strong_induction_on generalizing cache with
  | h i ih =>
      rw [demand]
      cases present : cache i with
      | some value =>
          simp only
          exact ⟨sound i value present, sound, Extends.refl _,
            by simp, by simp, by simp, by simp⟩
      | none =>
          simp only
          have children := sequence_valid g combine
            (fun child : Fin i => eager g combine child.val)
            (fun child : Fin i => fun c => demand g combine child.val c) i
            (g.children i) (by
              intro child _ c hs
              have h := ih child.val child.isLt c hs
              refine { h with bounded := ?_ }
              intro j hj
              have hj' := h.bounded j hj
              omega) cache sound
          have value_eq : combine (g.label i) (sequence (g.children i)
              (fun child c => demand g combine child.val c) cache).value =
              eager g combine i := by
            rw [children.value_eq, eager]
          refine ⟨value_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro j value hj
            by_cases hji : j = i
            · subst j
              simp only [Function.update_self, Option.some.injEq] at hj
              exact hj.symm.trans value_eq
            · have h := children.sound j value
              apply h
              simpa [Function.update, hji] using hj
          · intro j value hj
            have hji : j ≠ i := by intro h; subst j; simp [present] at hj
            simpa [Function.update, hji] using children.preserves j value hj
          · intro j hj
            rcases List.mem_append.mp hj with hj | hj
            · exact children.fresh j hj
            · have : j = i := by simpa using hj
              subst j
              exact present
          · intro j hj
            rcases List.mem_append.mp hj with hj | hj
            · have hji : j ≠ i := by have := children.bounded j hj; omega
              simpa [Function.update, hji] using children.stored j hj
            · have : j = i := by simpa using hj
              subst j
              simp
          · apply List.nodup_append.mpr
            refine ⟨children.nodup, by simp, ?_⟩
            intro j hj k hk heq
            have hj' := children.bounded j hj
            simp only [List.mem_singleton] at hk
            omega
          · intro j hj
            rcases List.mem_append.mp hj with hj | hj
            · have := children.bounded j hj
              omega
            · simp only [List.mem_singleton] at hj
              omega

theorem demand_exact (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) (sound : Sound g combine cache) :
    (demand g combine i cache).value = eager g combine i :=
  (demand_valid g combine i cache sound).value_eq

theorem empty_sound (g : Graph Label) (combine : Label → List Summary → Summary) :
    Sound g combine (fun _ => none) := by
  intro i value h
  cases h

theorem demand_stores (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) :
    (demand g combine i cache).cache i = some (demand g combine i cache).value := by
  rw [demand]
  cases present : cache i <;> simp [present]

/-- A second query of the same node neither recombines a summary nor changes
the cache. The theorem is about combinations, not constant-time C lookup. -/
theorem demand_again (g : Graph Label) (combine : Label → List Summary → Summary)
    (i : Nat) (cache : Cache Summary) :
    demand g combine i (demand g combine i cache).cache =
      ⟨(demand g combine i cache).value, (demand g combine i cache).cache, []⟩ := by
  conv_lhs => rw [demand, demand_stores]

def reachable (g : Graph Label) (i : Nat) : Finset Nat :=
  insert i ((g.children i).toFinset.biUnion fun child => reachable g child.val)
termination_by i

theorem sequence_computed_source {A : Type w} (xs : List A)
    (step : A → Cache Summary → Result Summary Summary) (cache : Cache Summary)
    (i : Nat) (hi : i ∈ (sequence xs step cache).computed) :
    ∃ x ∈ xs, ∃ intermediate, i ∈ (step x intermediate).computed := by
  induction xs generalizing cache with
  | nil => simp [sequence] at hi
  | cons x xs ih =>
      rcases List.mem_append.mp hi with hfirst | hrest
      · exact ⟨x, by simp, cache, hfirst⟩
      · obtain ⟨y, hy, c, hc⟩ := ih (step x cache).cache hrest
        exact ⟨y, by simp [hy], c, hc⟩

theorem demand_computed_reachable (g : Graph Label)
    (combine : Label → List Summary → Summary) (i : Nat) (cache : Cache Summary)
    (j : Nat) (computed : j ∈ (demand g combine i cache).computed) :
    j ∈ reachable g i := by
  induction i using Nat.strong_induction_on generalizing cache with
  | h i ih =>
      rw [demand] at computed
      cases present : cache i with
      | some value => simp [present] at computed
      | none =>
          simp only [present] at computed
          rcases List.mem_append.mp computed with hc | hc
          · obtain ⟨child, hchild, c, hcomputed⟩ :=
              sequence_computed_source _ _ _ j hc
            rw [reachable]
            apply Finset.mem_insert_of_mem
            apply Finset.mem_biUnion.mpr
            exact ⟨child, by simpa using hchild, ih child.val child.isLt c hcomputed⟩
          · have : j = i := by simpa using hc
            subst j
            rw [reachable]
            exact Finset.mem_insert_self _ _

/-- The number of combinations is bounded by distinct reachable nodes whose
summaries were absent initially. Sharing is counted once. An already cached
ancestor can make the inequality strict by avoiding all of its descendants. -/
theorem demand_combinations_le_uncached_reachable (g : Graph Label)
    (combine : Label → List Summary → Summary) (i : Nat) (cache : Cache Summary)
    (sound : Sound g combine cache) :
    (demand g combine i cache).computed.length ≤
      ((reachable g i).filter fun j => (cache j).isNone).card := by
  have valid := demand_valid g combine i cache sound
  rw [← List.toFinset_card_of_nodup valid.nodup]
  apply Finset.card_le_card
  intro j hj
  have member : j ∈ (demand g combine i cache).computed := by simpa using hj
  exact Finset.mem_filter.mpr
    ⟨demand_computed_reachable g combine i cache j member,
      by simp [valid.fresh j member]⟩

/-- Number of cache requests made by a sequence, threading the actual
post-request cache from the existing evaluator. -/
def sequenceRequests {A : Type w} (xs : List A)
    (step : A → Cache Summary → Result Summary Summary)
    (requests : A → Cache Summary → Nat) (cache : Cache Summary) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => requests x cache +
      sequenceRequests rest step requests (step x cache).cache

/-- One lookup on entry; a miss requests each physical outgoing edge in
order. Cache hits issue no descendant requests. -/
def demandRequests (graph : Graph Label) (combine : Label → List Summary → Summary)
    (root : Nat) (cache : Cache Summary) : Nat :=
  match cache root with
  | some _ => 1
  | none => 1 + sequenceRequests (graph.children root)
      (fun child current => demand graph combine child.val current)
      (fun child current => demandRequests graph combine child.val current) cache
termination_by root

/-- Ordered duplicate edges count separately even when their target is shared. -/
def edgeCount (graph : Graph Label) (nodes : List Nat) : Nat :=
  (nodes.map fun node => (graph.children node).length).sum

@[simp] theorem edgeCount_append (graph : Graph Label) (first second : List Nat) :
    edgeCount graph (first ++ second) = edgeCount graph first + edgeCount graph second := by
  simp [edgeCount, List.map_append, List.sum_append]

theorem sequenceRequests_eq {A : Type w} (graph : Graph Label)
    (xs : List A) (step : A → Cache Summary → Result Summary Summary)
    (requests : A → Cache Summary → Nat)
    (each : ∀ item ∈ xs, ∀ cache, requests item cache =
      1 + edgeCount graph (step item cache).computed) (cache : Cache Summary) :
    sequenceRequests xs step requests cache =
      xs.length + edgeCount graph (sequence xs step cache).computed := by
  induction xs generalizing cache with
  | nil => simp [sequenceRequests, sequence, edgeCount]
  | cons first rest ih =>
      simp only [sequenceRequests, sequence, List.length_cons, edgeCount_append]
      rw [each first (by simp), ih (fun item member => each item (by simp [member]))]
      omega

/-- The operational request count equals one root lookup plus exactly one
lookup for each outgoing edge of a newly computed node. -/
theorem demandRequests_eq (graph : Graph Label)
    (combine : Label → List Summary → Summary) (root : Nat) (cache : Cache Summary) :
    demandRequests graph combine root cache =
      1 + edgeCount graph (demand graph combine root cache).computed := by
  induction root using Nat.strong_induction_on generalizing cache with
  | h root ih =>
      rw [demandRequests, demand]
      cases present : cache root with
      | some value => simp [edgeCount]
      | none =>
          simp only
          rw [sequenceRequests_eq graph _ _ _ (fun child _ current =>
            ih child.val child.isLt current), edgeCount_append]
          simp [edgeCount, Nat.add_comm]

/-- Distinct computed nodes contribute all their physical child slots once.
Cache-table operations themselves are not charged as constant-time here. -/
theorem demandRequests_le_uncached_edges (graph : Graph Label)
    (combine : Label → List Summary → Summary) (root : Nat) (cache : Cache Summary)
    (sound : Sound graph combine cache) :
    demandRequests graph combine root cache ≤
      1 + ∑ node ∈ (reachable graph root).filter (fun node => (cache node).isNone),
        (graph.children node).length := by
  rw [demandRequests_eq]
  apply Nat.add_le_add_left
  unfold edgeCount
  have valid := demand_valid graph combine root cache sound
  rw [← List.sum_toFinset _ valid.nodup]
  apply Finset.sum_le_sum_of_subset
  intro node member
  have computed : node ∈ (demand graph combine root cache).computed := by
    simpa using member
  exact Finset.mem_filter.mpr
    ⟨demand_computed_reachable graph combine root cache node computed,
      by simp [valid.fresh node computed]⟩

/-- Ordered roots share one fixed interpretation and cache. -/
theorem sequence_demand_valid (graph : Graph Label)
    (combine : Label → List Summary → Summary) (roots : List Nat) (cache : Cache Summary)
    (sound : Sound graph combine cache) :
    Valid graph combine cache (sequence roots (demand graph combine) cache)
      (roots.map (eager graph combine)) (roots.sum + 1) := by
  apply sequence_valid
  · intro root member current valid
    have one := demand_valid graph combine root current valid
    refine { one with bounded := ?_ }
    intro node computed
    exact (one.bounded node computed).trans_le
      (Nat.add_le_add_right (List.le_sum_of_mem member) 1)
  · exact sound

/-- Multiple roots pay for their output occurrences and the edges of distinct
reachable nodes. Payload construction and memo-table cost remain separate. -/
theorem sequenceRequests_le_reachable_edges (graph : Graph Label)
    (combine : Label → List Summary → Summary) (roots : List Nat) (cache : Cache Summary)
    (sound : Sound graph combine cache) :
    sequenceRequests roots (demand graph combine) (demandRequests graph combine) cache ≤
      roots.length + ∑ node ∈ roots.toFinset.biUnion (reachable graph),
        (graph.children node).length := by
  rw [sequenceRequests_eq graph _ _ _
    (fun root _ current => demandRequests_eq graph combine root current)]
  apply Nat.add_le_add_left
  unfold edgeCount
  rw [← List.sum_toFinset _ (sequence_demand_valid graph combine roots cache sound).nodup]
  apply Finset.sum_le_sum_of_subset
  intro node member
  have computed : node ∈ (sequence roots (demand graph combine) cache).computed := by
    simpa using member
  obtain ⟨root, root_mem, current, reached⟩ :=
    sequence_computed_source _ _ _ node computed
  exact Finset.mem_biUnion.mpr ⟨root, by simpa using root_mem,
    demand_computed_reachable graph combine root current node reached⟩

/-- Dependency testing uses actual edges even when all caches are empty. -/
def affected (g : Graph Label) (changed : Nat → Bool) (i : Nat) : Bool :=
  changed i || (g.children i).any fun child => affected g changed child.val
termination_by i

def invalidate (g : Graph Label) (changed : Nat → Bool) (cache : Cache Summary) :
    Cache Summary :=
  fun i => if affected g changed i then none else cache i

/-- A revision marks every changed local label and child list. Labels include
all algebra inputs, such as allocation arena, older generation, head adjustment,
or a mutable leaf's revision-dependent summary. -/
structure Revision (before after : Graph Label) (changed : Nat → Bool) : Prop where
  labels : ∀ i, changed i = false → before.label i = after.label i
  edges : ∀ i, changed i = false → before.children i = after.children i

theorem unaffected_eager (before after : Graph Label)
    (combine : Label → List Summary → Summary) (changed : Nat → Bool)
    (revision : Revision before after changed) (i : Nat)
    (unaffected : affected before changed i = false) :
    eager before combine i = eager after combine i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      rw [affected] at unaffected
      have unchanged : changed i = false := (Bool.or_eq_false_iff.mp unaffected).1
      have children : ∀ child ∈ before.children i,
          affected before changed child.val = false := by
        have := (Bool.or_eq_false_iff.mp unaffected).2
        simpa using this
      rw [eager, eager, ← revision.labels i unchanged, ← revision.edges i unchanged]
      congr 1
      apply List.map_congr_left
      intro child hchild
      exact ih child.val child.isLt (children child hchild)

/-- Invalidation derived from the old dependency graph makes every retained
cache entry sound in the new graph. Edges added by the revision are safe:
their changed parent is itself invalidated, as are its old dependents. -/
theorem invalidate_sound (before after : Graph Label)
    (combine : Label → List Summary → Summary) (changed : Nat → Bool)
    (revision : Revision before after changed) (cache : Cache Summary)
    (sound : Sound before combine cache) :
    Sound after combine (invalidate before changed cache) := by
  intro i value present
  unfold invalidate at present
  split at present
  · cases present
  · rename_i unaffected
    have unaffected' : affected before changed i = false := by simpa using unaffected
    exact (sound i value present).trans
      (unaffected_eager before after combine changed revision i unaffected')

theorem unaffected_cache_retained (g : Graph Label) (changed : Nat → Bool)
    (cache : Cache Summary) (i : Nat) (unaffected : affected g changed i = false) :
    invalidate g changed cache i = cache i := by simp [invalidate, unaffected]

theorem changed_cache_removed (g : Graph Label) (changed : Nat → Bool)
    (cache : Cache Summary) (i : Nat) (changedHere : changed i = true) :
    invalidate g changed cache i = none := by
  have hit : affected g changed i = true := by
    rw [affected, changedHere]
    rfl
  simp [invalidate, hit]

theorem observed_demand_exact {Observation : Type w} (g : Graph Label)
    (combine : Label → List Summary → Summary) (observe : Summary → Observation)
    (i : Nat) (cache : Cache Summary) (sound : Sound g combine cache) :
    observe (demand g combine i cache).value = observe (eager g combine i) := by
  rw [demand_exact g combine i cache sound]

/-- A conservative presence test. Unknown is not a negative answer. -/
def mayHave (property : Summary → Bool) : Option Summary → Bool
  | none => true
  | some summary => property summary

/-- A conservative permission test. Unknown does not grant an optimization
such as retaining a graph without copying or sharing across threads. -/
def certified (property : Summary → Bool) : Option Summary → Bool
  | none => false
  | some summary => property summary

theorem mayHave_false_sound (g : Graph Label)
    (combine : Label → List Summary → Summary) (cache : Cache Summary)
    (sound : Sound g combine cache) (property : Summary → Bool) (i : Nat)
    (absent : mayHave property (cache i) = false) :
    property (eager g combine i) = false := by
  cases present : cache i with
  | none => simp [present, mayHave] at absent
  | some value =>
      have value_eq := sound i value present
      simpa [present, mayHave, value_eq] using absent

theorem certified_true_sound (g : Graph Label)
    (combine : Label → List Summary → Summary) (cache : Cache Summary)
    (sound : Sound g combine cache) (property : Summary → Bool) (i : Nat)
    (permission : certified property (cache i) = true) :
    property (eager g combine i) = true := by
  cases present : cache i with
  | none => simp [present, certified] at permission
  | some value =>
      have value_eq := sound i value present
      simpa [present, certified, value_eq] using permission

theorem demand_after_revision_exact (before after : Graph Label)
    (combine : Label → List Summary → Summary) (changed : Nat → Bool)
    (revision : Revision before after changed) (cache : Cache Summary)
    (sound : Sound before combine cache) (i : Nat) :
    (demand after combine i (invalidate before changed cache)).value =
      eager after combine i :=
  demand_exact after combine i _
    (invalidate_sound before after combine changed revision cache sound)

namespace Located

open ConstructorSummary Cursor.TailSummary

variable {Bit : Type u}

/-- Completed resident leaves carry their own located summaries. Constructor
labels contain the parent's arena, older generation, and head adjustments. -/
inductive Descriptor (Bit : Type u)
  | resident (summary : ConstructorSummary.Summary Bit)
  | constructor (label : ConstructorSummary.Label Bit)

def combine : Descriptor Bit → List (ConstructorSummary.Summary Bit) →
    ConstructorSummary.Summary Bit
  | .resident summary, _ => summary
  | .constructor label, children => ConstructorSummary.combine label children

/-- The generic memoization proof applies to the allocation-sensitive algebra
without treating arena closure as a disjunction of unlocated child bits. -/
theorem demand_exact (g : Graph (Descriptor Bit)) (i : Nat)
    (cache : Cache (ConstructorSummary.Summary Bit)) (sound : Sound g combine cache) :
    (demand g combine i cache).value = eager g combine i :=
  DemandSummary.demand_exact g combine i cache sound

/-- A plain child's complete aggregate is neutral only when its allocation
also satisfies the parent-relative closure and generation tests. -/
def NeutralChild (label : ConstructorSummary.Label Bit)
    (child : ConstructorSummary.Summary Bit) : Prop :=
  { child.aggregate with generation := true } = Aggregate.unit ∧
    sameArena label.arena child.home = true ∧
    generationAdmits label child = true

theorem contribution_neutral {label : ConstructorSummary.Label Bit}
    {child : ConstructorSummary.Summary Bit} (neutral : NeutralChild label child) :
    contribution label child = Aggregate.unit := by
  rcases neutral with ⟨aggregate, closed, generation⟩
  have childClosed : child.aggregate.closed = true := congrArg Aggregate.closed aggregate
  calc
    contribution label child = { child.aggregate with generation := true } := by
      ext <;> simp [contribution, childClosed, closed, generation]
    _ = Aggregate.unit := aggregate

/-- If every child is independently certified neutral, construction uses the
precomputed empty aggregate. Syntactic constructor shape alone is insufficient. -/
theorem neutral_children_fast_path (label : ConstructorSummary.Label Bit)
    (children : List (ConstructorSummary.Summary Bit))
    (neutral : ∀ child ∈ children, NeutralChild label child) :
    ConstructorSummary.combine label children = finish label Aggregate.unit := by
  unfold ConstructorSummary.combine
  congr 1
  induction children with
  | nil => rfl
  | cons child children ih =>
      simp only [List.map_cons, Aggregate.fold, List.foldr_cons]
      rw [contribution_neutral (neutral child (by simp)), Aggregate.unit_merge]
      exact ih (fun other hother => neutral other (by simp [hother]))

end Located

namespace Controls

/-- Two parents share the same leaf twice. The result is a DAG, not a tree. -/
def diamond : Graph Nat where
  label := fun _ => 1
  children
    | 0 => []
    | 1 => [⟨0, by omega⟩, ⟨0, by omega⟩]
    | 2 => [⟨0, by omega⟩, ⟨0, by omega⟩]
    | n + 3 => [⟨1, by omega⟩, ⟨2, by omega⟩]

def addSummary (label : Nat) (children : List Nat) : Nat := label + children.sum

theorem shared_leaf_computed_once :
    (demand diamond addSummary 3 (fun _ => none)).computed = [0, 1, 2, 3] ∧
    (demand diamond addSummary 3 (fun _ => none)).value = 7 := by decide +kernel

theorem cached_ancestor_avoids_descendants :
    let cache : Cache Nat := fun i => if i = 3 then some 7 else none
    (demand diamond addSummary 3 cache).computed = [] ∧
    (demand diamond addSummary 3 cache).cache 0 = none := by decide +kernel

def changedLeaf : Graph Nat :=
  { diamond with label := fun i => if i = 0 then 2 else 1 }

theorem stale_cache_changes_answer :
    let cache := (demand diamond addSummary 3 (fun _ => none)).cache
    (demand changedLeaf addSummary 3 cache).value = 7 ∧
    eager changedLeaf addSummary 3 = 11 := by decide +kernel

theorem invalidating_leaf_repairs_dependents :
    let cache := (demand diamond addSummary 3 (fun _ => none)).cache
    let repaired := invalidate diamond (fun i => i == 0) cache
    (demand changedLeaf addSummary 3 repaired).value = 11 ∧
    (demand changedLeaf addSummary 3 repaired).computed = [0, 1, 2, 3] := by decide +kernel

theorem irrelevant_revision_retains_cached_root :
    let cache := (demand diamond addSummary 3 (fun _ => none)).cache
    let retained := invalidate diamond (fun i => i == 20) cache
    (demand diamond addSummary 3 retained).computed = [] := by decide +kernel

open ConstructorSummary Cursor.TailSummary

def locatedPair (parentArena childArena : Nat) : Graph (Located.Descriptor Unit) where
  label i := if i = 0 then
    .resident (ConstructorSummary.Controls.leaf childArena)
    else .constructor (ConstructorSummary.Controls.plain parentArena)
  children
    | 0 => []
    | _ + 1 => [⟨0, by omega⟩]

theorem moving_parent_invalidates_closure :
    let old := locatedPair 1 1
    let moved := locatedPair 2 1
    let cache := (demand old Located.combine 1 (fun _ => none)).cache
    (demand moved Located.combine 1 cache).value.aggregate.closed = true ∧
    (eager moved Located.combine 1).aggregate.closed = false ∧
    (demand moved Located.combine 1
      (invalidate old (fun i => i == 1) cache)).value.aggregate.closed = false := by decide +kernel

theorem moving_child_invalidates_parent :
    let old := locatedPair 1 1
    let moved := locatedPair 1 2
    let cache := (demand old Located.combine 1 (fun _ => none)).cache
    (demand moved Located.combine 1 cache).value.aggregate.closed = true ∧
    (demand moved Located.combine 1
      (invalidate old (fun i => i == 0) cache)).value.aggregate.closed = false := by decide +kernel

/-- A data-shaped constructor may still contain a registry reference or other
inherited escape property. The head being ordinary does not certify the child. -/
theorem plain_constructor_can_contain_escape :
    let escaping : ConstructorSummary.Summary Unit := ⟨.arena 1,
      { Aggregate.unit with inherited := fun _ => true }⟩
    (ConstructorSummary.combine (ConstructorSummary.Controls.plain 1)
      [escaping]).aggregate.inherited () = true := by decide

/-- An ordinary scalar's stored generation bit is false; same-arena closure
still makes its parent-relative contribution neutral. -/
theorem closed_scalar_is_neutral :
    let scalar : ConstructorSummary.Summary Unit := ⟨.arena 1,
      { Aggregate.unit with generation := false }⟩
    Located.NeutralChild (ConstructorSummary.Controls.plain 1) scalar := by
  simp [Located.NeutralChild, ConstructorSummary.Controls.plain, sameArena,
    generationAdmits, Aggregate.unit]

/-- A zeroed pending summary would hide a real variable. An exact absence
query must demand the metadata or conservatively report possible presence. -/
theorem absent_cache_does_not_mean_absent_variable :
    let vSummary : ConstructorSummary.Summary Unit := ⟨.arena 1,
      { Aggregate.unit with vars := .one 7 }⟩
    let node : Graph (Located.Descriptor Unit) :=
      { label := fun _ => .resident vSummary, children := fun _ => [] }
    (none : Option (ConstructorSummary.Summary Unit)).isNone = true ∧
    (demand node Located.combine 0 (fun _ => none)).value.aggregate.vars = .one 7 := by decide +kernel

/-- Collector reachability includes children of uncached nodes. Cache absence
cannot justify treating a constructor as a leaf during tracing. -/
theorem uncached_node_has_live_edges :
    (none : Option Nat).isNone = true ∧ 0 ∈ reachable diamond 3 := by decide +kernel

/-- Sharing avoids duplicate construction, but each duplicate edge still
issues a request. A count of four nodes alone would omit three lookups. -/
theorem shared_leaf_requests_include_duplicate_edges :
    demandRequests Controls.diamond Controls.addSummary 3 (fun _ => none) = 7 ∧
    (demand Controls.diamond Controls.addSummary 3 (fun _ => none)).computed.length = 4 := by
  decide +kernel

theorem cached_root_one_request :
    demandRequests Controls.diamond Controls.addSummary 3
      (demand Controls.diamond Controls.addSummary 3 (fun _ => none)).cache = 1 := by
  rw [demandRequests, demand_stores]

end Controls

end Mettapedia.Machines.DemandSummary

/-!
## Retained source/role memo representation

The finite slot construction below reuses the read-only query and cursor
owners. Lookup distinguishes a pending walk from proved absence and from
refusal. Private clearing and migration derive their own placement, support
and source-coverage invariants before publishing a replacement table.

Keys include the immutable source identity and interpretation role; a source
revision, profile or environment must remain fixed or be included in that key.
Images may coincide. The occurrence inventory remains an ordered list and is
independent of the number of stored images. Effectful payload execution is
not authorized by these pure memo laws.

`inlineOrder` represents an inline region followed by hash probes. `Growth`
migrates a whole finite table. A native realization may instead retain its
eight inline entries and migrate only its overflow region. No control-state
or C-memory refinement is asserted. Allocation and release supply and retire
private buffers as external services; logical cell-operation receipts do not
bound those services or an entire native service slot.
-/

namespace Mettapedia.Machines.DemandSummary.RetainedMemo

variable {Key Value : Type} [DecidableEq Key]

/-- Probe order is a permutation of the physical slots. Hash arithmetic is
separate from the key/value representation laws. -/
structure Order (Key : Type) (capacity : Nat) where
  positions : Key → List Nat
  complete : ∀ key, (positions key).Perm (List.range capacity)

def cyclic (capacity : Nat) (hash : Key → Nat) : Order Key capacity where
  positions key := (List.range capacity).rotate (hash key)
  complete _key := List.rotate_perm _ _

structure Table (Key Value : Type) where
  capacity : Nat
  cell : Nat → Option (Key × Value)

def empty (capacity : Nat) : Table Key Value := ⟨capacity, fun _ => none⟩

def Present (table : Table Key Value) (key : Key) (value : Value) : Prop :=
  ∃ index < table.capacity, table.cell index = some (key, value)

/-- Uniqueness belongs to keys, not images. Different keys may have the
same image, including a shared normalized node. -/
def Unique (table : Table Key Value) : Prop :=
  ∀ i j key first second, i < table.capacity → j < table.capacity →
    table.cell i = some (key, first) → table.cell j = some (key, second) → i = j

/-- Every stored key is preceded only by occupied slots in its own probe
order. This is the open-addressing invariant, independent of lookup code. -/
def Placed (table : Table Key Value) (order : Order Key table.capacity) : Prop :=
  ∀ index key value, index < table.capacity → table.cell index = some (key, value) →
    ∃ before after, order.positions key = before ++ index :: after ∧
      ∀ earlier ∈ before, (table.cell earlier).isSome = true

inductive Probe (Value : Type) where
  | found (index : Nat) (value : Value)
  | vacant (index : Nat)
  | full
  deriving DecidableEq, Repr

def Probe.value : Probe Value → Option Value
  | .found _ value => some value
  | _ => none

/-- Reference for one physical probe walk. Encountering an empty slot ends
the walk; it is not a scan through all occupied entries. -/
def probe (table : Table Key Value) (key : Key) : List Nat → Probe Value
  | [] => .full
  | index :: rest => match table.cell index with
    | none => .vacant index
    | some (other, value) =>
        if key = other then .found index value else probe table key rest

omit [DecidableEq Key] in
theorem present_empty (capacity : Nat) (key : Key) (value : Value) :
    ¬ Present (empty capacity) key value := by
  rintro ⟨index, _, impossible⟩
  cases impossible

omit [DecidableEq Key] in
theorem unique_empty (capacity : Nat) : Unique (empty capacity : Table Key Value) := by
  intro i j key first second _ _ impossible
  cases impossible

omit [DecidableEq Key] in
theorem placed_empty (capacity : Nat) (order : Order Key capacity) :
    Placed (empty capacity : Table Key Value) order := by
  intro index key value _ impossible
  cases impossible

omit [DecidableEq Key] in
theorem unique_value (table : Table Key Value) (unique : Unique table)
    (key : Key) (first second : Value)
    (left : Present table key first) (right : Present table key second) : first = second := by
  obtain ⟨i, hi, left⟩ := left
  obtain ⟨j, hj, right⟩ := right
  have same := unique i j key first second hi hj left right
  subst j
  simpa [left] using right

theorem probe_found_cell (table : Table Key Value) (key : Key) (positions : List Nat)
    (index : Nat) (value : Value) (found : probe table key positions = .found index value) :
    index ∈ positions ∧ table.cell index = some (key, value) := by
  induction positions with
  | nil => cases found
  | cons first rest ih =>
      cases stored : table.cell first with
      | none => simp [probe, stored] at found
      | some entry =>
          rcases entry with ⟨other, image⟩
          by_cases same : key = other
          · simp only [probe, stored, same, if_true, Probe.found.injEq] at found
            obtain ⟨rfl, rfl⟩ := found
            exact ⟨by simp, by simpa [same] using stored⟩
          · have tail := ih (by simpa [probe, stored, same] using found)
            exact ⟨List.mem_cons_of_mem first tail.1, tail.2⟩

theorem probe_vacant_prefix (table : Table Key Value) (key : Key) (positions : List Nat)
    (index : Nat) (vacant : probe table key positions = .vacant index) :
    ∃ before after, positions = before ++ index :: after ∧
      table.cell index = none ∧ ∀ earlier ∈ before, (table.cell earlier).isSome = true := by
  induction positions with
  | nil => cases vacant
  | cons first rest ih =>
      cases stored : table.cell first with
      | none =>
          have same : first = index := by simpa [probe, stored] using vacant
          subst first
          exact ⟨[], rest, rfl, stored, by simp⟩
      | some entry =>
          rcases entry with ⟨other, image⟩
          by_cases same : key = other
          · simp [probe, stored, same] at vacant
          · obtain ⟨before, after, split, hole, occupied⟩ :=
              ih (by simpa [probe, stored, same] using vacant)
            refine ⟨first :: before, after, by simp [split], hole, ?_⟩
            intro earlier member
            rcases List.mem_cons.mp member with rfl | member
            · simp [stored]
            · exact occupied earlier member

theorem probe_full_occupied (table : Table Key Value) (key : Key) (positions : List Nat)
    (full : probe table key positions = .full) :
    ∀ index ∈ positions, (table.cell index).isSome = true := by
  induction positions with
  | nil => simp
  | cons first rest ih =>
      cases stored : table.cell first with
      | none => simp [probe, stored] at full
      | some entry =>
          rcases entry with ⟨other, value⟩
          by_cases same : key = other
          · simp [probe, stored, same] at full
          · have tail := ih (by simpa [probe, stored, same] using full)
            intro index member
            rcases List.mem_cons.mp member with rfl | member
            · simp [stored]
            · exact tail index member

private theorem probe_value_prefix (table : Table Key Value) (key : Key) (value : Value)
    (unique : Unique table) (index : Nat) (inside : index < table.capacity)
    (stored : table.cell index = some (key, value))
    (before after : List Nat)
    (bounded : ∀ earlier ∈ before, earlier < table.capacity)
    (occupied : ∀ earlier ∈ before, (table.cell earlier).isSome = true) :
    (probe table key (before ++ index :: after)).value = some value := by
  induction before with
  | nil => simp [probe, stored, Probe.value]
  | cons first rest ih =>
      cases firstStored : table.cell first with
      | none => simpa [firstStored] using occupied first (by simp)
      | some entry =>
          rcases entry with ⟨other, image⟩
          by_cases same : key = other
          · subst other
            have equal := unique_value table unique key image value
              ⟨first, bounded first (by simp), firstStored⟩ ⟨index, inside, stored⟩
            simp [probe, firstStored, equal, Probe.value]
          · simpa [probe, firstStored, same] using
              ih (fun earlier member => bounded earlier (by simp [member]))
                (fun earlier member => occupied earlier (by simp [member]))

/-- Exact lookup follows from slot placement and key uniqueness; no
injectivity condition is imposed on the stored values. -/
theorem probe_value_iff (table : Table Key Value) (order : Order Key table.capacity)
    (unique : Unique table) (placed : Placed table order) (key : Key) (value : Value) :
    (probe table key (order.positions key)).value = some value ↔ Present table key value := by
  constructor
  · intro found
    cases result : probe table key (order.positions key) with
    | vacant index => simp [result, Probe.value] at found
    | full => simp [result, Probe.value] at found
    | found index image =>
        have equal : image = value := by simpa [result, Probe.value] using found
        subst image
        obtain ⟨member, stored⟩ := probe_found_cell table key _ index value result
        exact ⟨index, List.mem_range.mp ((order.complete key).mem_iff.mp member), stored⟩
  · rintro ⟨index, inside, stored⟩
    obtain ⟨before, after, split, occupied⟩ := placed index key value inside stored
    rw [split]
    apply probe_value_prefix table key value unique index inside stored before after
    · intro earlier member
      apply List.mem_range.mp
      apply (order.complete key).mem_iff.mp
      simp [split, member]
    · exact occupied

def write (table : Table Key Value) (index : Nat) (key : Key) (value : Value) :
    Table Key Value :=
  { table with cell := Function.update table.cell index (some (key, value)) }

omit [DecidableEq Key] in
theorem write_occupied (table : Table Key Value) (index : Nat) (key : Key) (value : Value)
    (earlier : Nat) (occupied : (table.cell earlier).isSome = true) :
    ((write table index key value).cell earlier).isSome = true := by
  by_cases same : earlier = index
  · simp [write, same]
  · simpa [write, same] using occupied

omit [DecidableEq Key] in
theorem write_placed (table : Table Key Value) (order : Order Key table.capacity)
    (placed : Placed table order) (index : Nat) (key : Key) (value : Value)
    (reachable : ∃ before after, order.positions key = before ++ index :: after ∧
      ∀ earlier ∈ before, (table.cell earlier).isSome = true) :
    Placed (write table index key value) order := by
  intro position query image inside stored
  by_cases same : position = index
  · subst position
    have equal : (key, value) = (query, image) := by simpa [write] using stored
    cases equal
    obtain ⟨before, after, split, occupied⟩ := reachable
    exact ⟨before, after, split, fun earlier member =>
      write_occupied table index key value earlier (occupied earlier member)⟩
  · have old : table.cell position = some (query, image) := by
      simpa [write, same] using stored
    obtain ⟨before, after, split, occupied⟩ := placed position query image inside old
    exact ⟨before, after, split, fun earlier member =>
      write_occupied table index key value earlier (occupied earlier member)⟩

omit [DecidableEq Key] in
/-- A fresh insertion is an actual slot update. All prior observations
survive, and the new key may share its image with any old key. -/
theorem vacant_write_present (table : Table Key Value) (index : Nat)
    (inside : index < table.capacity) (hole : table.cell index = none)
    (key query : Key) (value image : Value) :
    Present (write table index key value) query image ↔
      (query = key ∧ image = value) ∨ Present table query image := by
  constructor
  · rintro ⟨position, bound, stored⟩
    by_cases same : position = index
    · subst position
      have equal : (key, value) = (query, image) := by simpa [write] using stored
      cases equal
      exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨position, bound, by simpa [write, same] using stored⟩
  · rintro (⟨rfl, rfl⟩ | ⟨position, bound, stored⟩)
    · exact ⟨index, inside, by simp [write]⟩
    · have different : position ≠ index := by
        intro equal
        subst position
        simp [hole] at stored
      exact ⟨position, bound, by simpa [write, different] using stored⟩

omit [DecidableEq Key] in
theorem vacant_write_unique (table : Table Key Value) (unique : Unique table)
    (index : Nat) (key : Key) (value : Value)
    (absent : ∀ image, ¬ Present table key image) :
    Unique (write table index key value) := by
  intro i j query first second hi hj left right
  by_cases li : i = index
  · subst i
    have equal : (key, value) = (query, first) := by simpa [write] using left
    cases equal
    by_cases rj : j = index
    · exact rj.symm
    · exact False.elim (absent second ⟨j, hj, by simpa [write, rj] using right⟩)
  · by_cases rj : j = index
    · subst j
      have equal : (key, value) = (query, second) := by simpa [write] using right
      cases equal
      exact False.elim (absent first ⟨i, hi, by simpa [write, li] using left⟩)
    · exact unique i j query first second hi hj
        (by simpa [write, li] using left) (by simpa [write, rj] using right)

/-- The existing adaptive read program reads exactly one cell per request.
Its continuation retains the collision-chain suffix. -/
def lookupProgram (key : Key) : List Nat →
    ReadOnlyQuery.Program Nat (Option (Key × Value)) (Probe Value)
  | [] => .pure .full
  | index :: rest => .read index fun cell => match cell with
    | none => .pure (.vacant index)
    | some (other, value) =>
        if key = other then .pure (.found index value) else lookupProgram key rest

theorem lookupProgram_exact (table : Table Key Value) (key : Key) (positions : List Nat) :
    (ReadOnlyQuery.run table.cell (lookupProgram key positions)).answer =
      probe table key positions := by
  induction positions with
  | nil => rfl
  | cons index rest ih =>
      cases stored : table.cell index with
      | none => simp [lookupProgram, ReadOnlyQuery.run, probe, stored]
      | some entry =>
          rcases entry with ⟨other, value⟩
          by_cases same : key = other <;>
            simp [lookupProgram, ReadOnlyQuery.run, probe, stored, same, ih]

abbrev LookupSaved (table : Table Key Value) :=
  Nat × Cursor.ReadOnlyQuery.Result (Answer := Probe Value) table.cell

def startLookup (table : Table Key Value) (key : Key) (positions : List Nat) :
    LookupSaved table :=
  (0, .paused ⟨PUnit.unit, lookupProgram key positions, []⟩)

def resumeLookup (table : Table Key Value) (allowance : Nat) (saved : LookupSaved table) :
    LookupSaved table :=
  Cursor.resume (Cursor.ReadOnlyQuery.provider table.cell) Cursor.ReadOnlyQuery.client
    (Cursor.ReadOnlyQuery.readCharge table.cell) allowance saved

inductive Reply (Value : Type) where
  | pending
  | found (value : Value)
  | absent
  | stored
  | refused
  deriving DecidableEq, Repr

def lookupReply (table : Table Key Value) (saved : LookupSaved table) : Reply Value :=
  match saved.2 with
  | .paused _ => .pending
  | .done ⟨_, answer, _⟩ => match answer with
    | .found _ value => .found value
    | .vacant _ | .full => .absent

/-- Revision mismatch refuses before executing or changing the saved cursor.
Natural revisions are never reused in this mathematical owner. -/
def pollLookup (table : Table Key Value) (captured current allowance : Nat)
    (saved : LookupSaved table) : Reply Value × LookupSaved table :=
  if current = captured then
    let next := resumeLookup table allowance saved
    (lookupReply table next, next)
  else (.refused, saved)

omit [DecidableEq Key] in
theorem lookup_zero (table : Table Key Value) (saved : LookupSaved table) :
    resumeLookup table 0 saved = saved := by
  exact Cursor.resume_zero _ _ _ saved

omit [DecidableEq Key] in
theorem lookup_pause_composition (table : Table Key Value) (first second : Nat)
    (saved : LookupSaved table) :
    resumeLookup table (first + second) saved =
      resumeLookup table second (resumeLookup table first saved) := by
  exact Cursor.resume_add _ _ _ first second saved

omit [DecidableEq Key] in
theorem lookup_revision_refused (table : Table Key Value) (captured current allowance : Nat)
    (saved : LookupSaved table) (changed : current ≠ captured) :
    pollLookup table captured current allowance saved = (.refused, saved) := by
  simp [pollLookup, changed]

/-- A bounded run keeps the independently interpreted residual meaning,
including the complete ordered read certificate and exact charge account. -/
theorem lookup_residual_exact (table : Table Key Value) (key : Key) (positions : List Nat)
    (allowance : Nat) :
    (Cursor.ReadOnlyQuery.residualMeaning table.cell
      (resumeLookup table allowance (startLookup table key positions)).2).answer =
      probe table key positions := by
  have law := Cursor.ReadOnlyQuery.advance_meaning table.cell allowance
    (lookupProgram key positions) []
  have answer := congrArg ReadOnlyQuery.Observation.answer law
  simpa [resumeLookup, startLookup, Cursor.resume, Nat.zero_add, lookupProgram_exact] using answer

omit [DecidableEq Key] in
theorem write_unique_at (table : Table Key Value) (unique : Unique table)
    (index : Nat) (key : Key) (value : Value)
    (only : ∀ position image, position < table.capacity →
      table.cell position = some (key, image) → position = index) :
    Unique (write table index key value) := by
  intro i j query first second hi hj left right
  by_cases li : i = index
  · subst i
    have equal : (key, value) = (query, first) := by simpa [write] using left
    cases equal
    by_cases rj : j = index
    · exact rj.symm
    · exact (rj (only j second hj (by simpa [write, rj] using right))).elim
  · by_cases rj : j = index
    · subst j
      have equal : (key, value) = (query, second) := by simpa [write] using right
      cases equal
      exact (li (only i first hi (by simpa [write, li] using left))).elim
    · exact unique i j query first second hi hj
        (by simpa [write, li] using left) (by simpa [write, rj] using right)

omit [DecidableEq Key] in
theorem replacement_present (table : Table Key Value) (unique : Unique table)
    (index : Nat) (inside : index < table.capacity) (key query : Key) (old value image : Value)
    (previous : table.cell index = some (key, old)) :
    Present (write table index key value) query image ↔
      (query = key ∧ image = value) ∨ (query ≠ key ∧ Present table query image) := by
  constructor
  · rintro ⟨position, bound, stored⟩
    by_cases same : position = index
    · subst position
      have equal : (key, value) = (query, image) := by simpa [write] using stored
      cases equal
      exact Or.inl ⟨rfl, rfl⟩
    · have oldCell : table.cell position = some (query, image) := by
        simpa [write, same] using stored
      refine Or.inr ⟨?_, position, bound, oldCell⟩
      intro equal
      subst query
      exact same (unique position index key image old bound inside oldCell previous)
  · rintro (⟨rfl, rfl⟩ | ⟨different, position, bound, stored⟩)
    · exact ⟨index, inside, by simp [write]⟩
    · have other : position ≠ index := by
        intro equal
        subst position
        have equal : (key, old) = (query, image) := by simpa [previous] using stored
        exact different (Prod.mk.inj equal).1.symm
      exact ⟨position, bound, by simpa [write, other] using stored⟩

/-- Only a returned lookup certificate may perform the corresponding slot
write. A paused lookup publishes no candidate entry. -/
def finishStore (table : Table Key Value) (captured current : Nat)
    (key : Key) (value : Value) (saved : LookupSaved table) :
    Reply Value × Table Key Value × Nat :=
  if current = captured then
    match saved.2 with
    | .paused _ => (.pending, table, current)
    | .done ⟨_, result, _⟩ => match result with
      | .found index _ | .vacant index =>
          (.stored, write table index key value, current + 1)
      | .full => (.refused, table, current)
  else (.refused, table, current)

omit [DecidableEq Key] in
theorem pending_cannot_store (table : Table Key Value) (captured current : Nat)
    (key : Key) (value : Value)
    (packet : Cursor.Packet (Cursor.ReadOnlyQuery.provider table.cell)
      (Cursor.ReadOnlyQuery.client (Answer := Probe Value)) PUnit.unit) (paid : Nat)
    (unchanged : current = captured) :
    finishStore table captured current key value (paid, .paused packet) =
      (.pending, table, current) := by
  simp [finishStore, unchanged]

omit [DecidableEq Key] in
theorem store_revision_refused (table : Table Key Value) (captured current : Nat)
    (key : Key) (value : Value) (saved : LookupSaved table) (changed : current ≠ captured) :
    finishStore table captured current key value saved = (.refused, table, current) := by
  simp [finishStore, changed]

inductive Phase (Key Value : Type) where
  | clearing (remaining : List Nat)
  | scanning (remaining : List Nat)
  | probing (key : Key) (value : Value) (sourceRemaining positions : List Nat)
  | committed
  | refused (key : Key) (value : Value) (sourceRemaining : List Nat)
  deriving DecidableEq, Repr

/-- Allocation supplies private, possibly uninitialized storage. It carries
no authority until clearing, source scanning and collision probing finish. -/
structure Growth (Key Value : Type) where
  cell : Nat → Option (Key × Value)
  phase : Phase Key Value

def destination (capacity : Nat) (growth : Growth Key Value) : Table Key Value :=
  ⟨capacity, growth.cell⟩

def beginGrowth (capacity : Nat) (storage : Nat → Option (Key × Value)) : Growth Key Value :=
  ⟨storage, .clearing (List.range capacity)⟩

/-- This is the sole migration transition. Clearing, reading one source slot,
and inspecting one collision slot are separate steps. Publication is separate
again. Allocation and release of the two buffers are external services. -/
def growthStep (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (growth : Growth Key Value) : Growth Key Value :=
  match growth.phase with
  | .clearing [] => { growth with phase := .scanning (List.range old.capacity) }
  | .clearing (index :: rest) =>
      ⟨Function.update growth.cell index none, .clearing rest⟩
  | .scanning [] => { growth with phase := .committed }
  | .scanning (index :: rest) => match old.cell index with
    | none => { growth with phase := .scanning rest }
    | some (key, value) => { growth with phase := .probing key value rest (order.positions key) }
  | .probing key value rest [] => { growth with phase := .refused key value rest }
  | .probing key value rest (index :: positions) => match growth.cell index with
    | none =>
        ⟨Function.update growth.cell index (some (key, value)), .scanning rest⟩
    | some (other, _) =>
        if key = other then { growth with phase := .scanning rest }
        else { growth with phase := .probing key value rest positions }
  | .committed | .refused _ _ _ => growth

def published (old : Table Key Value) (capacity : Nat) (growth : Growth Key Value) :
    Table Key Value :=
  match growth.phase with
  | .committed => destination capacity growth
  | _ => old

def SourceBounded (old : Table Key Value) (remaining : List Nat) : Prop :=
  ∀ index ∈ remaining, index < old.capacity

def Supported (old next : Table Key Value) : Prop :=
  ∀ key value, Present next key value → Present old key value

def Covered (old next : Table Key Value) (remaining : List Nat)
    (current : Option (Key × Value)) : Prop :=
  ∀ index key value, index < old.capacity → old.cell index = some (key, value) →
    Present next key value ∨ index ∈ remaining ∨ current = some (key, value)

def Core (old next : Table Key Value) (order : Order Key next.capacity) : Prop :=
  Unique next ∧ Placed next order ∧ Supported old next

/-- Coverage tracks actual source slots. Equal values at different keys do
not merge those slots or their outstanding obligations. -/
def Invariant (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (growth : Growth Key Value) : Prop :=
  let next := destination capacity growth
  match growth.phase with
  | .clearing remaining =>
      ∀ index < capacity, index ∉ remaining → growth.cell index = none
  | .scanning remaining =>
      Core old next order ∧ SourceBounded old remaining ∧ Covered old next remaining none
  | .probing key value remaining positions =>
      Core old next order ∧ SourceBounded old remaining ∧
      Covered old next remaining (some (key, value)) ∧ Present old key value ∧
      (∃ before, order.positions key = before ++ positions) ∧
      probe next key (order.positions key) = probe next key positions
  | .committed => Core old next order ∧ Covered old next [] none
  | .refused key value remaining =>
      Core old next order ∧ Covered old next remaining (some (key, value)) ∧
        Present old key value ∧ probe next key (order.positions key) = .full

omit [DecidableEq Key] in
theorem core_of_cleared (old next : Table Key Value) (order : Order Key next.capacity)
    (cleared : ∀ index < next.capacity, next.cell index = none) : Core old next order := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j key first second hi _ left
    simp [cleared i hi] at left
  · intro index key value inside stored
    simp [cleared index inside] at stored
  · rintro key value ⟨index, inside, stored⟩
    simp [cleared index inside] at stored

theorem begin_invariant (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (storage : Nat → Option (Key × Value)) :
    Invariant old capacity order (beginGrowth capacity storage) := by
  intro index inside absent
  exact (absent (List.mem_range.mpr inside)).elim

omit [DecidableEq Key] in
private theorem covered_scan_none (old next : Table Key Value) (index : Nat)
    (rest : List Nat) (covered : Covered old next (index :: rest) none)
    (hole : old.cell index = none) : Covered old next rest none := by
  intro position key value inside stored
  rcases covered position key value inside stored with present | member | impossible
  · exact Or.inl present
  · rcases List.mem_cons.mp member with rfl | member
    · simp [hole] at stored
    · exact Or.inr (Or.inl member)
  · cases impossible

omit [DecidableEq Key] in
private theorem covered_scan_some (old next : Table Key Value) (index : Nat)
    (rest : List Nat) (key : Key) (value : Value)
    (covered : Covered old next (index :: rest) none)
    (stored : old.cell index = some (key, value)) :
    Covered old next rest (some (key, value)) := by
  intro position query image inside found
  rcases covered position query image inside found with present | member | impossible
  · exact Or.inl present
  · rcases List.mem_cons.mp member with rfl | member
    · have equal : (key, value) = (query, image) := by simpa [stored] using found
      cases equal
      exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl member)
  · cases impossible

omit [DecidableEq Key] in
private theorem covered_finish_row (old next : Table Key Value) (rest : List Nat)
    (key : Key) (value : Value) (covered : Covered old next rest (some (key, value)))
    (present : Present next key value) : Covered old next rest none := by
  intro index query image inside found
  rcases covered index query image inside found with oldPresent | member | same
  · exact Or.inl oldPresent
  · exact Or.inr (Or.inl member)
  · have equal : (key, value) = (query, image) := Option.some.inj same
    cases equal
    exact Or.inl present

private theorem core_insert (old next : Table Key Value) (order : Order Key next.capacity)
    (core : Core old next order) (key : Key) (value : Value)
    (origin : Present old key value) (index : Nat)
    (vacant : probe next key (order.positions key) = .vacant index) :
    Core old (write next index key value) order := by
  obtain ⟨before, after, split, _, occupied⟩ :=
    probe_vacant_prefix next key _ index vacant
  refine ⟨vacant_write_unique next core.1 index key value ?_,
    write_placed next order core.2.1 index key value ⟨before, after, split, occupied⟩, ?_⟩
  · intro image present
    have found := (probe_value_iff next order core.1 core.2.1 key image).mpr present
    simp [vacant, Probe.value] at found
  · intro query image present
    have inside : index < next.capacity := by
      apply List.mem_range.mp
      apply (order.complete key).mem_iff.mp
      simp [split]
    have hole := (probe_vacant_prefix next key _ index vacant).choose_spec.choose_spec.2.1
    rcases (vacant_write_present next index inside hole key query value image).mp present with
      ⟨rfl, rfl⟩ | oldPresent
    · exact origin
    · exact core.2.2 query image oldPresent

omit [DecidableEq Key] in
private theorem covered_insert (old next : Table Key Value) (index : Nat)
    (inside : index < next.capacity) (hole : next.cell index = none)
    (rest : List Nat) (key : Key) (value : Value)
    (covered : Covered old next rest (some (key, value))) :
    Covered old (write next index key value) rest none := by
  apply covered_finish_row old (write next index key value) rest key value
  · intro position query image bound stored
    rcases covered position query image bound stored with present | member | current
    · exact Or.inl ((vacant_write_present next index inside hole key query value image).mpr
        (Or.inr present))
    · exact Or.inr (Or.inl member)
    · exact Or.inr (Or.inr current)
  · exact ⟨index, inside, by simp [write]⟩

theorem growth_step_invariant (old : Table Key Value) (oldUnique : Unique old)
    (capacity : Nat) (order : Order Key capacity) (growth : Growth Key Value)
    (invariant : Invariant old capacity order growth) :
    Invariant old capacity order (growthStep old capacity order growth) := by
  rcases growth with ⟨cells, phase⟩
  cases phase with
  | clearing remaining =>
      cases remaining with
      | nil =>
          have cleared : ∀ index < capacity, cells index = none := by
            intro index inside
            exact invariant index inside (by simp)
          refine ⟨core_of_cleared old ⟨capacity, cells⟩ order cleared, ?_, ?_⟩
          · intro index member
            exact List.mem_range.mp member
          · intro index key value inside _
            exact Or.inr (Or.inl (List.mem_range.mpr inside))
      | cons index rest =>
          intro position inside absent
          by_cases same : position = index
          · simp [growthStep, same]
          · simpa [growthStep, same] using invariant position inside (by simp [same, absent])
  | scanning remaining =>
      obtain ⟨core, bounded, covered⟩ := invariant
      cases remaining with
      | nil => exact ⟨core, covered⟩
      | cons index rest =>
          cases stored : old.cell index with
          | none =>
              dsimp only [growthStep]
              simp only [stored]
              dsimp only [Invariant, destination]
              exact ⟨core, fun position member => bounded position (by simp [member]),
                covered_scan_none old _ index rest covered stored⟩
          | some entry =>
              rcases entry with ⟨key, value⟩
              dsimp only [growthStep]
              simp only [stored]
              dsimp only [Invariant, destination]
              refine ⟨core, fun position member => bounded position (by simp [member]),
                covered_scan_some old _ index rest key value covered stored,
                ⟨index, bounded index (by simp), stored⟩, ⟨[], by simp⟩, rfl⟩
  | probing key value rest positions =>
      obtain ⟨core, bounded, covered, origin, suffix, residual⟩ := invariant
      dsimp only [destination] at core covered residual
      cases positions with
      | nil =>
          dsimp only [growthStep, Invariant, destination]
          exact ⟨core, covered, origin, by simpa [probe] using residual⟩
      | cons index positions =>
          have inside : index < capacity := by
            apply List.mem_range.mp
            apply (order.complete key).mem_iff.mp
            obtain ⟨before, split⟩ := suffix
            simp [split]
          cases stored : cells index with
          | none =>
              have vacant : probe ⟨capacity, cells⟩ key (order.positions key) = .vacant index := by
                rw [residual]
                simp [probe, stored]
              dsimp only [growthStep]
              simp only [stored]
              dsimp only [Invariant, destination]
              exact ⟨core_insert old ⟨capacity, cells⟩ order core key value origin index vacant,
                bounded, covered_insert old ⟨capacity, cells⟩ index inside stored rest key value covered⟩
          | some entry =>
              rcases entry with ⟨other, image⟩
              by_cases same : key = other
              · subst other
                dsimp only [growthStep]
                simp only [stored]
                dsimp only [Invariant, destination]
                have present : Present (⟨capacity, cells⟩ : Table Key Value) key image :=
                  ⟨index, inside, stored⟩
                have equal := unique_value old oldUnique key image value (core.2.2 key image present) origin
                refine ⟨core, bounded, covered_finish_row old _ rest key value covered ?_⟩
                simpa [equal] using present
              · dsimp only [growthStep]
                simp only [stored, if_neg same]
                dsimp only [Invariant, destination]
                refine ⟨core, bounded, covered, origin, ?_, ?_⟩
                · obtain ⟨before, split⟩ := suffix
                  exact ⟨before ++ [index], by simp [split, List.append_assoc]⟩
                · simpa [probe, stored, same] using residual
  | committed => exact invariant
  | refused key value rest => exact invariant

theorem committed_preserves_entries (old : Table Key Value) (capacity : Nat)
    (order : Order Key capacity) (growth : Growth Key Value)
    (invariant : Invariant old capacity order growth) (committed : growth.phase = .committed)
    (key : Key) (value : Value) :
    Present (published old capacity growth) key value ↔ Present old key value := by
  simp only [Invariant, committed] at invariant
  rw [published, committed]
  constructor
  · exact invariant.1.2.2 key value
  · rintro ⟨index, inside, stored⟩
    simpa using invariant.2 index key value inside stored

omit [DecidableEq Key] in
theorem unfinished_keeps_authoritative (old : Table Key Value) (capacity : Nat)
    (growth : Growth Key Value) (unfinished : growth.phase ≠ .committed) :
    published old capacity growth = old := by
  cases phase : growth.phase <;> simp_all [published]

def cancelGrowth (old : Table Key Value) (_growth : Growth Key Value) : Table Key Value := old

omit [DecidableEq Key] in
theorem cancel_keeps_old_observations (old : Table Key Value) (growth : Growth Key Value)
    (key : Key) (value : Value) :
    Present (cancelGrowth old growth) key value ↔ Present old key value := Iff.rfl

/-- Inline slots precede a rotated open-addressing region. The eight-slot
native instance is obtained by choosing `inline = 8`. -/
def inlineOrder (inline capacity : Nat) (hash : Key → Nat) : Order Key (inline + capacity) where
  positions key := List.range inline ++
    ((List.range capacity).rotate (hash key)).map (inline + ·)
  complete key := by
    rw [List.range_add]
    exact (List.Perm.refl _).append ((List.rotate_perm _ _).map _)

/-- A completed probe permits either replacement or insertion. Capacity
refusal is explicit and leaves the original table available. -/
def store (table : Table Key Value) (order : Order Key table.capacity)
    (key : Key) (value : Value) : Option (Table Key Value) :=
  match probe table key (order.positions key) with
  | .found index _ | .vacant index => some (write table index key value)
  | .full => none

theorem store_capacity (table : Table Key Value) (order : Order Key table.capacity)
    (key : Key) (value : Value) (next : Table Key Value)
    (stored : store table order key value = some next) : next.capacity = table.capacity := by
  cases result : probe table key (order.positions key) <;>
    simp only [store, result, Option.some.injEq] at stored
  · cases stored
    rfl
  · cases stored
    rfl
  · cases stored

theorem store_representation (table : Table Key Value) (order : Order Key table.capacity)
    (unique : Unique table) (placed : Placed table order)
    (key : Key) (value : Value) (next : Table Key Value)
    (stored : store table order key value = some next) :
    next.capacity = table.capacity ∧ Unique next ∧
      Placed next (by rw [store_capacity table order key value next stored]; exact order) ∧
      ∀ query image, Present next query image ↔
        (query = key ∧ image = value) ∨ (query ≠ key ∧ Present table query image) := by
  cases result : probe table key (order.positions key) with
  | full => simp [store, result] at stored
  | found index previous =>
      have equal : next = write table index key value := by simpa [store, result] using stored.symm
      subst next
      obtain ⟨member, atIndex⟩ := probe_found_cell table key _ index previous result
      have inside := List.mem_range.mp ((order.complete key).mem_iff.mp member)
      refine ⟨rfl, write_unique_at table unique index key value ?_,
        write_placed table order placed index key value (placed index key previous inside atIndex), ?_⟩
      · intro position image bound found
        exact unique position index key image previous bound inside found atIndex
      · intro query image
        exact replacement_present table unique index inside key query previous value image atIndex
  | vacant index =>
      have equal : next = write table index key value := by simpa [store, result] using stored.symm
      subst next
      obtain ⟨before, after, split, hole, occupied⟩ := probe_vacant_prefix table key _ index result
      have inside : index < table.capacity := by
        apply List.mem_range.mp
        apply (order.complete key).mem_iff.mp
        simp [split]
      have absent : ∀ image, ¬ Present table key image := by
        intro image present
        have found := (probe_value_iff table order unique placed key image).mpr present
        simp [result, Probe.value] at found
      refine ⟨rfl, vacant_write_unique table unique index key value absent,
        write_placed table order placed index key value ⟨before, after, split, occupied⟩, ?_⟩
      intro query image
      rw [vacant_write_present table index inside hole key query value image]
      constructor
      · rintro (fresh | old)
        · exact Or.inl fresh
        · refine Or.inr ⟨?_, old⟩
          intro same
          subst query
          exact absent image old
      · rintro (fresh | ⟨_, old⟩)
        · exact Or.inl fresh
        · exact Or.inr old

def cache (table : Table Nat Value) (order : Order Nat table.capacity) : Cache Value :=
  fun key => (probe table key (order.positions key)).value

theorem committed_lookup_exact (old : Table Key Value) (oldOrder : Order Key old.capacity)
    (unique : Unique old) (placed : Placed old oldOrder) (capacity : Nat)
    (order : Order Key capacity) (growth : Growth Key Value)
    (invariant : Invariant old capacity order growth) (committed : growth.phase = .committed)
    (key : Key) :
    (probe (destination capacity growth) key (order.positions key)).value =
      (probe old key (oldOrder.positions key)).value := by
  have core : Core old (destination capacity growth) order := by
    have law : Core old (destination capacity growth) order ∧
        Covered old (destination capacity growth) [] none := by
      simpa only [Invariant, committed] using invariant
    exact law.1
  apply Option.ext
  intro value
  rw [probe_value_iff _ _ core.1 core.2.1, probe_value_iff _ _ unique placed]
  simpa only [published, committed] using
    committed_preserves_entries old capacity order growth invariant committed key value

theorem committed_cache_exact (old : Table Nat Value) (oldOrder : Order Nat old.capacity)
    (unique : Unique old) (placed : Placed old oldOrder) (capacity : Nat)
    (order : Order Nat capacity) (growth : Growth Nat Value)
    (invariant : Invariant old capacity order growth) (committed : growth.phase = .committed) :
    cache (destination capacity growth) order = cache old oldOrder := by
  funext key
  exact committed_lookup_exact old oldOrder unique placed capacity order growth invariant committed key

def terminal (growth : Growth Key Value) : Bool :=
  match growth.phase with
  | .committed | .refused _ _ _ => true
  | _ => false

/-- The existing cursor driver runs migration's actual transition. A
terminal result is inert; a pending reply is never an absent-key answer. -/
def growthProvider (old : Table Key Value) (capacity : Nat) (order : Order Key capacity) :
    Cursor.Provider (Cursor.Sequence.protocol Unit) where
  State _ _ := Growth Key Value
  step growth _ :=
    if terminal growth then ⟨none, growth⟩
    else ⟨some (), growthStep old capacity order growth⟩

def growthClient : Cursor.Client (P := Cursor.Sequence.protocol Unit)
    (Return := fun _ _ => Unit) := Cursor.Fold.client (fun _ _ => ())

def growthCharge (old : Table Key Value) (capacity : Nat) (order : Order Key capacity) :
    Cursor.Charge (growthProvider old capacity order) :=
  fun growth _ => if terminal growth then 0 else 1

abbrev GrowthSaved (old : Table Key Value) (capacity : Nat) (order : Order Key capacity) :=
  Nat × Cursor.Outcome (growthProvider old capacity order) growthClient ()

def startMigration (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (growth : Growth Key Value) : GrowthSaved old capacity order :=
  (0, .paused ⟨(), .pulling (), growth⟩)

def resumeMigration (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (allowance : Nat) (saved : GrowthSaved old capacity order) : GrowthSaved old capacity order :=
  Cursor.resume (growthProvider old capacity order) growthClient
    (growthCharge old capacity order) allowance saved

def retained {old : Table Key Value} {capacity : Nat} {order : Order Key capacity}
    (saved : GrowthSaved old capacity order) : Growth Key Value :=
  match saved.2 with
  | .paused ⟨_, _, growth⟩ | .done ⟨_, _, growth⟩ => growth

theorem migration_zero (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (saved : GrowthSaved old capacity order) : resumeMigration old capacity order 0 saved = saved := by
  exact Cursor.resume_zero _ _ _ saved

theorem migration_pause_composition (old : Table Key Value) (capacity : Nat)
    (order : Order Key capacity) (first second : Nat) (saved : GrowthSaved old capacity order) :
    resumeMigration old capacity order (first + second) saved =
      resumeMigration old capacity order second (resumeMigration old capacity order first saved) := by
  exact Cursor.resume_add _ _ _ first second saved

private theorem migration_advance_invariant (old : Table Key Value) (unique : Unique old)
    (capacity : Nat) (order : Order Key capacity) (fuel : Nat)
    (control : Cursor.Fold.State Unit) (growth : Growth Key Value)
    (invariant : Invariant old capacity order growth) :
    Invariant old capacity order (retained
      (Cursor.advance (growthProvider old capacity order) growthClient
        (growthCharge old capacity order) fuel ⟨(), control, growth⟩)) := by
  induction fuel generalizing control growth with
  | zero => exact invariant
  | succ fuel ih =>
      cases control with
      | finished value => exact invariant
      | pulling value =>
          dsimp only [Cursor.advance, growthClient, Cursor.Fold.client]
          by_cases ended : terminal growth = true
          · simp only [growthProvider, ended, if_true]
            exact ih (.finished value) growth invariant
          · have notEnded : terminal growth = false := by simpa using ended
            simp only [growthProvider, notEnded, Bool.false_eq_true, if_false]
            exact ih (.pulling ()) (growthStep old capacity order growth)
              (growth_step_invariant old unique capacity order growth invariant)

theorem migration_resume_invariant (old : Table Key Value) (unique : Unique old)
    (capacity : Nat) (order : Order Key capacity) (fuel : Nat) (saved : GrowthSaved old capacity order)
    (invariant : Invariant old capacity order (retained saved)) :
    Invariant old capacity order (retained (resumeMigration old capacity order fuel saved)) := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | done result => exact invariant
  | paused packet =>
      rcases packet with ⟨index, control, growth⟩
      cases index
      simpa [resumeMigration, Cursor.resume, retained] using
        migration_advance_invariant old unique capacity order fuel control growth invariant

/-- Every finite schedule of retained slices starts from physical clearing
and keeps the representation invariant, including partially paid growth. -/
theorem migration_schedule_invariant (old : Table Key Value) (unique : Unique old)
    (capacity : Nat) (order : Order Key capacity) (storage : Nat → Option (Key × Value))
    (grants : List Nat) :
    Invariant old capacity order (retained (grants.foldl
      (fun saved grant => resumeMigration old capacity order grant saved)
      (startMigration old capacity order (beginGrowth capacity storage)))) := by
  have foldLaw : ∀ (saved : GrowthSaved old capacity order),
      Invariant old capacity order (retained saved) →
      Invariant old capacity order (retained (grants.foldl
        (fun saved grant => resumeMigration old capacity order grant saved) saved)) := by
    induction grants with
    | nil => intro saved invariant; exact invariant
    | cons grant rest ih =>
        intro saved invariant
        exact ih _ (migration_resume_invariant old unique capacity order grant saved invariant)
  exact foldLaw _ (begin_invariant old capacity order storage)

def pollMigration (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (captured current allowance : Nat) (saved : GrowthSaved old capacity order) :
    Reply Value × GrowthSaved old capacity order :=
  if current = captured then
    let next := resumeMigration old capacity order allowance saved
    (match (retained next).phase with
      | .committed => .stored
      | .refused _ _ _ => .refused
      | _ => .pending, next)
  else (.refused, saved)

theorem migration_revision_refused (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (captured current allowance : Nat) (saved : GrowthSaved old capacity order)
    (changed : current ≠ captured) :
    pollMigration old capacity order captured current allowance saved = (.refused, saved) := by
  simp [pollMigration, changed]

def remainingWork (oldCapacity capacity : Nat) (growth : Growth Key Value) : Nat :=
  match growth.phase with
  | .clearing remaining => remaining.length + oldCapacity * (capacity + 2) + 2
  | .scanning remaining => remaining.length * (capacity + 2) + 1
  | .probing _ _ rest positions => rest.length * (capacity + 2) + positions.length + 1
  | .committed | .refused _ _ _ => 0

/-- The finite slot model cannot remain pending forever. This decreases
logical cell operations, not allocation, cleanup or elapsed time. -/
theorem growth_step_decreases (old : Table Key Value) (capacity : Nat) (order : Order Key capacity)
    (growth : Growth Key Value) (pending : terminal growth = false) :
    remainingWork old.capacity capacity (growthStep old capacity order growth) <
      remainingWork old.capacity capacity growth := by
  rcases growth with ⟨cells, phase⟩
  cases phase with
  | clearing remaining =>
      cases remaining <;> simp [growthStep, remainingWork, List.length_range]
  | scanning remaining =>
      cases remaining with
      | nil => simp [growthStep, remainingWork]
      | cons index rest =>
          cases stored : old.cell index with
          | none => simp [growthStep, stored, remainingWork, Nat.add_mul]
          | some entry =>
              rcases entry with ⟨key, value⟩
              have length := (order.complete key).length_eq
              simp only [List.length_range] at length
              simp [growthStep, stored, remainingWork, length, Nat.add_mul]
  | probing key value rest positions =>
      cases positions with
      | nil => simp [growthStep, remainingWork]
      | cons index positions =>
          cases stored : cells index with
          | none => simp [growthStep, stored, remainingWork]
          | some entry =>
              rcases entry with ⟨other, image⟩
              by_cases same : key = other <;>
                simp [growthStep, stored, remainingWork, same]
  | committed => simp [terminal] at pending
  | refused key value rest => simp [terminal] at pending

theorem migration_eventually_terminal (old : Table Key Value) (capacity : Nat)
    (order : Order Key capacity) (growth : Growth Key Value) :
    ∃ steps ≤ remainingWork old.capacity capacity growth,
      terminal ((growthStep old capacity order)^[steps] growth) = true := by
  generalize measure : remainingWork old.capacity capacity growth = work
  induction work using Nat.strong_induction_on generalizing growth with
  | h work ih =>
      by_cases ended : terminal growth = true
      · exact ⟨0, by omega, ended⟩
      · have pending : terminal growth = false := by simpa using ended
        have less := growth_step_decreases old capacity order growth pending
        obtain ⟨steps, within, done⟩ := ih _ (by omega) (growthStep old capacity order growth) rfl
        refine ⟨steps + 1, by omega, ?_⟩
        simpa only [Function.iterate_succ_apply] using done

omit [DecidableEq Key] in
/-- The existing ordered read inventory keeps every occurrence, even when
several source keys or repeated occurrences have the same image. -/
theorem occurrence_inventory (lookup : Key → Option Value) (keys : List Key) :
    (ReadOnlyQuery.samples lookup keys).map Prod.fst = keys := by
  simp [ReadOnlyQuery.samples, List.map_map, Function.comp_def]

omit [DecidableEq Key] in
theorem occurrence_multiplicity (lookup : Key → Option Value) (keys : List Key) :
    (ReadOnlyQuery.samples lookup keys).length = keys.length := by
  simp [ReadOnlyQuery.samples]

omit [DecidableEq Key] in
theorem occurrence_append (lookup : Key → Option Value) (first second : List Key) :
    ReadOnlyQuery.samples lookup (first ++ second) =
      ReadOnlyQuery.samples lookup first ++ ReadOnlyQuery.samples lookup second := by
  simp [ReadOnlyQuery.samples]

/-- Completion is reached after exactly the actual probe reads and one
uncharged return inspection. Layout and hash order are held fixed. -/
theorem lookup_completion_account (table : Table Key Value) (key : Key) (positions : List Nat) :
    let observed := ReadOnlyQuery.run table.cell (lookupProgram key positions)
    resumeLookup table (observed.reads.length + 1) (startLookup table key positions) =
      (observed.reads.length, .done ⟨PUnit.unit, probe table key positions, observed.reads.reverse⟩) := by
  have law := Cursor.ReadOnlyQuery.advance_complete table.cell (lookupProgram key positions) []
  simpa [resumeLookup, startLookup, Cursor.resume, lookupProgram_exact] using law

theorem lookup_read_account (table : Table Key Value) (key : Key) (positions : List Nat)
    (allowance : Nat) :
    (Cursor.ReadOnlyQuery.recorded table.cell
      (resumeLookup table allowance (startLookup table key positions)).2).length =
      (resumeLookup table allowance (startLookup table key positions)).1 := by
  have law := Cursor.ReadOnlyQuery.advance_read_account table.cell allowance
    (lookupProgram key positions) []
  simpa [resumeLookup, startLookup, Cursor.resume] using law

theorem lookup_reads_le_slots (table : Table Key Value) (key : Key) (positions : List Nat) :
    (ReadOnlyQuery.run table.cell (lookupProgram key positions)).reads.length ≤ positions.length := by
  induction positions with
  | nil => simp [lookupProgram, ReadOnlyQuery.run]
  | cons index rest ih =>
      cases stored : table.cell index with
      | none => simp [lookupProgram, ReadOnlyQuery.run, stored]
      | some entry =>
          rcases entry with ⟨other, value⟩
          by_cases same : key = other
          · simp [lookupProgram, ReadOnlyQuery.run, stored, same]
          · simpa [lookupProgram, ReadOnlyQuery.run, stored, same] using Nat.succ_le_succ ih

theorem store_cache_update (table : Table Nat Value) (order : Order Nat table.capacity)
    (unique : Unique table) (placed : Placed table order) (key : Nat) (value : Value)
    (next : Table Nat Value) (stored : store table order key value = some next) :
    cache next (by rw [store_capacity table order key value next stored]; exact order) =
      Function.update (cache table order) key (some value) := by
  obtain ⟨capacity, nextUnique, nextPlaced, entries⟩ :=
    store_representation table order unique placed key value next stored
  funext query
  apply Option.ext
  intro image
  rw [cache, probe_value_iff _ _ nextUnique nextPlaced, entries]
  by_cases same : query = key
  · subst query
    simp [eq_comm]
  · simpa [same, cache] using (probe_value_iff table order unique placed query image).symm

/-- Installing the value of the existing DAG evaluator preserves its sound
cache and every old observation. The installed value is derived by `demand`,
not supplied by a cache-correctness premise. -/
theorem demand_store_sound {Label : Type} (graph : Graph Label) (combine : Label → List Value → Value)
    (table : Table Nat Value) (order : Order Nat table.capacity)
    (unique : Unique table) (placed : Placed table order)
    (sound : Sound graph combine (cache table order)) (root : Nat) (next : Table Nat Value)
    (stored : store table order root
      (demand graph combine root (cache table order)).value = some next) :
    let nextOrder : Order Nat next.capacity := by
      rw [store_capacity table order root _ next stored]; exact order
    Sound graph combine (cache next nextOrder) ∧ Extends (cache table order) (cache next nextOrder) := by
  dsimp only
  rw [store_cache_update table order unique placed root _ next stored]
  have computed := demand_exact graph combine root (cache table order) sound
  constructor
  · intro query value present
    by_cases same : query = root
    · subst query
      have sameValue : (demand graph combine root (cache table order)).value = value := by
        simpa only [Function.update_self, Option.some.injEq] using present
      exact sameValue.symm.trans computed
    · apply sound query value
      simpa [Function.update_of_ne same] using present
  · intro query value present
    by_cases same : query = root
    · subst query
      simp only [Function.update_self]
      exact congrArg some (computed.trans (sound root value present).symm)
    · simpa [Function.update_of_ne same] using present

def finishMigration (old : Table Key Value) (capacity : Nat) (captured current : Nat)
    (growth : Growth Key Value) : Reply Value × Table Key Value × Nat :=
  if current = captured then
    match growth.phase with
    | .committed => (.stored, destination capacity growth, current + 1)
    | .refused _ _ _ => (.refused, old, current)
    | _ => (.pending, old, current)
  else (.refused, old, current)

omit [DecidableEq Key] in
theorem changed_revision_cannot_publish (old : Table Key Value) (capacity captured current : Nat)
    (growth : Growth Key Value) (changed : current ≠ captured) :
    finishMigration old capacity captured current growth = (.refused, old, current) := by
  simp [finishMigration, changed]

omit [DecidableEq Key] in
theorem publication_revision_strict (old : Table Key Value) (capacity captured current : Nat)
    (growth : Growth Key Value) (unchanged : current = captured)
    (complete : growth.phase = .committed) :
    finishMigration old capacity captured current growth =
      (.stored, destination capacity growth, current + 1) ∧ current < current + 1 := by
  simp [finishMigration, unchanged, complete]

omit [DecidableEq Key] in
theorem supported_full_capacity (old next : Table Key Value)
    (unique : Unique next) (supported : Supported old next)
    (full : ∀ index < next.capacity, (next.cell index).isSome = true) :
    next.capacity ≤ old.capacity := by
  classical
  have entries : ∀ i : Fin next.capacity, ∃ entry, next.cell i.val = some entry := by
    intro i
    cases found : next.cell i.val with
    | none => simpa [found] using full i.val i.isLt
    | some entry => exact ⟨entry, rfl⟩
  choose entry stored using entries
  have originals : ∀ i : Fin next.capacity,
      ∃ j : Fin old.capacity, old.cell j.val = some (entry i) := by
    intro i
    obtain ⟨index, inside, present⟩ := supported (entry i).1 (entry i).2
      ⟨i.val, i.isLt, stored i⟩
    exact ⟨⟨index, inside⟩, present⟩
  choose address copied using originals
  have injective : Function.Injective address := by
    intro i j same
    have images : entry i = entry j := Option.some.inj
      ((copied i).symm.trans (by rw [same]; exact copied j))
    apply Fin.ext
    exact unique i.val j.val (entry i).1 (entry i).2 (entry i).2 i.isLt j.isLt
      (stored i) ((stored j).trans (congrArg some images.symm))
  simpa using Fintype.card_le_of_injective address injective

theorem adequate_capacity_cannot_refuse (old : Table Key Value) (capacity : Nat)
    (order : Order Key capacity) (growth : Growth Key Value)
    (invariant : Invariant old capacity order growth) (room : old.capacity < capacity)
    (key : Key) (value : Value) (rest : List Nat) :
    growth.phase ≠ .refused key value rest := by
  intro refused
  have inv : Core old (destination capacity growth) order ∧
      Covered old (destination capacity growth) rest (some (key, value)) ∧
      Present old key value ∧
      probe (destination capacity growth) key (order.positions key) = .full := by
    simpa only [Invariant, refused] using invariant
  have full := probe_full_occupied (destination capacity growth) key _ inv.2.2.2
  have bound := supported_full_capacity old (destination capacity growth) inv.1.1 inv.1.2.2
    (fun index inside => full index ((order.complete key).mem_iff.mpr (List.mem_range.mpr inside)))
  exact (Nat.not_le_of_gt room) bound

theorem migration_iterations_invariant (old : Table Key Value) (unique : Unique old)
    (capacity : Nat) (order : Order Key capacity) (steps : Nat) (growth : Growth Key Value)
    (invariant : Invariant old capacity order growth) :
    Invariant old capacity order ((growthStep old capacity order)^[steps] growth) := by
  induction steps generalizing growth with
  | zero => exact invariant
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (growth_step_invariant old unique capacity order growth invariant)

/-- Successful allocation of enough slots gives a finite committed migration,
not a terminal refusal. The proof counts distinct keys, so shared images do
not reduce the number of entries that must be moved. -/
theorem adequate_migration_commits (old : Table Key Value) (unique : Unique old)
    (capacity : Nat) (order : Order Key capacity) (room : old.capacity < capacity)
    (storage : Nat → Option (Key × Value)) :
    ∃ steps ≤ remainingWork old.capacity capacity (beginGrowth capacity storage),
      ((growthStep old capacity order)^[steps] (beginGrowth capacity storage)).phase = .committed := by
  obtain ⟨steps, bound, ended⟩ :=
    migration_eventually_terminal old capacity order (beginGrowth capacity storage)
  have invariant := migration_iterations_invariant old unique capacity order steps
    (beginGrowth capacity storage) (begin_invariant old capacity order storage)
  refine ⟨steps, bound, ?_⟩
  cases phase : ((growthStep old capacity order)^[steps] (beginGrowth capacity storage)).phase with
  | committed => rfl
  | clearing rest => simp [terminal, phase] at ended
  | scanning rest => simp [terminal, phase] at ended
  | probing key value rest positions => simp [terminal, phase] at ended
  | refused key value rest =>
      exact (adequate_capacity_cannot_refuse old capacity order _ invariant room key value rest phase).elim

/-- Every bounded schedule preserves all committed observations. This starts
with actual private clearing and holds through cancellation or publication. -/
theorem migration_schedule_preserves (old : Table Key Value) (unique : Unique old)
    (capacity : Nat) (order : Order Key capacity) (storage : Nat → Option (Key × Value))
    (grants : List Nat) (key : Key) (value : Value) :
    let saved := grants.foldl (fun saved grant => resumeMigration old capacity order grant saved)
      (startMigration old capacity order (beginGrowth capacity storage))
    Present (published old capacity (retained saved)) key value ↔ Present old key value := by
  dsimp only
  have invariant := migration_schedule_invariant old unique capacity order storage grants
  by_cases complete : (retained (grants.foldl
      (fun saved grant => resumeMigration old capacity order grant saved)
      (startMigration old capacity order (beginGrowth capacity storage)))).phase = .committed
  · exact committed_preserves_entries old capacity order _ invariant complete key value
  · rw [unfinished_keeps_authoritative old capacity _ complete]



/-- A pure preparation cursor and the memo lookup have separate completion
barriers. Neither a partial value nor a partial collision walk is installed. -/
def storePrepared {Node : Type} (source : Nat → Node)
    (prepared : Nat × Cursor.ReadOnlyQuery.Result (Answer := Value) source)
    (table : Table Key Value) (captured current : Nat) (key : Key)
    (lookup : LookupSaved table) : Reply Value × Table Key Value × Nat :=
  if current = captured then
    match prepared.2 with
    | .paused _ => (.pending, table, current)
    | .done ⟨_, value, _⟩ => finishStore table captured current key value lookup
  else (.refused, table, current)

omit [DecidableEq Key] in
theorem unfinished_preparation_cannot_insert {Node : Type} (source : Nat → Node)
    (packet : Cursor.Packet (Cursor.ReadOnlyQuery.provider source)
      (Cursor.ReadOnlyQuery.client (Answer := Value)) PUnit.unit)
    (paid : Nat) (table : Table Key Value) (captured current : Nat) (key : Key)
    (lookup : LookupSaved table) (unchanged : current = captured) :
    storePrepared source (paid, .paused packet) table captured current key lookup =
      (.pending, table, current) := by simp [storePrepared, unchanged]

omit [DecidableEq Key] in
theorem changed_revision_refuses_prepared_store {Node : Type} (source : Nat → Node)
    (prepared : Nat × Cursor.ReadOnlyQuery.Result (Answer := Value) source)
    (table : Table Key Value) (captured current : Nat) (key : Key)
    (lookup : LookupSaved table) (changed : current ≠ captured) :
    storePrepared source prepared table captured current key lookup = (.refused, table, current) := by
  simp [storePrepared, changed]

/-- The completed resumable lookup performs the very same physical write as
the independently defined probe/store implementation. -/
theorem completed_lookup_store (table : Table Key Value) (order : Order Key table.capacity)
    (key : Key) (value : Value) (allowance version : Nat) (result : Probe Value)
    (reads : ReadOnlyQuery.Reads Nat (Option (Key × Value)))
    (done : (resumeLookup table allowance (startLookup table key (order.positions key))).2 =
      .done ⟨PUnit.unit, result, reads⟩) :
    finishStore table version version key value
      (resumeLookup table allowance (startLookup table key (order.positions key))) =
      match store table order key value with
      | none => (.refused, table, version)
      | some next => (.stored, next, version + 1) := by
  have correct := lookup_residual_exact table key (order.positions key) allowance
  rw [done] at correct
  change result = probe table key (order.positions key) at correct
  simp only [finishStore, done]
  unfold store
  rw [← correct]
  cases result <;> rfl

namespace Controls

private def shared : Table Nat Nat := ⟨3, fun
  | 0 => some (11, 7)
  | 1 => some (22, 7)
  | _ => none⟩

private def sharedOrder : Order Nat 3 := cyclic 3 (fun _ => 0)

/-- Distinct source identities occupy distinct slots despite equal images. -/
theorem noninjective_physical_table_valid : Unique shared ∧ Placed shared sharedOrder := by
  constructor
  · intro i j key first second hi hj left right
    change i < 3 at hi
    change j < 3 at hj
    interval_cases i <;> interval_cases j <;> simp [shared] at left right <;> omega
  · intro index key value inside stored
    change index < 3 at inside
    interval_cases index
    · obtain ⟨rfl, rfl⟩ := (by simpa [shared] using stored : 11 = key ∧ 7 = value)
      exact ⟨[], [1, 2], rfl, by simp⟩
    · obtain ⟨rfl, rfl⟩ := (by simpa [shared] using stored : 22 = key ∧ 7 = value)
      exact ⟨[0], [2], rfl, by simp [shared]⟩
    · simp [shared] at stored

theorem noninjective_images_preserve_both_keys :
    cache shared sharedOrder 11 = some 7 ∧ cache shared sharedOrder 22 = some 7 ∧
      cache shared sharedOrder 33 = none := by decide

private def roleTable : Table (Nat × Nat) Nat := ⟨3, fun
  | 0 => some ((17, 0), 7)
  | 1 => some ((17, 1), 8)
  | _ => none⟩

theorem source_identity_does_not_erase_role :
    probe roleTable (17, 0) [0, 1, 2] = .found 0 7 ∧
    probe roleTable (17, 1) [0, 1, 2] = .found 1 8 ∧
    probe roleTable (17, 2) [0, 1, 2] = .vacant 2 := by decide

theorem pending_found_absent_and_refused_are_distinct :
    lookupReply shared (resumeLookup shared 1 (startLookup shared 22 [0, 1, 2])) = .pending ∧
    lookupReply shared (resumeLookup shared 3 (startLookup shared 22 [0, 1, 2])) = .found 7 ∧
    lookupReply shared (resumeLookup shared 4 (startLookup shared 33 [0, 1, 2])) = .absent ∧
    (pollLookup shared 0 1 4 (startLookup shared 22 [0, 1, 2])).1 = .refused := by decide

theorem a_pending_lookup_cannot_publish_a_candidate :
    let saved := resumeLookup shared 1 (startLookup shared 33 [0, 1, 2])
    (finishStore shared 0 0 33 9 saved).1 = .pending ∧
    ((finishStore shared 0 0 33 9 saved).2.1.cell 2) = none ∧
    (finishStore shared 0 0 33 9 saved).2.2 = 0 := by decide

theorem completed_lookup_inserts_only_its_finished_value :
    let saved := resumeLookup shared 4 (startLookup shared 33 [0, 1, 2])
    (finishStore shared 0 0 33 7 saved).1 = .stored ∧
    ((finishStore shared 0 0 33 7 saved).2.1.cell 2) = some (33, 7) ∧
    (finishStore shared 0 0 33 7 saved).2.2 = 1 := by decide

theorem generic_replacement_changes_only_the_requested_key :
    (store shared sharedOrder 11 99).map (fun next =>
      ((probe next 11 [0, 1, 2]).value, (probe next 22 [0, 1, 2]).value)) =
        some (some 99, some 7) := by decide

private def fullTable : Table Nat Nat := { shared with capacity := 2 }

theorem capacity_refusal_does_not_remove_old_answers :
    (store fullTable (cyclic 2 (fun _ => 0)) 33 8).isNone = true ∧
    (probe fullTable 11 [0, 1]).value = some 7 ∧
    (probe fullTable 22 [0, 1]).value = some 7 := by decide

private def nextOrder : Order Nat 5 := cyclic 5 (fun _ => 0)
private def dirtyStorage : Nat → Option (Nat × Nat) := fun _ => some (909, 666)
private def fresh := startMigration shared 5 nextOrder (beginGrowth 5 dirtyStorage)
private def cutEight := resumeMigration shared 5 nextOrder 8 fresh
private def finished := resumeMigration shared 5 nextOrder 30 fresh

theorem migration_clears_scans_probes_then_commits :
    finished.1 = 13 ∧ (retained finished).phase = .committed ∧
    (retained finished).cell 0 = some (11, 7) ∧
    (retained finished).cell 1 = some (22, 7) ∧
    (probe (destination 5 (retained finished)) 909 [0, 1, 2, 3, 4]).value = none := by decide

theorem incomplete_growth_keeps_unmigrated_old_key_visible :
    (retained cutEight).phase = .scanning [1, 2] ∧
    (probe (published shared 5 (retained cutEight)) 22 [0, 1, 2]).value = some 7 ∧
    (probe (destination 5 (retained cutEight)) 22 [0, 1, 2, 3, 4]).value = none := by decide

theorem cancellation_inside_a_collision_chain_keeps_old_answers :
    let cut := resumeMigration shared 5 nextOrder 10 fresh
    (retained cut).phase = .probing 22 7 [2] [1, 2, 3, 4] ∧
    (probe (cancelGrowth shared (retained cut)) 11 [0, 1, 2]).value = some 7 ∧
    (probe (cancelGrowth shared (retained cut)) 22 [0, 1, 2]).value = some 7 := by decide

theorem resuming_keeps_paid_work_while_restarting_repeats_it :
    (resumeMigration shared 5 nextOrder 30 cutEight).1 = 13 ∧
    cutEight.1 + finished.1 = 21 ∧
    (retained (resumeMigration shared 5 nextOrder 30 cutEight)).phase = .committed := by decide

/-- Publishing the same partial destination would lose a real old key. -/
theorem early_publication_loses_an_unmigrated_observation :
    let premature := { retained cutEight with phase := Phase.committed }
    (probe (published shared 5 premature) 22 [0, 1, 2, 3, 4]).value = none ∧
    (probe shared 22 [0, 1, 2]).value = some 7 := by decide

/-- Skipping physical clearing lets arbitrary private bytes become an entry. -/
theorem omitting_clearing_publishes_a_spurious_key :
    let unchecked : Growth Nat Nat := ⟨dirtyStorage, .scanning []⟩
    let premature := growthStep shared 5 nextOrder unchecked
    (probe (published shared 5 premature) 909 [0, 1, 2, 3, 4]).value = some 666 ∧
    (probe (published shared 5 (retained finished)) 909 [0, 1, 2, 3, 4]).value = none := by decide

theorem changed_revision_refuses_a_fully_prepared_publication :
    (finishMigration shared 5 0 1 (retained finished)).1 = .refused ∧
    ((finishMigration shared 5 0 1 (retained finished)).2.1.cell 1) = some (22, 7) ∧
    (finishMigration shared 5 0 1 (retained finished)).2.2 = 1 := by decide

theorem equal_images_preserve_duplicate_occurrence_inventory :
    ReadOnlyQuery.samples (cache shared sharedOrder) [11, 11, 22] =
      [(11, some 7), (11, some 7), (22, some 7)] ∧
    ReadOnlyQuery.samples (cache shared sharedOrder) [11, 11, 22] ≠
      ReadOnlyQuery.samples (cache shared sharedOrder) [11, 22] := by decide

theorem equal_images_do_not_hide_reordered_source_inventory :
    (ReadOnlyQuery.samples (cache shared sharedOrder) [11, 22]).map Prod.snd =
      (ReadOnlyQuery.samples (cache shared sharedOrder) [22, 11]).map Prod.snd ∧
    ReadOnlyQuery.samples (cache shared sharedOrder) [11, 22] ≠
      ReadOnlyQuery.samples (cache shared sharedOrder) [22, 11] := by decide

theorem a_duplicate_replacement_preserves_values_but_changes_inventory :
    (ReadOnlyQuery.samples (cache shared sharedOrder) [11, 22]).map Prod.snd =
      (ReadOnlyQuery.samples (cache shared sharedOrder) [11, 11]).map Prod.snd ∧
    ReadOnlyQuery.samples (cache shared sharedOrder) [11, 22] ≠
      ReadOnlyQuery.samples (cache shared sharedOrder) [11, 11] := by decide

private def reordered : Table Nat Nat := ⟨3, fun
  | 0 => some (22, 7)
  | 1 => some (11, 7)
  | _ => none⟩

/-- Equal key observations across layouts do not imply equal probe counts. -/
theorem changed_layout_can_change_lookup_work :
    (probe shared 22 [0, 1, 2]).value = (probe reordered 22 [0, 1, 2]).value ∧
    (ReadOnlyQuery.run shared.cell (lookupProgram 22 [0, 1, 2])).reads.length = 2 ∧
    (ReadOnlyQuery.run reordered.cell (lookupProgram 22 [0, 1, 2])).reads.length = 1 := by decide


private def preparation : ReadOnlyQuery.Program Nat Nat Nat :=
  .read 0 fun first => .read 1 fun second => .pure (first + second + 7)

private def prepared (allowance : Nat) :=
  Cursor.advance (Cursor.ReadOnlyQuery.provider (fun i : Nat => i)) Cursor.ReadOnlyQuery.client
    (Cursor.ReadOnlyQuery.readCharge (fun i : Nat => i)) (base := PUnit.unit) allowance
    ⟨PUnit.unit, preparation, []⟩

theorem completed_lookup_does_not_authorize_unfinished_node_preparation :
    let lookup := resumeLookup shared 4 (startLookup shared 33 [0, 1, 2])
    (storePrepared (fun i : Nat => i) (prepared 1) shared 0 0 33 lookup).1 = .pending ∧
    ((storePrepared (fun i : Nat => i) (prepared 1) shared 0 0 33 lookup).2.1.cell 2) = none ∧
    (storePrepared (fun i : Nat => i) (prepared 3) shared 0 0 33 lookup).1 = .stored ∧
    ((storePrepared (fun i : Nat => i) (prepared 3) shared 0 0 33 lookup).2.1.cell 2) = some (33, 8) := by decide

end Controls

end Mettapedia.Machines.DemandSummary.RetainedMemo
