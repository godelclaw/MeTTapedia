import Mettapedia.Logic.DerivationGraph.Schedules
import Mettapedia.Logic.DerivationGraph.BorrowedCursor

/-!
# Reusing retained evidence across theory changes

Retained evidence is checked against one rule system. When the theory changes —
an admitted extension, a changed definition, a different rule profile — the
evidence may be reused only after the new theory accepts every rule instance the
evidence actually used.

* `revalidate` rechecks the local rule instances of an accepted graph against a
  new interface, reading premises from the retained cache. It performs no new
  premise lookups beyond the retained ones. `revalidate_iff` proves it exact: it
  succeeds precisely when the graph replays under the new interface to the same
  cache.
* `replay_extend` transports accepted graphs along a witness map that keeps every
  accepted instance accepted (an admitted extension).
* `CheckedJudgment.extend` reuses a checked judgment in a larger rule system.
* `BorrowedCursor.run_reinterpret` gives the same law for the retained
  source-address worker: a checked schedule replays to the identical state under
  a new interface that accepts each instance it used.

Refusal is exact as well: if the new theory rejects one used instance, the graph
does not replay (`revalidate_iff`), so stale evidence cannot be reused by label.
The concrete propositional controls join this to the existing admission of
fresh definitions in `RuleMulticategoryKernels` and `PropositionalExtension`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DerivationGraph

universe u v w

variable {J : Type u} {Origin : Type w}

/-- Recheck every node's rule instance under a new interface, reading its
premises from the retained cache. -/
def revalidate {rules' : List J → J → Prop} {W : Type v} (interface' : RuleWitness rules')
    (cast : W → interface'.W) (cache : Array J) (nodes : List (Node J W Origin)) : Bool :=
  nodes.all fun node =>
    match lookupPremises cache node.parents with
    | none => false
    | some premises => interface'.isInstance (cast node.witness) premises node.conclusion

/-- **Revalidation is exact.** For a graph accepted under one interface,
rechecking its local instances under another interface (through a witness
map) succeeds exactly when the mapped graph replays under the new interface,
and then it produces the same cache. -/
theorem revalidate_iff {rules rules' : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (interface' : RuleWitness rules') (cast : interface.W → interface'.W)
    {nodes : List (Node J interface.W Origin)} {cache : Array J}
    (accepted : replay interface nodes = some cache) :
    revalidate interface' cast cache nodes = true ↔
      replay interface' (nodes.map (Node.map id cast id)) = some cache := by
  unfold replay at accepted ⊢
  rw [← replayWith_judgmentStep] at accepted ⊢
  obtain ⟨size, -, local_⟩ := (replayWith_iff_local _ #[] nodes cache).mp accepted
  constructor
  · intro checked
    apply (replayWith_iff_local _ #[] _ cache).mpr
    refine ⟨by simpa using size, fun i hi => absurd hi (by simp), ?_⟩
    intro k hk
    have hk' : k < nodes.length := by simpa using hk
    obtain ⟨backward, premises, found, computed⟩ := local_ k hk'
    have nodeEq : (nodes.map (Node.map id cast id))[k] = Node.map id cast id nodes[k] := by simp
    rw [nodeEq]
    refine ⟨backward, premises, found, ?_⟩
    have recheck := List.all_eq_true.mp checked nodes[k] (List.getElem_mem hk')
    rw [found] at recheck
    have recheck' : interface'.isInstance (cast nodes[k].witness) premises nodes[k].conclusion = true :=
      recheck
    simp only [judgmentStep] at computed ⊢
    by_cases old : interface.isInstance nodes[k].witness premises nodes[k].conclusion = true
    · simp only [old, if_true] at computed
      simp only [Node.map, id, recheck', if_true]
      exact computed
    · simp only [old] at computed
      have inside : (#[] : Array J).size + k < cache.size := by simp at size ⊢; omega
      rw [Array.getElem?_eq_getElem inside] at computed
      simp at computed
  · intro replayed
    obtain ⟨-, -, local'⟩ := (replayWith_iff_local _ #[] _ cache).mp replayed
    apply List.all_eq_true.mpr
    intro node member
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem member
    have hk' : k < (nodes.map (Node.map id cast id)).length := by simpa using hk
    obtain ⟨-, premises, found, computed⟩ := local' k hk'
    have nodeEq : (nodes.map (Node.map id cast id))[k] = Node.map id cast id nodes[k] := by simp
    rw [nodeEq] at found computed
    simp only [Node.map] at found
    rw [found]
    simp only [judgmentStep, Node.map, id] at computed
    by_cases now : interface'.isInstance (cast nodes[k].witness) premises nodes[k].conclusion = true
    · exact now
    · simp only [now] at computed
      have inside : (#[] : Array J).size + k < cache.size := by simp at size ⊢; omega
      rw [Array.getElem?_eq_getElem inside] at computed
      simp at computed

/-- **Admitted extensions transport evidence.** If a witness map keeps every
accepted instance accepted, every accepted graph replays, mapped, to the same
cache. -/
theorem replay_extend {rules rules' : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (interface' : RuleWitness rules') (cast : interface.W → interface'.W)
    (keeps : ∀ w premises conclusion, interface.isInstance w premises conclusion = true →
      interface'.isInstance (cast w) premises conclusion = true)
    {nodes : List (Node J interface.W Origin)} {cache : Array J}
    (accepted : replay interface nodes = some cache) :
    replay interface' (nodes.map (Node.map id cast id)) = some cache := by
  apply (revalidate_iff interface interface' cast accepted).mp
  apply List.all_eq_true.mpr
  intro node member
  unfold replay at accepted
  rw [← replayWith_judgmentStep] at accepted
  obtain ⟨size, -, local_⟩ := (replayWith_iff_local _ #[] nodes cache).mp accepted
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem member
  obtain ⟨-, premises, found, computed⟩ := local_ k hk
  rw [found]
  simp only [judgmentStep] at computed
  by_cases old : interface.isInstance nodes[k].witness premises nodes[k].conclusion = true
  · exact keeps _ _ _ old
  · simp only [old] at computed
    have inside : (#[] : Array J).size + k < cache.size := by simp at size ⊢; omega
    rw [Array.getElem?_eq_getElem inside] at computed
    simp at computed

/-- A checked judgment is reusable in every larger rule system. -/
def CheckedJudgment.extend {rules rules' : List J → J → Prop}
    (mono : ∀ premises conclusion, rules premises conclusion → rules' premises conclusion)
    (checked : CheckedJudgment rules) : CheckedJudgment rules' :=
  CheckedJudgment.ofDerivation checked.judgment (Derives.mono mono checked.valid)

@[simp] theorem CheckedJudgment.extend_judgment {rules rules' : List J → J → Prop}
    (mono : ∀ premises conclusion, rules premises conclusion → rules' premises conclusion)
    (checked : CheckedJudgment rules) : (checked.extend mono).judgment = checked.judgment := rfl

namespace BorrowedCursor

variable {W : Type v}

/-- **Retained cursor reinterpretation.** A schedule checked by the retained
source-address worker under one interface replays to the identical state under
another interface with the same witnesses, provided the new interface accepts
each instance the schedule used. -/
theorem run_reinterpret {rules rules' : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (interface' : RuleWitness.{u, v} rules') (sameW : interface'.W = interface.W)
    (store : Store J interface.W Origin)
    (keeps : ∀ w premises conclusion, interface.isInstance w premises conclusion = true →
      interface'.isInstance (sameW ▸ w) premises conclusion = true) :
    ∀ (state : State J) (schedule : List NodeId) {final : State J},
      run interface store state schedule = some final →
        run interface' (sameW ▸ store) state schedule = some final := by
  cases interface' with
  | mk W' isInstance' sound' complete' =>
      simp only at sameW
      subst sameW
      intro state schedule
      induction schedule generalizing state with
      | nil => intro final accepted; exact accepted
      | cons source rest ih =>
          intro final accepted
          simp only [run] at accepted ⊢
          cases stepped : step interface store state source with
          | none => rw [stepped] at accepted; cases accepted
          | some next =>
              rw [stepped] at accepted
              have stepped' : step ⟨interface.W, isInstance', sound', complete'⟩ store state source =
                  some next := by
                unfold step at stepped ⊢
                by_cases rev : state.revision = store.revision
                · by_cases dup : (indexAt state.checked source).isSome = true
                  · simp [rev, dup] at stepped
                  · cases found : store.read source with
                    | none => simp [rev, dup, found] at stepped
                    | some node =>
                        cases values : premiseValues state node.parents with
                        | none => simp [rev, dup, found, values] at stepped
                        | some values' =>
                            by_cases old : interface.isInstance node.request values' node.conclusion = true
                            · have new := keeps _ _ _ old
                              simp [rev, dup, found, values, old] at stepped
                              simp [rev, dup, values]
                              exact ⟨new, stepped⟩
                            · simp [rev, dup, found, values, old] at stepped
                · simp [rev] at stepped
              rw [stepped']
              exact ih next accepted

end BorrowedCursor

end Mettapedia.Logic.DerivationGraph
