import Mettapedia.GSLT.Coordination.ReplicaMerge

/-!
# Sagas: what compensation guarantees, and exactly what it does not

A saga (Garcia-Molina and Salem, SIGMOD 1987) runs a commit across owners as a sequence of local
steps, each committed at its own owner. If a later step cannot run, the steps already taken are
undone by **compensations**, run in reverse order. Here steps and compensations are commits of the
occurrence store, so each is atomic at its owner.

A compensation **compensates** a step (`Compensates`) when it takes exactly what the step made,
keeps nothing, has no predicate query, and makes occurrences carrying the labels the step took.

## What sagas guarantee

* **A compensation can run right after its step** (`compensation_enabled`), given fresh
  identities.
* **A compensated saga restores the contents** (`saga_compensated`): if the steps and then their
  compensations in reverse order form a legal run, the final store carries the same labels as the
  initial one, as a bag. This is the counted form of every run: labels after, plus labels taken,
  equal labels before, plus labels made (`labels_legal`).
* **A compensation stays possible while the step's results are reserved**
  (`compensation_enabled_of_reserved`): if no commit in between takes what the step made, and none
  makes the compensation's identities, the compensation is still enabled.

## What they do not guarantee

* **Isolation** (`Controls.dirty_read`): between a debit and its compensation, an auditor that
  queries the accounts sees one coin where every serial order of whole sagas shows two.
* **That a compensation can run at all** (`Controls.compensation_blocked`): a concurrent commit
  that takes the step's result disables the compensation; the saga can then neither finish nor
  undo itself.
* **Identity** (`identities_not_restored`, `Controls.old_token_dead`): a compensation restores
  labels, with new identities. Whatever referred to the identities the step took (a claim, a
  fencing token) stays dead after the compensation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.Sagas

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Coordination.ReplicaMerge

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v} [DecidableEq R] (label : O → R)

/-- A compensation of a step: it takes exactly what the step made, keeps nothing, has no predicate
query, and makes occurrences with the labels the step took. -/
structure Compensates (step comp : Commit O R) : Prop where
  takes_made : comp.taken = step.made
  keeps_none : comp.kept = ∅
  queries_none : comp.queries = []
  remakes : labels label comp.made = labels label step.taken

variable {label}

omit [DecidableEq R] in
/-- **A compensation can run right after its step.** -/
theorem compensation_enabled {store : Finset O} {step comp : Commit O R}
    (comp_ok : Compensates label step comp) (fresh : Disjoint comp.made (fire store step)) :
    Enabled label (fire store step) comp where
  taken_subset := by rw [comp_ok.takes_made]; exact made_subset_fire
  kept_subset := by rw [comp_ok.keeps_none]; exact Finset.empty_subset _
  apart := by rw [comp_ok.keeps_none]; exact Finset.disjoint_empty_right _
  fresh := fresh
  queries_hold := by rw [comp_ok.queries_none]; simp

/-- One firing, counted without subtraction. -/
theorem labels_fire_add {store : Finset O} {c : Commit O R} (enabled : Enabled label store c) :
    labels label (fire store c) + labels label c.taken = labels label store + labels label c.made := by
  rw [labels_fire enabled, add_right_comm, tsub_add_cancel_of_le (labels_mono enabled.taken_subset)]

/-- **Every executable run, counted**: labels after, plus labels taken, equal labels before, plus
labels made. -/
theorem labels_legal {store : Finset O} {cs : List (Commit O R)} (legal : Executable label store cs) :
    labels label (fireList store cs) + (cs.map fun c => labels label c.taken).sum =
      labels label store + (cs.map fun c => labels label c.made).sum := by
  induction legal with
  | nil => simp
  | @cons store c rest enabled _ ih =>
      simp only [fireList_cons, List.map_cons, List.sum_cons] at ih ⊢
      rw [show labels label (fireList (fire store c) rest) + (labels label c.taken +
          (rest.map fun c => labels label c.taken).sum) =
          (labels label (fireList (fire store c) rest) + (rest.map fun c => labels label c.taken).sum) +
            labels label c.taken by abel, ih,
        show labels label (fire store c) + (rest.map fun c => labels label c.made).sum + labels label c.taken =
          (labels label (fire store c) + labels label c.taken) + (rest.map fun c => labels label c.made).sum by abel,
        labels_fire_add enabled]
      abel

/-- **A compensated saga restores the contents**: steps, then their compensations in reverse order,
run legally from a store, end at a store with the same labels. -/
theorem saga_compensated {store : Finset O} (steps : List (Commit O R × Commit O R))
    (comps : ∀ p ∈ steps, Compensates label p.1 p.2)
    (legal : Executable label store (steps.map Prod.fst ++ (steps.map Prod.snd).reverse)) :
    labels label (fireList store (steps.map Prod.fst ++ (steps.map Prod.snd).reverse)) = labels label store := by
  have counted := labels_legal legal
  have takenSum : ((steps.map Prod.fst ++ (steps.map Prod.snd).reverse).map fun c => labels label c.taken).sum =
      (steps.map fun p => labels label p.1.taken).sum + (steps.map fun p => labels label p.1.made).sum := by
    rw [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse, List.map_map, List.map_map]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p member
    simp only [Function.comp_apply, (comps p member).takes_made]
  have madeSum : ((steps.map Prod.fst ++ (steps.map Prod.snd).reverse).map fun c => labels label c.made).sum =
      (steps.map fun p => labels label p.1.made).sum + (steps.map fun p => labels label p.1.taken).sum := by
    rw [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse, List.map_map, List.map_map]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p member
    simp only [Function.comp_apply, (comps p member).remakes]
  rw [takenSum, madeSum, add_comm ((steps.map fun p => labels label p.1.made).sum)] at counted
  exact add_right_cancel counted

omit [DecidableEq R] in
/-- **A compensation stays possible while the step's results are reserved**: after the step, any
legal run of commits that take nothing the step made and make none of the compensation's
identities leaves the compensation enabled. -/
theorem compensation_enabled_of_reserved {step comp : Commit O R}
    (comp_ok : Compensates label step comp) :
    ∀ {mid : Finset O} {ds : List (Commit O R)}, step.made ⊆ mid → Disjoint comp.made mid →
      Executable label mid ds → (∀ d ∈ ds, Disjoint d.taken step.made) →
      (∀ d ∈ ds, Disjoint d.made comp.made) → Enabled label (fireList mid ds) comp := by
  intro mid ds present fresh legal reserved apart
  induction legal with
  | nil store =>
      exact ⟨by rw [comp_ok.takes_made]; exact present, by rw [comp_ok.keeps_none]; exact Finset.empty_subset _,
        by rw [comp_ok.keeps_none]; exact Finset.disjoint_empty_right _, fresh,
        by rw [comp_ok.queries_none]; simp⟩
  | @cons store d rest enabled _ ih =>
      apply ih
      · intro o made
        refine mem_fire.mpr (Or.inl ⟨present made, fun taken => ?_⟩)
        exact Finset.disjoint_left.mp (reserved d (List.mem_cons_self ..)) taken made
      · refine Finset.disjoint_left.mpr fun o inComp inFire => ?_
        rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
        · exact Finset.disjoint_left.mp fresh inComp inStore
        · exact Finset.disjoint_left.mp (apart d (List.mem_cons_self ..)) made inComp
      · exact fun d' member => reserved d' (List.mem_cons_of_mem _ member)
      · exact fun d' member => apart d' (List.mem_cons_of_mem _ member)

omit [DecidableEq R] in
/-- **Compensation does not restore identities**: after a step and its compensation, nothing the
step took is in the store, when the compensation's identities are new. -/
theorem identities_not_restored {store : Finset O} {step comp : Commit O R}
    (enabledStep : Enabled label store step) (newIds : Disjoint comp.made step.taken) :
    Disjoint step.taken (fire (fire store step) comp) := by
  refine Finset.disjoint_left.mpr fun o taken inFinal => ?_
  rcases mem_fire.mp inFinal with ⟨inMid, _⟩ | made
  · exact Finset.disjoint_left.mp (disjoint_taken_fire enabledStep) taken inMid
  · exact Finset.disjoint_left.mp newIds made taken

/-! ## Controls -/

namespace Controls

/-- Coins at account `a`, coins at account `b`, and a reservation. -/
inductive Item where
  | coinA
  | coinB
  | reservation
  deriving DecidableEq

/-- Occurrences `0` and `1` are coins at `a`; `5` is a reservation; even numbers from `10` on are
coins at `a`, odd ones coins at `b`. -/
def item : ℕ → Item
  | 0 => .coinA
  | 1 => .coinA
  | 5 => .reservation
  | n => if n % 2 = 0 then .coinA else .coinB

/-- Debit: take coin `0` of account `a`. -/
def debit : Commit ℕ Item := ⟨{0}, ∅, ∅, []⟩

/-- Credit: make coin `11` at account `b`. -/
def credit : Commit ℕ Item := ⟨∅, ∅, {11}, []⟩

/-- Compensation of the debit: make coin `10` at account `a`. -/
def refund : Commit ℕ Item := ⟨∅, ∅, {10}, []⟩

/-- The coins a predicate query of the accounts sees. -/
def coins (store : Finset ℕ) : ℕ := (store.filter fun o => item o ≠ .reservation).card

/-- **No isolation**: between the debit and its compensation an auditor sees one coin; every
serial order of whole sagas (none run, the transfer completed, or debit and refund) shows two. -/
theorem dirty_read :
    coins (fire {0, 1} debit) = 1 ∧ coins {0, 1} = 2 ∧ coins (fire (fire {0, 1} debit) credit) = 2 ∧
      coins (fire (fire {0, 1} debit) refund) = 2 := by
  decide

/-- Reserve: take coin `1`, make reservation `5`. -/
def reserve : Commit ℕ Item := ⟨{1}, ∅, {5}, []⟩

/-- Cancel the reservation: take `5`, make a coin at `a` again. -/
def cancel : Commit ℕ Item := ⟨{5}, ∅, {12}, []⟩

/-- Somebody else consumes the reservation. -/
def consume : Commit ℕ Item := ⟨{5}, ∅, ∅, []⟩

theorem cancel_compensates : Compensates item reserve cancel :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- **A compensation can be blocked**: once another commit has taken the reservation, the
cancellation is not enabled; without that commit it is. -/
theorem compensation_blocked :
    ¬ Enabled item (fire (fire {0, 1} reserve) consume) cancel ∧ Enabled item (fire {0, 1} reserve) cancel := by
  refine ⟨fun enabled => ?_, compensation_enabled cancel_compensates (by decide)⟩
  have := enabled.taken_subset (Finset.mem_singleton_self 5)
  revert this
  decide

/-- Use the claim: a commit that refers to the identity of coin `1`. -/
def useCoinOne : Commit ℕ Item := ⟨{1}, ∅, {14}, []⟩

/-- **The old identity stays dead**: after reserving and cancelling, the account holds a coin again,
but a commit that names coin `1` is not enabled. -/
theorem old_token_dead :
    coins (fire (fire {0, 1} reserve) cancel) = 2 ∧ ¬ Enabled item (fire (fire {0, 1} reserve) cancel) useCoinOne := by
  refine ⟨by decide, fun enabled => ?_⟩
  have := enabled.taken_subset (Finset.mem_singleton_self 1)
  revert this
  decide

/-- **Compensation, negative**: consuming the reservation takes what the reservation made, but it
makes nothing, so the coin it took is not given back. (`cancel_compensates` is the positive
control.) -/
theorem consume_not_compensates : ¬ Compensates item reserve consume := by
  intro compensates
  have := compensates.remakes
  revert this
  unfold labels
  decide

end Controls

end Mettapedia.GSLT.Coordination.Sagas
