import Mathlib.Logic.Relation
import Mettapedia.Logic.Arithmetic.BuchiAutomaton

open Mettapedia.Logic.Arithmetic.BuchiAutomaton

/-!
# Reachability certificates

May-reachability along a decidable step is certified by a finite trace. The
checker reads each consecutive pair and the claim at the end. A successful
check is a reflexive-transitive reduct that satisfies the claim.

Must-reachability, read as inevitability, is certified by a natural-number
ranking. Off the claim every step drops the rank, and a state off the claim
has a successor. Any path that avoids the claim is then no longer than the
rank of its start, and every state can reach the claim. The same ranking
shape is what a progress measure gives a memoryless controller. This is not
a second Büchi condition.

Liveness of an ω-word is certified by a lasso of a nondeterministic Büchi
automaton. `Lasso.check` is that checker. The theorem below names it; it
does not reprove emptiness.

The descent checker speaks only about the states on the list it is given.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.ReachCertificate

def stepRel {α : Type} (step : α → α → Bool) : α → α → Prop :=
  fun source target => step source target = true

/-- A trace from `start` certifies may-reachability of `claim`. -/
def checkTrace {α : Type} (step : α → α → Bool) (claim : α → Bool) (start : α) :
    List α → Bool
  | [] => claim start
  | next :: rest => step start next && checkTrace step claim next rest

theorem checkTrace_sound {α : Type} (step : α → α → Bool) (claim : α → Bool)
    (start : α) (trace : List α) (h : checkTrace step claim start trace = true) :
    ∃ target, Relation.ReflTransGen (stepRel step) start target ∧
      claim target = true := by
  induction trace generalizing start with
  | nil =>
    simp only [checkTrace] at h
    exact ⟨start, Relation.ReflTransGen.refl, h⟩
  | cons next rest ih =>
    simp only [checkTrace, Bool.and_eq_true] at h
    obtain ⟨target, hreach, hclaim⟩ := ih next h.2
    exact ⟨target,
      Relation.ReflTransGen.trans
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl h.1) hreach,
      hclaim⟩

/-- States that stay off the claim, each reached by a step from the previous. -/
def avoids {α : Type} (step : α → α → Bool) (claim : α → Bool) (start : α) :
    List α → Prop
  | [] => claim start = false
  | next :: rest =>
      step start next = true ∧ claim start = false ∧ avoids step claim next rest

theorem avoids_length_le_rank {α : Type} (rank : α → Nat) (step : α → α → Bool)
    (claim : α → Bool)
    (descent : ∀ source target, step source target = true → claim source = false →
      rank target < rank source)
    (start : α) (walk : List α) (h : avoids step claim start walk) :
    walk.length ≤ rank start := by
  induction walk generalizing start with
  | nil => exact Nat.zero_le _
  | cons next rest ih =>
    rcases h with ⟨hstep, hoff, hrest⟩
    exact Nat.succ_le_of_lt
      (Nat.lt_of_le_of_lt (ih next hrest) (descent start next hstep hoff))

/-- Off the claim, a drop in rank and a successor put the claim on every path. -/
theorem ranking_hits {α : Type} (rank : α → Nat) (step : α → α → Bool)
    (claim : α → Bool)
    (descent : ∀ source target, step source target = true → claim source = false →
      rank target < rank source)
    (progress : ∀ source, claim source = false → ∃ target, step source target = true)
    (source : α) :
    ∃ target, Relation.ReflTransGen (stepRel step) source target ∧
      claim target = true := by
  suffices ∀ n source, rank source ≤ n →
      ∃ target, Relation.ReflTransGen (stepRel step) source target ∧
        claim target = true from
    this (rank source) source (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro source hs
    have hz : rank source = 0 := Nat.eq_zero_of_le_zero hs
    cases hclaim : claim source with
    | true => exact ⟨source, Relation.ReflTransGen.refl, hclaim⟩
    | false =>
      obtain ⟨target, hstep⟩ := progress source hclaim
      have hlt := descent source target hstep hclaim
      rw [hz] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro source hs
    cases hclaim : claim source with
    | true => exact ⟨source, Relation.ReflTransGen.refl, hclaim⟩
    | false =>
      obtain ⟨next, hstep⟩ := progress source hclaim
      have hle : rank next ≤ n :=
        Nat.le_of_lt_succ (lt_of_lt_of_le (descent source next hstep hclaim) hs)
      obtain ⟨target, hreach, htarget⟩ := ih next hle
      exact ⟨target,
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep) hreach,
        htarget⟩

/-- The listed states obey the ranking drop. -/
def checkDescent {α : Type} (rank : α → Nat) (step : α → α → Bool) (claim : α → Bool)
    (states : List α) : Bool :=
  states.all fun source =>
    states.all fun target =>
      !step source target || claim source || decide (rank target < rank source)

theorem checkDescent_sound {α : Type} (rank : α → Nat) (step : α → α → Bool)
    (claim : α → Bool) (states : List α)
    (h : checkDescent rank step claim states = true) {source target : α}
    (hsource : source ∈ states) (htarget : target ∈ states)
    (hstep : step source target = true) (hoff : claim source = false) :
    rank target < rank source := by
  have hrow := List.all_eq_true.mp h source hsource
  have hbit := List.all_eq_true.mp hrow target htarget
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hbit
  refine Or.elim hbit ?_ id
  · intro hbools
    refine Or.elim hbools ?_ ?_
    · intro hno
      exact absurd (hno.symm.trans hstep) Bool.false_ne_true
    · intro hclaim
      exact absurd (hoff.symm.trans hclaim) Bool.false_ne_true

/-- A checked lasso is the liveness certificate of the Büchi automaton. -/
theorem lasso_certifies_acceptance {α σ : Type} [DecidableEq σ]
    (A : NBA α σ) (L : Lasso α σ) (h : L.check A = true) :
    ∃ hloop : L.loop ≠ [], Accepts A (lassoWord L.stem L.loop hloop) :=
  Lasso.check_accepts A L h

def stepFlip (source target : Bool) : Bool := source && !target

def claimAtFalse (source : Bool) : Bool := !source

def rankDown (source : Bool) : Nat := if source then 1 else 0

def stepLoop (source target : Bool) : Bool :=
  decide (source = true ∧ target = true)

theorem control_trace_yes :
    checkTrace stepFlip claimAtFalse true [false] = true := by
  rfl

theorem control_trace_reaches :
    ∃ target, Relation.ReflTransGen (stepRel stepFlip) true target ∧
      claimAtFalse target = true :=
  checkTrace_sound stepFlip claimAtFalse true [false] control_trace_yes

theorem control_trace_no (trace : List Bool) :
    checkTrace (fun _ _ => false) (fun _ => false) true trace = false := by
  induction trace with
  | nil => rfl
  | cons _ _ _ih =>
    simp only [checkTrace]
    rfl

theorem control_may_impossible :
    ¬ ∃ target,
      Relation.ReflTransGen (stepRel (fun _ _ => false)) true target ∧
        (fun (_ : Bool) => false) target = true := by
  intro ⟨_, _, hclaim⟩
  exact Bool.false_ne_true hclaim

theorem control_avoid_empty :
    avoids stepFlip claimAtFalse true ([] : List Bool) ∧
      ([] : List Bool).length ≤ rankDown true :=
  ⟨rfl, Nat.zero_le _⟩

theorem control_hit_is_not_avoidance :
    ¬ avoids stepFlip claimAtFalse true [false] := by
  intro ⟨_, _, hrest⟩
  simp only [avoids, claimAtFalse] at hrest
  exact Bool.false_ne_true hrest.symm

theorem control_descent_yes :
    checkDescent rankDown stepFlip claimAtFalse [false, true] = true := by
  rfl

theorem control_loop_checker (rank : Bool → Nat) :
    checkDescent rank stepLoop claimAtFalse [true] = false := by
  unfold checkDescent stepLoop claimAtFalse
  simp only [List.all, Bool.not_true, Bool.or_false, Bool.and_true]
  exact decide_eq_false (Nat.lt_irrefl _)

theorem control_loop_unranked :
    ¬ ∃ rank : Bool → Nat,
      ∀ source target, stepLoop source target = true → claimAtFalse source = false →
        rank target < rank source := by
  intro ⟨rank, hdesc⟩
  have hstep : stepLoop true true = true := by decide
  have hoff : claimAtFalse true = false := rfl
  exact Nat.lt_irrefl _ (hdesc true true hstep hoff)

#print axioms checkTrace_sound
#print axioms avoids_length_le_rank
#print axioms ranking_hits
#print axioms checkDescent_sound
#print axioms lasso_certifies_acceptance

end Mettapedia.Logic.Arithmetic.ReachCertificate
