import Mettapedia.Logic.Arithmetic.BuchiAutomaton
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRootBuchiAuthority
import Mathlib.Data.Fintype.Card

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Büchi recurrence, shared with memoryless controllers

`RunAccepts` is the same predicate as `InfinitelyOftenAccepting`. A memoryless
controller wins when every execution of its selected transitions satisfies that
predicate. A nondeterministic Büchi automaton accepts when some letter-driven
run does. Those quantifiers are different. The identity below records only the
shared path predicate, so the ω-automaton development does not introduce a
second recurrence.

`controllerNBA` is the automaton of one deterministic controller. Its only
start state is the selected root. An edge carries the selected action to the
selected successor when the source is active and the labelled system admits
that step. Acceptance is the system's accepting predicate.
`controllerNBA_accepts_iff` says this automaton accepts the word of selected
actions exactly when the root recurrence claim holds.

`controllerLassoWithin` searches that canonical execution up to a supplied time
bound, by `List.findSome?` on `List.range`. For a finite carrier the bound
`Fintype.card State` is enough. `rootCheck_retained_lasso` reads an accepted
root certificate and returns a lasso that `Lasso.check` accepts and that the
retained `lassoChecker` finishes as accepted. The search is that finite
enumeration. The proof that a root-winning controller meets the bound uses the
pigeonhole principle on the state set.
-/

namespace Mettapedia.Logic.Arithmetic.BuchiAutomaton

set_option autoImplicit false

theorem RunAccepts_iff_infinitelyOften {σ : Type} (accept : σ → Bool) (path : Nat → σ) :
    RunAccepts accept path ↔
      InfinitelyOftenAccepting
        (⟨fun _ _ _ => true, accept⟩ : LabeledSystem σ Unit) path :=
  Iff.rfl

#print axioms RunAccepts_iff_infinitelyOften

/-- The letter at time `n` is the action selected at the `n`th state of the
canonical execution. -/
def controllerWord {State Action : Type}
    (controller : MemorylessController State Action) (root : State) (n : Nat) : Action :=
  controller.action (controller.next^[n] root)

/-- The Büchi automaton of one deterministic controller. -/
def controllerNBA {State Action : Type} [DecidableEq State] [DecidableEq Action]
    (system : LabeledSystem State Action)
    (claim : BuchiControllerClaim State Action) : NBA Action State where
  start s := decide (s = claim.root)
  accept := system.accepting
  step s a t :=
    decide (a = claim.controller.action s) &&
      decide (t = claim.controller.next s) &&
      claim.controller.active s &&
      system.step s a t

theorem controllerNBA_step_selected
    {State Action : Type} [DecidableEq State] [DecidableEq Action]
    (system : LabeledSystem State Action)
    (claim : BuchiControllerClaim State Action)
    {s : State} {a : Action} {t : State}
    (ha : a = claim.controller.action s)
    (ht : t = claim.controller.next s)
    (hactive : claim.controller.active s = true)
    (hstep : system.step s a t = true) :
    (controllerNBA system claim).step s a t = true := by
  unfold controllerNBA
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hstep⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hactive⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · rw [ha]
    exact decide_eq_true rfl
  · rw [ht]
    exact decide_eq_true rfl

theorem controllerNBA_canonical_step
    {State Action : Type} [DecidableEq State] [DecidableEq Action]
    {system : LabeledSystem State Action}
    {claim : BuchiControllerClaim State Action}
    (legal : ∀ index,
      claim.controller.active (claim.controller.next^[index] claim.root) = true ∧
        system.step (claim.controller.next^[index] claim.root)
          (claim.controller.action (claim.controller.next^[index] claim.root))
          (claim.controller.next (claim.controller.next^[index] claim.root)) = true)
    (n : Nat) :
    (controllerNBA system claim).step
      (claim.controller.next^[n] claim.root)
      (controllerWord claim.controller claim.root n)
      (claim.controller.next^[n + 1] claim.root) = true := by
  have hiter := Function.iterate_succ_apply' claim.controller.next n claim.root
  rw [Nat.succ_eq_add_one] at hiter
  apply controllerNBA_step_selected
  · rfl
  · exact hiter
  · exact (legal n).1
  · simpa [controllerWord, hiter] using (legal n).2

/-- Acceptance of the selected word is the root recurrence claim. -/
theorem controllerNBA_accepts_iff
    {State Action : Type} [DecidableEq State] [DecidableEq Action]
    (system : LabeledSystem State Action)
    (claim : BuchiControllerClaim State Action) :
    Accepts (controllerNBA system claim)
        (controllerWord claim.controller claim.root) ↔
      claim.RootMeaning system := by
  constructor
  · intro accepted
    obtain ⟨path, hstart, hstep, hacc⟩ := accepted
    have hpath : ∀ n, path n = claim.controller.next^[n] claim.root := by
      intro n
      induction n with
      | zero =>
        unfold controllerNBA at hstart
        exact (decide_eq_true_eq).mp hstart
      | succ n ih =>
        have hs := hstep n
        unfold controllerNBA at hs
        simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hs
        rw [hs.1.1.2, ih]
        exact (Function.iterate_succ_apply' claim.controller.next n claim.root).symm
    constructor
    · intro index
      have hs := hstep index
      unfold controllerNBA controllerWord at hs
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hs
      have hnext := Function.iterate_succ_apply' claim.controller.next index claim.root
      rw [Nat.succ_eq_add_one] at hnext
      rw [hpath index, hpath (index + 1), hnext] at hs
      exact ⟨hs.1.2, hs.2⟩
    · rw [MemorylessController.buchi_iff_canonical]
      intro lowerBound
      obtain ⟨visit, hv, haccv⟩ := hacc lowerBound
      rw [hpath visit] at haccv
      unfold controllerNBA at haccv
      exact ⟨visit, hv, haccv⟩
  · intro meaning
    refine ⟨fun n => claim.controller.next^[n] claim.root, ?_,
      controllerNBA_canonical_step meaning.1, ?_⟩
    · unfold controllerNBA
      exact decide_eq_true rfl
    · have hrec := meaning.2
      rw [MemorylessController.buchi_iff_canonical] at hrec
      exact hrec

#print axioms controllerNBA_accepts_iff

/-! ## Bounded search for a lasso on the canonical execution -/

theorem controllerPath_add_period {α : Type} (f : α → α) {a : α} {i d : Nat}
    (h : f^[i + d] a = f^[i] a) (q : Nat) :
    f^[i + q * d] a = f^[i] a := by
  induction q with
  | zero =>
    rw [Nat.zero_mul, Nat.add_zero]
  | succ q ih =>
    have hidx : i + (q + 1) * d = d + (i + q * d) := by
      calc i + (q + 1) * d
          = i + (q * d + 1 * d) := by rw [Nat.add_mul]
        _ = i + (q * d + d) := by rw [Nat.one_mul]
        _ = i + q * d + d := by rw [Nat.add_assoc]
        _ = d + (i + q * d) := Nat.add_comm _ _
    rw [hidx, Function.iterate_add_apply, ih, ← Function.iterate_add_apply,
      Nat.add_comm d i, h]

theorem controllerPath_mod_period {α : Type} (f : α → α) {a : α} {i d : Nat}
    (h : f^[i + d] a = f^[i] a) (m : Nat) :
    f^[i + m] a = f^[i + m % d] a := by
  have hsplit : m = d * (m / d) + m % d := (Nat.div_add_mod m d).symm
  have hidx : i + (d * (m / d) + m % d) = m % d + (i + (m / d) * d) := by
    rw [Nat.mul_comm d (m / d), ← Nat.add_assoc]
    exact Nat.add_comm _ _
  have hidx2 : i + m % d = m % d + i := Nat.add_comm _ _
  have hleft : i + m = m % d + (i + (m / d) * d) := by
    conv_lhs => rw [hsplit]
    exact hidx
  rw [hleft, Function.iterate_add_apply, controllerPath_add_period f h (m / d),
    hidx2, Function.iterate_add_apply]

theorem controllerPath_shift {α : Type} (f : α → α) {a : α} {i d k : Nat}
    (h : f^[i + d] a = f^[i] a) :
    f^[i + k + d] a = f^[i + k] a := by
  have hidx : i + k + d = k + (i + d) := by omega
  rw [hidx, Function.iterate_add_apply, h, Nat.add_comm i k, ← Function.iterate_add_apply]

/-- The first accepting offset in `len` steps, counting from `start`. -/
def findAcceptOffset {State Action : Type}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (root : State) (start len : Nat) : Option Nat :=
  (List.range len).findSome? fun k =>
    if system.accepting (controller.next^[start + k] root) = true then some k else none

theorem findAcceptOffset_spec
    {State Action : Type}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action}
    {root : State} {start len k : Nat}
    (h : findAcceptOffset system controller root start len = some k) :
    k < len ∧ system.accepting (controller.next^[start + k] root) = true := by
  unfold findAcceptOffset at h
  obtain ⟨k0, hk0, hk⟩ := List.exists_of_findSome?_eq_some h
  by_cases hacc : system.accepting (controller.next^[start + k0] root) = true
  · rw [if_pos hacc] at hk
    injection hk with hkEq
    rw [hkEq] at hk0 hacc
    exact ⟨List.mem_range.mp hk0, hacc⟩
  · rw [if_neg hacc] at hk
    cases hk

/-- Search times `0 … bound` for a repeated canonical state and an accepting
offset on the segment between the two visits. -/
def findClosedCycle {State Action : Type} [DecidableEq State]
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (root : State) (bound : Nat) : Option (Nat × Nat × Nat) :=
  (List.range (bound + 1)).findSome? fun j =>
    (List.range j).findSome? fun i =>
      if controller.next^[i] root = controller.next^[j] root then
        (findAcceptOffset system controller root i (j - i)).map fun k => (i, j, k)
      else
        none

theorem findClosedCycle_spec
    {State Action : Type} [DecidableEq State]
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action}
    {root : State} {bound i j k : Nat}
    (h : findClosedCycle system controller root bound = some (i, j, k)) :
    i < j ∧ j ≤ bound ∧
      controller.next^[i] root = controller.next^[j] root ∧
      k < j - i ∧
      system.accepting (controller.next^[i + k] root) = true := by
  unfold findClosedCycle at h
  obtain ⟨j0, hj0, hj⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨i0, hi0, hi⟩ := List.exists_of_findSome?_eq_some hj
  by_cases heq : controller.next^[i0] root = controller.next^[j0] root
  · rw [if_pos heq] at hi
    cases hoff : findAcceptOffset system controller root i0 (j0 - i0) with
    | none =>
      rw [hoff, Option.map_none] at hi
      cases hi
    | some k0 =>
      rw [hoff, Option.map_some] at hi
      injection hi with htrip
      obtain ⟨rfl, hrest⟩ := Prod.ext_iff.mp htrip
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hrest
      have hoffSpec := findAcceptOffset_spec hoff
      exact ⟨List.mem_range.mp hi0, Nat.le_of_lt_succ (List.mem_range.mp hj0), heq,
        hoffSpec.1, hoffSpec.2⟩
  · rw [if_neg heq] at hi
    cases hi

/-- On a finite carrier the canonical execution repeats by time
`Fintype.card State`, and root recurrence puts an accepting state on that
segment. The enumeration is `findClosedCycle`; this existence proof uses the
pigeonhole principle. -/
theorem findClosedCycle_isSome
    {State Action : Type} [Fintype State] [DecidableEq State]
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action} {root : State}
    (winning : controller.BuchiWinning system root)
    {bound : Nat} (hbound : Fintype.card State ≤ bound) :
    (findClosedCycle system controller root bound).isSome = true := by
  let n := Fintype.card State
  obtain ⟨x, y, hxy, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun p : Fin (n + 1) => controller.next^[p.val] root)
      (by rw [Fintype.card_fin]; exact Nat.lt_succ_self n)
  have hval : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  let i := min x.val y.val
  let j := max x.val y.val
  have hij : i < j := by
    rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
    · rw [show i = x.val from Nat.min_eq_left (Nat.le_of_lt hlt),
        show j = y.val from Nat.max_eq_right (Nat.le_of_lt hlt)]
      exact hlt
    · rw [show i = y.val from Nat.min_eq_right (Nat.le_of_lt hgt),
        show j = x.val from Nat.max_eq_left (Nat.le_of_lt hgt)]
      exact hgt
  have hjb : j ≤ bound := by
    have hx : x.val ≤ n := Nat.le_of_lt_succ x.isLt
    have hy : y.val ≤ n := Nat.le_of_lt_succ y.isLt
    have hjn : j ≤ n := by
      rcases Nat.le_total x.val y.val with hle | hle
      · rw [show j = y.val from Nat.max_eq_right hle]
        exact hy
      · rw [show j = x.val from Nat.max_eq_left hle]
        exact hx
    exact Nat.le_trans hjn hbound
  have hsame : controller.next^[i] root = controller.next^[j] root := by
    rcases Nat.le_total x.val y.val with hle | hle
    · rw [show i = x.val from Nat.min_eq_left hle,
        show j = y.val from Nat.max_eq_right hle]
      exact hf
    · rw [show i = y.val from Nat.min_eq_right hle,
        show j = x.val from Nat.max_eq_left hle]
      exact hf.symm
  rw [MemorylessController.buchi_iff_canonical] at winning
  obtain ⟨visit, hvisit, hacc⟩ := winning i
  let d := j - i
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  have hper : controller.next^[i + d] root = controller.next^[i] root := by
    rw [show i + d = j from Nat.add_sub_of_le (Nat.le_of_lt hij)]
    exact hsame.symm
  let r := (visit - i) % d
  have hr : r < d := Nat.mod_lt _ hd
  have haccR : system.accepting (controller.next^[i + r] root) = true := by
    have hm := controllerPath_mod_period controller.next hper (visit - i)
    have hidx : i + (visit - i) = visit := Nat.add_sub_of_le hvisit
    rw [hidx] at hm
    rw [← hm]
    exact hacc
  have hoff : (findAcceptOffset system controller root i d).isSome = true := by
    rw [findAcceptOffset, List.findSome?_isSome_iff]
    refine ⟨r, List.mem_range.mpr hr, ?_⟩
    rw [if_pos haccR]
    exact Option.isSome_some
  rw [findClosedCycle, List.findSome?_isSome_iff]
  refine ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hjb), ?_⟩
  rw [List.findSome?_isSome_iff]
  refine ⟨i, List.mem_range.mpr hij, ?_⟩
  rw [if_pos hsame]
  cases hopt : findAcceptOffset system controller root i d with
  | none =>
    rw [hopt, Option.isSome_none] at hoff
    cases hoff
  | some k =>
    rfl

#print axioms findClosedCycle_isSome

theorem runSeg_ne_nil {α σ : Type} (w : Nat → α) (path : Nat → σ) (i d : Nat)
    (hd : 0 < d) : runSeg w path i d ≠ [] := by
  cases d with
  | zero => omega
  | succ d =>
    rw [runSeg]
    exact List.cons_ne_nil _ _

/-- The lasso whose stem reaches the accepting offset and whose loop is one
period of the repeated canonical segment. -/
def controllerLassoOf {State Action : Type}
    (claim : BuchiControllerClaim State Action) (i j k : Nat) : Lasso Action State where
  startState := claim.root
  stem := runSeg (controllerWord claim.controller claim.root)
    (fun n => claim.controller.next^[n] claim.root) 0 (i + k)
  loop := runSeg (controllerWord claim.controller claim.root)
    (fun n => claim.controller.next^[n] claim.root) (i + k) (j - i)

/-- Return the lasso found inside `bound`, when the search succeeds. -/
def controllerLassoWithin {State Action : Type} [DecidableEq State]
    (system : LabeledSystem State Action)
    (claim : BuchiControllerClaim State Action) (bound : Nat) : Option (Lasso Action State) :=
  (findClosedCycle system claim.controller claim.root bound).map fun (i, j, k) =>
    controllerLassoOf claim i j k

#print axioms controllerLassoWithin

theorem controllerLassoOf_check
    {State Action : Type} [DecidableEq State] [DecidableEq Action]
    {system : LabeledSystem State Action}
    {claim : BuchiControllerClaim State Action}
    (meaning : claim.RootMeaning system)
    {i j k : Nat}
    (hij : i < j)
    (hsame : claim.controller.next^[i] claim.root =
      claim.controller.next^[j] claim.root)
    (hacc : system.accepting (claim.controller.next^[i + k] claim.root) = true) :
    (controllerLassoOf claim i j k).check (controllerNBA system claim) = true := by
  let path : Nat → State := fun n => claim.controller.next^[n] claim.root
  let word : Nat → Action := controllerWord claim.controller claim.root
  let A : NBA Action State := controllerNBA system claim
  let L : Lasso Action State := controllerLassoOf claim i j k
  have hstep : ∀ n, A.step (path n) (word n) (path (n + 1)) = true :=
    controllerNBA_canonical_step meaning.1
  have hrunStem := runSeg_valid A word path hstep 0 (i + k)
  have hrunLoop := runSeg_valid A word path hstep (i + k) (j - i)
  have hstemEnd : chainEnd L.startState L.stem = path (i + k) := by
    calc chainEnd L.startState L.stem
        = chainEnd (path 0) (runSeg word path 0 (i + k)) := rfl
      _ = path (0 + (i + k)) := hrunStem.2
      _ = path (i + k) := by rw [Nat.zero_add]
  have hper : claim.controller.next^[i + (j - i)] claim.root =
      claim.controller.next^[i] claim.root := by
    rw [Nat.add_sub_of_le (Nat.le_of_lt hij)]
    exact hsame.symm
  have hstemBool : chainValidBool A L.startState L.stem = true :=
    (chainValidBool_iff A _ _).mpr hrunStem.1
  have hloopBool : chainValidBool A (chainEnd L.startState L.stem) L.loop = true := by
    apply (chainValidBool_iff A _ _).mpr
    rw [hstemEnd]
    exact hrunLoop.1
  have hclose : chainEnd (chainEnd L.startState L.stem) L.loop =
      chainEnd L.startState L.stem := by
    rw [hstemEnd]
    calc chainEnd (path (i + k)) L.loop
        = chainEnd (path (i + k)) (runSeg word path (i + k) (j - i)) := rfl
      _ = path ((i + k) + (j - i)) := hrunLoop.2
      _ = path (i + k) := controllerPath_shift claim.controller.next hper
  have hempty : L.loop.isEmpty = false := by
    have hd : 0 < j - i := Nat.sub_pos_of_lt hij
    cases hlen : j - i with
    | zero => omega
    | succ n =>
      rw [show L.loop = runSeg word path (i + k) (j - i) from rfl, hlen, runSeg]
      rfl
  have haccept : A.accept (chainEnd L.startState L.stem) = true := by
    rw [hstemEnd]
    exact hacc
  have hstart : A.start L.startState = true := by
    unfold A controllerNBA L controllerLassoOf
    exact decide_eq_true rfl
  simp only [Lasso.check, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hstart, hstemBool⟩, hempty⟩, hloopBool⟩, hclose⟩, haccept⟩

/-- A legal recurrent root, searched through at least one full set of states,
yields a checked lasso and a retained run that finishes accepted. -/
theorem controllerLassoWithin_of_meaning
    {State Action : Type} [DecidableEq State] [DecidableEq Action] [Fintype State]
    {system : LabeledSystem State Action}
    {claim : BuchiControllerClaim State Action}
    (meaning : claim.RootMeaning system)
    {bound : Nat} (hbound : Fintype.card State ≤ bound) :
    ∃ L : Lasso Action State,
      controllerLassoWithin system claim bound = some L ∧
      L.check (controllerNBA system claim) = true ∧
      lassoChecker.run (lassoBudget L.stem L.loop)
        (Lasso.checkpoint (controllerNBA system claim) L) =
        (L.stem ++ L.loop, .finished true) := by
  have hrec : (findClosedCycle system claim.controller claim.root bound).isSome = true :=
    findClosedCycle_isSome meaning.2 hbound
  cases hcycle : findClosedCycle system claim.controller claim.root bound with
  | none =>
    rw [hcycle, Option.isSome_none] at hrec
    cases hrec
  | some triple =>
    obtain ⟨i, j, k⟩ := triple
    obtain ⟨hij, _, hsame, _, hacc⟩ := findClosedCycle_spec hcycle
    let L := controllerLassoOf claim i j k
    have hfound : controllerLassoWithin system claim bound = some L := by
      rw [controllerLassoWithin, hcycle, Option.map_some]
    have hcheck := controllerLassoOf_check meaning hij hsame hacc
    exact ⟨L, hfound, hcheck, lassoChecker_of_check _ L hcheck⟩

#print axioms controllerLassoWithin_of_meaning

/-- An accepted finite root certificate is a retained accepting lasso on the
controller automaton. The search bound is the number of states. -/
theorem rootCheck_retained_lasso
    {State Action : Type} [DecidableEq State] [DecidableEq Action] [Fintype State]
    {system : LabeledSystem State Action}
    {claim : BuchiControllerClaim State Action}
    {certificate : RootBuchiCertificate State}
    (accepted : certificate.check system claim = true) :
    ∃ L : Lasso Action State,
      controllerLassoWithin system claim (Fintype.card State) = some L ∧
      L.check (controllerNBA system claim) = true ∧
      lassoChecker.run (lassoBudget L.stem L.loop)
        (Lasso.checkpoint (controllerNBA system claim) L) =
        (L.stem ++ L.loop, .finished true) :=
  controllerLassoWithin_of_meaning (certificate.check_sound accepted) (Nat.le_refl _)

#print axioms rootCheck_retained_lasso

/-! ## Three-state controls -/

def cycleNext : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 1

def cycleSystem : LabeledSystem (Fin 3) Unit where
  step s _ t := decide (t = cycleNext s)
  accepting s := decide (s = 1)

def cycleController : MemorylessController (Fin 3) Unit where
  active _ := true
  action _ := ()
  next := cycleNext

def cycleClaim : BuchiControllerClaim (Fin 3) Unit where
  root := 0
  controller := cycleController

def cycleCertificate : RootBuchiCertificate (Fin 3) where
  region _ := true
  progress := ⟨fun _ => 0⟩

/-- Stem `0 → 1`, then the accepting cycle `1 → 2 → 1`. -/
def cycleLasso : Lasso Unit (Fin 3) where
  startState := 0
  stem := [((), 1)]
  loop := [((), 2), ((), 1)]

set_option maxHeartbeats 2000000 in
theorem control_cycle_root_check :
    cycleCertificate.check cycleSystem cycleClaim = true := by
  decide

set_option maxHeartbeats 2000000 in
theorem control_cycle_lasso_check :
    cycleLasso.check (controllerNBA cycleSystem cycleClaim) = true := by
  decide

theorem control_cycle_lasso_run :
    lassoChecker.run (lassoBudget cycleLasso.stem cycleLasso.loop)
      (Lasso.checkpoint (controllerNBA cycleSystem cycleClaim) cycleLasso) =
      (cycleLasso.stem ++ cycleLasso.loop, .finished true) := by
  rfl

theorem control_cycle_lasso_found :
    controllerLassoWithin cycleSystem cycleClaim (Fintype.card (Fin 3)) = some cycleLasso := by
  rw [Fintype.card_fin]
  rfl

theorem control_cycle_lasso_found_at_bound :
    controllerLassoWithin cycleSystem cycleClaim 3 = some cycleLasso := by
  rfl

theorem lassoWord_unit {σ : Type} (stem loop : List (Unit × σ)) (hloop : loop ≠ []) :
    lassoWord stem loop hloop = fun _ => () := by
  funext n
  unfold lassoWord
  split
  · next hlt =>
    cases (stem.get ⟨n, hlt⟩).1
    rfl
  · next hlt =>
    cases (loop.get ⟨(n - stem.length) % loop.length,
      Nat.mod_lt _ (listLength_pos_of_ne hloop)⟩).1
    rfl

theorem control_cycle_selected_accepts :
    Accepts (controllerNBA cycleSystem cycleClaim)
      (controllerWord cycleController 0) := by
  obtain ⟨hloop, hacc⟩ := Lasso.check_accepts
    (controllerNBA cycleSystem cycleClaim) cycleLasso control_cycle_lasso_check
  have hw := lassoWord_unit cycleLasso.stem cycleLasso.loop hloop
  have hc : controllerWord cycleController 0 = fun _ => () := by
    funext n
    rfl
  rw [hw, ← hc] at hacc
  exact hacc

#print axioms control_cycle_lasso_run
#print axioms control_cycle_lasso_found
#print axioms control_cycle_lasso_found_at_bound
#print axioms control_cycle_selected_accepts

/-- State `2` is an active nonaccepting self-loop, unreachable from the root. -/
def sideNext : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 1
  | 2 => 2

def sideSystem : LabeledSystem (Fin 3) Unit where
  step s _ t := decide (t = sideNext s)
  accepting s := decide (s = 1)

def sideController : MemorylessController (Fin 3) Unit where
  active _ := true
  action _ := ()
  next := sideNext

def sideClaim : BuchiControllerClaim (Fin 3) Unit where
  root := 0
  controller := sideController

def sideCertificate : RootBuchiCertificate (Fin 3) where
  region s := decide (s ≠ 2)
  progress := ⟨fun _ => 0⟩

def sideLasso : Lasso Unit (Fin 3) where
  startState := 0
  stem := [((), 1)]
  loop := [((), 1)]

def sideBadLasso : Lasso Unit (Fin 3) where
  startState := 2
  stem := []
  loop := [((), 2)]

set_option maxHeartbeats 2000000 in
theorem control_side_root_check :
    sideCertificate.check sideSystem sideClaim = true := by
  decide

set_option maxHeartbeats 2000000 in
theorem control_side_global_refused :
    (⟨fun _ => 0⟩ : ProgressMeasure (Fin 3)).check sideSystem sideController 0 = false := by
  decide

theorem control_side_no_progress :
    ¬ ∃ measure : ProgressMeasure (Fin 3),
      measure.Valid sideSystem sideController 0 := by
  rintro ⟨measure, valid⟩
  have impossible := valid.2 (2 : Fin 3) rfl
  have hacc : sideSystem.accepting (2 : Fin 3) = false := by decide
  have haccTrue : ¬ sideSystem.accepting (2 : Fin 3) = true := by
    rw [hacc]
    exact Bool.false_ne_true
  rw [if_neg haccTrue] at impossible
  have hnext : sideController.next (2 : Fin 3) = 2 := rfl
  rw [hnext] at impossible
  have haccNext : sideSystem.accepting (2 : Fin 3) = false := by decide
  rw [haccNext] at impossible
  rcases impossible with h | h
  · cases h
  · exact Nat.lt_irrefl _ h

set_option maxHeartbeats 2000000 in
theorem control_side_lasso_check :
    sideLasso.check (controllerNBA sideSystem sideClaim) = true := by
  decide

theorem control_side_lasso_run :
    lassoChecker.run (lassoBudget sideLasso.stem sideLasso.loop)
      (Lasso.checkpoint (controllerNBA sideSystem sideClaim) sideLasso) =
      (sideLasso.stem ++ sideLasso.loop, .finished true) := by
  rfl

theorem control_side_lasso_found :
    controllerLassoWithin sideSystem sideClaim (Fintype.card (Fin 3)) = some sideLasso := by
  rw [Fintype.card_fin]
  rfl

theorem control_side_lasso_found_at_bound :
    controllerLassoWithin sideSystem sideClaim 3 = some sideLasso := by
  rfl

set_option maxHeartbeats 2000000 in
theorem control_side_bad_lasso_check :
    sideBadLasso.check (controllerNBA sideSystem sideClaim) = false := by
  decide

theorem control_side_bad_lasso_run :
    lassoChecker.run (lassoBudget sideBadLasso.stem sideBadLasso.loop)
      (Lasso.checkpoint (controllerNBA sideSystem sideClaim) sideBadLasso) =
      ([], .faulted) := by
  rfl

theorem control_side_unreachable_edge :
    (controllerNBA sideSystem sideClaim).step 2 () 2 = true := by
  decide

#print axioms control_side_root_check
#print axioms control_side_no_progress
#print axioms control_side_lasso_found_at_bound
#print axioms control_side_bad_lasso_run

/-- The selected edge `1 → 2` is absent from the labelled system. -/
def illegalSystem : LabeledSystem (Fin 3) Unit where
  step s _ t := decide (t = cycleNext s) && decide (s ≠ 1)
  accepting s := decide (s = 1)

def illegalClaim : BuchiControllerClaim (Fin 3) Unit := cycleClaim

theorem control_illegal_edge :
    illegalSystem.step 1 () 2 = false := by
  decide

theorem control_illegal_not_meaning :
    ¬ illegalClaim.RootMeaning illegalSystem := by
  intro meaning
  have h := (meaning.1 1).2
  have hstate : illegalClaim.controller.next^[1] illegalClaim.root = 1 := by
    rw [illegalClaim, cycleClaim, cycleController, Function.iterate_one]
    rfl
  rw [hstate] at h
  have hnext : illegalClaim.controller.next 1 = 2 := by
    rw [illegalClaim, cycleClaim, cycleController]
    rfl
  have haction : illegalClaim.controller.action 1 = () := rfl
  rw [hnext, haction, control_illegal_edge] at h
  cases h

theorem control_illegal_certificate (certificate : RootBuchiCertificate (Fin 3)) :
    certificate.check illegalSystem illegalClaim = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  exact control_illegal_not_meaning (certificate.check_sound accepted)

set_option maxHeartbeats 2000000 in
theorem control_illegal_lasso :
    cycleLasso.check (controllerNBA illegalSystem illegalClaim) = false := by
  decide

/-- The stem `0 → 1` is published. The loop edge `1 → 2` is the illegal step,
so the run faults with the stem alone. -/
theorem control_illegal_run :
    lassoChecker.run (lassoBudget cycleLasso.stem cycleLasso.loop)
      (Lasso.checkpoint (controllerNBA illegalSystem illegalClaim) cycleLasso) =
      (cycleLasso.stem, .faulted) := by
  rfl

#print axioms control_illegal_not_meaning
#print axioms control_illegal_certificate
#print axioms control_illegal_run

end Mettapedia.Logic.Arithmetic.BuchiAutomaton
