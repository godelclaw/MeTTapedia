import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Basic

/-!
# Büchi automata over ω-words

Nondeterministic Büchi automata, in the sense of J. Richard Büchi, *On a Decision
Method in Restricted Second Order Arithmetic* (1962). An ω-word is a function
`ℕ → α`. A run accepts when an accepting state occurs beyond every finite prefix.
That recurrence predicate is the same one used for memoryless controllers; the
identity is recorded alongside the controller development.

Emptiness is decidable. A positive certificate is a lasso: a finite stem from a
start state to a pivot, and a nonempty cycle on that pivot, with the pivot
accepting. Checking a lasso reads the two lists once. A negative answer is the
Boolean reachability closure: no accepting state that is reachable from a start
state lies on a cycle.

`lassoChecker` runs that same check on the retained-execution machine. The
checkpoint stores the automaton, the current stem or loop edge, the pivot, the
current state, the remaining certificate and the verdict. Each primitive step
examines one supplied edge. A finished run agrees with `Lasso.check`. Refusal,
an exhausted budget and resumption of the saved checkpoint are separate
outcomes. The transition account charges a supplied price for each primitive
step; the certificate edge count is the length of the published list.

Union, intersection, and alphabet projection are proved correct for the accepted
language. Intersection uses the two-phase product: phase `0` waits for an
accepting state of the first automaton, phase `1` waits for one of the second,
and a product state is accepting when phase `0` sits on an accepting state of
the first automaton.

On the run DAG of a word, a vertex is endangered when only finitely many
vertices are reachable from it, and safe when no accepting vertex is reachable
from it. These two kinds of vertex are deleted in alternating rounds, following
Orna Kupferman and Moshe Y. Vardi, *Complementation Constructions for
Nondeterministic Automata on Infinite Words* (2005). `complement A` carries a
rank guess in `0, …, 2|Q|` and a breakpoint obligation on the even ranks.
`accepts_complement` states that this automaton accepts a word exactly when `A`
rejects that word. `finComplement` decides that same relation by a Boolean
matrix on codes in `Fin (guessCard n)`. `toRankGuess` reads a code as a
`RankGuess`, and `accepts_finComplement` transports acceptance through
`accepts_complement`.

## Open goal

Büchi's theorem for the whole monadic second-order language over `(ℕ, succ)`
is not proved in this file.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.BuchiAutomaton

/-- A nondeterministic Büchi automaton. `step s a t = true` means an edge
`s -a→ t`. -/
structure NBA (α σ : Type) where
  step : σ → α → σ → Bool
  start : σ → Bool
  accept : σ → Bool

/-- Accepting states occur beyond every finite prefix. -/
def RunAccepts {σ : Type} (accept : σ → Bool) (path : Nat → σ) : Prop :=
  ∀ lowerBound, ∃ visit, lowerBound ≤ visit ∧ accept (path visit) = true

/-- `A` accepts `w` when some run reads `w` and visits accepting states
infinitely often. -/
def Accepts {α σ : Type} (A : NBA α σ) (w : Nat → α) : Prop :=
  ∃ path : Nat → σ,
    A.start (path 0) = true ∧
    (∀ n, A.step (path n) (w n) (path (n + 1)) = true) ∧
    RunAccepts A.accept path

variable {α σ : Type}

def listAny {β : Type} (p : β → Bool) : List β → Bool
  | [] => false
  | b :: bs => p b || listAny p bs

theorem listAny_iff {β : Type} (p : β → Bool) :
    ∀ l : List β, listAny p l = true ↔ ∃ b ∈ l, p b = true
  | [] => by simp [listAny]
  | b :: bs => by
      rw [listAny, Bool.or_eq_true]
      constructor
      · intro h
        rcases h with hp | hrest
        · exact ⟨b, List.Mem.head _, hp⟩
        · rw [listAny_iff p bs] at hrest
          obtain ⟨c, hc, hpc⟩ := hrest
          exact ⟨c, List.Mem.tail _ hc, hpc⟩
      · intro h
        obtain ⟨c, hc, hpc⟩ := h
        rw [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact Or.inl hpc
        · exact Or.inr ((listAny_iff p bs).mpr ⟨c, hc, hpc⟩)

/-- A computable listing of every element. `Finset.toList` is avoided because
that representative of a multiset quotient is not computable. -/
class Enumerable (β : Type) where
  elems : List β
  mem_elems : ∀ b : β, b ∈ elems

theorem listLength_pos_of_ne {β : Type} {l : List β} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- A finite walk stored as successive labelled arrivals. -/
def chainValid (A : NBA α σ) : σ → List (α × σ) → Prop
  | _, [] => True
  | s, (a, q) :: rest => A.step s a q = true ∧ chainValid A q rest

def chainEnd : σ → List (α × σ) → σ
  | s, [] => s
  | _, (_, q) :: rest => chainEnd q rest

def chainNth (s : σ) (e : List (α × σ)) : Nat → σ
  | 0 => s
  | i + 1 =>
    match e with
    | [] => s
    | (_, q) :: rest => chainNth q rest i

def chainValidBool (A : NBA α σ) : σ → List (α × σ) → Bool
  | _, [] => true
  | s, (a, q) :: rest => A.step s a q && chainValidBool A q rest

@[simp] theorem chainEnd_nil (s : σ) : chainEnd s ([] : List (α × σ)) = s := rfl

@[simp] theorem chainNth_zero (s : σ) (e : List (α × σ)) : chainNth s e 0 = s := by
  cases e <;> rfl

theorem chainNth_length (s : σ) (e : List (α × σ)) :
    chainNth s e e.length = chainEnd s e := by
  induction e generalizing s with
  | nil => rfl
  | cons edge rest ih =>
    obtain ⟨a, q⟩ := edge
    simpa [chainNth, chainEnd, Nat.succ_eq_add_one] using ih q

theorem chainValidBool_iff (A : NBA α σ) (s : σ) (e : List (α × σ)) :
    chainValidBool A s e = true ↔ chainValid A s e := by
  induction e generalizing s with
  | nil => simp [chainValidBool, chainValid]
  | cons edge rest ih =>
    obtain ⟨a, q⟩ := edge
    rw [chainValidBool, chainValid, Bool.and_eq_true, ih q]

theorem chain_edge (A : NBA α σ) {s : σ} {e : List (α × σ)}
    (hv : chainValid A s e) {i : Nat} (hi : i < e.length) :
    A.step (chainNth s e i) (e.get ⟨i, hi⟩).1 (e.get ⟨i, hi⟩).2 = true ∧
      chainNth s e (i + 1) = (e.get ⟨i, hi⟩).2 := by
  induction e generalizing s i with
  | nil => cases hi
  | cons edge rest ih =>
    obtain ⟨a, q⟩ := edge
    cases i with
    | zero =>
      rcases hv with ⟨hstep, _⟩
      simp [chainNth, hstep]
    | succ i =>
      rcases hv with ⟨_, hv⟩
      simpa [chainNth] using ih hv (Nat.lt_of_succ_lt_succ hi)

theorem chainValid_take (A : NBA α σ) {s : σ} {e : List (α × σ)}
    (hv : chainValid A s e) (i : Nat) (hi : i ≤ e.length) :
    chainValid A s (e.take i) ∧ chainEnd s (e.take i) = chainNth s e i := by
  induction e generalizing s i with
  | nil =>
    have : i = 0 := Nat.le_zero.mp hi
    subst i
    simp [chainValid, chainNth]
  | cons edge rest ih =>
    obtain ⟨a, q⟩ := edge
    cases i with
    | zero => simp [chainValid, chainNth]
    | succ i =>
      rcases hv with ⟨hstep, hv⟩
      have hi' : i ≤ rest.length := by
        simpa using hi
      obtain ⟨hv', hend'⟩ := ih hv i hi'
      simp [chainValid, chainEnd, chainNth, hstep, hv', hend']

theorem chainValid_drop (A : NBA α σ) {s : σ} {e : List (α × σ)}
    (hv : chainValid A s e) (j : Nat) (hj : j ≤ e.length) :
    chainValid A (chainNth s e j) (e.drop j) ∧
      chainEnd (chainNth s e j) (e.drop j) = chainEnd s e := by
  induction e generalizing s j with
  | nil =>
    have : j = 0 := Nat.le_zero.mp hj
    subst j
    simp [chainNth, chainEnd, chainValid]
  | cons edge rest ih =>
    obtain ⟨a, q⟩ := edge
    cases j with
    | zero =>
      simp [chainNth, chainEnd, hv]
    | succ j =>
      rcases hv with ⟨_, hv⟩
      have hj' : j ≤ rest.length := by
        simpa using hj
      simpa [chainNth, chainEnd] using ih hv j hj'

theorem chainValid_append (A : NBA α σ) {s : σ} {e1 e2 : List (α × σ)}
    (hv1 : chainValid A s e1) (hv2 : chainValid A (chainEnd s e1) e2) :
    chainValid A s (e1 ++ e2) ∧
      chainEnd s (e1 ++ e2) = chainEnd (chainEnd s e1) e2 := by
  induction e1 generalizing s with
  | nil =>
    have hv2' : chainValid A s e2 := by simpa [chainEnd_nil] using hv2
    exact ⟨hv2', by simp [chainEnd_nil]⟩
  | cons edge rest ih =>
    obtain ⟨a, q⟩ := edge
    rcases hv1 with ⟨hstep, hv1⟩
    obtain ⟨hv', hend'⟩ := ih hv1 hv2
    simp [chainValid, chainEnd, hstep, hv', hend']

theorem chainValid_splice (A : NBA α σ) {s : σ} {e : List (α × σ)}
    (hv : chainValid A s e) {i j : Nat} (hij : i ≤ j) (hj : j ≤ e.length)
    (heq : chainNth s e i = chainNth s e j) :
    chainValid A s (e.take i ++ e.drop j) ∧
      chainEnd s (e.take i ++ e.drop j) = chainEnd s e ∧
      (e.take i ++ e.drop j).length = e.length - (j - i) := by
  obtain ⟨hvTake, hendTake⟩ := chainValid_take A hv i (le_trans hij hj)
  obtain ⟨hvDrop, hendDrop⟩ := chainValid_drop A hv j hj
  have hv2 : chainValid A (chainEnd s (e.take i)) (e.drop j) := by
    simpa [hendTake, heq] using hvDrop
  obtain ⟨hvApp, hendApp⟩ := chainValid_append A hvTake hv2
  refine ⟨hvApp, ?_, ?_⟩
  · have hendDrop' : chainEnd (chainEnd s (e.take i)) (e.drop j) = chainEnd s e := by
      simpa [hendTake, heq] using hendDrop
    rw [hendApp, hendDrop']
  · rw [List.length_append, List.length_take, List.length_drop, Nat.min_eq_left (le_trans hij hj)]
    omega

/-- Edges that exist for at least one letter. -/
def hasEdge (A : NBA α σ) [Enumerable α] (s t : σ) : Bool :=
  listAny (fun a => A.step s a t) (Enumerable.elems : List α)

theorem hasEdge_iff (A : NBA α σ) [Enumerable α] (s t : σ) :
    hasEdge A s t = true ↔ ∃ a, A.step s a t = true := by
  rw [hasEdge, listAny_iff]
  constructor
  · rintro ⟨a, _, hstep⟩
    exact ⟨a, hstep⟩
  · rintro ⟨a, hstep⟩
    exact ⟨a, Enumerable.mem_elems a, hstep⟩

def oneStep (A : NBA α σ) [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ]
    (S : Finset σ) : Finset σ :=
  Finset.univ.filter fun t =>
    listAny (fun s => decide (s ∈ S) && hasEdge A s t) (Enumerable.elems : List σ) = true

theorem mem_oneStep_iff (A : NBA α σ) [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ]
    {S : Finset σ} {t : σ} :
    t ∈ oneStep A S ↔ ∃ s ∈ S, ∃ a, A.step s a t = true := by
  simp only [oneStep, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [listAny_iff]
  constructor
  · rintro ⟨s, _, hand⟩
    rw [Bool.and_eq_true] at hand
    exact ⟨s, of_decide_eq_true hand.1, (hasEdge_iff A s t).mp hand.2⟩
  · rintro ⟨s, hs, a, hstep⟩
    refine ⟨s, Enumerable.mem_elems s, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hs, (hasEdge_iff A s t).mpr ⟨a, hstep⟩⟩

/-- States reachable in at most `n` edges. Fuel `n = 0` is the seed set. -/
def close (A : NBA α σ) [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ] :
    Nat → Finset σ → Finset σ
  | 0, S => S
  | n + 1, S => close A n (S ∪ oneStep A S)

theorem mem_close_iff (A : NBA α σ) [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ]
    (n : Nat) (S : Finset σ) (q : σ) :
    q ∈ close A n S ↔
      ∃ s ∈ S, ∃ e : List (α × σ), e.length ≤ n ∧ chainValid A s e ∧ chainEnd s e = q := by
  induction n generalizing S with
  | zero =>
    constructor
    · intro hq
      exact ⟨q, hq, [], Nat.zero_le _, trivial, rfl⟩
    · rintro ⟨s, hs, e, hlen, _, hend⟩
      have hempty : e = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      subst hempty
      rw [chainEnd_nil] at hend
      subst hend
      simpa [close] using hs
  | succ n ih =>
    rw [close, ih]
    constructor
    · rintro ⟨s, hs, e, hlen, hv, hend⟩
      rw [Finset.mem_union] at hs
      rcases hs with hs | hs
      · exact ⟨s, hs, e, Nat.le_succ_of_le hlen, hv, hend⟩
      · rw [mem_oneStep_iff] at hs
        obtain ⟨s0, hs0, a, hstep⟩ := hs
        refine ⟨s0, hs0, (a, s) :: e, ?_, ⟨hstep, hv⟩, ?_⟩
        · simp [hlen]
        · simpa [chainEnd] using hend
    · rintro ⟨s, hs, e, hlen, hv, hend⟩
      cases e with
      | nil =>
        have hsEq : s = q := by simpa [chainEnd] using hend
        subst hsEq
        exact ⟨s, Finset.mem_union_left _ hs, [], Nat.zero_le _, trivial, rfl⟩
      | cons edge rest =>
        obtain ⟨a, s1⟩ := edge
        rcases hv with ⟨hstep, hv⟩
        have hend' : chainEnd s1 rest = q := by simpa [chainEnd] using hend
        have hs1 : s1 ∈ oneStep A S := by
          rw [mem_oneStep_iff]
          exact ⟨s, hs, a, hstep⟩
        have hlen' : rest.length ≤ n := by
          have : rest.length + 1 ≤ n + 1 := by simpa using hlen
          omega
        exact ⟨s1, Finset.mem_union_right _ hs1, rest, hlen', hv, hend'⟩

theorem shorten_reach (A : NBA α σ) [Fintype σ] {s q : σ} (e : List (α × σ))
    (hv : chainValid A s e) (hend : chainEnd s e = q) :
    ∃ e' : List (α × σ),
      e'.length ≤ Fintype.card σ ∧ chainValid A s e' ∧ chainEnd s e' = q := by
  refine Nat.strongRecOn e.length
    (motive := fun n => ∀ e : List (α × σ), e.length = n →
      chainValid A s e → chainEnd s e = q →
      ∃ e', e'.length ≤ Fintype.card σ ∧ chainValid A s e' ∧ chainEnd s e' = q)
    ?_ e rfl hv hend
  intro n ih e hlen hv hend
  by_cases hcard : e.length ≤ Fintype.card σ
  · exact ⟨e, hcard, hv, hend⟩
  · have hlt : Fintype.card σ < e.length := (Nat.not_le).mp hcard
    have hcardLt : Fintype.card σ < Fintype.card (Fin (e.length + 1)) := by
      simpa [Fintype.card_fin] using Nat.lt_succ_of_lt hlt
    obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (e.length + 1) => chainNth s e k.val) hcardLt
    have hvalne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hord : i.val < j.val ∨ j.val < i.val := Nat.lt_or_gt_of_ne hvalne
    let i0 : Nat := if i.val < j.val then i.val else j.val
    let j0 : Nat := if i.val < j.val then j.val else i.val
    have hi0j0 : i0 < j0 := by
      rcases hord with hlt' | hgt
      · simp [i0, j0, hlt']
      · have : ¬ i.val < j.val := Nat.not_lt_of_gt hgt
        simp [i0, j0, this, hgt]
    have hj0len : j0 ≤ e.length := by
      rcases hord with hlt' | hgt
      · have : j.val ≤ e.length := Nat.le_of_lt_succ j.isLt
        simp [j0, hlt', this]
      · have : i.val ≤ e.length := Nat.le_of_lt_succ i.isLt
        have : ¬ i.val < j.val := Nat.not_lt_of_gt hgt
        simp [j0, this, ‹i.val ≤ e.length›]
    have heq0 : chainNth s e i0 = chainNth s e j0 := by
      rcases hord with hlt' | hgt
      · simpa [i0, j0, hlt'] using heq
      · have : ¬ i.val < j.val := Nat.not_lt_of_gt hgt
        simpa [i0, j0, this] using heq.symm
    obtain ⟨hv', hend', hlen'⟩ :=
      chainValid_splice A hv (Nat.le_of_lt hi0j0) hj0len heq0
    have hshorter : (e.take i0 ++ e.drop j0).length < n := by
      rw [← hlen, hlen']
      have : 0 < j0 - i0 := Nat.sub_pos_of_lt hi0j0
      omega
    exact ih _ hshorter _ rfl hv' (hend'.trans hend)

theorem shorten_cycle (A : NBA α σ) [Fintype σ] {q : σ} (e : List (α × σ))
    (hne : e ≠ []) (hv : chainValid A q e) (hend : chainEnd q e = q) :
    ∃ e' : List (α × σ),
      e'.length ≤ Fintype.card σ ∧ e' ≠ [] ∧ chainValid A q e' ∧ chainEnd q e' = q := by
  refine Nat.strongRecOn e.length
    (motive := fun n => ∀ e : List (α × σ), e.length = n → e ≠ [] →
      chainValid A q e → chainEnd q e = q →
      ∃ e', e'.length ≤ Fintype.card σ ∧ e' ≠ [] ∧
        chainValid A q e' ∧ chainEnd q e' = q)
    ?_ e rfl hne hv hend
  intro n ih e hlen hne hv hend
  by_cases hcard : e.length ≤ Fintype.card σ
  · exact ⟨e, hcard, hne, hv, hend⟩
  · have hlt : Fintype.card σ < e.length := (Nat.not_le).mp hcard
    have hcardLt : Fintype.card σ < Fintype.card (Fin e.length) := by
      simpa [Fintype.card_fin] using hlt
    obtain ⟨i, j, hneij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin e.length => chainNth q e k.val) hcardLt
    have hvalne : i.val ≠ j.val := fun h => hneij (Fin.ext h)
    have hord : i.val < j.val ∨ j.val < i.val := Nat.lt_or_gt_of_ne hvalne
    let i0 : Nat := if i.val < j.val then i.val else j.val
    let j0 : Nat := if i.val < j.val then j.val else i.val
    have hi0j0 : i0 < j0 := by
      rcases hord with hlt' | hgt
      · simp [i0, j0, hlt']
      · have : ¬ i.val < j.val := Nat.not_lt_of_gt hgt
        simp [i0, j0, this, hgt]
    have hj0lt : j0 < e.length := by
      rcases hord with hlt' | hgt
      · simp [j0, hlt', j.isLt]
      · have : ¬ i.val < j.val := Nat.not_lt_of_gt hgt
        simp [j0, this, i.isLt]
    have heq0 : chainNth q e i0 = chainNth q e j0 := by
      rcases hord with hlt' | hgt
      · simpa [i0, j0, hlt'] using heq
      · have : ¬ i.val < j.val := Nat.not_lt_of_gt hgt
        simpa [i0, j0, this] using heq.symm
    obtain ⟨hv', hend', hlen'⟩ :=
      chainValid_splice A hv (Nat.le_of_lt hi0j0) (Nat.le_of_lt hj0lt) heq0
    have hlenPos : 1 ≤ e.length - (j0 - i0) := by
      have hj0le : j0 ≤ e.length - 1 := Nat.le_pred_of_lt hj0lt
      have hsub : j0 - i0 ≤ e.length - 1 := by
        have : j0 - i0 ≤ j0 := Nat.sub_le _ _
        omega
      omega
    have hshorter : (e.take i0 ++ e.drop j0).length < n := by
      rw [← hlen, hlen']
      have : 0 < j0 - i0 := Nat.sub_pos_of_lt hi0j0
      omega
    have hne' : e.take i0 ++ e.drop j0 ≠ [] := by
      intro hempty
      have hzero : (e.take i0 ++ e.drop j0).length = 0 := by simp [hempty]
      rw [hlen'] at hzero
      omega
    exact ih _ hshorter _ rfl hne' hv' (hend'.trans hend)

/-- The segment of a run of duration `d`, starting at time `i`. -/
def runSeg {α σ : Type} (w : Nat → α) (path : Nat → σ) (i : Nat) : Nat → List (α × σ)
  | 0 => []
  | d + 1 => (w i, path (i + 1)) :: runSeg w path (i + 1) d

theorem runSeg_valid {α σ : Type} (A : NBA α σ) (w : Nat → α) (path : Nat → σ)
    (hstep : ∀ n, A.step (path n) (w n) (path (n + 1)) = true) (i d : Nat) :
    chainValid A (path i) (runSeg w path i d) ∧
      chainEnd (path i) (runSeg w path i d) = path (i + d) := by
  induction d generalizing i with
  | zero => simp [runSeg, chainValid]
  | succ d ih =>
    obtain ⟨hv, hend⟩ := ih (i + 1)
    constructor
    · exact ⟨hstep i, hv⟩
    · simpa [runSeg, chainEnd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend

def lassoWord (stem loop : List (α × σ)) (hloop : loop ≠ []) (n : Nat) : α :=
  if h : n < stem.length then
    (stem.get ⟨n, h⟩).1
  else
    (loop.get ⟨(n - stem.length) % loop.length,
      Nat.mod_lt _ (listLength_pos_of_ne hloop)⟩).1

def lassoState (s0 : σ) (stem loop : List (α × σ)) (n : Nat) : σ :=
  if n ≤ stem.length then
    chainNth s0 stem n
  else
    chainNth (chainEnd s0 stem) loop ((n - stem.length) % loop.length)

theorem lassoState_onLoop {s0 : σ} {stem loop : List (α × σ)}
    (_hloop : loop ≠ []) {n : Nat} (hn : stem.length ≤ n) :
    lassoState s0 stem loop n =
      chainNth (chainEnd s0 stem) loop ((n - stem.length) % loop.length) := by
  simp only [lassoState]
  split
  · next hle =>
    have hnEq : n = stem.length := le_antisymm hle hn
    subst hnEq
    rw [chainNth_length, Nat.sub_self, Nat.zero_mod, chainNth_zero]
  · rfl

theorem lasso_step (A : NBA α σ) {s0 : σ} {stem loop : List (α × σ)}
    (hstem : chainValid A s0 stem) (hloopne : loop ≠ [])
    (hloop : chainValid A (chainEnd s0 stem) loop)
    (hclose : chainEnd (chainEnd s0 stem) loop = chainEnd s0 stem) (n : Nat) :
    A.step (lassoState s0 stem loop n) (lassoWord stem loop hloopne n)
      (lassoState s0 stem loop (n + 1)) = true := by
  by_cases hn : n < stem.length
  · have hstepEdge := chain_edge A hstem hn
    have hstate : lassoState s0 stem loop n = chainNth s0 stem n := by
      simp [lassoState, Nat.le_of_lt hn]
    have hnext : lassoState s0 stem loop (n + 1) = chainNth s0 stem (n + 1) := by
      have : n + 1 ≤ stem.length := Nat.succ_le_of_lt hn
      simp [lassoState, this]
    have hword : lassoWord stem loop hloopne n = (stem.get ⟨n, hn⟩).1 := by
      simp [lassoWord, hn]
    rw [hstate, hnext, hword, hstepEdge.2]
    exact hstepEdge.1
  · have hnle : stem.length ≤ n := Nat.le_of_not_gt hn
    let pivot := chainEnd s0 stem
    let m := loop.length
    have hmpos : 0 < m := listLength_pos_of_ne hloopne
    let k := n - stem.length
    have hk1 : (n + 1) - stem.length = k + 1 := by omega
    have hstate := lassoState_onLoop (s0 := s0) hloopne hnle
    have hnext := lassoState_onLoop (s0 := s0) (stem := stem) (loop := loop) hloopne
      (Nat.le_succ_of_le hnle)
    have hword : lassoWord stem loop hloopne n =
        (loop.get ⟨k % m, Nat.mod_lt _ hmpos⟩).1 := by
      simp [lassoWord, hn, k, m]
    let i : Nat := k % m
    have hi : i < m := Nat.mod_lt _ hmpos
    have hedge := chain_edge A hloop hi
    have hmod : (k + 1) % m = (i + 1) % m := by
      simp [i, Nat.add_mod]
    have htarget : chainNth pivot loop ((k + 1) % m) = (loop.get ⟨i, hi⟩).2 := by
      rw [hmod]
      by_cases hwrap : i + 1 < m
      · have : (i + 1) % m = i + 1 := Nat.mod_eq_of_lt hwrap
        simpa [this] using hedge.2
      · have hiEq : i + 1 = m := by omega
        have hmod0 : (i + 1) % m = 0 := by simp [hiEq]
        have hnth : chainNth pivot loop (i + 1) = pivot := by
          rw [hiEq, chainNth_length, hclose]
        rw [hmod0, chainNth_zero, ← hnth]
        exact hedge.2
    rw [hstate, hnext, hword, hk1]
    rw [htarget]
    exact hedge.1

theorem lasso_accepts (A : NBA α σ) {s0 : σ} {stem loop : List (α × σ)}
    (hstart : A.start s0 = true) (hstem : chainValid A s0 stem)
    (hloopne : loop ≠ []) (hloop : chainValid A (chainEnd s0 stem) loop)
    (hclose : chainEnd (chainEnd s0 stem) loop = chainEnd s0 stem)
    (hacc : A.accept (chainEnd s0 stem) = true) :
    Accepts A (lassoWord stem loop hloopne) := by
  let path := lassoState s0 stem loop
  refine ⟨path, ?_, lasso_step A hstem hloopne hloop hclose, ?_⟩
  · have hpath : path 0 = s0 := by
      simp [path, lassoState, chainNth_zero]
    simpa [hpath] using hstart
  · intro lowerBound
    let m := loop.length
    have hmpos : 0 < m := listLength_pos_of_ne hloopne
    let visit := stem.length + lowerBound * m
    refine ⟨visit, ?_, ?_⟩
    · have : lowerBound ≤ lowerBound * m := Nat.le_mul_of_pos_right lowerBound hmpos
      omega
    · have hstate : path visit = chainEnd s0 stem := by
        have hle : stem.length ≤ visit := Nat.le_add_right _ _
        rw [show path visit = lassoState s0 stem loop visit from rfl,
          lassoState_onLoop (s0 := s0) hloopne hle]
        have hmod : (visit - stem.length) % m = 0 := by
          have hsub : visit - stem.length = lowerBound * m := by omega
          rw [hsub, Nat.mul_comm]
          exact Nat.mul_mod_right m lowerBound
        rw [hmod, chainNth_zero]
      simpa [hstate] using hacc

/-- A lasso is a stem from a start state to an accepting pivot, plus a
nonempty cycle based at that pivot. -/
structure Lasso (α σ : Type) where
  startState : σ
  stem : List (α × σ)
  loop : List (α × σ)

def Lasso.check [DecidableEq σ] (A : NBA α σ) (L : Lasso α σ) : Bool :=
  A.start L.startState &&
    chainValidBool A L.startState L.stem &&
    !L.loop.isEmpty &&
    chainValidBool A (chainEnd L.startState L.stem) L.loop &&
    decide (chainEnd (chainEnd L.startState L.stem) L.loop =
      chainEnd L.startState L.stem) &&
    A.accept (chainEnd L.startState L.stem)

theorem Lasso.check_accepts [DecidableEq σ] (A : NBA α σ) (L : Lasso α σ)
    (h : L.check A = true) :
    ∃ hloop : L.loop ≠ [],
      Accepts A (lassoWord L.stem L.loop hloop) := by
  simp only [Lasso.check, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hstart, hstem⟩, hloopb⟩, hloop⟩, hclose⟩, hacc⟩
  have hloopne : L.loop ≠ [] := by
    intro hempty
    have : L.loop.isEmpty = true := by simp [hempty]
    exact Bool.eq_false_iff.mp hloopb this
  have hstemP : chainValid A L.startState L.stem := (chainValidBool_iff A _ _).mp hstem
  have hloopP : chainValid A (chainEnd L.startState L.stem) L.loop :=
    (chainValidBool_iff A _ _).mp hloop
  exact ⟨hloopne, lasso_accepts A hstart hstemP hloopne hloopP hclose hacc⟩

/-- Every accepting state reachable from a start state, and lying on a cycle,
makes the language nonempty. The search is the Boolean closure `close`. -/
def decideNonempty (A : NBA α σ) [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ] :
    Bool :=
  let starts := Finset.univ.filter fun q => A.start q = true
  let reached := close A (Fintype.card σ) starts
  listAny (fun q =>
    A.accept q &&
      decide (q ∈ reached) &&
      decide (q ∈ close A (Fintype.card σ) (oneStep A {q})))
    (Enumerable.elems : List σ)

theorem exists_state_io [Fintype σ] (f : Nat → σ) :
    ∃ q, ∀ lowerBound, ∃ n, lowerBound ≤ n ∧ f n = q := by
  classical
  by_contra h
  push Not at h
  choose bound hb using h
  let M : Nat := Finset.univ.sup bound
  have hM : bound (f M) ≤ M := Finset.le_sup (Finset.mem_univ (f M))
  exact hb (f M) M hM rfl

theorem exists_accept_io {σ : Type} [Fintype σ] (accept : σ → Bool) (path : Nat → σ)
    (h : RunAccepts accept path) :
    ∃ q, accept q = true ∧ ∀ lowerBound, ∃ n, lowerBound ≤ n ∧ path n = q := by
  classical
  choose visit hv using h
  obtain ⟨q, hq⟩ := exists_state_io (fun lowerBound => path (visit lowerBound))
  refine ⟨q, ?_, ?_⟩
  · obtain ⟨lowerBound, _, heq⟩ := hq 0
    simpa [heq] using (hv lowerBound).2
  · intro lowerBound
    obtain ⟨index, hindex, heq⟩ := hq lowerBound
    exact ⟨visit index, le_trans hindex (hv index).1, heq⟩

theorem accepts_exists_lasso (A : NBA α σ) [Fintype σ] [DecidableEq σ]
    {w : Nat → α} (h : Accepts A w) :
    ∃ L : Lasso α σ, L.check A = true := by
  classical
  obtain ⟨path, hstart, hstep, hacc⟩ := h
  obtain ⟨q, hqacc, hqio⟩ := exists_accept_io A.accept path hacc
  obtain ⟨n1, _, hn1⟩ := hqio 0
  obtain ⟨n2, hn2, hn2q⟩ := hqio (n1 + 1)
  have hn12 : n1 < n2 := by omega
  obtain ⟨hstemV, hstemE⟩ := runSeg_valid A w path hstep 0 n1
  obtain ⟨hloopV, hloopE⟩ := runSeg_valid A w path hstep n1 (n2 - n1)
  have hstemEnd : chainEnd (path 0) (runSeg w path 0 n1) = q := by
    simpa [hn1] using hstemE
  have hloopEnd : chainEnd q (runSeg w path n1 (n2 - n1)) = q := by
    have hdiff : n1 + (n2 - n1) = n2 := Nat.add_sub_of_le (Nat.le_of_lt hn12)
    have hloopEnd' := hloopE
    rw [hn1] at hloopEnd'
    rw [hdiff] at hloopEnd'
    simpa [hn2q] using hloopEnd'
  have hloopne : runSeg w path n1 (n2 - n1) ≠ [] := by
    have hpos : 0 < n2 - n1 := Nat.sub_pos_of_lt hn12
    cases hdiff : n2 - n1 with
    | zero => omega
    | succ d => simp [runSeg]
  have hloopFrom : chainValid A q (runSeg w path n1 (n2 - n1)) := by
    simpa [hn1] using hloopV
  obtain ⟨stem, _, hstemS, hstemEndS⟩ :=
    shorten_reach A (runSeg w path 0 n1) hstemV hstemEnd
  obtain ⟨loop, _, hloopneS, hloopS, hloopEndS⟩ :=
    shorten_cycle A (runSeg w path n1 (n2 - n1)) hloopne hloopFrom hloopEnd
  refine ⟨⟨path 0, stem, loop⟩, ?_⟩
  simp only [Lasso.check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hstart, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (chainValidBool_iff A _ _).mpr hstemS
  · simpa [List.isEmpty_iff] using hloopneS
  · have : chainEnd (path 0) stem = q := hstemEndS
    simpa [this] using (chainValidBool_iff A q loop).mpr hloopS
  · have : chainEnd (path 0) stem = q := hstemEndS
    simpa [this] using hloopEndS
  · simpa [hstemEndS] using hqacc

theorem decideNonempty_of_lasso (A : NBA α σ)
    [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ]
    (L : Lasso α σ) (h : L.check A = true) :
    decideNonempty A = true := by
  simp only [Lasso.check, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hstart, hstem⟩, hloopb⟩, hloop⟩, hclose⟩, hacc⟩
  have hloopne : L.loop ≠ [] := by
    intro hempty
    exact Bool.eq_false_iff.mp hloopb (by simp [hempty])
  have hstemP := (chainValidBool_iff A _ _).mp hstem
  have hloopP := (chainValidBool_iff A _ _).mp hloop
  let pivot := chainEnd L.startState L.stem
  obtain ⟨stemS, hstemLen, hstemV, hstemE⟩ :=
    shorten_reach A L.stem hstemP rfl
  obtain ⟨loopS, hloopLen, hloopneS, hloopV, hloopE⟩ :=
    shorten_cycle A L.loop hloopne hloopP hclose
  have hpivot : chainEnd L.startState stemS = pivot := hstemE
  have hstartMem : L.startState ∈ Finset.univ.filter fun q => A.start q = true := by
    simpa [Finset.mem_filter] using hstart
  have hreach : pivot ∈ close A (Fintype.card σ)
      (Finset.univ.filter fun q => A.start q = true) := by
    rw [mem_close_iff]
    exact ⟨L.startState, hstartMem, stemS, hstemLen, hstemV, hstemE⟩
  cases loopS with
  | nil => exact absurd rfl hloopneS
  | cons edge tail =>
    obtain ⟨a, s1⟩ := edge
    rcases hloopV with ⟨hstep, htail⟩
    have htailEnd : chainEnd s1 tail = pivot := by simpa [chainEnd] using hloopE
    have hs1 : s1 ∈ oneStep A {pivot} := by
      rw [mem_oneStep_iff]
      exact ⟨pivot, Finset.mem_singleton.mpr rfl, a, hstep⟩
    have htailLen : tail.length ≤ Fintype.card σ := by
      have : tail.length + 1 ≤ Fintype.card σ := by simpa using hloopLen
      omega
    have hcyc : pivot ∈ close A (Fintype.card σ) (oneStep A {pivot}) := by
      rw [mem_close_iff]
      exact ⟨s1, hs1, tail, htailLen, htail, htailEnd⟩
    rw [decideNonempty, listAny_iff]
    refine ⟨pivot, Enumerable.mem_elems pivot, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨by simpa [pivot] using hacc, hreach⟩, hcyc⟩

theorem decideNonempty_accepts (A : NBA α σ)
    [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ]
    (h : decideNonempty A = true) : ∃ w, Accepts A w := by
  rw [decideNonempty, listAny_iff] at h
  obtain ⟨pivot, _, hflags⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hflags
  obtain ⟨haccReach, hcyc⟩ := hflags
  obtain ⟨hacc, hreach⟩ := haccReach
  rw [mem_close_iff] at hreach hcyc
  obtain ⟨s, hs, stem, _, hstem, hstemE⟩ := hreach
  obtain ⟨s1, hs1, tail, _, htail, htailE⟩ := hcyc
  rw [mem_oneStep_iff] at hs1
  obtain ⟨q0, hq0, a, hstep⟩ := hs1
  have hq0q : q0 = pivot := Finset.mem_singleton.mp hq0
  have hstepP : A.step pivot a s1 = true := hq0q ▸ hstep
  have hstart : A.start s = true := by
    rw [Finset.mem_filter] at hs
    exact hs.2
  have hloopne : ((a, s1) :: tail) ≠ [] := by simp
  have hloop : chainValid A pivot ((a, s1) :: tail) := ⟨hstepP, htail⟩
  have hclose : chainEnd pivot ((a, s1) :: tail) = pivot := by
    simpa [chainEnd] using htailE
  have hstemQ : chainEnd s stem = pivot := hstemE
  exact ⟨lassoWord stem ((a, s1) :: tail) hloopne,
    lasso_accepts A hstart hstem hloopne
      (hstemQ.symm ▸ hloop) (hstemQ.symm ▸ hclose) (hstemQ.symm ▸ hacc)⟩

/-- Emptiness is decidable, and a `true` answer is a witnessed nonempty language. -/
theorem decideNonempty_iff (A : NBA α σ)
    [Enumerable α] [Enumerable σ] [Fintype σ] [DecidableEq σ] :
    decideNonempty A = true ↔ ∃ w, Accepts A w := by
  constructor
  · exact decideNonempty_accepts A
  · intro h
    obtain ⟨w, hw⟩ := h
    obtain ⟨L, hL⟩ := accepts_exists_lasso A hw
    exact decideNonempty_of_lasso A L hL

instance : Enumerable Unit where
  elems := [()]
  mem_elems := by
    intro
    simp

instance : Enumerable Bool where
  elems := [false, true]
  mem_elems := by
    intro b
    cases b <;> simp

theorem fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by
  intro h
  exact Nat.zero_ne_one (congrArg Fin.val h)

theorem fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := fun h => fin2_zero_ne_one h.symm

theorem fin2_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  match i with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl

instance : Enumerable (Fin 2) where
  elems := [0, 1]
  mem_elems := by
    intro i
    rcases fin2_zero_or_one i with h | h
    · simp [h]
    · simp [h]

instance {β γ : Type} [Enumerable β] [Enumerable γ] : Enumerable (β × γ) where
  elems := (Enumerable.elems : List β) ×ˢ (Enumerable.elems : List γ)
  mem_elems := by
    intro p
    cases p with
    | mk b c =>
      simp only [List.mem_product]
      exact ⟨Enumerable.mem_elems b, Enumerable.mem_elems c⟩

instance {β γ : Type} [Enumerable β] [Enumerable γ] : Enumerable (β ⊕ γ) where
  elems := (Enumerable.elems : List β).map Sum.inl ++ (Enumerable.elems : List γ).map Sum.inr
  mem_elems := by
    intro x
    cases x with
    | inl b =>
      refine List.mem_append_left _ ?_
      rw [List.mem_map]
      exact ⟨b, Enumerable.mem_elems b, rfl⟩
    | inr c =>
      refine List.mem_append_right _ ?_
      rw [List.mem_map]
      exact ⟨c, Enumerable.mem_elems c, rfl⟩

/-- The one-state automaton that accepts every ω-word. -/
def allLoop : NBA Bool Unit where
  step := fun _ _ _ => true
  start := fun _ => true
  accept := fun _ => true

/-- The one-state automaton with no edges. Its language is empty. -/
def noStep : NBA Bool Unit where
  step := fun _ _ _ => false
  start := fun _ => true
  accept := fun _ => true

theorem control_allLoop_nonempty : decideNonempty allLoop = true := by
  rw [decideNonempty_iff]
  refine ⟨fun _ => true, fun _ => (), rfl, fun _ => rfl, ?_⟩
  intro lowerBound
  exact ⟨lowerBound, le_rfl, rfl⟩

theorem control_noStep_empty : decideNonempty noStep = false := by
  cases h : decideNonempty noStep
  · rfl
  · exfalso
    obtain ⟨_, _, _, hstep, _⟩ := (decideNonempty_iff noStep).mp h
    have := hstep 0
    simp [noStep] at this

def allLoopLasso : Lasso Bool Unit where
  startState := ()
  stem := []
  loop := [(true, ())]

theorem control_allLoop_lasso : allLoopLasso.check allLoop = true := by
  simp [Lasso.check, allLoopLasso, allLoop, chainValidBool, chainEnd, List.isEmpty]

theorem control_noStep_lasso_rejects (L : Lasso Bool Unit) :
    L.check noStep = false := by
  cases h : L.check noStep
  · rfl
  · exfalso
    obtain ⟨_, hw⟩ := Lasso.check_accepts noStep L h
    obtain ⟨_, _, hstep, _⟩ := hw
    have := hstep 0
    simp [noStep] at this

/-! ## Boolean operations -/

/-- Disjoint sum of state sets. There is no edge from one side to the other. -/
def union {τ : Type} (A : NBA α σ) (B : NBA α τ) : NBA α (σ ⊕ τ) where
  step := fun s a t =>
    match s, t with
    | .inl s, .inl t => A.step s a t
    | .inr s, .inr t => B.step s a t
    | _, _ => false
  start := fun s =>
    match s with
    | .inl s => A.start s
    | .inr s => B.start s
  accept := fun s =>
    match s with
    | .inl s => A.accept s
    | .inr s => B.accept s

theorem union_step_inl {τ : Type} (A : NBA α σ) (B : NBA α τ) (s t : σ) (a : α) :
    (union A B).step (Sum.inl s) a (Sum.inl t) = A.step s a t := by
  simp [union]

theorem union_step_inr {τ : Type} (A : NBA α σ) (B : NBA α τ) (s t : τ) (a : α) :
    (union A B).step (Sum.inr s) a (Sum.inr t) = B.step s a t := by
  simp [union]

theorem union_step_inl_inr {τ : Type} (A : NBA α σ) (B : NBA α τ) (s : σ) (t : τ) (a : α) :
    (union A B).step (Sum.inl s) a (Sum.inr t) = false := by
  simp [union]

theorem union_step_inr_inl {τ : Type} (A : NBA α σ) (B : NBA α τ) (s : τ) (t : σ) (a : α) :
    (union A B).step (Sum.inr s) a (Sum.inl t) = false := by
  simp [union]

theorem union_start_inl {τ : Type} (A : NBA α σ) (B : NBA α τ) (s : σ) :
    (union A B).start (Sum.inl s) = A.start s := by
  simp [union]

theorem union_start_inr {τ : Type} (A : NBA α σ) (B : NBA α τ) (s : τ) :
    (union A B).start (Sum.inr s) = B.start s := by
  simp [union]

theorem union_accept_inl {τ : Type} (A : NBA α σ) (B : NBA α τ) (s : σ) :
    (union A B).accept (Sum.inl s) = A.accept s := by
  simp [union]

theorem union_accept_inr {τ : Type} (A : NBA α σ) (B : NBA α τ) (s : τ) :
    (union A B).accept (Sum.inr s) = B.accept s := by
  simp [union]

theorem accepts_union_inl {τ : Type} (A : NBA α σ) (B : NBA α τ) (w : Nat → α)
    (path : Nat → σ ⊕ τ)
    (hstart : (union A B).start (path 0) = true)
    (hstep : ∀ n, (union A B).step (path n) (w n) (path (n + 1)) = true)
    (hacc : RunAccepts (union A B).accept path)
    (h0 : ∃ s, path 0 = Sum.inl s) : Accepts A w := by
  have stay : ∀ n, ∃ s, path n = Sum.inl s := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      cases hnext : path (n + 1) with
      | inl t => exact ⟨t, rfl⟩
      | inr t =>
        have hstepn := hstep n
        rw [hs, hnext, union_step_inl_inr] at hstepn
        exact absurd hstepn Bool.false_ne_true
  classical
  let proj n := (stay n).choose
  have hproj : ∀ n, path n = Sum.inl (proj n) := fun n => (stay n).choose_spec
  refine ⟨proj, ?_, ?_, ?_⟩
  · have h := hstart
    rw [hproj 0, union_start_inl] at h
    exact h
  · intro n
    have h := hstep n
    rw [hproj n, hproj (n + 1), union_step_inl] at h
    exact h
  · intro lowerBound
    obtain ⟨visit, hv, ha⟩ := hacc lowerBound
    have h := ha
    rw [hproj visit, union_accept_inl] at h
    exact ⟨visit, hv, h⟩

theorem accepts_union_inr {τ : Type} (A : NBA α σ) (B : NBA α τ) (w : Nat → α)
    (path : Nat → σ ⊕ τ)
    (hstart : (union A B).start (path 0) = true)
    (hstep : ∀ n, (union A B).step (path n) (w n) (path (n + 1)) = true)
    (hacc : RunAccepts (union A B).accept path)
    (h0 : ∃ s, path 0 = Sum.inr s) : Accepts B w := by
  have stay : ∀ n, ∃ s, path n = Sum.inr s := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      cases hnext : path (n + 1) with
      | inr t => exact ⟨t, rfl⟩
      | inl t =>
        have hstepn := hstep n
        rw [hs, hnext, union_step_inr_inl] at hstepn
        exact absurd hstepn Bool.false_ne_true
  classical
  let proj n := (stay n).choose
  have hproj : ∀ n, path n = Sum.inr (proj n) := fun n => (stay n).choose_spec
  refine ⟨proj, ?_, ?_, ?_⟩
  · have h := hstart
    rw [hproj 0, union_start_inr] at h
    exact h
  · intro n
    have h := hstep n
    rw [hproj n, hproj (n + 1), union_step_inr] at h
    exact h
  · intro lowerBound
    obtain ⟨visit, hv, ha⟩ := hacc lowerBound
    have h := ha
    rw [hproj visit, union_accept_inr] at h
    exact ⟨visit, hv, h⟩

/-- The accepted language of a disjoint sum is the union of the languages. -/
theorem accepts_union {τ : Type} (A : NBA α σ) (B : NBA α τ) (w : Nat → α) :
    Accepts (union A B) w ↔ Accepts A w ∨ Accepts B w := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    cases hpath0 : path 0 with
    | inl _ =>
      exact Or.inl (accepts_union_inl A B w path hstart hstep hacc ⟨_, hpath0⟩)
    | inr _ =>
      exact Or.inr (accepts_union_inr A B w path hstart hstep hacc ⟨_, hpath0⟩)
  · intro h
    rcases h with ⟨path, hstart, hstep, hacc⟩ | ⟨path, hstart, hstep, hacc⟩
    · refine ⟨fun n => Sum.inl (path n), ?_, ?_, ?_⟩
      · rw [union_start_inl]
        exact hstart
      · intro n
        rw [union_step_inl]
        exact hstep n
      · intro lowerBound
        obtain ⟨visit, hv, ha⟩ := hacc lowerBound
        exact ⟨visit, hv, by rw [union_accept_inl]; exact ha⟩
    · refine ⟨fun n => Sum.inr (path n), ?_, ?_, ?_⟩
      · rw [union_start_inr]
        exact hstart
      · intro n
        rw [union_step_inr]
        exact hstep n
      · intro lowerBound
        obtain ⟨visit, hv, ha⟩ := hacc lowerBound
        exact ⟨visit, hv, by rw [union_accept_inr]; exact ha⟩

/-- Phase `0` waits for an accepting state of the first automaton. Phase `1`
waits for an accepting state of the second. The phase recorded on an edge is
the phase of its source. -/
def phaseNext {τ : Type} (acceptA : σ → Bool) (acceptB : τ → Bool)
    (qA : σ) (qB : τ) (ph : Fin 2) : Fin 2 :=
  if ph = 0 then
    if acceptA qA = true then 1 else 0
  else
    if acceptB qB = true then 0 else 1

theorem phaseNext_of_zero {τ : Type} (acceptA : σ → Bool) (acceptB : τ → Bool)
    (qA : σ) (qB : τ) (h : acceptA qA = true) :
    phaseNext acceptA acceptB qA qB 0 = 1 := by
  simp [phaseNext, h]

theorem phaseNext_of_zero_false {τ : Type} (acceptA : σ → Bool) (acceptB : τ → Bool)
    (qA : σ) (qB : τ) (h : acceptA qA = false) :
    phaseNext acceptA acceptB qA qB 0 = 0 := by
  simp [phaseNext, h]

theorem phaseNext_of_one {τ : Type} (acceptA : σ → Bool) (acceptB : τ → Bool)
    (qA : σ) (qB : τ) :
    phaseNext acceptA acceptB qA qB 1 =
      if acceptB qB = true then (0 : Fin 2) else 1 := by
  unfold phaseNext
  rw [if_neg fin2_one_ne_zero]

/-- The phase forced by a pair of runs, starting at phase `0`. -/
def phaseRun {τ : Type} (acceptA : σ → Bool) (acceptB : τ → Bool)
    (pathA : Nat → σ) (pathB : Nat → τ) : Nat → Fin 2
  | 0 => 0
  | n + 1 =>
    phaseNext acceptA acceptB (pathA n) (pathB n)
      (phaseRun acceptA acceptB pathA pathB n)

theorem phaseRun_zero {τ : Type} (acceptA : σ → Bool) (acceptB : τ → Bool)
    (pathA : Nat → σ) (pathB : Nat → τ) :
    phaseRun acceptA acceptB pathA pathB 0 = 0 := rfl

theorem phaseRun_succ {τ : Type} (acceptA : σ → Bool) (acceptB : τ → Bool)
    (pathA : Nat → σ) (pathB : Nat → τ) (n : Nat) :
    phaseRun acceptA acceptB pathA pathB (n + 1) =
      phaseNext acceptA acceptB (pathA n) (pathB n)
        (phaseRun acceptA acceptB pathA pathB n) := rfl

/-- A product state is accepting exactly on phase `0` at an accepting state of
the first automaton. Those visits are the switches from phase `0` to phase `1`. -/
def inter {τ : Type} (A : NBA α σ) (B : NBA α τ) : NBA α (σ × τ × Fin 2) where
  step := fun ⟨qA, qB, ph⟩ a ⟨qA', qB', ph'⟩ =>
    A.step qA a qA' && B.step qB a qB' &&
      decide (ph' = phaseNext A.accept B.accept qA qB ph)
  start := fun ⟨qA, qB, ph⟩ =>
    A.start qA && B.start qB && decide (ph = 0)
  accept := fun ⟨qA, _, ph⟩ =>
    decide (ph = 0) && A.accept qA

theorem notEventuallyConst {τ : Type}
    (acceptA : σ → Bool) (acceptB : τ → Bool)
    (pathA : Nat → σ) (pathB : Nat → τ)
    (hA : RunAccepts acceptA pathA) (hB : RunAccepts acceptB pathB) :
    ∀ N, ∃ n, N ≤ n ∧
      phaseRun acceptA acceptB pathA pathB n ≠
        phaseRun acceptA acceptB pathA pathB N := by
  let phase := phaseRun acceptA acceptB pathA pathB
  have hsucc : ∀ n, phase (n + 1) =
      phaseNext acceptA acceptB (pathA n) (pathB n) (phase n) := by
    intro n
    unfold phase
    exact phaseRun_succ acceptA acceptB pathA pathB n
  intro N
  classical
  by_contra h
  have hconst : ∀ n, N ≤ n → phase n = phase N := by
    intro n hn
    by_contra hneq
    exact h ⟨n, hn, hneq⟩
  rcases fin2_zero_or_one (phase N) with hN | hN
  · have never : ∀ n, N ≤ n → acceptA (pathA n) = false := by
      intro n hn
      by_cases hEq : acceptA (pathA n) = true
      · have hdef : phase (n + 1) =
            phaseNext acceptA acceptB (pathA n) (pathB n) (phase n) := hsucc n
        rw [hconst n hn, hN,
          phaseNext_of_zero acceptA acceptB (pathA n) (pathB n) hEq] at hdef
        have hnext : phase (n + 1) = phase N := hconst (n + 1) (by omega)
        rw [hN] at hnext
        exact absurd (hnext.symm.trans hdef) fin2_zero_ne_one
      · exact Bool.eq_false_iff.mpr hEq
    obtain ⟨visit, hv, ha⟩ := hA N
    have hf := never visit hv
    rw [hf] at ha
    exact Bool.false_ne_true ha
  · have never : ∀ n, N ≤ n → acceptB (pathB n) = false := by
      intro n hn
      by_cases hEq : acceptB (pathB n) = true
      · have hdef : phase (n + 1) =
            phaseNext acceptA acceptB (pathA n) (pathB n) (phase n) := hsucc n
        rw [hconst n hn, hN, phaseNext_of_one acceptA acceptB (pathA n) (pathB n)] at hdef
        simp [hEq] at hdef
        have hnext : phase (n + 1) = phase N := hconst (n + 1) (by omega)
        rw [hN] at hnext
        exact absurd (hdef.symm.trans hnext) fin2_zero_ne_one
      · exact Bool.eq_false_iff.mpr hEq
    obtain ⟨visit, hv, ha⟩ := hB N
    have hf := never visit hv
    rw [hf] at ha
    exact Bool.false_ne_true ha

theorem phaseSwitch01 {τ : Type}
    (acceptA : σ → Bool) (acceptB : τ → Bool)
    (pathA : Nat → σ) (pathB : Nat → τ)
    (hA : RunAccepts acceptA pathA) (hB : RunAccepts acceptB pathB) :
    ∀ lowerBound, ∃ n, lowerBound ≤ n ∧
      phaseRun acceptA acceptB pathA pathB n = 0 ∧
      phaseRun acceptA acceptB pathA pathB (n + 1) = 1 := by
  let phase := phaseRun acceptA acceptB pathA pathB
  have notConst : ∀ N, ∃ n, N ≤ n ∧ phase n ≠ phase N :=
    notEventuallyConst acceptA acceptB pathA pathB hA hB
  have changes : ∀ N, ∃ n, N ≤ n ∧ phase (n + 1) ≠ phase n := by
    intro N
    have hex : ∃ n, N < n ∧ phase n ≠ phase N := by
      obtain ⟨n, hn, hne⟩ := notConst N
      refine ⟨n, ?_, hne⟩
      by_contra hle
      have : n = N := by omega
      subst this
      exact hne rfl
    classical
    let n0 := Nat.find hex
    have hn0 := Nat.find_spec hex
    have hpos : 0 < n0 := by omega
    let j := n0 - 1
    have hj1 : j + 1 = n0 := Nat.succ_pred_eq_of_pos hpos
    have hjN : N ≤ j := by omega
    have hphasej : phase j = phase N := by
      by_contra hneq
      by_cases hjeq : j = N
      · rw [hjeq] at hneq
        exact hneq rfl
      · exact Nat.find_min hex (by omega) ⟨by omega, hneq⟩
    refine ⟨j, hjN, ?_⟩
    rw [hj1, hphasej]
    exact hn0.2
  intro lowerBound
  obtain ⟨k, hk, hdiff⟩ := changes lowerBound
  rcases fin2_zero_or_one (phase k) with hk0 | hk1
  · have h1 : phase (k + 1) = 1 := by
      rcases fin2_zero_or_one (phase (k + 1)) with h0 | h1
      · exact absurd (h0.trans hk0.symm) hdiff
      · exact h1
    exact ⟨k, hk, hk0, h1⟩
  · have h0next : phase (k + 1) = 0 := by
      rcases fin2_zero_or_one (phase (k + 1)) with h0 | h1
      · exact h0
      · exact absurd (h1.trans hk1.symm) hdiff
    classical
    have hex : ∃ j, k + 1 ≤ j ∧ phase (j + 1) ≠ phase j := changes (k + 1)
    let j := Nat.find hex
    have hj := Nat.find_spec hex
    have hconst0 : ∀ d, k + 1 + d ≤ j → phase (k + 1 + d) = 0 := by
      intro d
      induction d with
      | zero =>
        intro _
        exact h0next
      | succ d ih =>
        intro hle
        have hpred : phase (k + 1 + d) = 0 := ih (by omega)
        have hnot := Nat.find_min hex (show k + 1 + d < j by omega)
        have heq : phase (k + 1 + d + 1) = phase (k + 1 + d) := by
          by_contra hneq
          exact hnot ⟨by omega, hneq⟩
        have hidx : k + 1 + (d + 1) = k + 1 + d + 1 := by omega
        rw [hidx, heq, hpred]
    have hphasej : phase j = 0 := by
      have hd : j = k + 1 + (j - (k + 1)) := by omega
      rw [hd]
      exact hconst0 (j - (k + 1)) (by omega)
    have hnext1 : phase (j + 1) = 1 := by
      rcases fin2_zero_or_one (phase (j + 1)) with h0 | h1
      · exact absurd (h0.trans hphasej.symm) hj.2
      · exact h1
    exact ⟨j, le_trans (le_trans hk (Nat.le_succ k)) hj.1, hphasej, hnext1⟩

/-- From infinitely many phase-`0` visits that accept for the first automaton,
the second automaton accepts infinitely often: each return from phase `1` to
phase `0` reads an accepting state of the second automaton. -/
theorem bAccepts_of_phaseAccepts {τ : Type}
    (acceptA : σ → Bool) (acceptB : τ → Bool)
    (pathA : Nat → σ) (pathB : Nat → τ) (phase : Nat → Fin 2)
    (hnext : ∀ n, phase (n + 1) =
      phaseNext acceptA acceptB (pathA n) (pathB n) (phase n))
    (hacc : ∀ lowerBound, ∃ n, lowerBound ≤ n ∧ phase n = 0 ∧ acceptA (pathA n) = true) :
    RunAccepts acceptB pathB := by
  intro lowerBound
  obtain ⟨n, hn, hphn, hAn⟩ := hacc lowerBound
  have hphn1 : phase (n + 1) = 1 := by
    rw [hnext n, hphn, phaseNext_of_zero acceptA acceptB (pathA n) (pathB n) hAn]
  obtain ⟨m, hm, hphm, _⟩ := hacc (n + 1)
  have hex : ∃ k, n < k ∧ phase k = 0 := ⟨m, by
    have hne : m ≠ n + 1 := by
      intro heq
      have : phase (n + 1) = 0 := by simpa [heq] using hphm
      exact fin2_zero_ne_one (this.symm.trans hphn1)
    omega, hphm⟩
  classical
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkgt : n + 1 < k := by
    have hne : k ≠ n + 1 := by
      intro heq
      have hk0 : phase k = 0 := hk.2
      rw [heq] at hk0
      exact fin2_zero_ne_one (hk0.symm.trans hphn1)
    omega
  have hpos : 0 < k := by omega
  let j := k - 1
  have hj1 : j + 1 = k := Nat.succ_pred_eq_of_pos hpos
  have hphj : phase j = 1 := by
    have hnot0 : phase j ≠ 0 := by
      intro h0
      exact Nat.find_min hex (show j < k by omega) ⟨by omega, h0⟩
    rcases fin2_zero_or_one (phase j) with h0 | h1
    · exact absurd h0 hnot0
    · exact h1
  have hB : acceptB (pathB j) = true := by
    have hstep : phaseNext acceptA acceptB (pathA j) (pathB j) (phase j) = 0 := by
      rw [← hnext j, hj1, hk.2]
    rw [hphj, phaseNext_of_one] at hstep
    by_cases hEq : acceptB (pathB j) = true
    · exact hEq
    · have hf : acceptB (pathB j) = false := Bool.eq_false_iff.mpr hEq
      simp [hf] at hstep
  exact ⟨j, by omega, hB⟩

theorem phaseProductAccepts {τ : Type} (A : NBA α σ) (B : NBA α τ)
    {w : Nat → α} {pathA : Nat → σ} {pathB : Nat → τ}
    (hstartA : A.start (pathA 0) = true)
    (hstepA : ∀ n, A.step (pathA n) (w n) (pathA (n + 1)) = true)
    (hA : RunAccepts A.accept pathA)
    (hstartB : B.start (pathB 0) = true)
    (hstepB : ∀ n, B.step (pathB n) (w n) (pathB (n + 1)) = true)
    (hB : RunAccepts B.accept pathB) :
    Accepts (inter A B) w := by
  let phase := phaseRun A.accept B.accept pathA pathB
  let path n := (pathA n, pathB n, phase n)
  refine ⟨path, ?_, ?_, ?_⟩
  · have h : (inter A B).start (pathA 0, pathB 0, phase 0) = true := by
      simp [inter, hstartA, hstartB, phase, phaseRun_zero]
    exact h
  · intro n
    have hph : phase (n + 1) =
        phaseNext A.accept B.accept (pathA n) (pathB n) (phase n) := by
      unfold phase
      exact phaseRun_succ A.accept B.accept pathA pathB n
    simp [path, inter, hstepA n, hstepB n, hph]
  · intro lowerBound
    obtain ⟨n, hn, h0, h1⟩ :=
      phaseSwitch01 A.accept B.accept pathA pathB hA hB lowerBound
    have h0p : phase n = 0 := by
      unfold phase
      exact h0
    have hAacc : A.accept (pathA n) = true := by
      have hdef : phase (n + 1) =
          phaseNext A.accept B.accept (pathA n) (pathB n) (phase n) := by
        unfold phase
        exact phaseRun_succ A.accept B.accept pathA pathB n
      unfold phase at hdef
      rw [h0] at hdef
      rw [h1] at hdef
      by_contra hnot
      have hf : A.accept (pathA n) = false := Bool.eq_false_iff.mpr hnot
      rw [phaseNext_of_zero_false A.accept B.accept (pathA n) (pathB n) hf] at hdef
      exact fin2_zero_ne_one hdef.symm
    refine ⟨n, hn, ?_⟩
    simp [path, inter, h0p, hAacc]

/-- The two-phase product accepts exactly the intersection of the languages. -/
theorem accepts_inter {τ : Type} (A : NBA α σ) (B : NBA α τ) (w : Nat → α) :
    Accepts (inter A B) w ↔ Accepts A w ∧ Accepts B w := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    let pathA n := (path n).1
    let pathB n := (path n).2.1
    let phase n := (path n).2.2
    have hproj : ∀ n, path n = (pathA n, pathB n, phase n) := fun _ => rfl
    have hstartS : A.start (pathA 0) = true ∧ B.start (pathB 0) = true ∧ phase 0 = 0 := by
      have h := hstart
      rw [hproj 0] at h
      simp only [inter, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hA, hB⟩, hph⟩ := h
      exact ⟨hA, hB, hph⟩
    have hstepS : ∀ n,
        A.step (pathA n) (w n) (pathA (n + 1)) = true ∧
        B.step (pathB n) (w n) (pathB (n + 1)) = true ∧
        phase (n + 1) = phaseNext A.accept B.accept (pathA n) (pathB n) (phase n) := by
      intro n
      have h := hstep n
      rw [hproj n, hproj (n + 1)] at h
      simp only [inter, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hA, hB⟩, hph⟩ := h
      exact ⟨hA, hB, hph⟩
    have haccA : RunAccepts A.accept pathA := by
      intro lowerBound
      obtain ⟨visit, hv, ha⟩ := hacc lowerBound
      have h := ha
      rw [hproj visit] at h
      simp only [inter, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨visit, hv, h.2⟩
    have haccPhase : ∀ lowerBound, ∃ n, lowerBound ≤ n ∧
        phase n = 0 ∧ A.accept (pathA n) = true := by
      intro lowerBound
      obtain ⟨visit, hv, ha⟩ := hacc lowerBound
      have h := ha
      rw [hproj visit] at h
      simp only [inter, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨visit, hv, h.1, h.2⟩
    have haccB : RunAccepts B.accept pathB :=
      bAccepts_of_phaseAccepts A.accept B.accept pathA pathB phase
        (fun n => (hstepS n).2.2) haccPhase
    exact ⟨⟨pathA, hstartS.1, fun n => (hstepS n).1, haccA⟩,
      ⟨pathB, hstartS.2.1, fun n => (hstepS n).2.1, haccB⟩⟩
  · intro ⟨hA, hB⟩
    obtain ⟨pathA, hstartA, hstepA, haccA⟩ := hA
    obtain ⟨pathB, hstartB, hstepB, haccB⟩ := hB
    exact phaseProductAccepts A B hstartA hstepA haccA hstartB hstepB haccB

/-- Existential quantification over a letter component. `β` is listed by
`Enumerable`, so a projected edge exists exactly when some concrete letter
makes the source edge true. -/
def project {β : Type} (A : NBA (α × β) σ) [Enumerable β] : NBA α σ where
  step := fun s a t => listAny (fun b => A.step s (a, b) t) (Enumerable.elems : List β)
  start := A.start
  accept := A.accept

/-- Projection accepts `w` exactly when some labelling of the hidden component
makes the source automaton accept the paired word. -/
theorem accepts_project {β : Type} (A : NBA (α × β) σ) [Enumerable β] (w : Nat → α) :
    Accepts (project A) w ↔
      ∃ labelling : Nat → β, Accepts A (fun n => (w n, labelling n)) := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    have hletter : ∀ n, ∃ b, A.step (path n) (w n, b) (path (n + 1)) = true := by
      intro n
      have h := hstep n
      simp only [project, listAny_iff] at h
      obtain ⟨b, _, hb⟩ := h
      exact ⟨b, hb⟩
    classical
    exact ⟨fun n => (hletter n).choose, path, hstart, fun n => (hletter n).choose_spec, hacc⟩
  · intro ⟨labelling, path, hstart, hstep, hacc⟩
    refine ⟨path, hstart, ?_, hacc⟩
    intro n
    simp only [project, listAny_iff]
    exact ⟨labelling n, Enumerable.mem_elems (labelling n), hstep n⟩

theorem control_union_with_empty :
    decideNonempty (union allLoop noStep) = true := by
  rw [decideNonempty_iff]
  refine ⟨fun _ => true, ?_⟩
  rw [accepts_union]
  refine Or.inl ⟨fun _ => (), rfl, fun _ => rfl, ?_⟩
  intro lowerBound
  exact ⟨lowerBound, le_rfl, rfl⟩

theorem control_union_both_empty :
    decideNonempty (union noStep noStep) = false := by
  cases h : decideNonempty (union noStep noStep) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨_, hw⟩ := (decideNonempty_iff (union noStep noStep)).mp h
    rw [accepts_union] at hw
    rcases hw with hw | hw
    · obtain ⟨_, _, hstep, _⟩ := hw
      have := hstep 0
      simp [noStep] at this
    · obtain ⟨_, _, hstep, _⟩ := hw
      have := hstep 0
      simp [noStep] at this

theorem control_inter_both_nonempty :
    decideNonempty (inter allLoop allLoop) = true := by
  rw [decideNonempty_iff]
  refine ⟨fun _ => true, ?_⟩
  rw [accepts_inter]
  exact ⟨⟨fun _ => (), rfl, fun _ => rfl, fun lowerBound => ⟨lowerBound, le_rfl, rfl⟩⟩,
    ⟨fun _ => (), rfl, fun _ => rfl, fun lowerBound => ⟨lowerBound, le_rfl, rfl⟩⟩⟩

theorem control_inter_one_empty :
    decideNonempty (inter allLoop noStep) = false := by
  cases h : decideNonempty (inter allLoop noStep) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨_, hw⟩ := (decideNonempty_iff (inter allLoop noStep)).mp h
    rw [accepts_inter] at hw
    obtain ⟨_, hB⟩ := hw
    obtain ⟨_, _, hstep, _⟩ := hB
    have := hstep 0
    simp [noStep] at this

def allLoopPair : NBA (Bool × Bool) Unit where
  step := fun _ _ _ => true
  start := fun _ => true
  accept := fun _ => true

def noStepPair : NBA (Bool × Bool) Unit where
  step := fun _ _ _ => false
  start := fun _ => true
  accept := fun _ => true

theorem control_project_nonempty :
    decideNonempty (project allLoopPair) = true := by
  rw [decideNonempty_iff]
  refine ⟨fun _ => true, ?_⟩
  rw [accepts_project]
  exact ⟨fun _ => false,
    ⟨fun _ => (), rfl, fun _ => rfl, fun lowerBound => ⟨lowerBound, le_rfl, rfl⟩⟩⟩

theorem control_project_empty :
    decideNonempty (project noStepPair) = false := by
  cases h : decideNonempty (project noStepPair) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨_, hw⟩ := (decideNonempty_iff (project noStepPair)).mp h
    rw [accepts_project] at hw
    obtain ⟨_, _, _, hstep, _⟩ := hw
    have := hstep 0
    simp [noStepPair] at this

/-! ## Run DAG -/

def listAll {β : Type} (p : β → Bool) : List β → Bool
  | [] => true
  | b :: bs => p b && listAll p bs

theorem listAll_iff {β : Type} (p : β → Bool) :
    ∀ l : List β, listAll p l = true ↔ ∀ b ∈ l, p b = true
  | [] => by simp [listAll]
  | b :: bs => by
      rw [listAll, Bool.and_eq_true, listAll_iff p bs]
      constructor
      · intro h c hc
        rw [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact h.1
        · exact h.2 c hc
      · intro h
        exact ⟨h b (List.Mem.head _), fun c hc => h c (List.Mem.tail _ hc)⟩

/-- A state read after `i` letters, starting from a start state. -/
def reachable (A : NBA α σ) (w : Nat → α) : Nat → σ → Prop
  | 0, q => A.start q = true
  | i + 1, q => ∃ p, reachable A w i p ∧ A.step p (w i) q = true

theorem reachable_zero (A : NBA α σ) (w : Nat → α) (q : σ) :
    reachable A w 0 q ↔ A.start q = true := by
  simp [reachable]

theorem reachable_succ (A : NBA α σ) (w : Nat → α) (i : Nat) (q : σ) :
    reachable A w (i + 1) q ↔ ∃ p, reachable A w i p ∧ A.step p (w i) q = true := by
  simp [reachable]

theorem reachable_path (A : NBA α σ) (w : Nat → α) (i : Nat) (q : σ)
    (h : reachable A w i q) :
    ∃ path : Nat → σ,
      path i = q ∧ A.start (path 0) = true ∧
        ∀ k < i, A.step (path k) (w k) (path (k + 1)) = true := by
  induction i generalizing q with
  | zero =>
    refine ⟨fun _ => q, rfl, ?_, fun k hk => ?_⟩
    · rw [reachable_zero] at h
      exact h
    · omega
  | succ i ih =>
    rw [reachable_succ] at h
    obtain ⟨p, hp, hstep⟩ := h
    obtain ⟨path, hend, hstart, hsteps⟩ := ih p hp
    let path' : Nat → σ := fun k => if k ≤ i then path k else q
    refine ⟨path', ?_, ?_, ?_⟩
    · simp [path', Nat.not_le.mpr (Nat.lt_succ_self i)]
    · simpa [path'] using hstart
    · intro k hk
      by_cases hklt : k < i
      · have hk1 : k + 1 ≤ i := Nat.succ_le_of_lt hklt
        have hs := hsteps k hklt
        simpa [path', Nat.le_of_lt hklt, hk1] using hs
      · have hkEq : k = i := by omega
        have hleft : path' k = p := by
          simp [path', hkEq, hend]
        have hright : path' (k + 1) = q := by
          have hnot : ¬ k + 1 ≤ i := by omega
          simp [path', hnot]
        rw [hleft, hright, hkEq]
        exact hstep

/-- A walk that stays inside a vertex set `V`. -/
def reaches (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    (i j : Nat) (src dst : σ) : Prop :=
  i ≤ j ∧ V i src ∧ V j dst ∧
    ∃ path : Nat → σ,
      path 0 = src ∧ path (j - i) = dst ∧
        ∀ k < j - i,
          A.step (path k) (w (i + k)) (path (k + 1)) = true ∧
            V (i + k) (path k) ∧ V (i + k + 1) (path (k + 1))

theorem reaches_refl (V : Nat → σ → Prop) (A : NBA α σ) (w : Nat → α)
    {i : Nat} {q : σ} (hV : V i q) :
    reaches A w V i i q q := by
  refine ⟨le_rfl, hV, hV, fun _ => q, rfl, rfl, ?_⟩
  intro k hk
  omega

theorem reaches_tail (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    {i j : Nat} {src dst : σ} (h : reaches A w V i j src dst) (hij : i < j) :
    ∃ mid, A.step src (w i) mid = true ∧ V (i + 1) mid ∧
      reaches A w V (i + 1) j mid dst := by
  obtain ⟨hijle, hVs, hVd, path, h0, hend, hst⟩ := h
  have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
  have hstep0 := hst 0 hpos
  refine ⟨path 1, ?_, hstep0.2.2, ?_⟩
  · simpa [h0] using hstep0.1
  · refine ⟨hij, hstep0.2.2, hVd, fun k => path (k + 1), rfl, ?_, ?_⟩
    · have hidx : (j - (i + 1)) + 1 = j - i := by omega
      show path ((j - (i + 1)) + 1) = dst
      rw [hidx]
      exact hend
    · intro k hk
      have hk' : k + 1 < j - i := by omega
      have hs := hst (k + 1) hk'
      have htime : i + 1 + k = i + (k + 1) := by omega
      simpa [htime] using hs

def consPath (src : σ) (path : Nat → σ) : Nat → σ
  | 0 => src
  | n + 1 => path n

theorem reaches_prepend (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    {i j : Nat} {src mid dst : σ}
    (hstep : A.step src (w i) mid = true)
    (hVs : V i src) (hVm : V (i + 1) mid)
    (h : reaches A w V (i + 1) j mid dst) :
    reaches A w V i j src dst := by
  obtain ⟨hle, _, hVd, path, h0, hend, hst⟩ := h
  have hij : i ≤ j := Nat.le_trans (Nat.le_succ i) hle
  have hpos : 0 < j - i := by omega
  refine ⟨hij, hVs, hVd, consPath src path, rfl, ?_, ?_⟩
  · have hidx : j - i = (j - (i + 1)) + 1 := by omega
    rw [hidx]
    simp [consPath, hend]
  · intro k hk
    cases k with
    | zero =>
      simp [consPath, h0, hstep, hVs, hVm]
    | succ k =>
      have hk' : k < j - (i + 1) := by omega
      have hs := hst k hk'
      have htime : i + (k + 1) = i + 1 + k := by omega
      simpa [consPath, htime] using hs

/-- Vertices of `V` occur at arbitrarily large levels, by walks that stay in `V`. -/
def infiniteFrom (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    (i : Nat) (q : σ) : Prop :=
  V i q ∧ ∀ N, ∃ j ≥ N, ∃ p, reaches A w V i j q p

/-- An accepting vertex of `V` is reachable from `q` inside `V`. -/
def canAccept (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    (i : Nat) (q : σ) : Prop :=
  ∃ j p, reaches A w V i j q p ∧ A.accept p = true

theorem canAccept_prepend (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    {i : Nat} {src mid : σ}
    (hstep : A.step src (w i) mid = true)
    (hVs : V i src) (hVm : V (i + 1) mid)
    (h : canAccept A w V (i + 1) mid) :
    canAccept A w V i src := by
  obtain ⟨j, p, hreach, hacc⟩ := h
  exact ⟨j, p, reaches_prepend A w V hstep hVs hVm hreach, hacc⟩

theorem exists_step_infinite [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    {i : Nat} {q : σ} (h : infiniteFrom A w V i q) :
    ∃ q', V (i + 1) q' ∧ A.step q (w i) q' = true ∧
      infiniteFrom A w V (i + 1) q' := by
  classical
  obtain ⟨hVq, hfar⟩ := h
  by_contra hnot
  push Not at hnot
  have hbound : ∀ q' : σ, ∃ N, ∀ j ≥ N, ∀ p,
      reaches A w V (i + 1) j q' p →
        ¬ V (i + 1) q' ∨ A.step q (w i) q' ≠ true := by
    intro q'
    by_cases hgood : V (i + 1) q' ∧ A.step q (w i) q' = true
    · have hnotinf : ¬ infiniteFrom A w V (i + 1) q' := hnot q' hgood.1 hgood.2
      have hV' : V (i + 1) q' := hgood.1
      have hfail : ¬ ∀ N, ∃ j ≥ N, ∃ p, reaches A w V (i + 1) j q' p := by
        intro hall
        exact hnotinf ⟨hV', hall⟩
      push Not at hfail
      obtain ⟨N, hN⟩ := hfail
      refine ⟨N, ?_⟩
      intro j hj p hreach
      exact absurd hreach (hN j hj p)
    · refine ⟨0, ?_⟩
      intro j _ p _
      exact not_and_or.mp hgood
  choose bound hb using hbound
  let M : Nat := Finset.univ.sup bound + (i + 2)
  obtain ⟨j, hjM, p, hreach⟩ := hfar M
  have hij : i < j := by
    have hM : i + 2 ≤ M := Nat.le_add_left _ _
    omega
  obtain ⟨mid, hstep, hVmid, htail⟩ := reaches_tail A w V hreach hij
  have hjtail : bound mid ≤ j := by
    have hle : bound mid ≤ Finset.univ.sup bound := Finset.le_sup (Finset.mem_univ mid)
    omega
  have hbad := hb mid j hjtail p htail
  rcases hbad with hnotV | hnotstep
  · exact hnotV hVmid
  · exact hnotstep hstep

theorem antitone_nat_eventually_const (f : Nat → Nat) (hf : ∀ k, f (k + 1) ≤ f k) :
    ∃ N, ∀ k ≥ N, f k = f N := by
  classical
  suffices ∀ (n : Nat) (g : Nat → Nat), (∀ k, g (k + 1) ≤ g k) → g 0 ≤ n →
      ∃ N, ∀ k ≥ N, g k = g N by
    exact this (f 0) f hf le_rfl
  intro n
  induction n with
  | zero =>
    intro g hg hle
    refine ⟨0, ?_⟩
    intro k _
    have hzero : ∀ t, g t = 0 := by
      intro t
      induction t with
      | zero =>
        exact Nat.eq_zero_of_le_zero hle
      | succ t ih =>
        exact Nat.eq_zero_of_le_zero (le_trans (hg t) (Nat.le_of_eq ih))
    exact (hzero k).trans (hzero 0).symm
  | succ n ih =>
    intro g hg hle
    by_cases hdrop : ∃ k, g k < g 0
    · let N := Nat.find hdrop
      have hN : g N < g 0 := Nat.find_spec hdrop
      have hpos : 0 < N := by
        by_contra hzero
        have hNz : N = 0 := Nat.eq_zero_of_not_pos hzero
        rw [hNz] at hN
        omega
      let gshift : Nat → Nat := fun k => g (N + k)
      have hgshift : ∀ k, gshift (k + 1) ≤ gshift k := fun k => hg (N + k)
      have hgle : gshift 0 ≤ n := by
        have hlt : gshift 0 < g 0 := by simpa [gshift] using hN
        omega
      obtain ⟨M, hM⟩ := ih gshift hgshift hgle
      refine ⟨N + M, ?_⟩
      intro k hk
      have hsub : M ≤ k - N := by omega
      have hgk := hM (k - N) hsub
      have hadd : N + (k - N) = k := Nat.add_sub_of_le (le_trans (Nat.le_add_right N M) hk)
      simpa [gshift, hadd] using hgk
    · push Not at hdrop
      refine ⟨0, ?_⟩
      intro k hk
      have hle' : g k ≤ g 0 := by
        clear hk
        induction k with
        | zero => exact le_rfl
        | succ k ihk => exact le_trans (hg k) ihk
      exact Nat.le_antisymm hle' (hdrop k)

/-- `P` holds at `0` and fails at `N + 1`, so it fails for a first time. -/
theorem exists_first_drop {P : Nat → Prop} {N : Nat}
    (h0 : P 0) (hN : ¬ P (N + 1)) :
    ∃ r ≤ N, P r ∧ ¬ P (r + 1) := by
  by_contra h
  push Not at h
  have hall : ∀ r, r ≤ N + 1 → P r := by
    intro r hr
    induction r with
    | zero => exact h0
    | succ r ih =>
      have hr' : r ≤ N := by omega
      exact h r hr' (ih (Nat.le_trans hr' (Nat.le_succ N)))
  exact hN (hall (N + 1) le_rfl)

/-! ## Deletion ranking -/

/-- Round `0` is the run DAG. An even round keeps vertices with an infinite
continuation. An odd round keeps vertices that can still reach an accepting
state. -/
def layer (A : NBA α σ) (w : Nat → α) : Nat → Nat → σ → Prop
  | 0, i, q => reachable A w i q
  | r + 1, i, q =>
    if r % 2 = 0 then
      layer A w r i q ∧ infiniteFrom A w (layer A w r) i q
    else
      layer A w r i q ∧ canAccept A w (layer A w r) i q

theorem layer_succ_left (A : NBA α σ) (w : Nat → α) (r i : Nat) (q : σ) :
    layer A w (r + 1) i q → layer A w r i q := by
  intro h
  rcases Nat.mod_two_eq_zero_or_one r with he | ho
  · simp [layer, he] at h
    exact h.1
  · have hnot : ¬ r % 2 = 0 := by
      intro hz
      rw [ho] at hz
      exact Nat.one_ne_zero hz
    simp [layer, hnot] at h
    exact h.1

theorem layer_le (A : NBA α σ) (w : Nat → α) {r s i : Nat} {q : σ}
    (hrs : r ≤ s) (h : layer A w s i q) : layer A w r i q := by
  induction s with
  | zero =>
    have hr : r = 0 := Nat.eq_zero_of_le_zero hrs
    subst hr
    exact h
  | succ s ih =>
    by_cases hr : r = s + 1
    · subst hr
      exact h
    · have hrs' : r ≤ s := by omega
      exact ih hrs' (layer_succ_left A w s i q h)

theorem layer_infinite_of_even (A : NBA α σ) (w : Nat → α) {r i : Nat} {q : σ}
    (he : r % 2 = 0) (h : layer A w (r + 1) i q) :
    infiniteFrom A w (layer A w r) i q := by
  simp [layer, he] at h
  exact h.2

theorem layer_canAccept_of_odd (A : NBA α σ) (w : Nat → α) {r i : Nat} {q : σ}
    (ho : r % 2 = 1) (h : layer A w (r + 1) i q) :
    canAccept A w (layer A w r) i q := by
  have hnot : ¬ r % 2 = 0 := by
    intro hz
    rw [ho] at hz
    exact Nat.one_ne_zero hz
  simp [layer, hnot] at h
  exact h.2

theorem pred_kept (A : NBA α σ) (w : Nat → α) (r i : Nat) (p q : σ)
    (hstep : A.step p (w i) q = true)
    (hp : layer A w r i p)
    (hq : layer A w (r + 1) (i + 1) q) :
    layer A w (r + 1) i p := by
  have hqR : layer A w r (i + 1) q := layer_succ_left A w r (i + 1) q hq
  rcases Nat.mod_two_eq_zero_or_one r with he | ho
  · have hinf : infiniteFrom A w (layer A w r) (i + 1) q :=
      layer_infinite_of_even A w he hq
    simp [layer, he]
    refine ⟨hp, ?_⟩
    refine ⟨hp, ?_⟩
    intro N
    obtain ⟨j, hj, dst, hreach⟩ := hinf.2 (max N (i + 1))
    have hij : i + 1 ≤ j := le_trans (le_max_right _ _) hj
    exact ⟨j, le_trans (le_max_left _ _) hj, dst,
      reaches_prepend A w (layer A w r) hstep hp hqR hreach⟩
  · have hacc : canAccept A w (layer A w r) (i + 1) q :=
      layer_canAccept_of_odd A w ho hq
    have hnot : ¬ r % 2 = 0 := by
      intro hz
      rw [ho] at hz
      exact Nat.one_ne_zero hz
    simp [layer, hnot]
    exact ⟨hp, canAccept_prepend A w (layer A w r) hstep hp hqR hacc⟩

def Fits (P : σ → Prop) (bound : Nat) : Prop :=
  ∃ l : List σ, l.Nodup ∧ l.length ≤ bound ∧ ∀ q, P q → q ∈ l

theorem fits_card [Fintype σ] [DecidableEq σ] (P : σ → Prop) :
    Fits P (Fintype.card σ) := by
  classical
  refine ⟨(Finset.univ : Finset σ).toList, Finset.nodup_toList _, ?_, ?_⟩
  · simp [Finset.length_toList, Finset.card_univ]
  · intro q _
    exact Finset.mem_toList.mpr (Finset.mem_univ q)

theorem fits_of_imp {P Q : σ → Prop} {b : Nat}
    (h : ∀ q, P q → Q q) (hQ : Fits Q b) : Fits P b := by
  obtain ⟨l, hnodup, hlen, hmem⟩ := hQ
  exact ⟨l, hnodup, hlen, fun q hq => hmem q (h q hq)⟩

theorem fits_erase [DecidableEq σ] {P Q : σ → Prop} {b : Nat} {q0 : σ}
    (hQ : Fits Q (b + 1)) (hq0 : Q q0) (hsub : ∀ q, P q → Q q) (hnot : ¬ P q0) :
    Fits P b := by
  obtain ⟨l, hnodup, hlen, hmem⟩ := hQ
  have hqmem : q0 ∈ l := hmem q0 hq0
  refine ⟨l.erase q0, hnodup.erase q0, ?_, ?_⟩
  · have hlen' : (l.erase q0).length + 1 = l.length := List.length_erase_add_one hqmem
    omega
  · intro q hq
    have hmemq : q ∈ l := hmem q (hsub q hq)
    have hne : q ≠ q0 := by
      intro heq
      exact hnot (heq ▸ hq)
    exact (List.mem_erase_of_ne hne).mpr hmemq

theorem succ_in_next_layer (A : NBA α σ) (w : Nat → α) {r i : Nat} {q : σ}
    [Fintype σ] [DecidableEq σ]
    (he : r % 2 = 0) (h : layer A w (r + 1) i q) :
    ∃ q', layer A w (r + 1) (i + 1) q' ∧ A.step q (w i) q' = true := by
  have hinf : infiniteFrom A w (layer A w r) i q := layer_infinite_of_even A w he h
  obtain ⟨q', hV, hstep, hinf'⟩ := exists_step_infinite A w (layer A w r) hinf
  refine ⟨q', ?_, hstep⟩
  simp [layer, he]
  exact ⟨hV, hinf'⟩

/-- A vertex that can reach an accepting vertex passes that ability to its source. -/
theorem not_canAccept_of_pred (A : NBA α σ) (w : Nat → α) (V : Nat → σ → Prop)
    {i : Nat} {p q : σ}
    (hstep : A.step p (w i) q = true) (hp : V i p) (hq : V (i + 1) q)
    (hsafe : ¬ canAccept A w V i p) :
    ¬ canAccept A w V (i + 1) q := by
  intro hacc
  exact hsafe (canAccept_prepend A w V hstep hp hq hacc)

/-! ## Accepting run when the kernel has no safe vertex -/

/-- One step that stays in the current kernel, followed by a walk to an
accepting state that also stays in the kernel. -/
structure AccExt (A : NBA α σ) (w : Nat → α) (r i : Nat) (q : σ) where
  q1 : σ
  j : Nat
  dst : σ
  path : Nat → σ
  step1 : A.step q (w i) q1 = true
  layer1 : layer A w (r + 1) (i + 1) q1
  lej : i + 1 ≤ j
  acc : A.accept dst = true
  layerDst : layer A w (r + 1) j dst
  path0 : path 0 = q1
  pathEnd : path (j - (i + 1)) = dst
  steps : ∀ k < j - (i + 1),
    A.step (path k) (w (i + 1 + k)) (path (k + 1)) = true

/-- A vertex of round `r + 1`. -/
structure LayerPt (A : NBA α σ) (w : Nat → α) (r : Nat) where
  i : Nat
  q : σ
  mem : layer A w (r + 1) i q

/-- A kernel vertex together with the accepting extension that leaves it. -/
structure Staged (A : NBA α σ) (w : Nat → α) (r : Nat) where
  pt : LayerPt A w r
  ext : AccExt A w r pt.i pt.q

/-- The hypothesis of `accepts_of_no_safe`: round `r` is even, and every vertex
kept at round `r + 1` can still reach an accepting vertex inside that round. -/
structure NoSafe (A : NBA α σ) (w : Nat → α) where
  r : Nat
  even : r % 2 = 0
  noSafe : ∀ i q, layer A w (r + 1) i q → canAccept A w (layer A w (r + 1)) i q
  i0 : Nat
  q0 : σ
  mem0 : layer A w (r + 1) i0 q0

theorem exists_accExt [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w)
    {i : Nat} {q : σ} (hq : layer A w (K.r + 1) i q) :
    Nonempty (AccExt A w K.r i q) := by
  obtain ⟨q1, hq1, hstep1⟩ := succ_in_next_layer A w K.even hq
  obtain ⟨j, dst, hreach, hacc⟩ := K.noSafe (i + 1) q1 hq1
  obtain ⟨hle, _, hVd, path, h0, hend, hst⟩ := hreach
  exact ⟨{
    q1 := q1
    j := j
    dst := dst
    path := path
    step1 := hstep1
    layer1 := hq1
    lej := hle
    acc := hacc
    layerDst := hVd
    path0 := h0
    pathEnd := hend
    steps := fun k hk => (hst k hk).1
  }⟩

noncomputable def chooseExt [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w)
    {i : Nat} {q : σ} (hq : layer A w (K.r + 1) i q) : AccExt A w K.r i q :=
  Classical.choice (exists_accExt A w K hq)

noncomputable def stages [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) : Nat → Staged A w K.r
  | 0 =>
    let pt : LayerPt A w K.r := ⟨K.i0, K.q0, K.mem0⟩
    ⟨pt, chooseExt A w K pt.mem⟩
  | n + 1 =>
    let prev := stages A w K n
    let pt : LayerPt A w K.r := ⟨prev.ext.j, prev.ext.dst, prev.ext.layerDst⟩
    ⟨pt, chooseExt A w K pt.mem⟩

theorem stages_zero_i [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) :
    (stages A w K 0).pt.i = K.i0 := by
  simp [stages]

theorem stages_zero_q [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) :
    (stages A w K 0).pt.q = K.q0 := by
  simp [stages]

theorem stages_succ_i [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (n : Nat) :
    (stages A w K (n + 1)).pt.i = (stages A w K n).ext.j := by
  simp [stages]

theorem stages_succ_q [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (n : Nat) :
    (stages A w K (n + 1)).pt.q = (stages A w K n).ext.dst := by
  simp [stages]

theorem stages_strict [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (n : Nat) :
    (stages A w K n).pt.i < (stages A w K (n + 1)).pt.i := by
  have hs := stages_succ_i A w K n
  have hle := (stages A w K n).ext.lej
  omega

theorem stages_mono [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) :
    ∀ {a b : Nat}, a ≤ b → (stages A w K a).pt.i ≤ (stages A w K b).pt.i := by
  intro a b hab
  induction b generalizing a with
  | zero =>
    have ha : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha
    exact le_rfl
  | succ b ih =>
    by_cases hab' : a = b + 1
    · subst hab'
      exact le_rfl
    · have hab'' : a ≤ b := by omega
      exact le_trans (ih hab'') (Nat.le_of_lt (stages_strict A w K b))

theorem stages_ge [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (n : Nat) :
    K.i0 + n ≤ (stages A w K n).pt.i := by
  induction n with
  | zero =>
    simp [stages_zero_i]
  | succ n ih =>
    have hs := stages_succ_i A w K n
    have hle := (stages A w K n).ext.lej
    omega

theorem stages_bound [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t : Nat) :
    ∃ n, t < (stages A w K (n + 1)).pt.i := by
  refine ⟨t, ?_⟩
  have hge := stages_ge A w K (t + 1)
  omega

noncomputable def stageIndex [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t : Nat) : Nat :=
  @Nat.find (fun n => t < (stages A w K (n + 1)).pt.i)
    (Classical.decPred _) (stages_bound A w K t)

theorem stageIndex_hi [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t : Nat) :
    t < (stages A w K (stageIndex A w K t + 1)).pt.i := by
  simpa [stageIndex] using
    (@Nat.find_spec (fun n => t < (stages A w K (n + 1)).pt.i)
      (Classical.decPred _) (stages_bound A w K t))

theorem stageIndex_min [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t m : Nat)
    (hm : m < stageIndex A w K t) :
    ¬ t < (stages A w K (m + 1)).pt.i := by
  have hm' : m < @Nat.find (fun n => t < (stages A w K (n + 1)).pt.i)
      (Classical.decPred _) (stages_bound A w K t) := by
    simpa [stageIndex] using hm
  exact (@Nat.find_min (fun n => t < (stages A w K (n + 1)).pt.i)
    (Classical.decPred _) (stages_bound A w K t)) hm'

theorem stageIndex_le [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t n : Nat)
    (hn : t < (stages A w K (n + 1)).pt.i) :
    stageIndex A w K t ≤ n := by
  simpa [stageIndex] using
    (@Nat.find_min' (fun k => t < (stages A w K (k + 1)).pt.i)
      (Classical.decPred _) (stages_bound A w K t) n hn)

theorem stageIndex_lo [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t : Nat) (ht : K.i0 ≤ t) :
    (stages A w K (stageIndex A w K t)).pt.i ≤ t := by
  by_cases hz : stageIndex A w K t = 0
  · rw [hz, stages_zero_i]
    exact ht
  · have hpred : stageIndex A w K t - 1 < stageIndex A w K t := by omega
    have hnot := stageIndex_min A w K t (stageIndex A w K t - 1) hpred
    have hidx : stageIndex A w K t - 1 + 1 = stageIndex A w K t := by omega
    rw [hidx] at hnot
    exact Nat.not_lt.mp hnot

theorem stageIndex_at [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (n : Nat) :
    stageIndex A w K (stages A w K n).pt.i = n := by
  set t := (stages A w K n).pt.i
  refine Nat.le_antisymm ?_ ?_
  · exact stageIndex_le A w K t n (stages_strict A w K n)
  · by_contra hlt
    have hlt' : stageIndex A w K t < n := by omega
    have hmono := stages_mono A w K (Nat.succ_le_of_lt hlt')
    rw [Nat.succ_eq_add_one] at hmono
    have hhi := stageIndex_hi A w K t
    omega

theorem stageIndex_same [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t : Nat) (_ht : K.i0 ≤ t)
    (hinside : t + 1 < (stages A w K (stageIndex A w K t)).ext.j) :
    stageIndex A w K (t + 1) = stageIndex A w K t := by
  have htop : t + 1 < (stages A w K (stageIndex A w K t + 1)).pt.i := by
    rw [stages_succ_i]
    exact hinside
  have hle : stageIndex A w K (t + 1) ≤ stageIndex A w K t :=
    stageIndex_le A w K (t + 1) (stageIndex A w K t) htop
  have hge : stageIndex A w K t ≤ stageIndex A w K (t + 1) := by
    by_contra hlt
    have hlt' : stageIndex A w K (t + 1) < stageIndex A w K t := by omega
    have hnot := stageIndex_min A w K t _ hlt'
    have hhi := stageIndex_hi A w K (t + 1)
    omega
  omega

theorem stageIndex_cross [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (t : Nat) (_ht : K.i0 ≤ t)
    (hcross : t + 1 = (stages A w K (stageIndex A w K t)).ext.j) :
    stageIndex A w K (t + 1) = stageIndex A w K t + 1 := by
  have htime : t + 1 = (stages A w K (stageIndex A w K t + 1)).pt.i := by
    rw [stages_succ_i]
    exact hcross
  have htop : t + 1 < (stages A w K (stageIndex A w K t + 1 + 1)).pt.i := by
    rw [htime]
    exact stages_strict A w K (stageIndex A w K t + 1)
  have hle : stageIndex A w K (t + 1) ≤ stageIndex A w K t + 1 :=
    stageIndex_le A w K (t + 1) (stageIndex A w K t + 1) htop
  have hge : stageIndex A w K t + 1 ≤ stageIndex A w K (t + 1) := by
    by_contra hlt
    have hlt' : stageIndex A w K (t + 1) ≤ stageIndex A w K t := by omega
    have hmono := stages_mono A w K (Nat.add_le_add_right hlt' 1)
    have hhi := stageIndex_hi A w K (t + 1)
    omega
  omega

noncomputable def rankPath [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (stem : Nat → σ) (t : Nat) : σ :=
  if _ : t < K.i0 then
    stem t
  else
    let s := stages A w K (stageIndex A w K t)
    if t = s.pt.i then s.pt.q else s.ext.path (t - (s.pt.i + 1))

theorem rankPath_stem [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (stem : Nat → σ)
    {t : Nat} (ht : t < K.i0) :
    rankPath A w K stem t = stem t := by
  simp [rankPath, ht]

theorem rankPath_at_index [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (stem : Nat → σ)
    {t n : Nat} (ht : K.i0 ≤ t) (hn : stageIndex A w K t = n) :
    rankPath A w K stem t =
      if t = (stages A w K n).pt.i then (stages A w K n).pt.q
      else (stages A w K n).ext.path (t - ((stages A w K n).pt.i + 1)) := by
  have hnot : ¬ t < K.i0 := Nat.not_lt.mpr ht
  subst hn
  simp [rankPath, hnot]

theorem rankPath_at_stage [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (stem : Nat → σ) (n : Nat) :
    rankPath A w K stem (stages A w K n).pt.i = (stages A w K n).pt.q := by
  have hge : K.i0 ≤ (stages A w K n).pt.i := by
    have := stages_ge A w K n
    omega
  have hidx := stageIndex_at A w K n
  rw [rankPath_at_index A w K stem hge hidx, if_pos rfl]

theorem rankPath_start [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (stem : Nat → σ)
    (hstart : A.start (stem 0) = true) (hstemEnd : stem K.i0 = K.q0) :
    A.start (rankPath A w K stem 0) = true := by
  by_cases h0 : K.i0 = 0
  · have hge : K.i0 ≤ K.i0 := le_rfl
    have hidx : stageIndex A w K K.i0 = 0 := by
      have hidx0 := stageIndex_at A w K 0
      rw [stages_zero_i] at hidx0
      exact hidx0
    have hpt := rankPath_at_index A w K stem hge hidx
    rw [if_pos (stages_zero_i A w K).symm] at hpt
    rw [stages_zero_q] at hpt
    rw [← h0, hpt, ← hstemEnd, h0]
    exact hstart
  · have hlt : 0 < K.i0 := by omega
    rw [rankPath_stem A w K stem hlt]
    exact hstart

theorem rankPath_step [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (K : NoSafe A w) (stem : Nat → σ)
    (hstemEnd : stem K.i0 = K.q0)
    (hstemStep : ∀ k < K.i0, A.step (stem k) (w k) (stem (k + 1)) = true) :
    ∀ t, A.step (rankPath A w K stem t) (w t)
      (rankPath A w K stem (t + 1)) = true := by
  intro t
  by_cases ht : t < K.i0
  · by_cases ht1 : t + 1 < K.i0
    · rw [rankPath_stem A w K stem ht, rankPath_stem A w K stem ht1]
      exact hstemStep t ht
    · have heq : t + 1 = K.i0 := by omega
      have hleft : rankPath A w K stem t = stem t := rankPath_stem A w K stem ht
      have hright : rankPath A w K stem (t + 1) = stem (t + 1) := by
        rw [heq]
        have hpt := rankPath_at_stage A w K stem 0
        rw [stages_zero_i, stages_zero_q, ← hstemEnd] at hpt
        exact hpt
      rw [hleft, hright]
      exact hstemStep t ht
  · have htge : K.i0 ≤ t := Nat.le_of_not_gt ht
    let n := stageIndex A w K t
    let s := stages A w K n
    have hn : stageIndex A w K t = n := rfl
    have hlo : s.pt.i ≤ t := by
      simpa [s, n] using stageIndex_lo A w K t htge
    have hhi : t < s.ext.j := by
      have htop := stageIndex_hi A w K t
      rw [stages_succ_i A w K n] at htop
      simpa [s, n] using htop
    have hpt := rankPath_at_index A w K stem htge hn
    have ht1 : K.i0 ≤ t + 1 := Nat.le_trans htge (Nat.le_succ t)
    by_cases hinside : t + 1 < s.ext.j
    · have hidx1 : stageIndex A w K (t + 1) = n := by
        have h := stageIndex_same A w K t htge (by simpa [s, n] using hinside)
        simpa [n] using h
      have hpt1 := rankPath_at_index A w K stem ht1 hidx1
      by_cases heq : t = s.pt.i
      · have hne : t + 1 ≠ s.pt.i := by omega
        have h0 : t + 1 - (s.pt.i + 1) = 0 := by omega
        rw [if_pos heq] at hpt
        rw [if_neg hne, h0, s.ext.path0] at hpt1
        rw [hpt, hpt1, heq]
        exact s.ext.step1
      · have hgt : s.pt.i + 1 ≤ t := by omega
        have hk : t - (s.pt.i + 1) < s.ext.j - (s.pt.i + 1) := by omega
        have hk1 : t + 1 - (s.pt.i + 1) = t - (s.pt.i + 1) + 1 := by omega
        have htime : s.pt.i + 1 + (t - (s.pt.i + 1)) = t := by omega
        rw [if_neg heq] at hpt
        have hne : t + 1 ≠ s.pt.i := by omega
        rw [if_neg hne, hk1] at hpt1
        have hstep := s.ext.steps (t - (s.pt.i + 1)) hk
        rw [htime] at hstep
        rw [hpt, hpt1]
        exact hstep
    · have hcross : t + 1 = s.ext.j := by omega
      have hidx1 : stageIndex A w K (t + 1) = n + 1 := by
        have h := stageIndex_cross A w K t htge (by simpa [s, n] using hcross)
        simpa [n] using h
      have hpt1 := rankPath_at_index A w K stem ht1 hidx1
      have htime1 : t + 1 = (stages A w K (n + 1)).pt.i := by
        rw [stages_succ_i A w K n]
        simpa [s, n] using hcross
      rw [htime1, if_pos rfl] at hpt1
      rw [stages_succ_q A w K n] at hpt1
      by_cases heq : t = s.pt.i
      · have hzero : s.ext.j - (s.pt.i + 1) = 0 := by omega
        have hdst : s.ext.dst = s.ext.q1 := by
          have hend := s.ext.pathEnd
          rw [hzero, s.ext.path0] at hend
          exact hend.symm
        rw [if_pos heq] at hpt
        rw [← htime1] at hpt1
        rw [hpt, hpt1, heq, hdst]
        exact s.ext.step1
      · have hgt : s.pt.i + 1 ≤ t := by omega
        have hk : t - (s.pt.i + 1) < s.ext.j - (s.pt.i + 1) := by omega
        have hk1 : t - (s.pt.i + 1) + 1 = s.ext.j - (s.pt.i + 1) := by omega
        have htime : s.pt.i + 1 + (t - (s.pt.i + 1)) = t := by omega
        have hlast : s.ext.path (t - (s.pt.i + 1) + 1) = s.ext.dst := by
          rw [hk1]
          exact s.ext.pathEnd
        rw [if_neg heq] at hpt
        rw [← htime1] at hpt1
        have hstep := s.ext.steps (t - (s.pt.i + 1)) hk
        rw [htime, hlast] at hstep
        rw [hpt, hpt1]
        exact hstep

/-- If every vertex kept at an even-round successor can still reach an accepting
vertex, and at least one such vertex exists, the word is accepted. -/
theorem accepts_of_no_safe [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (r : Nat) (he : r % 2 = 0)
    (hno : ∀ i q, layer A w (r + 1) i q → canAccept A w (layer A w (r + 1)) i q)
    (h0 : ∃ i q, layer A w (r + 1) i q) :
    Accepts A w := by
  obtain ⟨i0, q0, hq0⟩ := h0
  let K : NoSafe A w := ⟨r, he, hno, i0, q0, hq0⟩
  obtain ⟨stem, hstemEnd, hstart, hstemStep⟩ :=
    reachable_path A w i0 q0 (layer_le A w (Nat.zero_le _) hq0)
  have hstemEnd' : stem K.i0 = K.q0 := by simpa [K] using hstemEnd
  have hstemStep' : ∀ k < K.i0, A.step (stem k) (w k) (stem (k + 1)) = true := by
    simpa [K] using hstemStep
  refine ⟨rankPath A w K stem, ?_, ?_, ?_⟩
  · exact rankPath_start A w K stem hstart hstemEnd'
  · exact rankPath_step A w K stem hstemEnd' hstemStep'
  · intro N
    refine ⟨(stages A w K (N + 1)).pt.i, ?_, ?_⟩
    · have hge := stages_ge A w K (N + 1)
      omega
    · rw [rankPath_at_stage A w K stem (N + 1), stages_succ_q]
      exact (stages A w K N).ext.acc


theorem fits_none {P : σ → Prop} {b : Nat} (h : ∀ q, ¬ P q) : Fits P b :=
  ⟨[], List.nodup_nil, Nat.zero_le _, fun q hq => (h q hq).elim⟩

theorem fits_zero {P : σ → Prop} (h : Fits P 0) (q : σ) : ¬ P q := by
  intro hq
  obtain ⟨l, _, hlen, hmem⟩ := h
  have hmemq : q ∈ l := hmem q hq
  have hnil : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
  rw [hnil] at hmemq
  cases hmemq

/-- A vertex of an even-round successor that cannot reach an accepting vertex. -/
structure SafePt (A : NBA α σ) (w : Nat → α) (r : Nat) where
  i : Nat
  q : σ
  mem : layer A w (r + 1) i q
  safe : ¬ canAccept A w (layer A w (r + 1)) i q

structure SafeStep (A : NBA α σ) (w : Nat → α) (r : Nat) (p : SafePt A w r) where
  q' : σ
  step : A.step p.q (w p.i) q' = true
  mem : layer A w (r + 1) (p.i + 1) q'
  safe : ¬ canAccept A w (layer A w (r + 1)) (p.i + 1) q'

theorem safeStep_nonempty [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) {r : Nat} (he : r % 2 = 0) (p : SafePt A w r) :
    Nonempty (SafeStep A w r p) := by
  obtain ⟨q', hq', hstep⟩ := succ_in_next_layer A w he p.mem
  exact ⟨⟨q', hstep, hq',
    not_canAccept_of_pred A w (layer A w (r + 1)) hstep p.mem hq' p.safe⟩⟩

noncomputable def takeSafeStep [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) {r : Nat} (he : r % 2 = 0) (p : SafePt A w r) :
    SafeStep A w r p :=
  Classical.choice (safeStep_nonempty A w he p)

noncomputable def safeChain [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) {r : Nat} (he : r % 2 = 0)
    (p0 : SafePt A w r) : Nat → SafePt A w r
  | 0 => p0
  | n + 1 =>
    let prev := safeChain A w he p0 n
    let s := takeSafeStep A w he prev
    ⟨prev.i + 1, s.q', s.mem, s.safe⟩

theorem safeChain_zero [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) {r : Nat} (he : r % 2 = 0) (p0 : SafePt A w r) :
    safeChain A w he p0 0 = p0 := rfl

theorem safeChain_succ_i [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) {r : Nat} (he : r % 2 = 0)
    (p0 : SafePt A w r) (n : Nat) :
    (safeChain A w he p0 (n + 1)).i = (safeChain A w he p0 n).i + 1 := rfl

theorem safeChain_index [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) {r : Nat} (he : r % 2 = 0)
    (p0 : SafePt A w r) (n : Nat) :
    (safeChain A w he p0 n).i = p0.i + n := by
  induction n with
  | zero => simp [safeChain_zero]
  | succ n ih =>
    rw [safeChain_succ_i, ih]
    omega

theorem not_layer_of_safe (A : NBA α σ) (w : Nat → α) {r i : Nat} {q : σ}
    (he : r % 2 = 0) (_hmem : layer A w (r + 1) i q)
    (hsafe : ¬ canAccept A w (layer A w (r + 1)) i q) :
    ¬ layer A w (r + 2) i q := by
  have hodd : (r + 1) % 2 = 1 := by omega
  intro h
  exact hsafe (layer_canAccept_of_odd A w hodd h)

/-- On a rejecting word, round `2k` is eventually at most `|Q| - k` states wide. -/
theorem level_narrow [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) :
    ∀ k, k ≤ Fintype.card σ →
      ∃ N, ∀ i ≥ N, Fits (fun q => layer A w (2 * k) i q) (Fintype.card σ - k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, fun i _ => ?_⟩
    simpa [Nat.sub_zero, Nat.mul_zero] using
      (fits_card (fun q => layer A w 0 i q))
  | succ k ih =>
    intro hk
    have hk' : k ≤ Fintype.card σ := by omega
    obtain ⟨N, hN⟩ := ih hk'
    let r := 2 * k
    have he : r % 2 = 0 := by omega
    have hr2 : r + 2 = 2 * (k + 1) := by omega
    by_cases hempty : ∃ M, ∀ i ≥ M, ∀ q, ¬ layer A w (r + 1) i q
    · obtain ⟨M, hM⟩ := hempty
      refine ⟨M, ?_⟩
      intro i hi
      apply fits_none
      intro q hq
      have hsub : layer A w (r + 1) i q :=
        layer_le A w (by omega : r + 1 ≤ r + 2) (by simpa [← hr2] using hq)
      exact hM i hi q hsub
    · have hunb : ∀ M, ∃ i ≥ M, ∃ q, layer A w (r + 1) i q := by
        intro M
        by_contra hnone
        apply hempty
        refine ⟨M, ?_⟩
        intro i hi q hq
        apply hnone
        exact ⟨i, hi, q, hq⟩
      have hsafe : ∃ i q, layer A w (r + 1) i q ∧
          ¬ canAccept A w (layer A w (r + 1)) i q := by
        by_contra hall
        have hno : ∀ i q, layer A w (r + 1) i q →
            canAccept A w (layer A w (r + 1)) i q := by
          intro i q hq
          by_contra hnot
          exact hall ⟨i, q, hq, hnot⟩
        obtain ⟨i, _, ⟨q, hq⟩⟩ := hunb 0
        exact hrej (accepts_of_no_safe A w r he hno ⟨i, q, hq⟩)
      obtain ⟨i0, q0, hmem0, hsafe0⟩ := hsafe
      let p0 : SafePt A w r := ⟨i0, q0, hmem0, hsafe0⟩
      refine ⟨max N i0, ?_⟩
      intro i hi
      have hiN : N ≤ i := le_trans (le_max_left _ _) hi
      have hi0 : i0 ≤ i := le_trans (le_max_right _ _) hi
      have hfit := hN i hiN
      have hbound : Fintype.card σ - k = Fintype.card σ - (k + 1) + 1 := by omega
      rw [hbound] at hfit
      let nDrop := i - i0
      have hp0i : p0.i = i0 := rfl
      have hidx := safeChain_index A w he p0 nDrop
      have htime : (safeChain A w he p0 nDrop).i = i := by
        rw [hidx, hp0i]
        exact Nat.add_sub_of_le hi0
      have hmemS : layer A w (r + 1) i (safeChain A w he p0 nDrop).q := by
        have hmem := (safeChain A w he p0 nDrop).mem
        rwa [htime] at hmem
      have hsafeS : ¬ canAccept A w (layer A w (r + 1)) i
          (safeChain A w he p0 nDrop).q := by
        have hsafeC := (safeChain A w he p0 nDrop).safe
        rwa [htime] at hsafeC
      have hinR : layer A w r i (safeChain A w he p0 nDrop).q :=
        layer_le A w (Nat.le_succ r) hmemS
      have hnot : ¬ layer A w (r + 2) i (safeChain A w he p0 nDrop).q :=
        not_layer_of_safe A w he hmemS hsafeS
      have hsub : ∀ q, layer A w (r + 2) i q → layer A w r i q :=
        fun q hq => layer_le A w (by omega : r ≤ r + 2) hq
      have hfit' : Fits (fun q => layer A w (r + 2) i q) (Fintype.card σ - (k + 1)) :=
        fits_erase hfit hinR hsub hnot
      simpa [hr2] using hfit'

theorem fits_eventually_empty [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) :
    ∃ N, ∀ i ≥ N, ∀ q, ¬ layer A w (2 * Fintype.card σ) i q := by
  obtain ⟨N, hN⟩ := level_narrow A w hrej (Fintype.card σ) le_rfl
  refine ⟨N, ?_⟩
  intro i hi q hq
  exact fits_zero (by simpa using hN i hi) q hq

theorem not_infinite_of_eventually_empty (A : NBA α σ) (w : Nat → α)
    (V : Nat → σ → Prop)
    (h : ∃ N, ∀ i ≥ N, ∀ q, ¬ V i q) (i : Nat) (q : σ) :
    ¬ infiniteFrom A w V i q := by
  intro hinf
  obtain ⟨N, hN⟩ := h
  obtain ⟨j, hj, p, hreach⟩ := hinf.2 (N + i + 1)
  obtain ⟨_, _, hVj, _⟩ := hreach
  have hjN : N ≤ j := by omega
  exact hN j hjN p hVj

theorem not_layer_succ_of_no_infinite (A : NBA α σ) (w : Nat → α) {r : Nat}
    (he : r % 2 = 0)
    (hfin : ∀ i q, ¬ infiniteFrom A w (layer A w r) i q) (i : Nat) (q : σ) :
    ¬ layer A w (r + 1) i q := by
  intro h
  exact hfin i q (layer_infinite_of_even A w he h)

theorem rank_ceiling [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) (q : σ) :
    ¬ layer A w (2 * Fintype.card σ + 1) i q := by
  have hempty := fits_eventually_empty A w hrej
  have he : (2 * Fintype.card σ) % 2 = 0 := by omega
  exact not_layer_succ_of_no_infinite A w he
    (fun j p => not_infinite_of_eventually_empty A w (layer A w (2 * Fintype.card σ)) hempty j p)
    i q

theorem exists_rank_drop [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    {i : Nat} {q : σ} (h : reachable A w i q) :
    ∃ r ≤ 2 * Fintype.card σ, layer A w r i q ∧ ¬ layer A w (r + 1) i q := by
  have h0 : layer A w 0 i q := by simpa [layer] using h
  exact exists_first_drop h0 (rank_ceiling A w hrej i q)

/-- A ranking of the run DAG. Odd ranks are rejecting, ranks do not rise along
an edge, and every infinite path is eventually constant at an odd rank. -/
structure VertexRank (A : NBA α σ) (w : Nat → α) where
  val : Nat → σ → Option Nat
  bound : Nat
  defined_iff : ∀ i q, (val i q).isSome = true ↔ reachable A w i q
  le_bound : ∀ i q r, val i q = some r → r ≤ bound
  odd_not_accept : ∀ i q r, val i q = some r → r % 2 = 1 → A.accept q = false
  nonincreasing : ∀ (i : Nat) (p q : σ) (rp rq : Nat),
    val i p = some rp → val (i + 1) q = some rq →
      A.step p (w i) q = true → rq ≤ rp
  trapped_odd : ∀ (i0 : Nat) (path : Nat → σ),
    reachable A w i0 (path 0) →
    (∀ k, A.step (path k) (w (i0 + k)) (path (k + 1)) = true) →
    ∃ N r, r % 2 = 1 ∧ ∀ k ≥ N, val (i0 + k) (path k) = some r

theorem oddRank_not_accepts
    (A : NBA α σ) (w : Nat → α) (R : VertexRank A w) : ¬ Accepts A w := by
  intro hacc
  obtain ⟨path, hstart, hstep, hrun⟩ := hacc
  have hreach0 : reachable A w 0 (path 0) := by simpa [reachable] using hstart
  have hstep0 : ∀ k, A.step (path k) (w (0 + k)) (path (k + 1)) = true := by
    intro k
    simpa [Nat.zero_add] using hstep k
  obtain ⟨N, r, hodd, hconst⟩ := R.trapped_odd 0 path hreach0 hstep0
  obtain ⟨visit, hv, haccv⟩ := hrun N
  have hval : R.val visit (path visit) = some r := by
    simpa [Nat.zero_add] using hconst visit hv
  have hfalse := R.odd_not_accept visit (path visit) r hval hodd
  rw [hfalse] at haccv
  exact Bool.false_ne_true haccv

/-! ## Deletion rank of one word -/

noncomputable def rankOf [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) (q : σ) : Option Nat :=
  @dite _ (reachable A w i q) (Classical.propDecidable _)
    (fun h => some (Classical.choose (exists_rank_drop A w hrej h)))
    (fun _ => none)

theorem rankOf_pos [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    {i : Nat} {q : σ} (h : reachable A w i q) :
    rankOf A w hrej i q =
      some (Classical.choose (exists_rank_drop A w hrej h)) := by
  unfold rankOf
  exact dif_pos h

theorem rankOf_neg [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    {i : Nat} {q : σ} (h : ¬ reachable A w i q) :
    rankOf A w hrej i q = none := by
  unfold rankOf
  exact dif_neg h

theorem rankOf_spec [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    {i : Nat} {q : σ} (h : reachable A w i q) :
    ∃ r, rankOf A w hrej i q = some r ∧ r ≤ 2 * Fintype.card σ ∧
      layer A w r i q ∧ ¬ layer A w (r + 1) i q := by
  refine ⟨Classical.choose (exists_rank_drop A w hrej h), rankOf_pos A w hrej h, ?_⟩
  have spec := Classical.choose_spec (exists_rank_drop A w hrej h)
  exact ⟨spec.1, spec.2.1, spec.2.2⟩

theorem rankOf_of_some [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    {i : Nat} {q : σ} {r : Nat} (h : rankOf A w hrej i q = some r) :
    r ≤ 2 * Fintype.card σ ∧ layer A w r i q ∧ ¬ layer A w (r + 1) i q ∧
      reachable A w i q := by
  by_cases hreach : reachable A w i q
  · obtain ⟨r', heq, hle, hlayer, hnot⟩ := rankOf_spec A w hrej hreach
    have hr : r' = r := by
      rw [heq] at h
      exact Option.some_inj.mp h
    subst hr
    exact ⟨hle, hlayer, hnot, hreach⟩
  · rw [rankOf_neg A w hrej hreach] at h
    cases h

theorem rankOf_odd_reject [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    {i : Nat} {q : σ} {r : Nat} (h : rankOf A w hrej i q = some r) (hodd : r % 2 = 1) :
    A.accept q = false := by
  obtain ⟨_, hlayer, hnot, _⟩ := rankOf_of_some A w hrej h
  by_contra hacc
  apply hnot
  have hmod : ¬ r % 2 = 0 := by
    intro hz
    rw [hodd] at hz
    exact Nat.one_ne_zero hz
  have htrue : A.accept q = true := by
    cases hb : A.accept q
    · exact (hacc hb).elim
    · rfl
  have hcan : canAccept A w (layer A w r) i q :=
    ⟨i, q, reaches_refl (layer A w r) A w hlayer, htrue⟩
  simpa [layer, hmod] using And.intro hlayer hcan

theorem rankOf_nonincreasing [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    {i : Nat} {p q : σ} {rp rq : Nat}
    (hp : rankOf A w hrej i p = some rp) (hq : rankOf A w hrej (i + 1) q = some rq)
    (hstep : A.step p (w i) q = true) : rq ≤ rp := by
  obtain ⟨_, hpL, hpN, _⟩ := rankOf_of_some A w hrej hp
  obtain ⟨_, hqL, _, _⟩ := rankOf_of_some A w hrej hq
  by_contra hlt
  have hle : rp + 1 ≤ rq := by omega
  exact hpN (pred_kept A w rp i p q hstep hpL (layer_le A w hle hqL))

theorem reachable_along_path (A : NBA α σ) (w : Nat → α)
    (i0 : Nat) (path : Nat → σ)
    (h0 : reachable A w i0 (path 0))
    (hstep : ∀ k, A.step (path k) (w (i0 + k)) (path (k + 1)) = true) :
    ∀ k, reachable A w (i0 + k) (path k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hidx : i0 + (k + 1) = i0 + k + 1 := by omega
    rw [hidx, reachable_succ]
    exact ⟨path k, ih, hstep k⟩

theorem reaches_segment (A : NBA α σ) (w : Nat → α)
    (V : Nat → σ → Prop) (i len : Nat) (path : Nat → σ)
    (hV : ∀ k, k ≤ len → V (i + k) (path k))
    (hstep : ∀ k, k < len →
      A.step (path k) (w (i + k)) (path (k + 1)) = true) :
    reaches A w V i (i + len) (path 0) (path len) := by
  refine ⟨Nat.le_add_right _ _, ?_, hV len le_rfl, path, rfl, ?_, ?_⟩
  · simpa using hV 0 (Nat.zero_le _)
  · rw [Nat.add_sub_cancel_left]
  · intro k hk
    have hlen : k < len := by
      rw [Nat.add_sub_cancel_left] at hk
      exact hk
    refine ⟨hstep k hlen, hV k (Nat.le_of_lt hlen), ?_⟩
    have htime : i + k + 1 = i + (k + 1) := by omega
    have hVk := hV (k + 1) (Nat.succ_le_of_lt hlen)
    rwa [← htime] at hVk

theorem rankOf_trapped [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    (i0 : Nat) (path : Nat → σ)
    (h0 : reachable A w i0 (path 0))
    (hstep : ∀ k, A.step (path k) (w (i0 + k)) (path (k + 1)) = true) :
    ∃ N r, r % 2 = 1 ∧ ∀ k ≥ N, rankOf A w hrej (i0 + k) (path k) = some r := by
  have hreach : ∀ k, reachable A w (i0 + k) (path k) :=
    reachable_along_path A w i0 path h0 hstep
  let f : Nat → Nat := fun k =>
    Classical.choose (exists_rank_drop A w hrej (hreach k))
  have hf : ∀ k, rankOf A w hrej (i0 + k) (path k) = some (f k) := by
    intro k
    simpa [f] using rankOf_pos A w hrej (hreach k)
  have hmono : ∀ k, f (k + 1) ≤ f k := by
    intro k
    have hidx : i0 + (k + 1) = i0 + k + 1 := by omega
    have hq : rankOf A w hrej (i0 + k + 1) (path (k + 1)) = some (f (k + 1)) := by
      simpa [hidx] using hf (k + 1)
    exact rankOf_nonincreasing A w hrej (hf k) hq (hstep k)
  obtain ⟨N, hN⟩ := antitone_nat_eventually_const f hmono
  refine ⟨N, f N, ?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one (f N) with he | ho
    · exfalso
      have hmem : layer A w (f N) (i0 + N) (path N) :=
        (rankOf_of_some A w hrej (hf N)).2.1
      have hnot : ¬ layer A w (f N + 1) (i0 + N) (path N) :=
        (rankOf_of_some A w hrej (hf N)).2.2.1
      apply hnot
      have hinf : infiniteFrom A w (layer A w (f N)) (i0 + N) (path N) := by
        refine ⟨hmem, ?_⟩
        intro M
        let len := M + 1
        let path' : Nat → σ := fun k => path (N + k)
        have hV : ∀ k, k ≤ len →
            layer A w (f N) ((i0 + N) + k) (path' k) := by
          intro k _
          have hge : N ≤ N + k := Nat.le_add_right _ _
          have hidx : i0 + (N + k) = i0 + N + k := by omega
          have heq : rankOf A w hrej (i0 + N + k) (path (N + k)) = some (f N) := by
            have hfk : f (N + k) = f N := hN (N + k) hge
            rw [← hfk]
            simpa [hidx] using hf (N + k)
          exact (rankOf_of_some A w hrej heq).2.1
        have hst : ∀ k, k < len →
            A.step (path' k) (w ((i0 + N) + k)) (path' (k + 1)) = true := by
          intro k _
          have htime : i0 + (N + k) = (i0 + N) + k := by omega
          have hnext : path ((N + k) + 1) = path' (k + 1) := by
            have hassoc : (N + k) + 1 = N + (k + 1) := by omega
            simp [path', hassoc]
          have hstepk := hstep (N + k)
          rw [htime, hnext] at hstepk
          exact hstepk
        have hseg := reaches_segment A w (layer A w (f N)) (i0 + N) len path' hV hst
        refine ⟨(i0 + N) + len, ?_, path' len, hseg⟩
        omega
      simpa [layer, he] using And.intro hmem hinf
    · exact ho
  · intro k hk
    have hrk : f k = f N := hN k hk
    rw [← hrk]
    exact hf k

noncomputable def deletionRank [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) : VertexRank A w where
  val := rankOf A w hrej
  bound := 2 * Fintype.card σ
  defined_iff := by
    intro i q
    constructor
    · intro hs
      by_contra hnot
      rw [rankOf_neg A w hrej hnot] at hs
      exact Bool.false_ne_true hs
    · intro h
      obtain ⟨r, heq, _⟩ := rankOf_spec A w hrej h
      simp [heq]
  le_bound := by
    intro i q r hr
    exact (rankOf_of_some A w hrej hr).1
  odd_not_accept := by
    intro i q r hr hodd
    exact rankOf_odd_reject A w hrej hr hodd
  nonincreasing := by
    intro i p q rp rq hp hq hstep
    exact rankOf_nonincreasing A w hrej hp hq hstep
  trapped_odd := by
    intro i0 path h0 hstep
    exact rankOf_trapped A w hrej i0 path h0 hstep

theorem exists_oddRank_of_not_accepts [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) :
    Nonempty (VertexRank A w) :=
  ⟨deletionRank A w hrej⟩

theorem oddRank_iff_not_accepts [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) :
    Nonempty (VertexRank A w) ↔ ¬ Accepts A w := by
  constructor
  · rintro ⟨R⟩
    exact oddRank_not_accepts A w R
  · exact exists_oddRank_of_not_accepts A w

/-! ## Rank complement

The state of the complement carries a rank guess and a breakpoint obligation,
in the sense of Orna Kupferman and Moshe Y. Vardi, *Complementation Constructions
for Nondeterministic Automata on Infinite Words* (2005). Ranks lie in
`0, …, 2|Q|`. An odd rank is rejecting. The obligation records the even-rank
states that still owe a visit to an odd rank.
-/

noncomputable def propBit (p : Prop) : Bool :=
  @decide p (Classical.propDecidable p)

@[simp] theorem propBit_iff (p : Prop) : propBit p = true ↔ p := by
  simp [propBit]

structure RankGuess (σ : Type) [Fintype σ] where
  rank : σ → Option (Fin (2 * Fintype.card σ + 1))
  owe : σ → Bool

def supported {n : Nat} (g : σ → Option (Fin n)) (q : σ) : Prop :=
  (g q).isSome = true

def supportExact (A : NBA α σ) (a : α) {n : Nat}
    (g g' : σ → Option (Fin n)) : Prop :=
  ∀ q, supported g' q ↔ ∃ p, supported g p ∧ A.step p a q = true

def monoRank (A : NBA α σ) (a : α) {n : Nat}
    (g g' : σ → Option (Fin n)) : Prop :=
  ∀ p q rp rq, g p = some rp → g' q = some rq →
    A.step p a q = true → rq.val ≤ rp.val

def oddReject (A : NBA α σ) {n : Nat} (g : σ → Option (Fin n)) : Prop :=
  ∀ q r, g q = some r → r.val % 2 = 1 → A.accept q = false

def noOwe (owe : σ → Bool) : Prop :=
  ∀ q, owe q = false

def evenAt {n : Nat} (g : σ → Option (Fin n)) (q : σ) : Prop :=
  ∃ r, g q = some r ∧ r.val % 2 = 0

def oweStep (A : NBA α σ) (a : α) {n : Nat}
    (g' : σ → Option (Fin n)) (owe owe' : σ → Bool) : Prop :=
  (noOwe owe ∧ ∀ q, owe' q = true ↔ evenAt g' q) ∨
    (¬ noOwe owe ∧ ∀ q, owe' q = true ↔
      evenAt g' q ∧ ∃ p, owe p = true ∧ A.step p a q = true)

def stepProp [Fintype σ] (A : NBA α σ) (a : α) (s t : RankGuess σ) : Prop :=
  supportExact A a s.rank t.rank ∧
    monoRank A a s.rank t.rank ∧
      oddReject A t.rank ∧
        oweStep A a t.rank s.owe t.owe

def startProp [Fintype σ] (A : NBA α σ) (s : RankGuess σ) : Prop :=
  (∀ q, supported s.rank q ↔ A.start q = true) ∧
    oddReject A s.rank ∧
      (∀ q, s.owe q = true ↔ evenAt s.rank q)

noncomputable def complement [Fintype σ] (A : NBA α σ) : NBA α (RankGuess σ) where
  step s a t := propBit (stepProp A a s t)
  start s := propBit (startProp A s)
  accept s := propBit (noOwe s.owe)

theorem complement_step_iff [Fintype σ] (A : NBA α σ)
    (s : RankGuess σ) (a : α) (t : RankGuess σ) :
    (complement A).step s a t = true ↔ stepProp A a s t := by
  simp [complement]

theorem complement_start_iff [Fintype σ] (A : NBA α σ) (s : RankGuess σ) :
    (complement A).start s = true ↔ startProp A s := by
  simp [complement]

theorem complement_accept_iff [Fintype σ] (A : NBA α σ) (s : RankGuess σ) :
    (complement A).accept s = true ↔ noOwe s.owe := by
  simp [complement]

def guessVal [Fintype σ] (s : RankGuess σ) (q : σ) : Option Nat :=
  (s.rank q).map Fin.val

theorem guessVal_eq [Fintype σ] {s : RankGuess σ} {q : σ}
    {r : Fin (2 * Fintype.card σ + 1)} (h : s.rank q = some r) :
    guessVal s q = some r.val := by
  simp [guessVal, h]

theorem option_some_of_isSome {β : Type} {o : Option β} (h : o.isSome = true) :
    ∃ a, o = some a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

theorem run_supported [Fintype σ]
    (A : NBA α σ) (w : Nat → α) (path : Nat → RankGuess σ)
    (hstart : (complement A).start (path 0) = true)
    (hstep : ∀ i, (complement A).step (path i) (w i) (path (i + 1)) = true) :
    ∀ i q, supported (path i).rank q ↔ reachable A w i q := by
  intro i
  induction i with
  | zero =>
    intro q
    rw [reachable_zero]
    exact ((complement_start_iff A (path 0)).mp hstart).1 q
  | succ i ih =>
    intro q
    have ht := (complement_step_iff A (path i) (w i) (path (i + 1))).mp (hstep i)
    rw [reachable_succ]
    constructor
    · intro hsup
      obtain ⟨p, hp, hst⟩ := (ht.1 q).mp hsup
      exact ⟨p, (ih p).mp hp, hst⟩
    · intro ⟨p, hp, hst⟩
      exact (ht.1 q).mpr ⟨p, (ih p).mpr hp, hst⟩

theorem run_odd_at [Fintype σ]
    (A : NBA α σ) (w : Nat → α) (path : Nat → RankGuess σ)
    (hstart : (complement A).start (path 0) = true)
    (hstep : ∀ i, (complement A).step (path i) (w i) (path (i + 1)) = true)
    (i : Nat) : oddReject A (path i).rank := by
  cases i with
  | zero => exact ((complement_start_iff A (path 0)).mp hstart).2.1
  | succ i =>
    exact ((complement_step_iff A (path i) (w i) (path (i + 1))).mp (hstep i)).2.2.1

theorem run_mono_at [Fintype σ]
    (A : NBA α σ) (w : Nat → α) (path : Nat → RankGuess σ)
    (hstep : ∀ i, (complement A).step (path i) (w i) (path (i + 1)) = true)
    (i : Nat) : monoRank A (w i) (path i).rank (path (i + 1)).rank :=
  ((complement_step_iff A (path i) (w i) (path (i + 1))).mp (hstep i)).2.1

theorem run_owe_at [Fintype σ]
    (A : NBA α σ) (w : Nat → α) (path : Nat → RankGuess σ)
    (hstep : ∀ i, (complement A).step (path i) (w i) (path (i + 1)) = true)
    (i : Nat) : oweStep A (w i) (path (i + 1)).rank (path i).owe (path (i + 1)).owe :=
  ((complement_step_iff A (path i) (w i) (path (i + 1))).mp (hstep i)).2.2.2

/-- An accepting run of the complement is an odd ranking of the source. -/
noncomputable def complementRanking [Fintype σ]
    (A : NBA α σ) (w : Nat → α) (path : Nat → RankGuess σ)
    (hstart : (complement A).start (path 0) = true)
    (hstep : ∀ i, (complement A).step (path i) (w i) (path (i + 1)) = true)
    (hacc : RunAccepts (complement A).accept path) : VertexRank A w where
  val i q := guessVal (path i) q
  bound := 2 * Fintype.card σ
  defined_iff := by
    intro i q
    constructor
    · intro hs
      have hsup : supported (path i).rank q := by
        cases h : (path i).rank q with
        | none => simp [guessVal, h] at hs
        | some _ => simp [supported, h]
      exact (run_supported A w path hstart hstep i q).mp hsup
    · intro hr
      have hsup := (run_supported A w path hstart hstep i q).mpr hr
      obtain ⟨r, hr⟩ := option_some_of_isSome hsup
      simp [guessVal, hr]
  le_bound := by
    intro i q n hn
    cases h : (path i).rank q with
    | none => simp [guessVal, h] at hn
    | some r =>
      simp [guessVal, h] at hn
      have hlt : r.val < 2 * Fintype.card σ + 1 := r.isLt
      omega
  odd_not_accept := by
    intro i q n hn hodd
    cases h : (path i).rank q with
    | none => simp [guessVal, h] at hn
    | some r =>
      simp [guessVal, h] at hn
      exact run_odd_at A w path hstart hstep i q r h (hn.symm ▸ hodd)
  nonincreasing := by
    intro i p q rp rq hp hq hst
    cases hpR : (path i).rank p with
    | none => simp [guessVal, hpR] at hp
    | some rP =>
      cases hqR : (path (i + 1)).rank q with
      | none => simp [guessVal, hqR] at hq
      | some rQ =>
        simp [guessVal, hpR, hqR] at hp hq
        have hle := run_mono_at A w path hstep i p q rP rQ hpR hqR hst
        omega
  trapped_odd := by
    intro i0 sp h0 hstepS
    have hreach := reachable_along_path A w i0 sp h0 hstepS
    have hfin : ∀ k, ∃ r, (path (i0 + k)).rank (sp k) = some r := by
      intro k
      exact option_some_of_isSome
        ((run_supported A w path hstart hstep (i0 + k) (sp k)).mpr (hreach k))
    let rk : Nat → Fin (2 * Fintype.card σ + 1) :=
      fun k => Classical.choose (hfin k)
    have hrk : ∀ k, (path (i0 + k)).rank (sp k) = some (rk k) :=
      fun k => Classical.choose_spec (hfin k)
    let f : Nat → Nat := fun k => (rk k).val
    have hf : ∀ k, guessVal (path (i0 + k)) (sp k) = some (f k) :=
      fun k => guessVal_eq (hrk k)
    have hmono : ∀ k, f (k + 1) ≤ f k := by
      intro k
      have hidx : i0 + (k + 1) = i0 + k + 1 := by omega
      have hrk1 : (path (i0 + k + 1)).rank (sp (k + 1)) = some (rk (k + 1)) := by
        simpa [hidx] using hrk (k + 1)
      have hle := run_mono_at A w path hstep (i0 + k) (sp k) (sp (k + 1))
        (rk k) (rk (k + 1)) (hrk k) hrk1 (hstepS k)
      simpa [f] using hle
    obtain ⟨N, hN⟩ := antitone_nat_eventually_const f hmono
    refine ⟨N, f N, ?_, ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one (f N) with he | ho
      · exfalso
        obtain ⟨T, hTle, haccT⟩ := hacc (i0 + N)
        have hnoT : noOwe (path T).owe := (complement_accept_iff A (path T)).mp haccT
        have hi0T : i0 ≤ T := le_trans (Nat.le_add_right i0 N) hTle
        let k0 := T - i0
        have hk0 : i0 + k0 = T := Nat.add_sub_of_le hi0T
        have hk0N : N ≤ k0 := by omega
        have hrank1 : f (k0 + 1) = f N := hN (k0 + 1) (Nat.le_succ_of_le hk0N)
        have heven1 : (rk (k0 + 1)).val % 2 = 0 := by
          simpa [f, hrank1] using he
        have hidx1 : i0 + (k0 + 1) = T + 1 := by omega
        have hr1 : (path (T + 1)).rank (sp (k0 + 1)) = some (rk (k0 + 1)) := by
          simpa [hidx1, hk0] using hrk (k0 + 1)
        have hev : evenAt (path (T + 1)).rank (sp (k0 + 1)) :=
          ⟨rk (k0 + 1), hr1, heven1⟩
        have howe1 : (path (T + 1)).owe (sp (k0 + 1)) = true := by
          rcases run_owe_at A w path hstep T with ⟨_, hiff⟩ | ⟨hbad, _⟩
          · exact (hiff (sp (k0 + 1))).mpr hev
          · exact (hbad hnoT).elim
        have owed : ∀ j, (path (T + 1 + j)).owe (sp (k0 + 1 + j)) = true := by
          intro j
          induction j with
          | zero => simpa using howe1
          | succ j ihj =>
            have hne : ¬ noOwe (path (T + 1 + j)).owe := by
              intro hall
              exact Bool.false_ne_true ((hall (sp (k0 + 1 + j))).symm.trans ihj)
            have hidxj : i0 + (k0 + 1 + j) = T + 1 + j := by omega
            have hidxj1 : i0 + (k0 + 1 + (j + 1)) = T + 1 + (j + 1) := by omega
            have hge : N ≤ k0 + 1 + (j + 1) := by omega
            have hval : f (k0 + 1 + (j + 1)) = f N := hN _ hge
            have heven : (rk (k0 + 1 + (j + 1))).val % 2 = 0 := by
              simpa [f, hval] using he
            have hrj1 : (path (T + 1 + (j + 1))).rank (sp (k0 + 1 + (j + 1))) =
                some (rk (k0 + 1 + (j + 1))) := by
              simpa [hidxj1] using hrk (k0 + 1 + (j + 1))
            have hevj : evenAt (path (T + 1 + (j + 1))).rank (sp (k0 + 1 + (j + 1))) :=
              ⟨_, hrj1, heven⟩
            have hnextT : T + 1 + j + 1 = T + 1 + (j + 1) := by omega
            have hstj : A.step (sp (k0 + 1 + j)) (w (T + 1 + j))
                (sp (k0 + 1 + (j + 1))) = true := by
              have hraw := hstepS (k0 + 1 + j)
              have hix : (k0 + 1 + j) + 1 = k0 + 1 + (j + 1) := by omega
              rw [hidxj, hix] at hraw
              exact hraw
            rcases run_owe_at A w path hstep (T + 1 + j) with ⟨hempty, _⟩ | ⟨_, hiff⟩
            · exact (hne hempty).elim
            · have hmem := (hiff (sp (k0 + 1 + (j + 1)))).mpr ⟨hevj, sp (k0 + 1 + j), ihj, hstj⟩
              simpa [hnextT] using hmem
        obtain ⟨T2, hT2, hacc2⟩ := hacc (T + 1)
        have hno2 : noOwe (path T2).owe := (complement_accept_iff A (path T2)).mp hacc2
        have hgap : T + 1 ≤ T2 := hT2
        let j := T2 - (T + 1)
        have hj : T + 1 + j = T2 := Nat.add_sub_of_le hgap
        have howed := owed j
        rw [hj] at howed
        exact Bool.false_ne_true ((hno2 (sp (k0 + 1 + j))).symm.trans howed)
      · exact ho
    · intro k hk
      have hrkN : f k = f N := hN k hk
      rw [← hrkN]
      exact hf k

theorem complement_accepts_not [Fintype σ]
    (A : NBA α σ) (w : Nat → α) (path : Nat → RankGuess σ)
    (hstart : (complement A).start (path 0) = true)
    (hstep : ∀ i, (complement A).step (path i) (w i) (path (i + 1)) = true)
    (hacc : RunAccepts (complement A).accept path) : ¬ Accepts A w :=
  oddRank_not_accepts A w (complementRanking A w path hstart hstep hacc)

noncomputable def canonicalGuess [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) (q : σ) :
    Option (Fin (2 * Fintype.card σ + 1)) :=
  match h : rankOf A w hrej i q with
  | none => none
  | some r => some ⟨r, Nat.lt_succ_of_le (rankOf_of_some A w hrej h).1⟩

theorem canonicalGuess_none [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) {i : Nat} {q : σ}
    (h : rankOf A w hrej i q = none) :
    canonicalGuess A w hrej i q = none := by
  unfold canonicalGuess
  split
  · rfl
  · rename_i r hr
    rw [h] at hr
    cases hr

theorem canonicalGuess_some [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) {i : Nat} {q : σ} {r : Nat}
    (h : rankOf A w hrej i q = some r) :
    canonicalGuess A w hrej i q =
      some ⟨r, Nat.lt_succ_of_le (rankOf_of_some A w hrej h).1⟩ := by
  unfold canonicalGuess
  split
  · rename_i hn
    rw [h] at hn
    cases hn
  · rename_i r' hr
    have hrEq : r' = r := by
      rw [h] at hr
      exact (Option.some_inj.mp hr).symm
    subst hrEq
    exact congrArg some (Fin.eq_of_val_eq rfl)

theorem canonical_supported [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) (q : σ) :
    supported (fun p => canonicalGuess A w hrej i p) q ↔ reachable A w i q := by
  constructor
  · intro hsup
    by_contra hnot
    unfold supported at hsup
    change (canonicalGuess A w hrej i q).isSome = true at hsup
    rw [canonicalGuess_none A w hrej (rankOf_neg A w hrej hnot)] at hsup
    exact Bool.false_ne_true hsup
  · intro hreach
    obtain ⟨r, heq, _⟩ := rankOf_spec A w hrej hreach
    unfold supported
    change (canonicalGuess A w hrej i q).isSome = true
    rw [canonicalGuess_some A w hrej heq]
    rfl

theorem propBit_eq_false {p : Prop} (h : ¬ p) : propBit p = false := by
  cases hb : propBit p
  · rfl
  · exact (h ((propBit_iff p).mp hb)).elim

noncomputable def canonicalOwe [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) : Nat → σ → Bool
  | 0, q => propBit (evenAt (fun p => canonicalGuess A w hrej 0 p) q)
  | i + 1, q =>
    let owe := canonicalOwe A w hrej i
    let g' := fun p => canonicalGuess A w hrej (i + 1) p
    if propBit (noOwe owe) then propBit (evenAt g' q)
    else propBit (evenAt g' q ∧ ∃ p, owe p = true ∧ A.step p (w i) q = true)

theorem canonicalOwe_zero [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (q : σ) :
    canonicalOwe A w hrej 0 q =
      propBit (evenAt (fun p => canonicalGuess A w hrej 0 p) q) := rfl

theorem canonicalOwe_succ [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) (q : σ) :
    canonicalOwe A w hrej (i + 1) q =
      (if propBit (noOwe (canonicalOwe A w hrej i)) then
        propBit (evenAt (fun p => canonicalGuess A w hrej (i + 1) p) q)
      else
        propBit (evenAt (fun p => canonicalGuess A w hrej (i + 1) p) q ∧
          ∃ p, canonicalOwe A w hrej i p = true ∧ A.step p (w i) q = true)) := rfl

noncomputable def canonicalState [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) : RankGuess σ where
  rank q := canonicalGuess A w hrej i q
  owe q := canonicalOwe A w hrej i q

theorem canonical_rank_of_guess [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) {i : Nat} {q : σ}
    {f : Fin (2 * Fintype.card σ + 1)}
    (h : canonicalGuess A w hrej i q = some f) :
    rankOf A w hrej i q = some f.val := by
  by_cases hreach : reachable A w i q
  · obtain ⟨r, heq, _⟩ := rankOf_spec A w hrej hreach
    have hg := canonicalGuess_some A w hrej heq
    rw [hg] at h
    have hinj := Option.some_inj.mp h
    have hv : f.val = r := congrArg Fin.val hinj.symm
    simpa [hv] using heq
  · rw [canonicalGuess_none A w hrej (rankOf_neg A w hrej hreach)] at h
    cases h

theorem guess_odd_reject [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) :
    oddReject A (fun q => canonicalGuess A w hrej i q) := by
  intro q f hf hodd
  have hr := canonical_rank_of_guess A w hrej hf
  exact rankOf_odd_reject A w hrej hr hodd

theorem canonical_even_of_owe [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) {i : Nat} {q : σ}
    (h : canonicalOwe A w hrej i q = true) :
    ∃ r, rankOf A w hrej i q = some r ∧ r % 2 = 0 := by
  suffices evenAt (fun p => canonicalGuess A w hrej i p) q by
    obtain ⟨f, hf, he⟩ := this
    exact ⟨f.val, canonical_rank_of_guess A w hrej hf, he⟩
  cases i with
  | zero =>
    rw [canonicalOwe_zero] at h
    exact (propBit_iff _).mp h
  | succ i =>
    rw [canonicalOwe_succ] at h
    by_cases hempty : noOwe (canonicalOwe A w hrej i)
    · rw [if_pos ((propBit_iff _).mpr hempty)] at h
      exact (propBit_iff _).mp h
    · rw [if_neg (by
        intro ht
        exact hempty ((propBit_iff _).mp ht))] at h
      exact ((propBit_iff _).mp h).1

theorem canonical_pred [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) (q : σ)
    (hnon : ¬ noOwe (canonicalOwe A w hrej i))
    (hq : canonicalOwe A w hrej (i + 1) q = true) :
    ∃ p, canonicalOwe A w hrej i p = true ∧ A.step p (w i) q = true := by
  rw [canonicalOwe_succ] at hq
  rw [if_neg (by
    intro ht
    exact hnon ((propBit_iff _).mp ht))] at hq
  exact ((propBit_iff _).mp hq).2

theorem canonical_start [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) :
    startProp A (canonicalState A w hrej 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simpa [canonicalState, reachable] using canonical_supported A w hrej 0 q
  · intro q f hf hodd
    exact guess_odd_reject A w hrej 0 q f (by simpa [canonicalState] using hf) hodd
  · intro q
    constructor
    · intro ho
      have ho' : canonicalOwe A w hrej 0 q = true := by simpa [canonicalState] using ho
      rw [canonicalOwe_zero] at ho'
      simpa [canonicalState] using (propBit_iff _).mp ho'
    · intro he
      simpa [canonicalState, canonicalOwe_zero] using
        (propBit_iff _).mpr (by simpa [canonicalState] using he)

theorem canonical_step [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (i : Nat) :
    stepProp A (w i) (canonicalState A w hrej i) (canonicalState A w hrej (i + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    constructor
    · intro hsup
      have hr := (canonical_supported A w hrej (i + 1) q).mp
        (by simpa [canonicalState] using hsup)
      rw [reachable_succ] at hr
      obtain ⟨p, hp, hst⟩ := hr
      exact ⟨p, by simpa [canonicalState] using (canonical_supported A w hrej i p).mpr hp, hst⟩
    · intro ⟨p, hp, hst⟩
      have hp' := (canonical_supported A w hrej i p).mp (by simpa [canonicalState] using hp)
      have hr : reachable A w (i + 1) q := (reachable_succ A w i q).mpr ⟨p, hp', hst⟩
      simpa [canonicalState] using (canonical_supported A w hrej (i + 1) q).mpr hr
  · intro p q rp rq hp hq hst
    have hgp : canonicalGuess A w hrej i p = some rp := by simpa [canonicalState] using hp
    have hgq : canonicalGuess A w hrej (i + 1) q = some rq := by
      simpa [canonicalState] using hq
    have hrp := canonical_rank_of_guess A w hrej hgp
    have hrq := canonical_rank_of_guess A w hrej hgq
    simpa using rankOf_nonincreasing A w hrej hrp hrq hst
  · intro q f hf hodd
    exact guess_odd_reject A w hrej (i + 1) q f (by simpa [canonicalState] using hf) hodd
  · by_cases hempty : noOwe (canonicalOwe A w hrej i)
    · refine Or.inl ⟨by simpa [canonicalState] using hempty, ?_⟩
      intro q
      constructor
      · intro ho
        have ho' : canonicalOwe A w hrej (i + 1) q = true := by
          simpa [canonicalState] using ho
        rw [canonicalOwe_succ, if_pos ((propBit_iff _).mpr hempty)] at ho'
        simpa [canonicalState] using (propBit_iff _).mp ho'
      · intro he
        have ho' : canonicalOwe A w hrej (i + 1) q = true := by
          rw [canonicalOwe_succ, if_pos ((propBit_iff _).mpr hempty)]
          exact (propBit_iff _).mpr (by simpa [canonicalState] using he)
        simpa [canonicalState] using ho'
    · refine Or.inr ⟨by simpa [canonicalState] using hempty, ?_⟩
      intro q
      constructor
      · intro ho
        have ho' : canonicalOwe A w hrej (i + 1) q = true := by
          simpa [canonicalState] using ho
        rw [canonicalOwe_succ, if_neg (by
          intro ht
          exact hempty ((propBit_iff _).mp ht))] at ho'
        simpa [canonicalState] using (propBit_iff _).mp ho'
      · intro he
        have he' : evenAt (fun p => canonicalGuess A w hrej (i + 1) p) q ∧
            ∃ p, canonicalOwe A w hrej i p = true ∧
              A.step p (w i) q = true := by
          simpa [canonicalState] using he
        obtain ⟨hev, hex⟩ := he'
        obtain ⟨p, hp, hst⟩ := hex
        have ho' : canonicalOwe A w hrej (i + 1) q = true := by
          rw [canonicalOwe_succ, if_neg (by
            intro ht
            exact hempty ((propBit_iff _).mp ht))]
          exact (propBit_iff _).mpr ⟨hev, ⟨p, hp, hst⟩⟩
        simpa [canonicalState] using ho'

theorem owe_back [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (N M : Nat) (q : σ)
    (hnon : ∀ i, N ≤ i → ¬ noOwe (canonicalOwe A w hrej i))
    (hq : canonicalOwe A w hrej (N + M) q = true) :
    ∃ path : Nat → σ, path M = q ∧
      (∀ k, k ≤ M → canonicalOwe A w hrej (N + k) (path k) = true) ∧
      (∀ k, k < M → A.step (path k) (w (N + k)) (path (k + 1)) = true) := by
  induction M generalizing q with
  | zero =>
    refine ⟨fun _ => q, rfl, ?_, fun k hk => by omega⟩
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    simpa [hk0] using hq
  | succ M ih =>
    have hidx : N + (M + 1) = N + M + 1 := by omega
    have hq1 : canonicalOwe A w hrej (N + M + 1) q = true := by
      simpa [hidx] using hq
    obtain ⟨p, hp, hstep⟩ :=
      canonical_pred A w hrej (N + M) q (hnon (N + M) (Nat.le_add_right _ _)) hq1
    obtain ⟨path0, hend, howe, hst⟩ := ih p hp
    let path : Nat → σ := fun k => if k ≤ M then path0 k else q
    refine ⟨path, ?_, ?_, ?_⟩
    · have hnot : ¬ M + 1 ≤ M := by omega
      simp [path, if_neg hnot]
    · intro k hk
      by_cases hle : k ≤ M
      · have howek := howe k hle
        simpa [path, if_pos hle] using howek
      · have hkEq : k = M + 1 := by omega
        have hnot : ¬ M + 1 ≤ M := by omega
        rw [hkEq]
        simpa [path, if_neg hnot] using hq
    · intro k hk
      by_cases hlt : k < M
      · have hle : k ≤ M := Nat.le_of_lt hlt
        have hk1 : k + 1 ≤ M := Nat.succ_le_of_lt hlt
        have hs := hst k hlt
        simpa [path, if_pos hle, if_pos hk1] using hs
      · have hkEq : k = M := by omega
        have hleft : path k = p := by
          rw [hkEq]
          simp [path, if_pos le_rfl, hend]
        have hright : path (k + 1) = q := by
          have hnot : ¬ k + 1 ≤ M := by omega
          simp [path, if_neg hnot]
        rw [hleft, hright, hkEq]
        exact hstep

theorem owe_inhabited [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) {i : Nat}
    (h : ¬ noOwe (canonicalOwe A w hrej i)) :
    ∃ q, canonicalOwe A w hrej i q = true := by
  unfold noOwe at h
  push Not at h
  obtain ⟨q, hq⟩ := h
  cases hb : canonicalOwe A w hrej i q
  · exact (hq hb).elim
  · exact ⟨q, hb⟩

structure OweInf [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) where
  i : Nat
  q : σ
  inf : infiniteFrom A w (fun t r => canonicalOwe A w hrej t r = true) i q

noncomputable def oweInfStep [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    (p : OweInf A w hrej) : OweInf A w hrej :=
  let hex := exists_step_infinite A w (fun t r => canonicalOwe A w hrej t r = true) p.inf
  ⟨p.i + 1, Classical.choose hex, (Classical.choose_spec hex).2.2⟩

theorem oweInfStep_i [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (p : OweInf A w hrej) :
    (oweInfStep A w hrej p).i = p.i + 1 := rfl

theorem oweInfStep_step [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (p : OweInf A w hrej) :
    A.step p.q (w p.i) (oweInfStep A w hrej p).q = true := by
  simpa [oweInfStep] using
    (Classical.choose_spec
      (exists_step_infinite A w (fun t r => canonicalOwe A w hrej t r = true) p.inf)).2.1

noncomputable def oweRay [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w)
    (p0 : OweInf A w hrej) : Nat → OweInf A w hrej
  | 0 => p0
  | n + 1 => oweInfStep A w hrej (oweRay A w hrej p0 n)

theorem oweRay_zero [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (p0 : OweInf A w hrej) :
    oweRay A w hrej p0 0 = p0 := rfl

theorem oweRay_succ [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (p0 : OweInf A w hrej) (n : Nat) :
    oweRay A w hrej p0 (n + 1) = oweInfStep A w hrej (oweRay A w hrej p0 n) := rfl

theorem oweRay_i [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (p0 : OweInf A w hrej) (n : Nat) :
    (oweRay A w hrej p0 n).i = p0.i + n := by
  induction n with
  | zero => simp [oweRay_zero]
  | succ n ih =>
    rw [oweRay_succ, oweInfStep_i, ih]
    omega

theorem stuck_rank_false [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) (N : Nat)
    (hnon : ∀ i, N ≤ i → ¬ noOwe (canonicalOwe A w hrej i)) : False := by
  have hwalk : ∀ M, ∃ path : Nat → σ,
      (∀ k, k ≤ M → canonicalOwe A w hrej (N + k) (path k) = true) ∧
      (∀ k, k < M → A.step (path k) (w (N + k)) (path (k + 1)) = true) := by
    intro M
    obtain ⟨q, hq⟩ := owe_inhabited A w hrej (hnon (N + M) (Nat.le_add_right _ _))
    obtain ⟨path, _, howe, hst⟩ := owe_back A w hrej N M q hnon hq
    exact ⟨path, howe, hst⟩
  let walk : Nat → Nat → σ := fun M => Classical.choose (hwalk M)
  have hwalk_spec : ∀ M,
      (∀ k, k ≤ M → canonicalOwe A w hrej (N + k) ((walk M) k) = true) ∧
      (∀ k, k < M → A.step ((walk M) k) (w (N + k)) ((walk M) (k + 1)) = true) :=
    fun M => Classical.choose_spec (hwalk M)
  let f : Nat → σ := fun M => walk M 0
  obtain ⟨q0, hqio⟩ := exists_state_io f
  let V : Nat → σ → Prop := fun t r => canonicalOwe A w hrej t r = true
  have hinf : infiniteFrom A w V N q0 := by
    refine ⟨?_, ?_⟩
    · obtain ⟨M, _, heq⟩ := hqio 0
      have howe := (hwalk_spec M).1 0 (Nat.zero_le _)
      simpa [V, f, heq] using howe
    · intro bound
      obtain ⟨M, hM, heq⟩ := hqio bound
      let path := walk M
      have howe := (hwalk_spec M).1
      have hst := (hwalk_spec M).2
      have hV : ∀ k, k ≤ M → V (N + k) (path k) := fun k hk => howe k hk
      have hstep : ∀ k, k < M → A.step (path k) (w (N + k)) (path (k + 1)) = true :=
        fun k hk => hst k hk
      have hseg := reaches_segment A w V N M path hV hstep
      have h0 : path 0 = q0 := by simpa [path, f] using heq
      refine ⟨N + M, ?_, path M, ?_⟩
      · omega
      · simpa [h0] using hseg
  let p0 : OweInf A w hrej := ⟨N, q0, hinf⟩
  let rayPt := oweRay A w hrej p0
  let ray : Nat → σ := fun k => (rayPt k).q
  have hstepR : ∀ k, A.step (ray k) (w (N + k)) (ray (k + 1)) = true := by
    intro k
    have hs := oweInfStep_step A w hrej (rayPt k)
    have hidx : (rayPt k).i = N + k := by
      have hpi : p0.i = N := rfl
      unfold rayPt
      rw [oweRay_i, hpi]
    have hsrc : (rayPt k).q = ray k := by simp [ray]
    have hpt : (oweInfStep A w hrej (rayPt k)).q = ray (k + 1) := by
      have hsuf : rayPt (k + 1) = oweInfStep A w hrej (rayPt k) := by
        unfold rayPt
        exact oweRay_succ A w hrej p0 k
      simp [ray, hsuf]
    rw [hidx, hsrc, hpt] at hs
    exact hs
  have hreach0 : reachable A w N (ray 0) := by
    have hray0 : ray 0 = q0 := by simp [ray, rayPt, oweRay_zero, p0]
    have ho : canonicalOwe A w hrej N q0 = true := hinf.1
    obtain ⟨r, hr, _⟩ := canonical_even_of_owe A w hrej ho
    simpa [hray0] using (rankOf_of_some A w hrej hr).2.2.2
  obtain ⟨K, r, hodd, hconst⟩ :=
    (deletionRank A w hrej).trapped_odd N ray hreach0 hstepR
  have hval : rankOf A w hrej (N + K) (ray K) = some r := by
    simpa [deletionRank] using hconst K le_rfl
  have hoK : canonicalOwe A w hrej (N + K) (ray K) = true := by
    have hidx : (rayPt K).i = N + K := by
      have hpi : p0.i = N := rfl
      unfold rayPt
      rw [oweRay_i, hpi]
    have hV := (rayPt K).inf.1
    have hq : (rayPt K).q = ray K := by simp [ray]
    rw [hidx, hq] at hV
    exact hV
  obtain ⟨r', hr', heven⟩ := canonical_even_of_owe A w hrej hoK
  have hrEq : r' = r := by
    rw [hr'] at hval
    exact Option.some_inj.mp hval
  rw [hrEq, hodd] at heven
  exact Nat.one_ne_zero heven

theorem canonical_accepts [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) (hrej : ¬ Accepts A w) :
    Accepts (complement A) w := by
  refine ⟨canonicalState A w hrej, ?_, ?_, ?_⟩
  · exact (complement_start_iff A (canonicalState A w hrej 0)).mpr
      (canonical_start A w hrej)
  · intro i
    exact (complement_step_iff A (canonicalState A w hrej i) (w i)
      (canonicalState A w hrej (i + 1))).mpr (canonical_step A w hrej i)
  · intro lower
    by_contra hnone
    push Not at hnone
    have hstuck : ∀ i, lower ≤ i → ¬ noOwe (canonicalOwe A w hrej i) := by
      intro i hi hempty
      have hacc : (complement A).accept (canonicalState A w hrej i) = true :=
        (complement_accept_iff A (canonicalState A w hrej i)).mpr
          (by simpa [canonicalState] using hempty)
      exact hnone i hi hacc
    exact stuck_rank_false A w hrej lower hstuck

theorem accepts_complement [Fintype σ] [DecidableEq σ]
    (A : NBA α σ) (w : Nat → α) :
    Accepts (complement A) w ↔ ¬ Accepts A w := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    exact complement_accepts_not A w path hstart hstep hacc
  · exact canonical_accepts A w

theorem noStep_rejects (w : Nat → Bool) : ¬ Accepts noStep w := by
  intro h
  obtain ⟨_, _, hstep, _⟩ := h
  have := hstep 0
  simp [noStep] at this

theorem allLoop_accepts (w : Nat → Bool) : Accepts allLoop w := by
  refine ⟨fun _ => (), rfl, fun _ => rfl, ?_⟩
  intro lower
  exact ⟨lower, le_rfl, rfl⟩

theorem control_complement_noStep (w : Nat → Bool) :
    Accepts (complement noStep) w :=
  (accepts_complement noStep w).mpr (noStep_rejects w)

theorem control_complement_allLoop (w : Nat → Bool) :
    ¬ Accepts (complement allLoop) w := by
  intro h
  exact (accepts_complement allLoop w).mp h (allLoop_accepts w)

/-! ## Executable rank complement

`finComplement` decides the rank-and-breakpoint transitions of `complement`.
A state is a code in `Fin (guessCard n)`. The code stores one rank digit per
source state, in base `2 * n + 2`, and one obligation bit per source state.
Digit `0` omits the state. Digit `k + 1` stores rank `k`. The matrix walks
`List.finRange`. `toRankGuess` is the representation into `RankGuess`, and
`accepts_finComplement` reuses `accepts_complement`.
-/

/-- Every `Fin n`, listed in order. This is a value, not an `Enumerable` instance. -/
@[instance_reducible]
def enumerableFin (n : Nat) : Enumerable (Fin n) where
  elems := List.finRange n
  mem_elems := List.mem_finRange

/-- Rank digits use `2 * n + 2` symbols: omission, then ranks `0, …, 2n`. -/
def rankSymCount (n : Nat) : Nat := 2 * n + 2

/-- Codes for a rank guess and an obligation bit on `n` states. -/
def guessCard (n : Nat) : Nat := rankSymCount n ^ n * 2 ^ n

theorem rankSymCount_pos (n : Nat) : 1 ≤ rankSymCount n := by
  simp [rankSymCount]

theorem guessCard_pos (n : Nat) : 0 < guessCard n := by
  have hb : 0 < rankSymCount n := Nat.lt_of_lt_of_le Nat.zero_lt_one (rankSymCount_pos n)
  exact Nat.mul_pos (Nat.pow_pos hb) (Nat.two_pow_pos n)

def packDigits (base : Nat) : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k + 1, f =>
      packDigits base k (fun i => f i.castSucc) + f (Fin.last k) * base ^ k

theorem packDigits_lt {base k : Nat} (f : Fin k → Nat)
    (hb : 1 ≤ base) (hf : ∀ i, f i < base) :
    packDigits base k f < base ^ k := by
  induction k with
  | zero =>
    rw [packDigits, Nat.pow_zero]
    exact Nat.zero_lt_one
  | succ k ih =>
    rw [packDigits, Nat.pow_succ]
    have hpre := ih (fun i => f i.castSucc) (fun i => hf i.castSucc)
    have hlast : f (Fin.last k) ≤ base - 1 := Nat.le_pred_of_lt (hf _)
    have hmul : f (Fin.last k) * base ^ k ≤ (base - 1) * base ^ k :=
      Nat.mul_le_mul_right _ hlast
    have hsum :
        packDigits base k (fun i => f i.castSucc) + f (Fin.last k) * base ^ k <
          base ^ k + (base - 1) * base ^ k :=
      Nat.add_lt_add_of_lt_of_le hpre hmul
    have hrewrite : base ^ k + (base - 1) * base ^ k = base ^ k * base := by
      have hone : 1 + (base - 1) = base := by
        rw [Nat.add_comm, Nat.sub_add_cancel hb]
      calc
        base ^ k + (base - 1) * base ^ k = (1 + (base - 1)) * base ^ k := by
          rw [Nat.add_mul, Nat.one_mul]
        _ = base * base ^ k := by rw [hone]
        _ = base ^ k * base := Nat.mul_comm _ _
    exact hrewrite ▸ hsum

theorem digit_stable {base i k c : Nat} (_hb : 1 ≤ base) (hi : i < k) :
    ((c % base ^ k) / base ^ i) % base = (c / base ^ i) % base := by
  have hexp : i + (k - i) = k := Nat.add_sub_of_le (Nat.le_of_lt hi)
  have hpow : base ^ k = base ^ i * base ^ (k - i) := by
    have hpow' := Nat.pow_add base i (k - i)
    rwa [hexp] at hpow'
  have hdiv : (c % base ^ k) / base ^ i = (c / base ^ i) % base ^ (k - i) := by
    rw [hpow]
    exact Nat.mod_mul_right_div_self c (base ^ i) (base ^ (k - i))
  rw [hdiv]
  have hs : (k - i - 1).succ = k - i := by
    rw [Nat.succ_eq_add_one]
    omega
  have hsplit : base ^ (k - i) = base * base ^ (k - i - 1) := by
    have hpow' := Nat.pow_succ base (k - i - 1)
    rw [hs] at hpow'
    rwa [Nat.mul_comm] at hpow'
  rw [hsplit]
  exact Nat.mod_mul_right_mod (c / base ^ i) base (base ^ (k - i - 1))

theorem pack_of_digits {base k c : Nat} (hb : 1 ≤ base) (hc : c < base ^ k) :
    packDigits base k (fun i => (c / base ^ (i : Nat)) % base) = c := by
  induction k generalizing c with
  | zero =>
    simp only [packDigits, Nat.pow_zero] at hc ⊢
    omega
  | succ k ih =>
    simp only [packDigits]
    have hbpos : 0 < base := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    have hposk : 0 < base ^ k := Nat.pow_pos hbpos
    have hcdiv : c / base ^ k < base := by
      rw [Nat.pow_succ] at hc
      exact Nat.div_lt_of_lt_mul hc
    have hlow :
        packDigits base k (fun i : Fin k => (c / base ^ (i : Nat)) % base) =
          c % base ^ k := by
      have hfun :
          (fun i : Fin k => (c / base ^ (i : Nat)) % base) =
            fun i : Fin k => ((c % base ^ k) / base ^ (i : Nat)) % base := by
        funext i
        exact (digit_stable hb i.isLt).symm
      rw [hfun]
      exact ih (Nat.mod_lt _ hposk)
    have hhigh : (c / base ^ k) % base = c / base ^ k := Nat.mod_eq_of_lt hcdiv
    have hcast :
        packDigits base k
            (fun i => (c / base ^ ((i.castSucc : Fin (k + 1)) : Nat)) % base) =
          packDigits base k (fun i : Fin k => (c / base ^ (i : Nat)) % base) := by
      congr 1
    rw [Fin.val_last k, hhigh, hcast, hlow]
    exact Nat.mod_add_div' c (base ^ k)

theorem packDigits_digit {base k : Nat} (f : Fin k → Nat)
    (hb : 1 ≤ base) (hf : ∀ i, f i < base) (i : Fin k) :
    (packDigits base k f / base ^ (i : Nat)) % base = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    simp only [packDigits]
    have hbpos : 0 < base := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    have hpre := packDigits_lt (fun j => f j.castSucc) hb (fun j => hf j.castSucc)
    by_cases hlast : (i : Nat) = k
    · have hi : i = Fin.last k := Fin.ext hlast
      rw [hi, Fin.val_last k]
      have hposk : 0 < base ^ k := Nat.pow_pos hbpos
      have hdiv :
          (packDigits base k (fun j => f j.castSucc) + f (Fin.last k) * base ^ k) /
              base ^ k = f (Fin.last k) := by
        rw [Nat.mul_comm (f (Fin.last k)), Nat.add_mul_div_left _ _ hposk,
          Nat.div_eq_of_lt hpre, Nat.zero_add]
      rw [hdiv, Nat.mod_eq_of_lt (hf (Fin.last k))]
    · have hi : (i : Nat) < k := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hlast
      let j : Fin k := ⟨i.val, hi⟩
      have hij : (i : Nat) = j.val := rfl
      rw [hij]
      have hpow : base ^ k = base ^ (j : Nat) * base ^ (k - (j : Nat)) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
      have hposj : 0 < base ^ (j : Nat) := Nat.pow_pos hbpos
      have hmul :
          f (Fin.last k) * base ^ k =
            base ^ (j : Nat) * (f (Fin.last k) * base ^ (k - (j : Nat))) := by
        rw [hpow, Nat.mul_left_comm]
      have hdiv :
          (packDigits base k (fun t => f t.castSucc) + f (Fin.last k) * base ^ k) /
              base ^ (j : Nat) =
            packDigits base k (fun t => f t.castSucc) / base ^ (j : Nat) +
              f (Fin.last k) * base ^ (k - (j : Nat)) := by
        rw [hmul, Nat.add_mul_div_left _ _ hposj]
      rw [hdiv]
      have hs : (k - (j : Nat) - 1).succ = k - (j : Nat) := by
        rw [Nat.succ_eq_add_one]
        omega
      have hsplit : base ^ (k - (j : Nat)) = base * base ^ (k - (j : Nat) - 1) := by
        have hpow' := Nat.pow_succ base (k - (j : Nat) - 1)
        rw [hs] at hpow'
        rwa [Nat.mul_comm] at hpow'
      have hhigh :
          f (Fin.last k) * base ^ (k - (j : Nat)) =
            base * (f (Fin.last k) * base ^ (k - (j : Nat) - 1)) := by
        rw [hsplit, Nat.mul_left_comm]
      rw [hhigh, Nat.add_mul_mod_self_left]
      have heq : j.castSucc = i := Fin.ext (Fin.val_castSucc j ▸ hij.symm)
      exact heq ▸ ih (fun t => f t.castSucc) (fun t => hf t.castSucc) j

/-- Rank digit of state `q` in a code. `0` omits the state. -/
def rankDigit (n code q : Nat) : Nat :=
  ((code / 2 ^ n) / rankSymCount n ^ q) % rankSymCount n

/-- Obligation bit of state `q` in a code. -/
def oweBit (n code q : Nat) : Bool :=
  decide (((code % 2 ^ n) / 2 ^ q) % 2 = 1)

theorem rankDigit_lt (n code q : Nat) : rankDigit n code q < rankSymCount n :=
  Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (rankSymCount_pos n))

theorem rankDigit_of_parts {n rank owe : Nat} (q : Fin n)
    (ho : owe < 2 ^ n) :
    rankDigit n (rank * 2 ^ n + owe) q.val =
      (rank / rankSymCount n ^ q.val) % rankSymCount n := by
  have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
  have hdiv : (rank * 2 ^ n + owe) / 2 ^ n = rank := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ h2,
      Nat.div_eq_of_lt ho, Nat.zero_add]
  simp [rankDigit, hdiv]

theorem oweBit_of_parts {n rank owe : Nat} (q : Fin n) (ho : owe < 2 ^ n) :
    oweBit n (rank * 2 ^ n + owe) q.val =
      decide ((owe / 2 ^ q.val) % 2 = 1) := by
  have hmod : (rank * 2 ^ n + owe) % 2 ^ n = owe := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ho]
  simp [oweBit, hmod]

def rawRank (n code : Nat) (q : Fin n) : Option (Fin (2 * n + 1)) :=
  let d := rankDigit n code q.val
  if h : d = 0 then none
  else some ⟨d - 1, by
    have hd : d < 2 * n + 2 := by simpa [rankSymCount] using rankDigit_lt n code q.val
    omega⟩

def supportedBit (n code : Nat) (q : Fin n) : Bool :=
  decide (rankDigit n code q.val ≠ 0)

def evenAtBit (n code : Nat) (q : Fin n) : Bool :=
  supportedBit n code q && decide ((rankDigit n code q.val - 1) % 2 = 0)

def supportExactBit {n : Nat} (A : NBA α (Fin n)) (a : α) (s t : Nat) : Bool :=
  listAll (fun q =>
    decide (supportedBit n t q =
      listAny (fun p => supportedBit n s p && A.step p a q) (List.finRange n)))
    (List.finRange n)

def monoRankBit {n : Nat} (A : NBA α (Fin n)) (a : α) (s t : Nat) : Bool :=
  listAll (fun p =>
    listAll (fun q =>
      if supportedBit n s p && supportedBit n t q && A.step p a q then
        decide (rankDigit n t q.val - 1 ≤ rankDigit n s p.val - 1)
      else true) (List.finRange n)) (List.finRange n)

def oddRejectBit {n : Nat} (A : NBA α (Fin n)) (code : Nat) : Bool :=
  listAll (fun q =>
    if supportedBit n code q && decide ((rankDigit n code q.val - 1) % 2 = 1) then
      decide (A.accept q = false)
    else true) (List.finRange n)

def noOweBit (n code : Nat) : Bool :=
  listAll (fun q : Fin n => decide (oweBit n code q.val = false)) (List.finRange n)

def oweStepBit {n : Nat} (A : NBA α (Fin n)) (a : α) (s t : Nat) : Bool :=
  if noOweBit n s then
    listAll (fun q => decide (oweBit n t q.val = evenAtBit n t q)) (List.finRange n)
  else
    listAll (fun q =>
      decide (oweBit n t q.val =
        (evenAtBit n t q &&
          listAny (fun p => oweBit n s p.val && A.step p a q) (List.finRange n))))
      (List.finRange n)

def startBit {n : Nat} (A : NBA α (Fin n)) (code : Nat) : Bool :=
  listAll (fun q => decide (supportedBit n code q = A.start q)) (List.finRange n) &&
    oddRejectBit A code &&
    listAll (fun q => decide (oweBit n code q.val = evenAtBit n code q)) (List.finRange n)

def stepBit {n : Nat} (A : NBA α (Fin n)) (a : α) (s t : Nat) : Bool :=
  supportExactBit A a s t && monoRankBit A a s t && oddRejectBit A t && oweStepBit A a s t

def rankCast (n : Nat) (r : Fin (2 * n + 1)) : Fin (2 * Fintype.card (Fin n) + 1) :=
  Fin.cast (congrArg (fun k => 2 * k + 1) (Fintype.card_fin n)).symm r

theorem RankGuess.ext {σ : Type} [Fintype σ] {s t : RankGuess σ}
    (hr : s.rank = t.rank) (ho : s.owe = t.owe) : s = t := by
  cases s
  cases t
  cases hr
  cases ho
  rfl

def rankIndex {n : Nat} (r : Option (Fin (2 * Fintype.card (Fin n) + 1))) : Nat :=
  r.elim 0 (fun k => k.val + 1)

theorem rankIndex_lt {n : Nat} (r : Option (Fin (2 * Fintype.card (Fin n) + 1))) :
    rankIndex r < rankSymCount n := by
  cases r with
  | none =>
    simp [rankIndex, rankSymCount]
  | some k =>
    have hk : k.val + 1 < 2 * n + 2 := by
      have hlt : k.val < 2 * Fintype.card (Fin n) + 1 := k.isLt
      have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
      omega
    simpa [rankIndex, rankSymCount] using hk

def ofRankCode {n : Nat} (g : RankGuess (Fin n)) : Nat :=
  packDigits (rankSymCount n) n (fun q => rankIndex (g.rank q)) * 2 ^ n +
    packDigits 2 n (fun q => bif g.owe q then 1 else 0)

theorem ofRankCode_lt {n : Nat} (g : RankGuess (Fin n)) : ofRankCode g < guessCard n := by
  have hbase : 1 ≤ rankSymCount n := rankSymCount_pos n
  have hrank :=
    packDigits_lt (fun q => rankIndex (g.rank q)) hbase (fun q => rankIndex_lt (g.rank q))
  have howe :=
    packDigits_lt (fun q => bif g.owe q then 1 else 0) (by decide : 1 ≤ 2)
      (fun q => by cases g.owe q <;> decide)
  have hone : 1 ≤ rankSymCount n ^ n :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hbase)))
  have hmul : packDigits (rankSymCount n) n (fun q => rankIndex (g.rank q)) ≤
      rankSymCount n ^ n - 1 := Nat.le_pred_of_lt hrank
  have hsum :
      packDigits (rankSymCount n) n (fun q => rankIndex (g.rank q)) * 2 ^ n +
        packDigits 2 n (fun q => bif g.owe q then 1 else 0) <
      rankSymCount n ^ n * 2 ^ n := by
    calc
      packDigits (rankSymCount n) n (fun q => rankIndex (g.rank q)) * 2 ^ n +
          packDigits 2 n (fun q => bif g.owe q then 1 else 0) ≤
          (rankSymCount n ^ n - 1) * 2 ^ n +
            packDigits 2 n (fun q => bif g.owe q then 1 else 0) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hmul) _
      _ < (rankSymCount n ^ n - 1) * 2 ^ n + 2 ^ n := Nat.add_lt_add_left howe _
      _ = (rankSymCount n ^ n - 1).succ * 2 ^ n := (Nat.succ_mul _ _).symm
      _ = rankSymCount n ^ n * 2 ^ n := by
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hone]
  simpa [ofRankCode, guessCard] using hsum

def ofRankGuess {n : Nat} (g : RankGuess (Fin n)) : Fin (guessCard n) :=
  ⟨ofRankCode g, ofRankCode_lt g⟩

def toRankGuess {n : Nat} (c : Fin (guessCard n)) : RankGuess (Fin n) where
  rank q := (rawRank n c.val q).map (rankCast n)
  owe q := oweBit n c.val q.val

theorem bool_eq_of_true_iff {b c : Bool} (h : b = true ↔ c = true) : b = c := by
  cases b <;> cases c <;> simp_all

theorem supported_iff {n : Nat} (c : Fin (guessCard n)) (q : Fin n) :
    supported (toRankGuess c).rank q ↔ rankDigit n c.val q.val ≠ 0 := by
  unfold supported toRankGuess rawRank
  by_cases hd : rankDigit n c.val q.val = 0
  · simp [hd, Option.isSome]
  · simp [hd, Option.isSome]

theorem rank_some_val {n : Nat} (c : Fin (guessCard n)) (q : Fin n)
    {r : Fin (2 * Fintype.card (Fin n) + 1)}
    (h : (toRankGuess c).rank q = some r) :
    rankDigit n c.val q.val ≠ 0 ∧ r.val = rankDigit n c.val q.val - 1 := by
  have hsup : supported (toRankGuess c).rank q := by simp [supported, h]
  have hd := (supported_iff c q).mp hsup
  unfold toRankGuess rawRank at h
  simp [hd] at h
  refine ⟨hd, ?_⟩
  cases h
  rfl

theorem evenAt_iff {n : Nat} (c : Fin (guessCard n)) (q : Fin n) :
    evenAt (toRankGuess c).rank q ↔ evenAtBit n c.val q = true := by
  constructor
  · intro ⟨r, hr, heven⟩
    obtain ⟨hd, hv⟩ := rank_some_val c q hr
    have hbit : supportedBit n c.val q = true := by
      simp [supportedBit, hd]
    have hmod : (rankDigit n c.val q.val - 1) % 2 = 0 := by rw [← hv]; exact heven
    simp [evenAtBit, hbit, hmod]
  · intro h
    rw [evenAtBit, Bool.and_eq_true_iff, decide_eq_true_iff] at h
    obtain ⟨hsup, hmod⟩ := h
    have hd : rankDigit n c.val q.val ≠ 0 := by
      simp [supportedBit] at hsup
      exact hsup
    refine ⟨rankCast n ⟨rankDigit n c.val q.val - 1, by
      have hlt := rankDigit_lt n c.val q.val
      simp [rankSymCount] at hlt
      omega⟩, ?_, ?_⟩
    · unfold toRankGuess rawRank
      simp [hd]
    · exact hmod

theorem owe_toRankGuess {n : Nat} (c : Fin (guessCard n)) (q : Fin n) :
    (toRankGuess c).owe q = oweBit n c.val q.val := rfl

theorem noOweBit_iff {n : Nat} (c : Fin (guessCard n)) :
    noOweBit n c.val = true ↔ noOwe (toRankGuess c).owe := by
  rw [noOweBit, listAll_iff]
  constructor
  · intro h q
    have hq := h q (List.mem_finRange q)
    rw [decide_eq_true_iff] at hq
    simpa [owe_toRankGuess] using hq
  · intro h q _
    rw [decide_eq_true_iff]
    simpa [owe_toRankGuess] using h q

theorem oddRejectBit_iff {n : Nat} (A : NBA α (Fin n)) (c : Fin (guessCard n)) :
    oddRejectBit A c.val = true ↔ oddReject A (toRankGuess c).rank := by
  rw [oddRejectBit, listAll_iff]
  constructor
  · intro h q r hr hodd
    have hq := h q (List.mem_finRange q)
    obtain ⟨hd, hv⟩ := rank_some_val c q hr
    have hcond :
        (supportedBit n c.val q &&
          decide ((rankDigit n c.val q.val - 1) % 2 = 1)) = true := by
      rw [Bool.and_eq_true_iff]
      refine ⟨?_, ?_⟩
      · simp [supportedBit, hd]
      · rw [decide_eq_true_iff, ← hv]
        exact hodd
    rw [if_pos hcond, decide_eq_true_iff] at hq
    exact hq
  · intro h q _
    by_cases hcond :
        (supportedBit n c.val q &&
          decide ((rankDigit n c.val q.val - 1) % 2 = 1)) = true
    · rw [if_pos hcond]
      rw [Bool.and_eq_true_iff] at hcond
      obtain ⟨hsup, hmod⟩ := hcond
      rw [decide_eq_true_iff] at hmod
      have hd : rankDigit n c.val q.val ≠ 0 := by
        simp [supportedBit] at hsup
        exact hsup
      let r0 : Fin (2 * n + 1) := ⟨rankDigit n c.val q.val - 1, by
        have hlt := rankDigit_lt n c.val q.val
        simp [rankSymCount] at hlt
        omega⟩
      have hr : (toRankGuess c).rank q = some (rankCast n r0) := by
        unfold toRankGuess rawRank
        simp [hd]
        apply congrArg (rankCast n)
        apply Fin.ext
        rfl
      rw [decide_eq_true_iff]
      exact h q _ hr hmod
    · rw [if_neg hcond]

theorem supportedBit_eq {n code : Nat} {q : Fin n} :
    supportedBit n code q = true ↔ rankDigit n code q.val ≠ 0 := by
  simp [supportedBit]

theorem supportExactBit_iff {n : Nat} (A : NBA α (Fin n)) (a : α)
    (s t : Fin (guessCard n)) :
    supportExactBit A a s.val t.val = true ↔
      supportExact A a (toRankGuess s).rank (toRankGuess t).rank := by
  rw [supportExactBit, listAll_iff]
  constructor
  · intro h q
    have hq := h q (List.mem_finRange q)
    rw [decide_eq_true_iff] at hq
    constructor
    · intro hsup
      have hbit : supportedBit n t.val q = true :=
        supportedBit_eq.mpr ((supported_iff t q).mp hsup)
      rw [hbit, eq_comm] at hq
      rw [listAny_iff] at hq
      obtain ⟨p, _, hp⟩ := hq
      rw [Bool.and_eq_true_iff] at hp
      exact ⟨p, (supported_iff s p).mpr (supportedBit_eq.mp hp.1), hp.2⟩
    · intro ⟨p, hp, hstep⟩
      apply (supported_iff t q).mpr
      apply supportedBit_eq.mp
      rw [hq, listAny_iff]
      refine ⟨p, List.mem_finRange p, ?_⟩
      rw [Bool.and_eq_true_iff]
      exact ⟨supportedBit_eq.mpr ((supported_iff s p).mp hp), hstep⟩
  · intro h q _
    rw [decide_eq_true_iff]
    apply bool_eq_of_true_iff
    constructor
    · intro hbit
      obtain ⟨p, hp, hstep⟩ := (h q).mp ((supported_iff t q).mpr (supportedBit_eq.mp hbit))
      rw [listAny_iff]
      refine ⟨p, List.mem_finRange p, ?_⟩
      rw [Bool.and_eq_true_iff]
      exact ⟨supportedBit_eq.mpr ((supported_iff s p).mp hp), hstep⟩
    · intro hany
      rw [listAny_iff] at hany
      obtain ⟨p, _, hp⟩ := hany
      rw [Bool.and_eq_true_iff] at hp
      exact supportedBit_eq.mpr ((supported_iff t q).mp
        ((h q).mpr ⟨p, (supported_iff s p).mpr (supportedBit_eq.mp hp.1), hp.2⟩))

theorem monoRankBit_iff {n : Nat} (A : NBA α (Fin n)) (a : α)
    (s t : Fin (guessCard n)) :
    monoRankBit A a s.val t.val = true ↔
      monoRank A a (toRankGuess s).rank (toRankGuess t).rank := by
  rw [monoRankBit, listAll_iff]
  constructor
  · intro h p q rp rq hp hq hstep
    have hp' := h p (List.mem_finRange p)
    rw [listAll_iff] at hp'
    have hcond := hp' q (List.mem_finRange q)
    obtain ⟨hsp, hvp⟩ := rank_some_val s p hp
    obtain ⟨hsq, hvq⟩ := rank_some_val t q hq
    have hflag :
        (supportedBit n s.val p && supportedBit n t.val q && A.step p a q) = true := by
      rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
      exact ⟨⟨by simp [supportedBit, hsp], by simp [supportedBit, hsq]⟩, hstep⟩
    rw [if_pos hflag, decide_eq_true_iff] at hcond
    rw [← hvq, ← hvp] at hcond
    exact hcond
  · intro h p _
    rw [listAll_iff]
    intro q _
    by_cases hflag :
        (supportedBit n s.val p && supportedBit n t.val q && A.step p a q) = true
    · rw [if_pos hflag]
      rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at hflag
      obtain ⟨⟨hsp, hsq⟩, hstep⟩ := hflag
      have hpd : rankDigit n s.val p.val ≠ 0 := by
        simp [supportedBit] at hsp
        exact hsp
      have hqd : rankDigit n t.val q.val ≠ 0 := by
        simp [supportedBit] at hsq
        exact hsq
      let rp0 : Fin (2 * n + 1) := ⟨rankDigit n s.val p.val - 1, by
        have hlt := rankDigit_lt n s.val p.val
        simp [rankSymCount] at hlt
        omega⟩
      let rq0 : Fin (2 * n + 1) := ⟨rankDigit n t.val q.val - 1, by
        have hlt := rankDigit_lt n t.val q.val
        simp [rankSymCount] at hlt
        omega⟩
      have hp : (toRankGuess s).rank p = some (rankCast n rp0) := by
        unfold toRankGuess rawRank
        simp [hpd]
        apply congrArg (rankCast n)
        apply Fin.ext
        rfl
      have hq : (toRankGuess t).rank q = some (rankCast n rq0) := by
        unfold toRankGuess rawRank
        simp [hqd]
        apply congrArg (rankCast n)
        apply Fin.ext
        rfl
      have hle := h p q _ _ hp hq hstep
      rw [decide_eq_true_iff]
      exact hle
    · rw [if_neg hflag]

theorem oweStepBit_iff {n : Nat} (A : NBA α (Fin n)) (a : α)
    (s t : Fin (guessCard n)) :
    oweStepBit A a s.val t.val = true ↔
      oweStep A a (toRankGuess t).rank (toRankGuess s).owe (toRankGuess t).owe := by
  unfold oweStepBit
  by_cases hempty : noOweBit n s.val = true
  · rw [if_pos hempty, listAll_iff]
    constructor
    · intro h
      refine Or.inl ⟨(noOweBit_iff s).mp hempty, ?_⟩
      intro q
      have hq := h q (List.mem_finRange q)
      rw [decide_eq_true_iff] at hq
      rw [owe_toRankGuess, hq, evenAt_iff]
    · intro h q _
      rw [decide_eq_true_iff]
      rcases h with ⟨_, hall⟩ | ⟨hnot, _⟩
      · apply bool_eq_of_true_iff
        rw [← owe_toRankGuess, ← evenAt_iff]
        exact hall q
      · exact absurd ((noOweBit_iff s).mp hempty) hnot
  · rw [if_neg hempty, listAll_iff]
    have hnot : ¬ noOwe (toRankGuess s).owe := by
      intro h
      exact hempty ((noOweBit_iff s).mpr h)
    constructor
    · intro h
      refine Or.inr ⟨hnot, ?_⟩
      intro q
      have hq := h q (List.mem_finRange q)
      rw [decide_eq_true_iff] at hq
      rw [owe_toRankGuess, hq]
      constructor
      · intro hbit
        rw [Bool.and_eq_true_iff] at hbit
        obtain ⟨hev, hany⟩ := hbit
        rw [listAny_iff] at hany
        obtain ⟨p, _, hp⟩ := hany
        rw [Bool.and_eq_true_iff] at hp
        exact ⟨(evenAt_iff t q).mpr hev,
          ⟨p, by simpa [owe_toRankGuess] using hp.1, hp.2⟩⟩
      · intro ⟨hev, p, hp, hstep⟩
        rw [Bool.and_eq_true_iff, listAny_iff]
        exact ⟨(evenAt_iff t q).mp hev,
          ⟨p, List.mem_finRange p, by
            rw [Bool.and_eq_true_iff]
            exact ⟨by simpa [owe_toRankGuess] using hp, hstep⟩⟩⟩
    · intro h q _
      rw [decide_eq_true_iff]
      rcases h with ⟨hemptyP, _⟩ | ⟨_, hall⟩
      · exact absurd hemptyP hnot
      · apply bool_eq_of_true_iff
        rw [← owe_toRankGuess]
        constructor
        · intro hb
          obtain ⟨hev, p, hp, hstep⟩ := (hall q).mp hb
          rw [Bool.and_eq_true_iff, listAny_iff]
          exact ⟨(evenAt_iff t q).mp hev,
            ⟨p, List.mem_finRange p, by
              rw [Bool.and_eq_true_iff, ← owe_toRankGuess]
              exact ⟨hp, hstep⟩⟩⟩
        · intro hbit
          rw [Bool.and_eq_true_iff] at hbit
          obtain ⟨hev, hany⟩ := hbit
          rw [listAny_iff] at hany
          obtain ⟨p, _, hp⟩ := hany
          rw [Bool.and_eq_true_iff] at hp
          rw [← owe_toRankGuess] at hp
          exact (hall q).mpr ⟨(evenAt_iff t q).mpr hev, ⟨p, hp.1, hp.2⟩⟩

theorem stepBit_iff {n : Nat} (A : NBA α (Fin n)) (a : α)
    (s t : Fin (guessCard n)) :
    stepBit A a s.val t.val = true ↔ stepProp A a (toRankGuess s) (toRankGuess t) := by
  rw [stepBit, Bool.and_eq_true_iff, Bool.and_eq_true_iff, Bool.and_eq_true_iff]
  constructor
  · intro ⟨⟨⟨hsup, hmono⟩, hodd⟩, howe⟩
    exact ⟨(supportExactBit_iff A a s t).mp hsup,
      (monoRankBit_iff A a s t).mp hmono,
      (oddRejectBit_iff A t).mp hodd,
      (oweStepBit_iff A a s t).mp howe⟩
  · intro ⟨hsup, hmono, hodd, howe⟩
    exact ⟨⟨⟨(supportExactBit_iff A a s t).mpr hsup,
      (monoRankBit_iff A a s t).mpr hmono⟩,
      (oddRejectBit_iff A t).mpr hodd⟩,
      (oweStepBit_iff A a s t).mpr howe⟩

theorem startBit_iff {n : Nat} (A : NBA α (Fin n)) (c : Fin (guessCard n)) :
    startBit A c.val = true ↔ startProp A (toRankGuess c) := by
  rw [startBit, Bool.and_eq_true_iff, Bool.and_eq_true_iff]
  constructor
  · intro ⟨⟨hsup, hodd⟩, howe⟩
    refine ⟨?_, (oddRejectBit_iff A c).mp hodd, ?_⟩
    · rw [listAll_iff] at hsup
      intro q
      have hq := hsup q (List.mem_finRange q)
      rw [decide_eq_true_iff] at hq
      rw [supported_iff, ← supportedBit_eq]
      constructor
      · intro hb
        rw [← hq, hb]
      · intro hb
        rw [hq, hb]
    · rw [listAll_iff] at howe
      intro q
      have hq := howe q (List.mem_finRange q)
      rw [decide_eq_true_iff] at hq
      rw [owe_toRankGuess, evenAt_iff, hq]
  · intro ⟨hsup, hodd, howe⟩
    refine ⟨⟨?_, (oddRejectBit_iff A c).mpr hodd⟩, ?_⟩
    · rw [listAll_iff]
      intro q _
      rw [decide_eq_true_iff]
      apply bool_eq_of_true_iff
      rw [supportedBit_eq, ← supported_iff]
      exact hsup q
    · rw [listAll_iff]
      intro q _
      rw [decide_eq_true_iff]
      apply bool_eq_of_true_iff
      rw [← owe_toRankGuess, ← evenAt_iff]
      exact howe q

/-- The Boolean rank complement. Transitions are the matrix `stepBit`. -/
def finComplement {n : Nat} (A : NBA α (Fin n)) : NBA α (Fin (guessCard n)) where
  step s a t := stepBit A a s.val t.val
  start s := startBit A s.val
  accept s := noOweBit n s.val

theorem finComplement_step_iff {n : Nat} (A : NBA α (Fin n))
    (s : Fin (guessCard n)) (a : α) (t : Fin (guessCard n)) :
    (finComplement A).step s a t = true ↔ stepProp A a (toRankGuess s) (toRankGuess t) := by
  simpa [finComplement] using stepBit_iff A a s t

theorem finComplement_start_iff {n : Nat} (A : NBA α (Fin n)) (s : Fin (guessCard n)) :
    (finComplement A).start s = true ↔ startProp A (toRankGuess s) := by
  simpa [finComplement] using startBit_iff A s

theorem finComplement_accept_iff {n : Nat} (A : NBA α (Fin n)) (s : Fin (guessCard n)) :
    (finComplement A).accept s = true ↔ noOwe (toRankGuess s).owe := by
  simpa [finComplement] using noOweBit_iff s

theorem rankDigit_ofRank {n : Nat} (g : RankGuess (Fin n)) (q : Fin n) :
    rankDigit n (ofRankCode g) q.val = rankIndex (g.rank q) := by
  have hbase : 1 ≤ rankSymCount n := rankSymCount_pos n
  have howe_lt :=
    packDigits_lt (fun i => bif g.owe i then 1 else 0) (by decide : 1 ≤ 2)
      (fun i => by cases g.owe i <;> decide)
  rw [ofRankCode, rankDigit_of_parts q howe_lt]
  exact packDigits_digit (fun i => rankIndex (g.rank i)) hbase
    (fun i => rankIndex_lt (g.rank i)) q

theorem oweBit_ofRank {n : Nat} (g : RankGuess (Fin n)) (q : Fin n) :
    oweBit n (ofRankCode g) q.val = g.owe q := by
  have howe_lt :=
    packDigits_lt (fun i => bif g.owe i then 1 else 0) (by decide : 1 ≤ 2)
      (fun i => by cases g.owe i <;> decide)
  rw [ofRankCode, oweBit_of_parts q howe_lt]
  have hdigit :=
    packDigits_digit (fun i => bif g.owe i then 1 else 0) (by decide : 1 ≤ 2)
      (fun i => by cases g.owe i <;> decide) q
  cases hg : g.owe q
  · simp [hg] at hdigit
    simp [hdigit]
  · simp [hg] at hdigit
    simp [hdigit]

theorem toRankGuess_ofRankGuess {n : Nat} (g : RankGuess (Fin n)) :
    toRankGuess (ofRankGuess g) = g := by
  apply RankGuess.ext
  · funext q
    have hdigit := rankDigit_ofRank g q
    change (rawRank n (ofRankCode g) q).map (rankCast n) = g.rank q
    cases hg : g.rank q with
    | none =>
      have hz : rankIndex (g.rank q) = 0 := by simp [hg, rankIndex]
      rw [hz] at hdigit
      simp only [rawRank, hdigit]
      rw [dif_pos trivial]
      rfl
    | some k =>
      have hidx : rankIndex (g.rank q) = k.val + 1 := by simp [hg, rankIndex]
      rw [hidx] at hdigit
      simp only [rawRank, hdigit]
      apply congrArg some
      apply Fin.ext
      simp [rankCast]
  · funext q
    change oweBit n (ofRankCode g) q.val = g.owe q
    exact oweBit_ofRank g q

theorem code_eq_digits {n c : Nat} (hc : c < guessCard n) :
    c = packDigits (rankSymCount n) n (fun q => rankDigit n c q.val) * 2 ^ n +
      packDigits 2 n (fun q => bif oweBit n c q.val then 1 else 0) := by
  have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
  have hbase : 1 ≤ rankSymCount n := rankSymCount_pos n
  have hrank : c / 2 ^ n < rankSymCount n ^ n := by
    have hc' : c < 2 ^ n * rankSymCount n ^ n := by
      simpa [guessCard, Nat.mul_comm] using hc
    exact Nat.div_lt_of_lt_mul hc'
  have howe : c % 2 ^ n < 2 ^ n := Nat.mod_lt _ h2
  have hrankPack := pack_of_digits hbase hrank
  have howePack := pack_of_digits (by decide : 1 ≤ 2) howe
  have hrankFun :
      (fun q : Fin n => ((c / 2 ^ n) / rankSymCount n ^ q.val) % rankSymCount n) =
        fun q : Fin n => rankDigit n c q.val := by
    funext q
    rfl
  have howeFun :
      (fun q : Fin n => ((c % 2 ^ n) / 2 ^ q.val) % 2) =
        fun q : Fin n => bif oweBit n c q.val then 1 else 0 := by
    funext q
    have hd : ((c % 2 ^ n) / 2 ^ q.val) % 2 < 2 := Nat.mod_lt _ (by decide)
    cases hbit : ((c % 2 ^ n) / 2 ^ q.val) % 2 with
    | zero =>
      simp [oweBit, hbit]
    | succ d =>
      have hd0 : d = 0 := by omega
      simp [oweBit, hbit, hd0]
  rw [hrankFun] at hrankPack
  rw [howeFun] at howePack
  calc
    c = c / 2 ^ n * 2 ^ n + c % 2 ^ n := (Nat.div_add_mod' c (2 ^ n)).symm
    _ = packDigits (rankSymCount n) n (fun q => rankDigit n c q.val) * 2 ^ n +
          c % 2 ^ n := by rw [← hrankPack]
    _ = packDigits (rankSymCount n) n (fun q => rankDigit n c q.val) * 2 ^ n +
          packDigits 2 n (fun q => bif oweBit n c q.val then 1 else 0) := by
      rw [← howePack]

theorem ofRankGuess_toRankGuess {n : Nat} (c : Fin (guessCard n)) :
    ofRankGuess (toRankGuess c) = c := by
  apply Fin.ext
  have hcode := code_eq_digits c.isLt
  have hrank : packDigits (rankSymCount n) n (fun q => rankIndex ((toRankGuess c).rank q)) =
      packDigits (rankSymCount n) n (fun q => rankDigit n c.val q.val) := by
    congr 1
    funext q
    by_cases hd : rankDigit n c.val q.val = 0
    · have hnone : (toRankGuess c).rank q = none := by
        unfold toRankGuess rawRank
        simp [hd]
      simp [hnone, rankIndex, hd]
    · have hsome : (toRankGuess c).rank q =
          some (rankCast n ⟨rankDigit n c.val q.val - 1, by
            have hlt := rankDigit_lt n c.val q.val
            simp [rankSymCount] at hlt
            omega⟩) := by
        unfold toRankGuess rawRank
        simp [hd]
      simp [hsome, rankIndex]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)
  have howe : packDigits 2 n (fun q => bif (toRankGuess c).owe q then 1 else 0) =
      packDigits 2 n (fun q => bif oweBit n c.val q.val then 1 else 0) := by
    congr 1
  change ofRankCode (toRankGuess c) = c.val
  simp only [ofRankCode, hrank, howe]
  exact hcode.symm

theorem accepts_recode {τ : Type} (A : NBA α σ) (decode : τ → σ) (encode : σ → τ)
    (hde : ∀ s, decode (encode s) = s) (B : NBA α τ)
    (hstep : ∀ t a t', B.step t a t' = A.step (decode t) a (decode t'))
    (hstart : ∀ t, B.start t = A.start (decode t))
    (hacc : ∀ t, B.accept t = A.accept (decode t)) (w : Nat → α) :
    Accepts B w ↔ Accepts A w := by
  constructor
  · intro ⟨path, h0, hs, ha⟩
    refine ⟨fun i => decode (path i), ?_, ?_, ?_⟩
    · simpa [hstart] using h0
    · intro i
      simpa [hstep] using hs i
    · intro lower
      obtain ⟨visit, hv, hx⟩ := ha lower
      exact ⟨visit, hv, by simpa [hacc] using hx⟩
  · intro ⟨path, h0, hs, ha⟩
    refine ⟨fun i => encode (path i), ?_, ?_, ?_⟩
    · simpa [hstart, hde] using h0
    · intro i
      simpa [hstep, hde] using hs i
    · intro lower
      obtain ⟨visit, hv, hx⟩ := ha lower
      exact ⟨visit, hv, by simpa [hacc, hde] using hx⟩

theorem finComplement_step_eq {n : Nat} (A : NBA α (Fin n))
    (s : Fin (guessCard n)) (a : α) (t : Fin (guessCard n)) :
    (finComplement A).step s a t =
      (complement A).step (toRankGuess s) a (toRankGuess t) :=
  bool_eq_of_true_iff
    ((finComplement_step_iff A s a t).trans (complement_step_iff A _ _ _).symm)

theorem finComplement_start_eq {n : Nat} (A : NBA α (Fin n)) (s : Fin (guessCard n)) :
    (finComplement A).start s = (complement A).start (toRankGuess s) :=
  bool_eq_of_true_iff
    ((finComplement_start_iff A s).trans (complement_start_iff A _).symm)

theorem finComplement_accept_eq {n : Nat} (A : NBA α (Fin n)) (s : Fin (guessCard n)) :
    (finComplement A).accept s = (complement A).accept (toRankGuess s) :=
  bool_eq_of_true_iff
    ((finComplement_accept_iff A s).trans (complement_accept_iff A _).symm)

theorem accepts_finComplement_rank {n : Nat} (A : NBA α (Fin n)) (w : Nat → α) :
    Accepts (finComplement A) w ↔ Accepts (complement A) w :=
  accepts_recode (complement A) toRankGuess ofRankGuess toRankGuess_ofRankGuess
    (finComplement A) (fun s a t => finComplement_step_eq A s a t)
    (fun s => finComplement_start_eq A s)
    (fun s => finComplement_accept_eq A s) w

/-- Acceptance of the Boolean complement is rejection by the source automaton. -/
theorem accepts_finComplement {n : Nat} (A : NBA α (Fin n)) (w : Nat → α) :
    Accepts (finComplement A) w ↔ ¬ Accepts A w := by
  rw [accepts_finComplement_rank, accepts_complement]

def splitFin {m n : Nat} (hn : 0 < n) (i : Fin (m * n)) : Fin m × Fin n :=
  (⟨i.val / n, by
      let v : Nat := i.val
      have hv : v < m * n := i.isLt
      have hv' : v < n * m := by rwa [Nat.mul_comm m n] at hv
      exact Nat.div_lt_of_lt_mul hv'⟩,
    ⟨i.val % n, Nat.mod_lt _ hn⟩)

def joinFin {m n : Nat} (p : Fin m × Fin n) : Fin (m * n) :=
  ⟨p.2.val + n * p.1.val, by
    have h2 : p.2.val < n := p.2.isLt
    have h1 : p.1.val < m := p.1.isLt
    calc
      p.2.val + n * p.1.val < n + n * p.1.val := Nat.add_lt_add_right h2 _
      _ = n * (p.1.val + 1) := by rw [Nat.add_comm, ← Nat.mul_succ]
      _ ≤ n * m := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h1)
      _ = m * n := Nat.mul_comm _ _⟩

theorem joinFin_splitFin {m n : Nat} (hn : 0 < n) (i : Fin (m * n)) :
    joinFin (splitFin hn i) = i := by
  apply Fin.ext
  simp [joinFin, splitFin]
  exact Nat.mod_add_div i.val n

theorem splitFin_joinFin {m n : Nat} (hn : 0 < n) (p : Fin m × Fin n) :
    splitFin hn (joinFin p) = p := by
  apply Prod.ext
  · apply Fin.ext
    simp [splitFin, joinFin]
    rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]
  · apply Fin.ext
    simp [splitFin, joinFin]
    exact Nat.mod_eq_of_lt p.2.isLt

def decodeSum {m n : Nat} (i : Fin (m + n)) : Fin m ⊕ Fin n :=
  if h : i.val < m then .inl ⟨i.val, h⟩ else .inr ⟨i.val - m, by have := i.isLt; omega⟩

def encodeSum {m n : Nat} : Fin m ⊕ Fin n → Fin (m + n)
  | .inl i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩
  | .inr j => ⟨m + j.val, by omega⟩

theorem encodeSum_decodeSum {m n : Nat} (i : Fin (m + n)) :
    encodeSum (decodeSum i) = i := by
  unfold decodeSum
  by_cases h : i.val < m
  · simp [h, encodeSum]
  · simp [h, encodeSum]
    apply Fin.ext
    exact Nat.add_sub_of_le (Nat.le_of_not_lt h)

theorem decodeSum_encodeSum {m n : Nat} (s : Fin m ⊕ Fin n) :
    decodeSum (encodeSum s) = s := by
  cases s with
  | inl i =>
    simp [decodeSum, encodeSum, i.isLt]
  | inr j =>
    have hge : ¬ m + j.val < m := Nat.not_lt.mpr (Nat.le_add_right _ _)
    simp [decodeSum, encodeSum, hge]

def finStuck : NBA Unit (Fin 1) where
  step := fun _ _ _ => false
  start := fun _ => true
  accept := fun _ => true

def finLoop : NBA Unit (Fin 1) where
  step := fun _ _ _ => true
  start := fun _ => true
  accept := fun _ => true

theorem finStuck_rejects (w : Nat → Unit) : ¬ Accepts finStuck w := by
  intro h
  obtain ⟨_, _, hs, _⟩ := h
  exact Bool.false_ne_true (hs 0)

theorem finLoop_accepts (w : Nat → Unit) : Accepts finLoop w := by
  refine ⟨fun _ => 0, rfl, fun _ => rfl, ?_⟩
  intro lower
  exact ⟨lower, le_rfl, rfl⟩

theorem control_finComplement_stuck (w : Nat → Unit) :
    Accepts (finComplement finStuck) w :=
  (accepts_finComplement finStuck w).mpr (finStuck_rejects w)

theorem control_finComplement_loop (w : Nat → Unit) :
    ¬ Accepts (finComplement finLoop) w := by
  intro h
  exact (accepts_finComplement finLoop w).mp h (finLoop_accepts w)

/-! ## Retained lasso checking

`lassoChecker` is the generic retained-execution machine. Its checkpoint keeps
the automaton, the edge now under consideration, the pivot, the current state,
the remaining stem and loop, and the verdict. A primitive step examines one
supplied edge. The step reads Boolean transition data and does not assume the
certificate is valid. `.finished true` is completed acceptance, `.faulted` is
refusal, and `.exhausted` keeps the checkpoint for an exact resume.
-/

open Mettapedia.GSLT.Distinction.ProductiveBlocks

inductive LassoFocus where
  | admit
  | stem
  | loop
  | close

/-- Retained state of one lasso check. The head of the list selected by
`focus` is the current stem or loop edge. `stem` and `loop` are the remaining
certificate. -/
structure LassoCheckpoint (α σ : Type) where
  automaton : NBA α σ
  focus : LassoFocus
  current : σ
  pivot : σ
  stem : List (α × σ)
  loop : List (α × σ)
  verdict : Option Bool

@[implicit_reducible]
def atAdmit (A : NBA α σ) (start : σ) (stem loop : List (α × σ)) : LassoCheckpoint α σ where
  automaton := A
  focus := .admit
  current := start
  pivot := start
  stem := stem
  loop := loop
  verdict := none

@[implicit_reducible]
def atStem (A : NBA α σ) (current pivot : σ) (stem loop : List (α × σ)) :
    LassoCheckpoint α σ where
  automaton := A
  focus := .stem
  current := current
  pivot := pivot
  stem := stem
  loop := loop
  verdict := none

@[implicit_reducible]
def atLoop (A : NBA α σ) (current pivot : σ) (loop : List (α × σ)) : LassoCheckpoint α σ where
  automaton := A
  focus := .loop
  current := current
  pivot := pivot
  stem := []
  loop := loop
  verdict := none

theorem atStem_take (A : NBA α σ) (current pivot : σ) (a : α) (q : σ)
    (rest loop : List (α × σ)) :
    { atStem A current pivot ((a, q) :: rest) loop with current := q, stem := rest } =
      atStem A q pivot rest loop := rfl

theorem atLoop_take (A : NBA α σ) (current pivot : σ) (a : α) (q : σ) (rest : List (α × σ)) :
    { atLoop A current pivot ((a, q) :: rest) with current := q, loop := rest } =
      atLoop A q pivot rest := rfl

theorem atAdmit_to_stem (A : NBA α σ) (start : σ) (stem loop : List (α × σ)) :
    { atAdmit A start stem loop with focus := .stem } = atStem A start start stem loop := rfl

theorem atStem_to_loop (A : NBA α σ) (current pivot : σ) (loop : List (α × σ)) :
    { atStem A current pivot [] loop with focus := .loop, pivot := current } =
      atLoop A current current loop := rfl

def Lasso.checkpoint (A : NBA α σ) (L : Lasso α σ) : LassoCheckpoint α σ :=
  atAdmit A L.startState L.stem L.loop

def lassoBudget {γ : Type} (stem loop : List γ) : Nat :=
  stem.length + loop.length + 4

/-- One primitive step of the lasso check. -/
def LassoCheckpoint.react [DecidableEq σ] (cp : LassoCheckpoint α σ) :
    Transition (LassoCheckpoint α σ) (α × σ) Bool Unit :=
  match cp.verdict with
  | some true => .finish true
  | some false => .fail []
  | none =>
    match cp.focus with
    | .admit =>
      match cp.automaton.start cp.current with
      | true => .silent { cp with focus := .stem }
      | false => .silent { cp with verdict := some false }
    | .stem =>
      match cp.stem with
      | [] =>
        match cp.loop.isEmpty with
        | true =>
          .silent { cp with focus := .close, pivot := cp.current, verdict := some false }
        | false =>
          .silent { cp with focus := .loop, pivot := cp.current }
      | edge :: rest =>
        match cp.automaton.step cp.current edge.1 edge.2 with
        | true => .publish [edge] { cp with current := edge.2, stem := rest }
        | false => .silent { cp with verdict := some false }
    | .loop =>
      match cp.loop with
      | [] =>
        match decide (cp.current = cp.pivot) && cp.automaton.accept cp.pivot with
        | true => .silent { cp with focus := .close, verdict := some true }
        | false => .silent { cp with focus := .close, verdict := some false }
      | edge :: rest =>
        match cp.automaton.step cp.current edge.1 edge.2 with
        | true => .publish [edge] { cp with current := edge.2, loop := rest }
        | false => .silent { cp with verdict := some false }
    | .close =>
      .silent { cp with verdict := some false }

/-- The lasso checker on the generic retained-execution machine. -/
def lassoChecker [DecidableEq σ] :
    Machine (LassoCheckpoint α σ) (α × σ) Bool Unit where
  step cp := some cp.react

theorem lassoChecker_not_stuck [DecidableEq σ] (fuel : Nat) (cp stopped : LassoCheckpoint α σ) :
    (lassoChecker.run fuel cp).2 ≠ .stuck stopped :=
  lassoChecker.run_not_stuck_of_moves
    (fun state hnone => by simp [lassoChecker] at hnone) fuel cp stopped

theorem run_verdict_true [DecidableEq σ] (cp : LassoCheckpoint α σ) (extra : Nat)
    (h : cp.verdict = some true) :
    lassoChecker.run (extra + 1) cp = ([], .finished true) := by
  have hstep : lassoChecker.step cp = some (.finish true) := by
    simp [lassoChecker, LassoCheckpoint.react, h]
  have h1 : lassoChecker.run 1 cp = ([], .finished true) :=
    lassoChecker.run_succ_finish (fuel := 0) hstep
  have hnot : ∀ residual, (lassoChecker.run 1 cp).2 ≠ .exhausted residual := by
    simp [h1]
  rw [Nat.add_comm]
  exact (lassoChecker.run_stable 1 extra cp hnot).trans h1

theorem run_verdict_false [DecidableEq σ] (cp : LassoCheckpoint α σ) (extra : Nat)
    (h : cp.verdict = some false) :
    lassoChecker.run (extra + 1) cp = ([], .faulted) := by
  have hstep : lassoChecker.step cp = some (.fail []) := by
    simp [lassoChecker, LassoCheckpoint.react, h]
  have h1 : lassoChecker.run 1 cp = ([], .faulted) :=
    lassoChecker.run_succ_fail (fuel := 0) hstep
  have hnot : ∀ residual, (lassoChecker.run 1 cp).2 ≠ .exhausted residual := by
    simp [h1]
  rw [Nat.add_comm]
  exact (lassoChecker.run_stable 1 extra cp hnot).trans h1

theorem react_admit_yes [DecidableEq σ] (A : NBA α σ) (start : σ) (stem loop : List (α × σ))
    (hstart : A.start start = true) :
    (atAdmit A start stem loop).react = .silent (atStem A start start stem loop) := by
  unfold LassoCheckpoint.react
  simp only [atAdmit, hstart]
  rfl

theorem react_admit_no [DecidableEq σ] (A : NBA α σ) (start : σ) (stem loop : List (α × σ))
    (hstart : ¬ A.start start = true) :
    (atAdmit A start stem loop).react =
      .silent { atAdmit A start stem loop with verdict := some false } := by
  unfold LassoCheckpoint.react
  simp only [atAdmit, Bool.eq_false_iff.mpr hstart]

theorem react_stem_publish [DecidableEq σ] (A : NBA α σ) (current pivot : σ) (a : α) (q : σ)
    (rest loop : List (α × σ)) (hstep : A.step current a q = true) :
    (atStem A current pivot ((a, q) :: rest) loop).react =
      .publish [(a, q)] (atStem A q pivot rest loop) := by
  unfold LassoCheckpoint.react
  simp only [atStem, hstep]

theorem react_stem_fail [DecidableEq σ] (A : NBA α σ) (current pivot : σ) (a : α) (q : σ)
    (rest loop : List (α × σ)) (hstep : ¬ A.step current a q = true) :
    (atStem A current pivot ((a, q) :: rest) loop).react =
      .silent { atStem A current pivot ((a, q) :: rest) loop with verdict := some false } := by
  unfold LassoCheckpoint.react
  simp only [atStem, Bool.eq_false_iff.mpr hstep]

theorem react_stem_enter [DecidableEq σ] (A : NBA α σ) (current pivot : σ) (loop : List (α × σ))
    (hloop : ¬ loop.isEmpty = true) :
    (atStem A current pivot [] loop).react = .silent (atLoop A current current loop) := by
  unfold LassoCheckpoint.react
  simp only [atStem, Bool.eq_false_iff.mpr hloop]
  rfl

theorem react_stem_empty [DecidableEq σ] (A : NBA α σ) (current pivot : σ) (loop : List (α × σ))
    (hempty : loop.isEmpty = true) :
    (atStem A current pivot [] loop).react =
      .silent { atStem A current pivot [] loop with
        focus := .close, pivot := current, verdict := some false } := by
  unfold LassoCheckpoint.react
  simp only [atStem, hempty]

theorem react_loop_publish [DecidableEq σ] (A : NBA α σ) (current pivot : σ) (a : α) (q : σ)
    (rest : List (α × σ)) (hstep : A.step current a q = true) :
    (atLoop A current pivot ((a, q) :: rest)).react =
      .publish [(a, q)] (atLoop A q pivot rest) := by
  unfold LassoCheckpoint.react
  simp only [atLoop, hstep]

theorem react_loop_fail [DecidableEq σ] (A : NBA α σ) (current pivot : σ) (a : α) (q : σ)
    (rest : List (α × σ)) (hstep : ¬ A.step current a q = true) :
    (atLoop A current pivot ((a, q) :: rest)).react =
      .silent { atLoop A current pivot ((a, q) :: rest) with verdict := some false } := by
  unfold LassoCheckpoint.react
  simp only [atLoop, Bool.eq_false_iff.mpr hstep]

theorem react_loop_close_yes [DecidableEq σ] (A : NBA α σ) (current pivot : σ)
    (hcond : (decide (current = pivot) && A.accept pivot) = true) :
    (atLoop A current pivot []).react =
      .silent { atLoop A current pivot [] with focus := .close, verdict := some true } := by
  unfold LassoCheckpoint.react
  simp only [atLoop, hcond]

theorem react_loop_close_no [DecidableEq σ] (A : NBA α σ) (current pivot : σ)
    (hcond : (decide (current = pivot) && A.accept pivot) = false) :
    (atLoop A current pivot []).react =
      .silent { atLoop A current pivot [] with focus := .close, verdict := some false } := by
  unfold LassoCheckpoint.react
  simp only [atLoop, hcond]

theorem run_stem_valid [DecidableEq σ] (A : NBA α σ) (pivot : σ) (loop : List (α × σ)) :
    ∀ (current : σ) (stem : List (α × σ)) (extra : Nat),
      chainValidBool A current stem = true →
      lassoChecker.run (stem.length + extra) (atStem A current pivot stem loop) =
        (stem ++ (lassoChecker.run extra (atStem A (chainEnd current stem) pivot [] loop)).1,
          (lassoChecker.run extra (atStem A (chainEnd current stem) pivot [] loop)).2) := by
  intro current stem
  induction stem generalizing current with
  | nil =>
    intro extra _
    simp [chainEnd_nil, List.length_nil, List.nil_append]
  | cons edge rest ih =>
    intro extra hchain
    obtain ⟨a, q⟩ := edge
    simp only [chainValidBool, Bool.and_eq_true] at hchain
    have hmachine : lassoChecker.step (atStem A current pivot ((a, q) :: rest) loop) =
        some (.publish [(a, q)] (atStem A q pivot rest loop)) := by
      simpa [lassoChecker] using congrArg some (react_stem_publish A current pivot a q rest loop hchain.1)
    have hfuel : ((a, q) :: rest).length + extra = (rest.length + extra) + 1 := by
      simp only [List.length_cons]
      omega
    rw [hfuel, lassoChecker.run_succ_publish hmachine, ih q extra hchain.2]
    simp [chainEnd]

theorem run_stem_invalid [DecidableEq σ] (A : NBA α σ) (pivot : σ) (loop : List (α × σ)) :
    ∀ (current : σ) (stem : List (α × σ)) (extra : Nat),
      chainValidBool A current stem = false →
      (lassoChecker.run (stem.length + (extra + 2)) (atStem A current pivot stem loop)).2 =
        .faulted := by
  intro current stem
  induction stem generalizing current with
  | nil =>
    intro extra hchain
    simp [chainValidBool] at hchain
  | cons edge rest ih =>
    intro extra hchain
    obtain ⟨a, q⟩ := edge
    by_cases hstep : A.step current a q = true
    · have hrest : chainValidBool A q rest = false := by
        simp only [chainValidBool, hstep, Bool.true_and] at hchain
        exact hchain
      have hmachine : lassoChecker.step (atStem A current pivot ((a, q) :: rest) loop) =
          some (.publish [(a, q)] (atStem A q pivot rest loop)) := by
        simpa [lassoChecker] using
          congrArg some (react_stem_publish A current pivot a q rest loop hstep)
      have hfuel : ((a, q) :: rest).length + (extra + 2) =
          (rest.length + (extra + 2)) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hfuel, lassoChecker.run_succ_publish hmachine]
      exact ih q extra hrest
    · have hmachine : lassoChecker.step (atStem A current pivot ((a, q) :: rest) loop) =
          some (.silent { atStem A current pivot ((a, q) :: rest) loop with
            verdict := some false }) := by
        simpa [lassoChecker] using
          congrArg some (react_stem_fail A current pivot a q rest loop hstep)
      have hfuel : ((a, q) :: rest).length + (extra + 2) =
          (((a, q) :: rest).length + extra) + 1 + 1 := by
        omega
      rw [hfuel, lassoChecker.run_succ_silent hmachine]
      exact congrArg Prod.snd <|
        run_verdict_false
          { atStem A current pivot ((a, q) :: rest) loop with verdict := some false }
          (((a, q) :: rest).length + extra) rfl

theorem run_loop_valid [DecidableEq σ] (A : NBA α σ) (pivot : σ) :
    ∀ (current : σ) (loop : List (α × σ)) (extra : Nat),
      chainValidBool A current loop = true →
      lassoChecker.run (loop.length + extra) (atLoop A current pivot loop) =
        (loop ++ (lassoChecker.run extra (atLoop A (chainEnd current loop) pivot [])).1,
          (lassoChecker.run extra (atLoop A (chainEnd current loop) pivot [])).2) := by
  intro current loop
  induction loop generalizing current with
  | nil =>
    intro extra _
    simp [chainEnd_nil, List.length_nil, List.nil_append]
  | cons edge rest ih =>
    intro extra hchain
    obtain ⟨a, q⟩ := edge
    simp only [chainValidBool, Bool.and_eq_true] at hchain
    have hmachine : lassoChecker.step (atLoop A current pivot ((a, q) :: rest)) =
        some (.publish [(a, q)] (atLoop A q pivot rest)) := by
      simpa [lassoChecker] using congrArg some (react_loop_publish A current pivot a q rest hchain.1)
    have hfuel : ((a, q) :: rest).length + extra = (rest.length + extra) + 1 := by
      simp only [List.length_cons]
      omega
    rw [hfuel, lassoChecker.run_succ_publish hmachine, ih q extra hchain.2]
    simp [chainEnd]

theorem run_loop_invalid [DecidableEq σ] (A : NBA α σ) (pivot : σ) :
    ∀ (current : σ) (loop : List (α × σ)) (extra : Nat),
      chainValidBool A current loop = false →
      (lassoChecker.run (loop.length + (extra + 2)) (atLoop A current pivot loop)).2 =
        .faulted := by
  intro current loop
  induction loop generalizing current with
  | nil =>
    intro extra hchain
    simp [chainValidBool] at hchain
  | cons edge rest ih =>
    intro extra hchain
    obtain ⟨a, q⟩ := edge
    by_cases hstep : A.step current a q = true
    · have hrest : chainValidBool A q rest = false := by
        simp only [chainValidBool, hstep, Bool.true_and] at hchain
        exact hchain
      have hmachine : lassoChecker.step (atLoop A current pivot ((a, q) :: rest)) =
          some (.publish [(a, q)] (atLoop A q pivot rest)) := by
        simpa [lassoChecker] using congrArg some (react_loop_publish A current pivot a q rest hstep)
      have hfuel : ((a, q) :: rest).length + (extra + 2) =
          (rest.length + (extra + 2)) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hfuel, lassoChecker.run_succ_publish hmachine]
      exact ih q extra hrest
    · have hmachine : lassoChecker.step (atLoop A current pivot ((a, q) :: rest)) =
          some (.silent { atLoop A current pivot ((a, q) :: rest) with
            verdict := some false }) := by
        simpa [lassoChecker] using congrArg some (react_loop_fail A current pivot a q rest hstep)
      have hfuel : ((a, q) :: rest).length + (extra + 2) =
          (((a, q) :: rest).length + extra) + 1 + 1 := by
        omega
      rw [hfuel, lassoChecker.run_succ_silent hmachine]
      exact congrArg Prod.snd <|
        run_verdict_false
          { atLoop A current pivot ((a, q) :: rest) with verdict := some false }
          (((a, q) :: rest).length + extra) rfl

theorem run_enter_loop [DecidableEq σ] (A : NBA α σ) (current pivot : σ)
    (loop : List (α × σ)) (extra : Nat) (hloop : ¬ loop.isEmpty = true) :
    lassoChecker.run (extra + 1) (atStem A current pivot [] loop) =
      lassoChecker.run extra (atLoop A current current loop) := by
  have hmachine : lassoChecker.step (atStem A current pivot [] loop) =
      some (.silent (atLoop A current current loop)) := by
    simpa [lassoChecker] using congrArg some (react_stem_enter A current pivot loop hloop)
  exact lassoChecker.run_succ_silent hmachine

theorem run_refuse_empty [DecidableEq σ] (A : NBA α σ) (current pivot : σ)
    (loop : List (α × σ)) (extra : Nat) (hempty : loop.isEmpty = true) :
    lassoChecker.run (extra + 2) (atStem A current pivot [] loop) = ([], .faulted) := by
  have hmachine : lassoChecker.step (atStem A current pivot [] loop) =
      some (.silent { atStem A current pivot [] loop with
        focus := .close, pivot := current, verdict := some false }) := by
    simpa [lassoChecker] using congrArg some (react_stem_empty A current pivot loop hempty)
  have hfuel : extra + 2 = (extra + 1) + 1 := by omega
  rw [hfuel, lassoChecker.run_succ_silent hmachine]
  exact run_verdict_false _ extra rfl

theorem run_close_yes [DecidableEq σ] (A : NBA α σ) (current pivot : σ)
    (hcond : (decide (current = pivot) && A.accept pivot) = true) :
    lassoChecker.run 2 (atLoop A current pivot []) = ([], .finished true) := by
  have hmachine : lassoChecker.step (atLoop A current pivot []) =
      some (.silent { atLoop A current pivot [] with focus := .close, verdict := some true }) := by
    simpa [lassoChecker] using congrArg some (react_loop_close_yes A current pivot hcond)
  rw [show (2 : Nat) = 1 + 1 by omega, lassoChecker.run_succ_silent hmachine]
  exact run_verdict_true _ 0 rfl

theorem run_close_no [DecidableEq σ] (A : NBA α σ) (current pivot : σ) (extra : Nat)
    (hcond : (decide (current = pivot) && A.accept pivot) = false) :
    lassoChecker.run (extra + 2) (atLoop A current pivot []) = ([], .faulted) := by
  have hmachine : lassoChecker.step (atLoop A current pivot []) =
      some (.silent { atLoop A current pivot [] with focus := .close, verdict := some false }) := by
    simpa [lassoChecker] using congrArg some (react_loop_close_no A current pivot hcond)
  have hfuel : extra + 2 = (extra + 1) + 1 := by omega
  rw [hfuel, lassoChecker.run_succ_silent hmachine]
  exact run_verdict_false _ extra rfl

theorem lassoChecker_of_check [DecidableEq σ] (A : NBA α σ) (L : Lasso α σ)
    (h : L.check A = true) :
    lassoChecker.run (lassoBudget L.stem L.loop) (Lasso.checkpoint A L) =
      (L.stem ++ L.loop, .finished true) := by
  simp only [Lasso.check, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hstart, hstem⟩, hempty⟩, hloop⟩, hclose⟩, hacc⟩
  have hneg : ¬ L.loop.isEmpty = true := (Bool.eq_false_iff.mp hempty)
  have hbudget : lassoBudget L.stem L.loop = (L.stem.length + (L.loop.length + 3)) + 1 := by
    simp [lassoBudget]
    omega
  have hadmit : lassoChecker.step (Lasso.checkpoint A L) =
      some (.silent (atStem A L.startState L.startState L.stem L.loop)) := by
    simpa [Lasso.checkpoint, lassoChecker] using
      congrArg some (react_admit_yes A L.startState L.stem L.loop hstart)
  rw [hbudget, lassoChecker.run_succ_silent hadmit]
  have hwalk := run_stem_valid A L.startState L.loop L.startState L.stem (L.loop.length + 3) hstem
  rw [hwalk]
  have hfuel : L.loop.length + 3 = (L.loop.length + 2) + 1 := by omega
  rw [hfuel, run_enter_loop A (chainEnd L.startState L.stem) L.startState L.loop (L.loop.length + 2) hneg]
  have hloopWalk := run_loop_valid A (chainEnd L.startState L.stem)
      (chainEnd L.startState L.stem) L.loop 2 hloop
  rw [hloopWalk]
  have hcond : (decide (chainEnd (chainEnd L.startState L.stem) L.loop =
      chainEnd L.startState L.stem) && A.accept (chainEnd L.startState L.stem)) = true := by
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hclose, hacc⟩
  rw [run_close_yes A (chainEnd (chainEnd L.startState L.stem) L.loop)
    (chainEnd L.startState L.stem) hcond]
  simp [List.append_nil]

theorem lassoChecker_of_refused [DecidableEq σ] (A : NBA α σ) (L : Lasso α σ)
    (h : L.check A = false) :
    (lassoChecker.run (lassoBudget L.stem L.loop) (Lasso.checkpoint A L)).2 = .faulted := by
  by_cases hstart : A.start L.startState = true
  · by_cases hstem : chainValidBool A L.startState L.stem = true
    · by_cases hempty : L.loop.isEmpty = true
      · have hlist : L.loop = [] := List.nil_of_isEmpty hempty
        have hbudget : lassoBudget L.stem L.loop = (L.stem.length + 3) + 1 := by
          simp [lassoBudget, hlist, List.length_nil]
        have hadmit : lassoChecker.step (Lasso.checkpoint A L) =
            some (.silent (atStem A L.startState L.startState L.stem L.loop)) := by
          simpa [Lasso.checkpoint, lassoChecker] using
            congrArg some (react_admit_yes A L.startState L.stem L.loop hstart)
        rw [hbudget, lassoChecker.run_succ_silent hadmit]
        have hwalk := run_stem_valid A L.startState L.loop L.startState L.stem 3 hstem
        rw [hwalk, hlist]
        exact congrArg Prod.snd (run_refuse_empty A (chainEnd L.startState L.stem)
          L.startState [] 1 (by simp))
      · have hneg : ¬ L.loop.isEmpty = true := hempty
        by_cases hloop : chainValidBool A (chainEnd L.startState L.stem) L.loop = true
        · by_cases hcond : (decide (chainEnd (chainEnd L.startState L.stem) L.loop =
              chainEnd L.startState L.stem) &&
              A.accept (chainEnd L.startState L.stem)) = true
          · apply False.elim
            have htrue : L.check A = true := by
              simp only [Lasso.check, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              exact ⟨⟨⟨⟨⟨hstart, hstem⟩, Bool.eq_false_iff.mpr hneg⟩, hloop⟩, hcond.1⟩, hcond.2⟩
            exact Bool.false_ne_true (h.symm.trans htrue)
          · have hbudget : lassoBudget L.stem L.loop =
                (L.stem.length + ((L.loop.length + 2) + 1)) + 1 := by
              simp [lassoBudget]
              omega
            have hadmit : lassoChecker.step (Lasso.checkpoint A L) =
                some (.silent (atStem A L.startState L.startState L.stem L.loop)) := by
              simpa [Lasso.checkpoint, lassoChecker] using
                congrArg some (react_admit_yes A L.startState L.stem L.loop hstart)
            rw [hbudget, lassoChecker.run_succ_silent hadmit]
            have hwalk := run_stem_valid A L.startState L.loop L.startState L.stem
                (((L.loop.length + 2) + 1)) hstem
            rw [hwalk, run_enter_loop A (chainEnd L.startState L.stem) L.startState L.loop
              (L.loop.length + 2) hneg]
            have hloopWalk := run_loop_valid A (chainEnd L.startState L.stem)
                (chainEnd L.startState L.stem) L.loop 2 hloop
            rw [hloopWalk]
            exact congrArg Prod.snd (run_close_no A
              (chainEnd (chainEnd L.startState L.stem) L.loop)
              (chainEnd L.startState L.stem) 0 (Bool.eq_false_iff.mpr hcond))
        · have hbudget : lassoBudget L.stem L.loop =
              (L.stem.length + ((L.loop.length + 2) + 1)) + 1 := by
            simp [lassoBudget]
            omega
          have hadmit : lassoChecker.step (Lasso.checkpoint A L) =
              some (.silent (atStem A L.startState L.startState L.stem L.loop)) := by
            simpa [Lasso.checkpoint, lassoChecker] using
              congrArg some (react_admit_yes A L.startState L.stem L.loop hstart)
          rw [hbudget, lassoChecker.run_succ_silent hadmit]
          have hwalk := run_stem_valid A L.startState L.loop L.startState L.stem
              ((L.loop.length + 2) + 1) hstem
          rw [hwalk, run_enter_loop A (chainEnd L.startState L.stem) L.startState L.loop
            (L.loop.length + 2) hneg]
          exact run_loop_invalid A (chainEnd L.startState L.stem)
            (chainEnd L.startState L.stem) L.loop 0 (Bool.eq_false_iff.mpr hloop)
    · have hbudget : lassoBudget L.stem L.loop =
          (L.stem.length + ((L.loop.length + 1) + 2)) + 1 := by
        simp [lassoBudget]
        omega
      have hadmit : lassoChecker.step (Lasso.checkpoint A L) =
          some (.silent (atStem A L.startState L.startState L.stem L.loop)) := by
        simpa [Lasso.checkpoint, lassoChecker] using
          congrArg some (react_admit_yes A L.startState L.stem L.loop hstart)
      rw [hbudget, lassoChecker.run_succ_silent hadmit]
      exact run_stem_invalid A L.startState L.loop L.startState L.stem (L.loop.length + 1)
        (Bool.eq_false_iff.mpr hstem)
  · have hbudget : lassoBudget L.stem L.loop =
        (L.stem.length + L.loop.length + 2) + 1 + 1 := by
      simp [lassoBudget]
    have hmachine : lassoChecker.step (Lasso.checkpoint A L) =
        some (.silent { atAdmit A L.startState L.stem L.loop with verdict := some false }) := by
      simpa [Lasso.checkpoint, lassoChecker] using
        congrArg some (react_admit_no A L.startState L.stem L.loop hstart)
    rw [hbudget, lassoChecker.run_succ_silent hmachine]
    exact congrArg Prod.snd (run_verdict_false
      { atAdmit A L.startState L.stem L.loop with verdict := some false }
      (L.stem.length + L.loop.length + 2) rfl)

/-- Acceptance of some word has a retained run that finishes accepted, and a
retained run that finishes accepted is a lasso accepted by `Lasso.check`. -/
theorem accepts_iff_lassoChecker [Fintype σ] [DecidableEq σ] (A : NBA α σ) :
    (∃ w, Accepts A w) ↔
      ∃ L, (lassoChecker.run (lassoBudget L.stem L.loop) (Lasso.checkpoint A L)).2 =
        .finished true := by
  constructor
  · intro ⟨w, hw⟩
    obtain ⟨L, hL⟩ := accepts_exists_lasso A hw
    exact ⟨L, congrArg Prod.snd (lassoChecker_of_check A L hL)⟩
  · intro ⟨L, hfin⟩
    have hcheck : L.check A = true := by
      cases hL : L.check A with
      | true => rfl
      | false =>
        have href := lassoChecker_of_refused A L hL
        rw [href] at hfin
        cases hfin
    obtain ⟨_, hacc⟩ := Lasso.check_accepts A L hcheck
    exact ⟨_, hacc⟩

/-- The transition account is the supplied per-step price times the number of
primitive steps. That step count is the account at price one. -/
theorem lassoChecker_spent_mul [DecidableEq σ] (matrixCost : Nat) :
    ∀ (fuel : Nat) (cp : LassoCheckpoint α σ),
      lassoChecker.spent (fun _ => matrixCost) fuel cp =
        matrixCost * lassoChecker.spent (fun _ => 1) fuel cp := by
  intro fuel
  induction fuel with
  | zero =>
    intro cp
    simp [Machine.spent]
  | succ fuel ih =>
    intro cp
    cases hstep : lassoChecker.step cp with
    | none => simp [Machine.spent, hstep]
    | some transition =>
      cases transition with
      | silent next =>
        simp only [Machine.spent, hstep, ih next]
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      | publish _ next =>
        simp only [Machine.spent, hstep, ih next]
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      | finish _ =>
        simp only [Machine.spent, hstep, Nat.mul_one]
      | fail _ =>
        simp only [Machine.spent, hstep, Nat.mul_one]
      | call _ _ =>
        simp only [Machine.spent, hstep, Nat.mul_one]

def goodLasso : Lasso Unit (Fin 1) where
  startState := 0
  stem := []
  loop := [((), 0)]

def emptyLasso : Lasso Unit (Fin 1) where
  startState := 0
  stem := []
  loop := []

def badLasso : Lasso Unit (Fin 1) where
  startState := 0
  stem := []
  loop := [((), 0)]

/-- One edge from `0` to `1`. The loop is a real transition and it does not
return to the pivot. -/
def hopOut : NBA Unit (Fin 2) where
  step s _ t := decide (s = 0) && decide (t = 1)
  start s := decide (s = 0)
  accept s := decide (s = 0)

def nonclosingLasso : Lasso Unit (Fin 2) where
  startState := 0
  stem := []
  loop := [((), 1)]

def splitCheckpoint : LassoCheckpoint Unit (Fin 1) where
  automaton := finLoop
  focus := .stem
  current := 0
  pivot := 0
  stem := [((), 0), ((), 0)]
  loop := [((), 0)]
  verdict := none

def splitMid : LassoCheckpoint Unit (Fin 1) where
  automaton := finLoop
  focus := .stem
  current := 0
  pivot := 0
  stem := [((), 0)]
  loop := [((), 0)]
  verdict := none

def splitAfter : LassoCheckpoint Unit (Fin 1) where
  automaton := finLoop
  focus := .stem
  current := 0
  pivot := 0
  stem := []
  loop := [((), 0)]
  verdict := none

theorem control_lasso_good :
    goodLasso.check finLoop = true ∧
    lassoChecker.run (lassoBudget goodLasso.stem goodLasso.loop)
      (Lasso.checkpoint finLoop goodLasso) =
      (goodLasso.stem ++ goodLasso.loop, .finished true) := by
  have hcheck : goodLasso.check finLoop = true := by decide
  exact ⟨hcheck, lassoChecker_of_check finLoop goodLasso hcheck⟩

theorem control_lasso_empty_loop :
    emptyLasso.check finLoop = false ∧
    (lassoChecker.run (lassoBudget emptyLasso.stem emptyLasso.loop)
      (Lasso.checkpoint finLoop emptyLasso)).2 = .faulted := by
  have hcheck : emptyLasso.check finLoop = false := by decide
  exact ⟨hcheck, lassoChecker_of_refused finLoop emptyLasso hcheck⟩

theorem control_lasso_bad_transition :
    badLasso.check finStuck = false ∧
    (lassoChecker.run (lassoBudget badLasso.stem badLasso.loop)
      (Lasso.checkpoint finStuck badLasso)).2 = .faulted := by
  have hcheck : badLasso.check finStuck = false := by decide
  exact ⟨hcheck, lassoChecker_of_refused finStuck badLasso hcheck⟩

theorem control_lasso_nonclosing :
    nonclosingLasso.check hopOut = false ∧
    (lassoChecker.run (lassoBudget nonclosingLasso.stem nonclosingLasso.loop)
      (Lasso.checkpoint hopOut nonclosingLasso)).2 = .faulted := by
  have hcheck : nonclosingLasso.check hopOut = false := by decide
  exact ⟨hcheck, lassoChecker_of_refused hopOut nonclosingLasso hcheck⟩

theorem control_split_first :
    lassoChecker.run 1 splitCheckpoint = ([((), 0)], .exhausted splitMid) := by
  have hreact : splitCheckpoint.react = .publish [((), 0)] splitMid := by
    unfold LassoCheckpoint.react
    simp [splitCheckpoint, splitMid, finLoop]
  simp [Machine.run, lassoChecker, hreact]

theorem control_split_second :
    lassoChecker.run 1 splitMid = ([((), 0)], .exhausted splitAfter) := by
  have hreact : splitMid.react = .publish [((), 0)] splitAfter := by
    unfold LassoCheckpoint.react
    simp [splitMid, splitAfter, finLoop]
  simp [Machine.run, lassoChecker, hreact]

/-- One step publishes the first stem edge and exhausts at the residual.
Resuming that residual publishes the pending edge. The two-step run is the
concatenation, so the residual segment does not republish the first edge. -/
theorem control_lasso_split :
    lassoChecker.run 1 splitCheckpoint = ([((), 0)], .exhausted splitMid) ∧
    lassoChecker.run 1 splitMid = ([((), 0)], .exhausted splitAfter) ∧
    lassoChecker.run (1 + 1) splitCheckpoint =
      ([((), 0)] ++ [((), 0)], .exhausted splitAfter) ∧
    (lassoChecker.run 1 splitMid).1.length = 1 ∧
    (lassoChecker.run (1 + 1) splitCheckpoint).1.length = 2 := by
  refine ⟨control_split_first, control_split_second, ?_, ?_, ?_⟩
  · simpa [control_split_first, control_split_second] using
      lassoChecker.established_and_pending 1 1 splitCheckpoint splitMid [((), 0)]
        control_split_first
  · simp [control_split_second]
  · have hresume := lassoChecker.established_and_pending 1 1 splitCheckpoint splitMid [((), 0)]
      control_split_first
    simp [hresume, control_split_second]

theorem control_lasso_budget :
    lassoChecker.run 0 (Lasso.checkpoint finLoop goodLasso) =
      ([], .exhausted (Lasso.checkpoint finLoop goodLasso)) := rfl

theorem control_lasso_refusal_not_budget :
    (lassoChecker.run (lassoBudget emptyLasso.stem emptyLasso.loop)
      (Lasso.checkpoint finLoop emptyLasso)).2 ≠
      (lassoChecker.run 0 (Lasso.checkpoint finLoop goodLasso)).2 := by
  intro hsame
  have href := control_lasso_empty_loop.2
  rw [href, control_lasso_budget] at hsame
  cases hsame

/-- A one-edge accepting lasso publishes one edge and takes five primitive
steps. At matrix price 8 the account is 40. -/
theorem control_lasso_transition_cost :
    (lassoChecker.run (lassoBudget goodLasso.stem goodLasso.loop)
      (Lasso.checkpoint finLoop goodLasso)).1.length = 1 ∧
    lassoChecker.spent (fun _ => 1) (lassoBudget goodLasso.stem goodLasso.loop)
      (Lasso.checkpoint finLoop goodLasso) = 5 ∧
    lassoChecker.spent (fun _ => 8) (lassoBudget goodLasso.stem goodLasso.loop)
      (Lasso.checkpoint finLoop goodLasso) = 40 := by
  have hrun := control_lasso_good.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun]
    simp [goodLasso]
  · decide
  · have hmul := lassoChecker_spent_mul 8
      (lassoBudget goodLasso.stem goodLasso.loop) (Lasso.checkpoint finLoop goodLasso)
    have hsteps : lassoChecker.spent (fun _ => 1) (lassoBudget goodLasso.stem goodLasso.loop)
        (Lasso.checkpoint finLoop goodLasso) = 5 := by decide
    rw [hmul, hsteps]

#print axioms accepts_finComplement
#print axioms finComplement
#print axioms toRankGuess
#print axioms ofRankGuess

#print axioms level_narrow
#print axioms exists_rank_drop
#print axioms oddRank_not_accepts
#print axioms exists_oddRank_of_not_accepts
#print axioms oddRank_iff_not_accepts
#print axioms complement_accepts_not
#print axioms accepts_complement
#print axioms control_complement_noStep
#print axioms control_complement_allLoop

#print axioms decideNonempty_iff
#print axioms Lasso.check_accepts
#print axioms accepts_exists_lasso
#print axioms lasso_accepts
#print axioms accepts_union
#print axioms accepts_inter
#print axioms accepts_project

#print axioms lassoChecker_of_check
#print axioms lassoChecker_of_refused
#print axioms accepts_iff_lassoChecker
#print axioms lassoChecker_spent_mul
#print axioms lassoChecker
#print axioms control_lasso_good
#print axioms control_lasso_empty_loop
#print axioms control_lasso_bad_transition
#print axioms control_lasso_nonclosing
#print axioms control_lasso_split
#print axioms control_lasso_transition_cost
#print axioms control_lasso_budget
#print axioms control_lasso_refusal_not_budget

end Mettapedia.Logic.Arithmetic.BuchiAutomaton
