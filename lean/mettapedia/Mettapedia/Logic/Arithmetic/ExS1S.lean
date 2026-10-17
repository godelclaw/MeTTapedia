import Mettapedia.Logic.Arithmetic.BuchiAutomaton
import Mathlib.Tactic.SplitIfs

open Mettapedia.Logic.Arithmetic.BuchiAutomaton

/-!
# Monadic second-order logic of one successor

Monadic second-order logic over `(ℕ, succ)`. Formulas use equality, succession,
and membership, with Boolean connectives, individual quantifiers, and set
quantifiers. An individual is true at exactly one position. A set is an
arbitrary predicate. `compileMSO` sends a formula to a nondeterministic Büchi
automaton. `compileMSO_iff` says that automaton accepts a word exactly when the
word is a valid assignment and the formula holds. `decideMSO` decides a closed
sentence by emptiness. `decideMSO_iff` says the answer is `true` exactly when
the sentence holds of `(ℕ, succ)`. `msoBubble` is that decision. J. Richard
Büchi, *On a Decision Method in Restricted Second Order Arithmetic* (1962).

Complementation is `accepts_complement` in `BuchiAutomaton`. The complement
stores a rank guess in `0, …, 2|Q|` and a breakpoint obligation on the even
ranks. An odd rank is rejecting. Orna Kupferman and Moshe Y. Vardi,
*Complementation Constructions for Nondeterministic Automata on Infinite Words*
(2005).

The older entry `exS1SBubble` decides an existential sentence whose matrix is a
Boolean combination of four atoms on one monadic predicate: infinitely often a
letter, eventually a letter, always a letter, and finitely often a letter.
Negation of each atom is again one of the four atoms, so that entry pushes
Boolean negation to the atoms. A universal sentence of that entry returns
`none`.

`toMSO` sends a finite nondeterministic Büchi automaton on this alphabet to a
formula. `toMSO_iff` says the formula holds of an ω-word exactly when the
automaton accepts that word. Acceptance is the run condition of
`BuchiAutomaton`: the run starts in a start state, reads the word along the
transition relation, and visits an accepting state beyond every finite prefix.

`execCompile` builds the same acceptance relation by a recursive Boolean
automaton whose states are codes in `Fin (execCount φ)`. Negation uses
`finComplement`. `execDecide` decides a closed sentence by the Boolean emptiness
search, and `execDecide_iff` says that answer is `true` exactly when the
sentence holds of `(ℕ, succ)`. `execCompile_sat_iff_checkedLasso` says that
same sentence holds exactly when a retained run of `Lasso.check` on
`execCompile φ` finishes accepted. `control_exec_succ_lasso_check` and
`control_exec_succ_lasso_run` are an explicit lasso on the compiled automaton
of `∃x. ∃y. succ(x, y)`, kernel-checked, with a refused certificate and a
split resume on that same automaton.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.ExS1S

inductive Atom where
  | infinitelyOften (b : Bool)
  | eventually (b : Bool)
  | always (b : Bool)
  | finitelyOften (b : Bool)

inductive Matrix where
  | atom (a : Atom)
  | and (φ ψ : Matrix)
  | or (φ ψ : Matrix)
  | not (φ : Matrix)

inductive Sentence where
  | exists_ (φ : Matrix)
  | forall_ (φ : Matrix)

def satAtom (a : Atom) (w : Nat → Bool) : Prop :=
  match a with
  | .infinitelyOften b => ∀ n, ∃ m, n ≤ m ∧ w m = b
  | .eventually b => ∃ m, w m = b
  | .always b => ∀ m, w m = b
  | .finitelyOften b => ∃ n, ∀ m, n ≤ m → w m ≠ b

def satMatrix : Matrix → (Nat → Bool) → Prop
  | .atom a, w => satAtom a w
  | .and φ ψ, w => satMatrix φ w ∧ satMatrix ψ w
  | .or φ ψ, w => satMatrix φ w ∨ satMatrix ψ w
  | .not φ, w => ¬ satMatrix φ w

def negAtom : Atom → Atom
  | .infinitelyOften b => .finitelyOften b
  | .finitelyOften b => .infinitelyOften b
  | .eventually b => .always (!b)
  | .always b => .eventually (!b)

theorem bool_ne_iff_eq_not (x b : Bool) : x ≠ b ↔ x = !b := by
  cases x <;> cases b <;> decide

theorem negAtom_iff (a : Atom) (w : Nat → Bool) :
    satAtom (negAtom a) w ↔ ¬ satAtom a w := by
  cases a with
  | infinitelyOften b =>
    simp only [negAtom, satAtom]
    constructor
    · intro ⟨n, hn⟩ hall
      obtain ⟨m, hm, heq⟩ := hall n
      exact hn m hm heq
    · intro hall
      classical
      push Not at hall
      exact hall
  | finitelyOften b =>
    simp only [negAtom, satAtom]
    constructor
    · intro hall ⟨n, hn⟩
      obtain ⟨m, hm, heq⟩ := hall n
      exact hn m hm heq
    · intro hall
      classical
      push Not at hall
      exact hall
  | eventually b =>
    simp only [negAtom, satAtom]
    constructor
    · intro hall ⟨m, hm⟩
      exact (bool_ne_iff_eq_not (w m) b).mpr (hall m) hm
    · intro hall m
      exact (bool_ne_iff_eq_not (w m) b).mp (fun heq => hall ⟨m, heq⟩)
  | always b =>
    simp only [negAtom, satAtom]
    constructor
    · intro ⟨m, hm⟩ hall
      exact ((bool_ne_iff_eq_not (w m) b).mpr hm) (hall m)
    · intro hall
      classical
      push Not at hall
      obtain ⟨m, hm⟩ := hall
      exact ⟨m, (bool_ne_iff_eq_not (w m) b).mp hm⟩

inductive Pos where
  | atom (a : Atom)
  | and (φ ψ : Pos)
  | or (φ ψ : Pos)

def satPos : Pos → (Nat → Bool) → Prop
  | .atom a, w => satAtom a w
  | .and φ ψ, w => satPos φ w ∧ satPos ψ w
  | .or φ ψ, w => satPos φ w ∨ satPos ψ w

def toPos : Bool → Matrix → Pos
  | true, .atom a => .atom a
  | false, .atom a => .atom (negAtom a)
  | true, .and φ ψ => .and (toPos true φ) (toPos true ψ)
  | false, .and φ ψ => .or (toPos false φ) (toPos false ψ)
  | true, .or φ ψ => .or (toPos true φ) (toPos true ψ)
  | false, .or φ ψ => .and (toPos false φ) (toPos false ψ)
  | p, .not φ => toPos (!p) φ

theorem toPos_iff (p : Bool) (φ : Matrix) (w : Nat → Bool) :
    satPos (toPos p φ) w ↔ if p then satMatrix φ w else ¬ satMatrix φ w := by
  classical
  induction φ generalizing p with
  | atom a =>
    cases p
    · simp only [toPos, satPos, satMatrix, Bool.false_eq_true, if_false, negAtom_iff]
    · simp only [toPos, satPos, satMatrix, if_true]
  | and φ ψ ihφ ihψ =>
    cases p
    · have ihφ' := ihφ false
      have ihψ' := ihψ false
      simp only [Bool.false_eq_true, if_false] at ihφ' ihψ'
      simp only [toPos, satPos, satMatrix, Bool.false_eq_true, if_false]
      rw [ihφ', ihψ']
      constructor
      · intro h ⟨hφ, hψ⟩
        rcases h with hnφ | hnψ
        · exact hnφ hφ
        · exact hnψ hψ
      · intro hn
        by_cases hφ : satMatrix φ w
        · exact Or.inr (fun hψ => hn ⟨hφ, hψ⟩)
        · exact Or.inl hφ
    · have ihφ' := ihφ true
      have ihψ' := ihψ true
      simp only [if_true] at ihφ' ihψ'
      simp only [toPos, satPos, satMatrix, if_true]
      rw [ihφ', ihψ']
  | or φ ψ ihφ ihψ =>
    cases p
    · have ihφ' := ihφ false
      have ihψ' := ihψ false
      simp only [Bool.false_eq_true, if_false] at ihφ' ihψ'
      simp only [toPos, satPos, satMatrix, Bool.false_eq_true, if_false]
      rw [ihφ', ihψ']
      constructor
      · intro ⟨hnφ, hnψ⟩ h
        rcases h with hφ | hψ
        · exact hnφ hφ
        · exact hnψ hψ
      · intro hn
        refine ⟨?_, ?_⟩
        · intro hφ
          exact hn (Or.inl hφ)
        · intro hψ
          exact hn (Or.inr hψ)
    · have ihφ' := ihφ true
      have ihψ' := ihψ true
      simp only [if_true] at ihφ' ihψ'
      simp only [toPos, satPos, satMatrix, if_true]
      rw [ihφ', ihψ']
  | not φ ih =>
    cases p
    · have ih' := ih true
      simp only [if_true] at ih'
      simp only [toPos, Bool.not_false, satMatrix, Bool.false_eq_true, if_false]
      rw [ih']
      constructor
      · intro h hn
        exact hn h
      · intro hn
        exact Classical.not_not.mp hn
    · have ih' := ih false
      simp only [Bool.false_eq_true, if_false] at ih'
      simp only [toPos, satMatrix, if_true]
      exact ih'

theorem toPos_true_iff (φ : Matrix) (w : Nat → Bool) :
    satPos (toPos true φ) w ↔ satMatrix φ w := by
  simpa using toPos_iff true φ w

/-! ## Atomata -/

def atomInfOften (b : Bool) : NBA Bool Bool where
  step := fun _ a q' => decide (q' = (a == b))
  start := fun q => decide (q = false)
  accept := fun q => decide (q = true)

def atomEventually (b : Bool) : NBA Bool Bool where
  step := fun q a q' =>
    if q = true then decide (q' = true) else decide (q' = (a == b))
  start := fun q => decide (q = false)
  accept := fun q => decide (q = true)

def atomAlways (b : Bool) : NBA Bool Bool where
  step := fun q a q' =>
    if q = false then decide (q' = false) else decide (q' = (a == b))
  start := fun q => decide (q = true)
  accept := fun q => decide (q = true)

/-- Guess the position after which `b` does not occur, then stay there. -/
def atomFinitelyOften (b : Bool) : NBA Bool Bool where
  step := fun q a q' =>
    if q = false && q' = false then true
    else if q' = true then decide (a ≠ b)
    else false
  start := fun q => decide (q = false)
  accept := fun q => decide (q = true)

theorem beq_eq_true_iff (x b : Bool) : (x == b) = true ↔ x = b := by
  cases x <;> cases b <;> decide

theorem atomInfOften_iff (b : Bool) (w : Nat → Bool) :
    Accepts (atomInfOften b) w ↔ ∀ n, ∃ m, n ≤ m ∧ w m = b := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    have h0 : path 0 = false := by
      simp only [atomInfOften, decide_eq_true_eq] at hstart
      exact hstart
    have hnext : ∀ n, path (n + 1) = (w n == b) := by
      intro n
      have h := hstep n
      simp only [atomInfOften, decide_eq_true_eq] at h
      exact h
    intro lowerBound
    -- The letter sits one step before the accepting state.
    obtain ⟨visit, hv, ha⟩ := hacc (lowerBound + 1)
    have htrue : path visit = true := by
      simp only [atomInfOften, decide_eq_true_eq] at ha
      exact ha
    have hpos : 0 < visit := by
      by_contra hle
      have : visit = 0 := by omega
      rw [this, h0] at htrue
      exact Bool.false_ne_true htrue
    refine ⟨visit - 1, by omega, ?_⟩
    have hletter : path visit = (w (visit - 1) == b) := by
      have hv' : visit = (visit - 1) + 1 := by omega
      rw [hv']
      exact hnext (visit - 1)
    rw [htrue] at hletter
    exact (beq_eq_true_iff _ _).mp hletter.symm
  · intro hall
    let path : Nat → Bool
      | 0 => false
      | n + 1 => w n == b
    have path_zero : path 0 = false := rfl
    have path_succ : ∀ n, path (n + 1) = (w n == b) := fun _ => rfl
    refine ⟨path, ?_, ?_, ?_⟩
    · simp [atomInfOften, path_zero]
    · intro n
      simp [atomInfOften, path_succ n]
    · intro lowerBound
      obtain ⟨m, hm, hw⟩ := hall lowerBound
      refine ⟨m + 1, by omega, ?_⟩
      simp [atomInfOften, path_succ m, hw]

def eventuallyPath (b : Bool) (w : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => if eventuallyPath b w n = true then true else w n == b

theorem eventuallyPath_zero (b : Bool) (w : Nat → Bool) :
    eventuallyPath b w 0 = false := rfl

theorem eventuallyPath_succ (b : Bool) (w : Nat → Bool) (n : Nat) :
    eventuallyPath b w (n + 1) =
      if eventuallyPath b w n = true then true else w n == b := rfl

theorem eventuallyPath_stay (b : Bool) (w : Nat → Bool) {n : Nat}
    (h : eventuallyPath b w n = true) (k : Nat) :
    eventuallyPath b w (n + k) = true := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Nat.add_succ, eventuallyPath_succ, ih]
    simp

theorem atomEventually_iff (b : Bool) (w : Nat → Bool) :
    Accepts (atomEventually b) w ↔ ∃ m, w m = b := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    have h0 : path 0 = false := by
      simp only [atomEventually, decide_eq_true_eq] at hstart
      exact hstart
    obtain ⟨visit, _, ha⟩ := hacc 0
    have htrue : path visit = true := by
      simp only [atomEventually, decide_eq_true_eq] at ha
      exact ha
    classical
    have hex : ∃ k, path k = true := ⟨visit, htrue⟩
    let k := Nat.find hex
    have hk : path k = true := Nat.find_spec hex
    have hpos : 0 < k := by
      by_contra hle
      have : k = 0 := by omega
      rw [this, h0] at hk
      exact Bool.false_ne_true hk
    have hprev : path (k - 1) = false := by
      have hmin := Nat.find_min hex (show k - 1 < k by omega)
      exact Bool.eq_false_iff.mpr hmin
    have hstepk := hstep (k - 1)
    simp only [atomEventually, hprev, Bool.false_eq_true, if_false, decide_eq_true_eq] at hstepk
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hk1, hk] at hstepk
    exact ⟨k - 1, (beq_eq_true_iff _ _).mp hstepk.symm⟩
  · intro ⟨m, hm⟩
    classical
    have hex : ∃ k, w k = b := ⟨m, hm⟩
    let k := Nat.find hex
    have hk : w k = b := Nat.find_spec hex
    have hbefore : ∀ i, i < k → w i ≠ b := by
      intro i hi heq
      exact Nat.find_min hex hi heq
    have hfalse : ∀ i, i ≤ k → eventuallyPath b w i = false := by
      intro i hi
      induction i with
      | zero => exact eventuallyPath_zero b w
      | succ i ih =>
        rw [eventuallyPath_succ, ih (by omega)]
        have hwne : w i ≠ b := hbefore i (by omega)
        have hbeq : (w i == b) = false := by
          cases hb : w i <;> cases b <;> simp_all
        simp [hbeq]
    have henter : eventuallyPath b w (k + 1) = true := by
      rw [eventuallyPath_succ, hfalse k le_rfl, hk]
      simp
    let path := eventuallyPath b w
    refine ⟨path, ?_, ?_, ?_⟩
    · simp [atomEventually, path, eventuallyPath_zero]
    · intro n
      by_cases hp : path n = true
      · have hnext : path (n + 1) = true := by
          simpa [path, Nat.add_zero] using eventuallyPath_stay b w hp 1
        simp [atomEventually, path, hp, hnext]
      · have hf : path n = false := Bool.eq_false_iff.mpr hp
        have hnext : path (n + 1) = (w n == b) := by
          simp [path, eventuallyPath_succ, hf]
        simp [atomEventually, path, hf, hnext]
    · intro lowerBound
      refine ⟨k + 1 + lowerBound, by omega, ?_⟩
      have hstay : path (k + 1 + lowerBound) = true := eventuallyPath_stay b w henter lowerBound
      simp [atomEventually, hstay]

theorem atomAlways_iff (b : Bool) (w : Nat → Bool) :
    Accepts (atomAlways b) w ↔ ∀ m, w m = b := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    have h0 : path 0 = true := by
      simp only [atomAlways, decide_eq_true_eq] at hstart
      exact hstart
    have stay : ∀ n, path n = true := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih =>
        by_contra hnot
        have hf : path (n + 1) = false := Bool.eq_false_iff.mpr hnot
        have stuck : ∀ j, path (n + 1 + j) = false := by
          intro j
          induction j with
          | zero => exact hf
          | succ j ihj =>
            have h := hstep (n + 1 + j)
            simp only [atomAlways, ihj, if_true, decide_eq_true_eq] at h
            exact h
        obtain ⟨visit, hv, ha⟩ := hacc (n + 1)
        have htrue : path visit = true := by
          simp only [atomAlways, decide_eq_true_eq] at ha
          exact ha
        have hfalse : path visit = false := by
          have hsplit : visit = n + 1 + (visit - (n + 1)) := by omega
          rw [hsplit]
          exact stuck (visit - (n + 1))
        exact Bool.false_ne_true (hfalse.symm.trans htrue)
    intro m
    have h := hstep m
    simp only [atomAlways, stay m, stay (m + 1)] at h
    have hne : (true : Bool) ≠ false := by decide
    rw [if_neg hne, decide_eq_true_eq] at h
    exact (beq_eq_true_iff (w m) b).mp h.symm
  · intro hall
    refine ⟨fun _ => true, ?_, ?_, ?_⟩
    · simp [atomAlways]
    · intro n
      simp [atomAlways, hall n]
    · intro lowerBound
      exact ⟨lowerBound, le_rfl, by simp [atomAlways]⟩

theorem atomFinitelyOften_iff (b : Bool) (w : Nat → Bool) :
    Accepts (atomFinitelyOften b) w ↔ ∃ n, ∀ m, n ≤ m → w m ≠ b := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    have h0 : path 0 = false := by
      simp only [atomFinitelyOften, decide_eq_true_eq] at hstart
      exact hstart
    obtain ⟨visit, _, ha⟩ := hacc 1
    have htrue : path visit = true := by
      simp only [atomFinitelyOften, decide_eq_true_eq] at ha
      exact ha
    classical
    have hex : ∃ k, path k = true := ⟨visit, htrue⟩
    let k := Nat.find hex
    have hk : path k = true := Nat.find_spec hex
    have hpos : 0 < k := by
      by_contra hle
      have : k = 0 := by omega
      rw [this, h0] at hk
      exact Bool.false_ne_true hk
    have hprev : path (k - 1) = false :=
      Bool.eq_false_iff.mpr (Nat.find_min hex (by omega))
    have stay : ∀ j, k ≤ j → path j = true := by
      intro j hj
      induction hdist : j - k generalizing j with
      | zero =>
        have : j = k := by omega
        simpa [this] using hk
      | succ d ih =>
        have hpred : path (j - 1) = true := ih (j - 1) (by omega) (by omega)
        have h := hstep (j - 1)
        simp [atomFinitelyOften, hpred] at h
        have hj1 : (j - 1) + 1 = j := by omega
        rw [hj1] at h
        exact h.1
    refine ⟨k - 1, ?_⟩
    intro m hm
    by_cases hmEq : m = k - 1
    · subst hmEq
      have h := hstep (k - 1)
      simp [atomFinitelyOften, hprev] at h
      have hk1 : (k - 1) + 1 = k := by omega
      rw [hk1] at h
      rcases h with hfalse | ⟨_, hne⟩
      · exact absurd (hfalse.symm.trans hk) Bool.false_ne_true
      · exact hne
    · have hge : k ≤ m := by omega
      have hpm : path m = true := stay m hge
      have hpm1 : path (m + 1) = true := stay (m + 1) (by omega)
      have h := hstep m
      simp [atomFinitelyOften, hpm, hpm1] at h
      exact h
  · intro ⟨N, hN⟩
    let path n := decide (N < n)
    refine ⟨path, ?_, ?_, ?_⟩
    · simp [atomFinitelyOften, path]
    · intro n
      rcases (show n < N ∨ n = N ∨ N < n by omega) with hlt | heq | hgt
      · have hp : path n = false := by
          have : ¬ N < n := by omega
          simp [path, this]
        have hp1 : path (n + 1) = false := by
          have : ¬ N < n + 1 := by omega
          simp [path, this]
        simp [atomFinitelyOften, hp, hp1]
      · have hp : path n = false := by simp [path, heq]
        have hp1 : path (n + 1) = true := by
          have : N < n + 1 := by omega
          simp [path, this]
        have hw : w n ≠ b := hN n (by omega)
        simp [atomFinitelyOften, hp, hp1, hw]
      · have hp : path n = true := by simp [path, hgt]
        have hp1 : path (n + 1) = true := by
          have : N < n + 1 := by omega
          simp [path, this]
        have hw : w n ≠ b := hN n (by omega)
        simp [atomFinitelyOften, hp, hp1, hw]
    · intro lowerBound
      refine ⟨N + 1 + lowerBound, by omega, ?_⟩
      have : N < N + 1 + lowerBound := by omega
      simp [atomFinitelyOften, path, this]

/-! ## Compilation -/

@[reducible]
def PosState : Pos → Type
  | .atom _ => Bool
  | .and φ ψ => PosState φ × PosState ψ × Fin 2
  | .or φ ψ => PosState φ ⊕ PosState ψ

@[instance_reducible]
def enumerablePos : (φ : Pos) → Enumerable (PosState φ)
  | .atom _ => inferInstance
  | .and φ ψ =>
    letI := enumerablePos φ
    letI := enumerablePos ψ
    inferInstance
  | .or φ ψ =>
    letI := enumerablePos φ
    letI := enumerablePos ψ
    inferInstance

@[instance_reducible]
def fintypePos : (φ : Pos) → Fintype (PosState φ)
  | .atom _ => inferInstance
  | .and φ ψ =>
    letI := fintypePos φ
    letI := fintypePos ψ
    inferInstance
  | .or φ ψ =>
    letI := fintypePos φ
    letI := fintypePos ψ
    inferInstance

@[instance_reducible]
def decidableEqPos : (φ : Pos) → DecidableEq (PosState φ)
  | .atom _ => inferInstance
  | .and φ ψ =>
    letI := decidableEqPos φ
    letI := decidableEqPos ψ
    inferInstance
  | .or φ ψ =>
    letI := decidableEqPos φ
    letI := decidableEqPos ψ
    inferInstance

def compileAtom : Atom → NBA Bool Bool
  | .infinitelyOften b => atomInfOften b
  | .eventually b => atomEventually b
  | .always b => atomAlways b
  | .finitelyOften b => atomFinitelyOften b

theorem compileAtom_iff (a : Atom) (w : Nat → Bool) :
    Accepts (compileAtom a) w ↔ satAtom a w := by
  cases a with
  | infinitelyOften b => simpa [compileAtom, satAtom] using atomInfOften_iff b w
  | eventually b => simpa [compileAtom, satAtom] using atomEventually_iff b w
  | always b => simpa [compileAtom, satAtom] using atomAlways_iff b w
  | finitelyOften b => simpa [compileAtom, satAtom] using atomFinitelyOften_iff b w

def compile : (φ : Pos) → NBA Bool (PosState φ)
  | .atom a => compileAtom a
  | .and φ ψ => inter (compile φ) (compile ψ)
  | .or φ ψ => union (compile φ) (compile ψ)

theorem compile_iff (φ : Pos) (w : Nat → Bool) :
    Accepts (compile φ) w ↔ satPos φ w := by
  induction φ with
  | atom a =>
    rw [compile, satPos]
    exact compileAtom_iff a w
  | and φ ψ ihφ ihψ =>
    have h := (accepts_inter (compile φ) (compile ψ) w).trans (and_congr ihφ ihψ)
    simpa [compile, satPos] using h
  | or φ ψ ihφ ihψ =>
    have h := (accepts_union (compile φ) (compile ψ) w).trans (or_congr ihφ ihψ)
    simpa [compile, satPos] using h

@[instance_reducible]
def enumBool : Enumerable Bool := inferInstance

def decidePos (φ : Pos) : Bool :=
  @decideNonempty Bool (PosState φ) (compile φ)
    enumBool (enumerablePos φ) (fintypePos φ) (decidableEqPos φ)

theorem decidePos_iff (φ : Pos) :
    decidePos φ = true ↔ ∃ w, satPos φ w := by
  rw [decidePos,
    @decideNonempty_iff Bool (PosState φ) (compile φ)
      enumBool (enumerablePos φ) (fintypePos φ) (decidableEqPos φ)]
  constructor
  · intro ⟨w, hw⟩
    exact ⟨w, (compile_iff φ w).mp hw⟩
  · intro ⟨w, hw⟩
    exact ⟨w, (compile_iff φ w).mpr hw⟩

def decideSentence : Sentence → Option Bool
  | .exists_ φ => some (decidePos (toPos true φ))
  | .forall_ _ => none

/-- Where the procedure returns a bit, that bit is truth of the existential
sentence in the standard model of ω-words. -/
theorem decideSentence_iff (φ : Matrix) {b : Bool}
    (h : decideSentence (.exists_ φ) = some b) :
    b = true ↔ ∃ w, satMatrix φ w := by
  simp [decideSentence] at h
  rw [← h]
  constructor
  · intro ht
    obtain ⟨w, hw⟩ := (decidePos_iff (toPos true φ)).mp ht
    exact ⟨w, (toPos_true_iff φ w).mp hw⟩
  · intro ⟨w, hw⟩
    exact (decidePos_iff (toPos true φ)).mpr ⟨w, (toPos_true_iff φ w).mpr hw⟩

/-- Presentation of the fragment. `decide` returns `none` on a universal
sentence. -/
structure Bubble where
  name : String
  decide : Sentence → Option Bool

def exS1SBubble : Bubble where
  name := "existential one-predicate S1S"
  decide := decideSentence

theorem exS1SBubble_decides (φ : Matrix) {b : Bool}
    (h : exS1SBubble.decide (.exists_ φ) = some b) :
    b = true ↔ ∃ w, satMatrix φ w :=
  decideSentence_iff φ h

theorem control_exists_infOften :
    decideSentence (.exists_ (.atom (.infinitelyOften true))) = some true := by
  have hw : ∃ w, satMatrix (.atom (.infinitelyOften true)) w := by
    refine ⟨fun _ => true, ?_⟩
    intro n
    exact ⟨n, le_rfl, rfl⟩
  cases h : decideSentence (.exists_ (.atom (.infinitelyOften true))) with
  | none => simp [decideSentence] at h
  | some b =>
    cases b
    · exfalso
      exact Bool.false_ne_true ((decideSentence_iff _ h).mpr hw)
    · rfl

theorem control_always_conflict :
    decideSentence (.exists_ (.and (.atom (.always true)) (.atom (.always false)))) = some false := by
  have hnone : ¬ ∃ w,
      satMatrix (.and (.atom (.always true)) (.atom (.always false))) w := by
    intro ⟨w, hw⟩
    simp [satMatrix, satAtom] at hw
    exact Bool.false_ne_true ((hw.2 0).symm.trans (hw.1 0))
  cases h : decideSentence (.exists_ (.and (.atom (.always true)) (.atom (.always false)))) with
  | none => simp [decideSentence] at h
  | some b =>
    cases b
    · rfl
    · exfalso
      exact hnone ((decideSentence_iff _ h).mp rfl)

theorem control_neg_always :
    decideSentence (.exists_ (.not (.atom (.always true)))) = some true := by
  have hw : ∃ w, satMatrix (.not (.atom (.always true))) w := by
    refine ⟨fun _ => false, ?_⟩
    intro hall
    exact Bool.false_ne_true (hall 0)
  cases h : decideSentence (.exists_ (.not (.atom (.always true)))) with
  | none => simp [decideSentence] at h
  | some b =>
    cases b
    · exfalso
      exact Bool.false_ne_true ((decideSentence_iff _ h).mpr hw)
    · rfl

theorem control_universal_abstain (φ : Matrix) :
    decideSentence (.forall_ φ) = none := by
  simp [decideSentence]

#print axioms decideSentence_iff
#print axioms exS1SBubble_decides
#print axioms compile_iff
#print axioms negAtom_iff

/-! ## Monadic second-order logic of one successor

Individual variables and monadic predicates, with equality, successor, and
membership. A word is a valid assignment when each free individual is true at
exactly one position. J. Richard Büchi, *On a Decision Method in Restricted
Second Order Arithmetic* (1962).
-/

inductive MSO : Nat → Nat → Type where
  | bot {f s : Nat} : MSO f s
  | eq {f s : Nat} : Fin f → Fin f → MSO f s
  | succ {f s : Nat} : Fin f → Fin f → MSO f s
  | mem {f s : Nat} : Fin f → Fin s → MSO f s
  | and {f s : Nat} : MSO f s → MSO f s → MSO f s
  | or {f s : Nat} : MSO f s → MSO f s → MSO f s
  | not {f s : Nat} : MSO f s → MSO f s
  | exInd {f s : Nat} : MSO (f + 1) s → MSO f s
  | exSet {f s : Nat} : MSO f (s + 1) → MSO f s

abbrev Letter (f s : Nat) := (Fin f → Bool) × (Fin s → Bool)

def packInd {f s : Nat} (p : Letter f s × Bool) : Letter (f + 1) s :=
  ⟨Fin.cases p.2 p.1.1, p.1.2⟩

def packSet {f s : Nat} (p : Letter f s × Bool) : Letter f (s + 1) :=
  ⟨p.1.1, Fin.cases p.2 p.1.2⟩

def envInd {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) : Nat → Letter (f + 1) s :=
  fun n => packInd (w n, b n)

def envSet {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) : Nat → Letter f (s + 1) :=
  fun n => packSet (w n, b n)

def bit {f s : Nat} (w : Nat → Letter f s) (i : Fin f) : Nat → Bool :=
  fun n => (w n).1 i

def setBit {f s : Nat} (w : Nat → Letter f s) (X : Fin s) : Nat → Bool :=
  fun n => (w n).2 X

def exactlyOne (b : Nat → Bool) : Prop :=
  ∃ n, b n = true ∧ ∀ m, b m = true → m = n

def valid {f s : Nat} (w : Nat → Letter f s) : Prop :=
  ∀ i, exactlyOne (bit w i)

def sat {f s : Nat} : MSO f s → (Nat → Letter f s) → Prop
  | .bot, _ => False
  | .eq i j, w => ∃ n, bit w i n = true ∧ bit w j n = true
  | .succ i j, w => ∃ n, bit w i n = true ∧ bit w j (n + 1) = true
  | .mem i X, w => ∃ n, bit w i n = true ∧ setBit w X n = true
  | .and φ ψ, w => sat φ w ∧ sat ψ w
  | .or φ ψ, w => sat φ w ∨ sat ψ w
  | .not φ, w => ¬ sat φ w
  | .exInd φ, w => ∃ b, exactlyOne b ∧ sat φ (envInd w b)
  | .exSet φ, w => ∃ b, sat φ (envSet w b)

theorem bit_envInd_zero {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) :
    bit (envInd w b) 0 = b := by
  funext n
  simp [bit, envInd, packInd]

theorem bit_envInd_succ {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) (i : Fin f) :
    bit (envInd w b) i.succ = bit w i := by
  funext n
  simp [bit, envInd, packInd]

theorem bit_envSet {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) (i : Fin f) :
    bit (envSet w b) i = bit w i := by
  funext n
  simp [bit, envSet, packSet]

theorem setBit_envInd {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) (X : Fin s) :
    setBit (envInd w b) X = setBit w X := by
  funext n
  simp [setBit, envInd, packInd]

theorem setBit_envSet_zero {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) :
    setBit (envSet w b) 0 = b := by
  funext n
  simp [setBit, envSet, packSet]

theorem setBit_envSet_succ {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) (X : Fin s) :
    setBit (envSet w b) X.succ = setBit w X := by
  funext n
  simp [setBit, envSet, packSet]

theorem valid_envInd {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) :
    valid (envInd w b) ↔ exactlyOne b ∧ valid w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [bit_envInd_zero] using h 0
    · intro i
      simpa [bit_envInd_succ] using h i.succ
  · intro ⟨hb, hw⟩ i
    induction i using Fin.cases with
    | zero => simpa [bit_envInd_zero] using hb
    | succ i => simpa [bit_envInd_succ] using hw i

theorem valid_envSet {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) :
    valid (envSet w b) ↔ valid w := by
  constructor
  · intro h i
    simpa [bit_envSet] using h i
  · intro h i
    simpa [bit_envSet] using h i

theorem sat_congr {f s : Nat} {φ : MSO f s} {w w' : Nat → Letter f s}
    (h : ∀ n, w n = w' n) : sat φ w ↔ sat φ w' := by
  induction φ with
  | bot => simp [sat]
  | eq i j =>
    constructor <;> intro ⟨n, hi, hj⟩ <;> exact ⟨n, by simpa [bit, h] using hi, by simpa [bit, h] using hj⟩
  | succ i j =>
    constructor <;> intro ⟨n, hi, hj⟩ <;>
      exact ⟨n, by simpa [bit, h] using hi, by simpa [bit, h] using hj⟩
  | mem i X =>
    constructor <;> intro ⟨n, hi, hX⟩ <;>
      exact ⟨n, by simpa [bit, h] using hi, by simpa [setBit, h] using hX⟩
  | and φ ψ ihφ ihψ =>
    have ihφ' := ihφ h
    have ihψ' := ihψ h
    simp [sat, ihφ', ihψ']
  | or φ ψ ihφ ihψ =>
    have ihφ' := ihφ h
    have ihψ' := ihψ h
    simp [sat, ihφ', ihψ']
  | not φ ih =>
    simp [sat, ih h]
  | exInd φ ih =>
    constructor
    · intro ⟨b, hb, hs⟩
      have henv : ∀ n, envInd w b n = envInd w' b n := by
        intro n
        simp [envInd, packInd, h]
      exact ⟨b, hb, (ih henv).mp hs⟩
    · intro ⟨b, hb, hs⟩
      have henv : ∀ n, envInd w' b n = envInd w b n := by
        intro n
        simp [envInd, packInd, h]
      exact ⟨b, hb, (ih henv).mp hs⟩
  | exSet φ ih =>
    constructor
    · intro ⟨b, hs⟩
      have henv : ∀ n, envSet w b n = envSet w' b n := by
        intro n
        simp [envSet, packSet, h]
      exact ⟨b, (ih henv).mp hs⟩
    · intro ⟨b, hs⟩
      have henv : ∀ n, envSet w' b n = envSet w b n := by
        intro n
        simp [envSet, packSet, h]
      exact ⟨b, (ih henv).mp hs⟩

def relabel {α β σ : Type} (A : NBA β σ) (e : α → β) : NBA α σ where
  step s a t := A.step s (e a) t
  start := A.start
  accept := A.accept

theorem accepts_relabel {α β σ : Type} (A : NBA β σ) (e : α → β) (w : Nat → α) :
    Accepts (relabel A e) w ↔ Accepts A (fun n => e (w n)) := by
  constructor
  · intro ⟨path, h0, hs, ha⟩
    exact ⟨path, by simpa [relabel] using h0, fun n => by simpa [relabel] using hs n, ha⟩
  · intro ⟨path, h0, hs, ha⟩
    exact ⟨path, by simpa [relabel] using h0, fun n => by simpa [relabel] using hs n, ha⟩

abbrev Track (f : Nat) := (Fin f → Bool) × Bool

def trackStart (f : Nat) : Track f := (fun _ => false, true)

def seenOr {f : Nat} (seen bits : Fin f → Bool) : Fin f → Bool :=
  fun i => seen i || bits i

def seenClash {f : Nat} (seen bits : Fin f → Bool) : Bool :=
  (List.finRange f).any (fun i => seen i && bits i)

def seenAll {f : Nat} (seen : Fin f → Bool) : Bool :=
  (List.finRange f).all (fun i => seen i)

def trackStep {f : Nat} (t : Track f) (bits : Fin f → Bool) : Track f :=
  if t.2 = false then t
  else if seenClash t.1 bits = true then (t.1, false)
  else (seenOr t.1 bits, true)

def trackRun {f s : Nat} (w : Nat → Letter f s) : Nat → Track f
  | 0 => trackStart f
  | n + 1 => trackStep (trackRun w n) (w n).1

def guard (f s : Nat) : NBA (Letter f s) (Track f) where
  step t a t' := decide (t' = trackStep t a.1)
  start t := decide (t = trackStart f)
  accept t := t.2 && seenAll t.1

theorem seenAll_iff {f : Nat} (seen : Fin f → Bool) :
    seenAll seen = true ↔ ∀ i, seen i = true := by
  simp [seenAll, List.mem_finRange]

theorem seenClash_iff {f : Nat} (seen bits : Fin f → Bool) :
    seenClash seen bits = true ↔ ∃ i, seen i = true ∧ bits i = true := by
  simp [seenClash, List.mem_finRange, Bool.and_eq_true]

theorem step_alive_record {f : Nat} (t : Track f) (bits : Fin f → Bool)
    (ha : (trackStep t bits).2 = true) :
    t.2 = true ∧ seenClash t.1 bits = false ∧
      trackStep t bits = (seenOr t.1 bits, true) := by
  have hnotdead : ¬ t.2 = false := by
    intro hd
    have hdead : (trackStep t bits).2 = false := by
      simp [trackStep, if_pos hd]
      exact hd
    exact Bool.false_ne_true (hdead.symm.trans ha)
  have ht : t.2 = true := by
    cases hb : t.2
    · exact (hnotdead hb).elim
    · rfl
  have hnotc : ¬ seenClash t.1 bits = true := by
    intro hc
    have hdead : (trackStep t bits).2 = false := by
      simp [trackStep, if_neg hnotdead, if_pos hc]
    exact Bool.false_ne_true (hdead.symm.trans ha)
  have hcf : seenClash t.1 bits = false := by
    cases hb : seenClash t.1 bits
    · rfl
    · exact (hnotc hb).elim
  refine ⟨ht, hcf, ?_⟩
  simp [trackStep, if_neg hnotdead, if_neg (by
    intro ht
    exact hnotc ht)]

theorem guard_path {f s : Nat} (w : Nat → Letter f s) (path : Nat → Track f)
    (h0 : (guard f s).start (path 0) = true)
    (hs : ∀ n, (guard f s).step (path n) (w n) (path (n + 1)) = true) :
    ∀ n, path n = trackRun w n := by
  intro n
  induction n with
  | zero =>
    simpa [guard, trackRun] using h0
  | succ n ih =>
    have hstep := hs n
    simp [guard] at hstep
    rw [ih] at hstep
    simpa [trackRun] using hstep

theorem dead_stays {f s : Nat} (w : Nat → Letter f s) {n m : Nat}
    (hn : (trackRun w n).2 = false) (hm : n ≤ m) : (trackRun w m).2 = false := by
  induction m with
  | zero =>
    have hz : n = 0 := Nat.eq_zero_of_le_zero hm
    simpa [hz] using hn
  | succ m ih =>
    by_cases hnm : n = m + 1
    · simpa [hnm] using hn
    · have hle : n ≤ m := by omega
      have hdead := ih hle
      have hnot : (trackRun w m).2 = false := hdead
      simp [trackRun, trackStep, if_pos hnot]
      exact hnot

theorem shape_of_alive {f s : Nat} (w : Nat → Letter f s)
    (hall : ∀ n, (trackRun w n).2 = true) :
    ∀ n i, (trackRun w n).1 i = true ↔ ∃ k, k < n ∧ (w k).1 i = true := by
  intro n
  induction n with
  | zero =>
    intro i
    simp [trackRun, trackStart]
  | succ n ih =>
    intro i
    have hrec := step_alive_record (trackRun w n) (w n).1
      (by simpa [trackRun] using hall (n + 1))
    have hfun := hrec.2.2
    have hseen : (trackRun w (n + 1)).1 i = ((trackRun w n).1 i || (w n).1 i) := by
      have hidx : trackRun w (n + 1) = trackStep (trackRun w n) (w n).1 := rfl
      simp [hidx, hfun, seenOr]
    rw [hseen, Bool.or_eq_true]
    constructor
    · intro h
      rcases h with hs | hb
      · obtain ⟨k, hk, hkbit⟩ := (ih i).mp hs
        exact ⟨k, Nat.lt_succ_of_lt hk, hkbit⟩
      · exact ⟨n, Nat.lt_succ_self n, hb⟩
    · intro ⟨k, hk, hkbit⟩
      have hk' : k ≤ n := Nat.lt_succ_iff.mp hk
      rcases Nat.eq_or_lt_of_le hk' with heq | hlt
      · exact Or.inr (heq ▸ hkbit)
      · exact Or.inl ((ih i).mpr ⟨k, hlt, hkbit⟩)

theorem always_alive_of_accepts {f s : Nat} (w : Nat → Letter f s)
    (path : Nat → Track f)
    (h0 : (guard f s).start (path 0) = true)
    (hs : ∀ n, (guard f s).step (path n) (w n) (path (n + 1)) = true)
    (hacc : RunAccepts (guard f s).accept path) :
    ∀ n, (trackRun w n).2 = true := by
  have hrun := guard_path w path h0 hs
  intro n
  by_contra hd
  have hfalse : (trackRun w n).2 = false := by
    cases hb : (trackRun w n).2
    · rfl
    · exact (hd hb).elim
  obtain ⟨visit, hv, ha⟩ := hacc n
  have hdead := dead_stays w hfalse hv
  rw [hrun visit, guard] at ha
  exact Bool.false_ne_true (hdead.symm.trans (Bool.and_eq_true_iff.mp ha).1)

theorem at_most_one {f s : Nat} (w : Nat → Letter f s)
    (hall : ∀ n, (trackRun w n).2 = true) (i : Fin f)
    {a b : Nat} (ha : (w a).1 i = true) (hb : (w b).1 i = true) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hseen : (trackRun w b).1 i = true :=
      (shape_of_alive w hall b i).mpr ⟨a, hlt, ha⟩
    have hcl : seenClash (trackRun w b).1 (w b).1 = true :=
      (seenClash_iff _ _).mpr ⟨i, hseen, hb⟩
    have hrec := step_alive_record (trackRun w b) (w b).1
      (by simpa [trackRun] using hall (b + 1))
    exact False.elim (Bool.false_ne_true (hrec.2.1.symm.trans hcl))
  · exact heq
  · have hseen : (trackRun w a).1 i = true :=
      (shape_of_alive w hall a i).mpr ⟨b, hgt, hb⟩
    have hcl : seenClash (trackRun w a).1 (w a).1 = true :=
      (seenClash_iff _ _).mpr ⟨i, hseen, ha⟩
    have hrec := step_alive_record (trackRun w a) (w a).1
      (by simpa [trackRun] using hall (a + 1))
    exact False.elim (Bool.false_ne_true (hrec.2.1.symm.trans hcl))

noncomputable def thePos {b : Nat → Bool} (h : exactlyOne b) : Nat :=
  Classical.choose h

theorem thePos_spec {b : Nat → Bool} (h : exactlyOne b) :
    b (thePos h) = true ∧ ∀ m, b m = true → m = thePos h :=
  Classical.choose_spec h

noncomputable def lastPos {f s : Nat} (w : Nat → Letter f s) (hv : valid w) : Nat :=
  (List.finRange f).foldr (fun i m => max m (thePos (hv i))) 0

theorem foldr_max_ge {f : Nat} (l : List (Fin f)) (i : Fin f) (hi : i ∈ l)
    (p : Fin f → Nat) :
    p i ≤ l.foldr (fun j m => max m (p j)) 0 := by
  induction l with
  | nil => cases hi
  | cons j js ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hi with rfl | hrest
    · exact le_max_right _ _
    · exact le_trans (ih hrest) (le_max_left _ _)

theorem pos_le_last {f s : Nat} (w : Nat → Letter f s) (hv : valid w) (i : Fin f) :
    thePos (hv i) ≤ lastPos w hv :=
  foldr_max_ge (List.finRange f) i (List.mem_finRange i) (fun j => thePos (hv j))

theorem run_shape_valid {f s : Nat} (w : Nat → Letter f s) (hv : valid w) :
    ∀ n, (trackRun w n).2 = true ∧
      ∀ i, (trackRun w n).1 i = true ↔ ∃ k, k < n ∧ (w k).1 i = true := by
  intro n
  induction n with
  | zero =>
    constructor
    · simp [trackRun, trackStart]
    · intro i
      simp [trackRun, trackStart]
  | succ n ih =>
    have ht : (trackRun w n).2 = true := ih.1
    have hnoclash : seenClash (trackRun w n).1 (w n).1 = false := by
      apply Bool.eq_false_iff.mpr
      intro hcl
      obtain ⟨i, hseen, hbit⟩ := (seenClash_iff _ _).mp hcl
      obtain ⟨k, hk, hkbit⟩ := (ih.2 i).mp hseen
      have hkpos := (thePos_spec (hv i)).2 k hkbit
      have hnpos := (thePos_spec (hv i)).2 n hbit
      omega
    have hnotdead : ¬ (trackRun w n).2 = false := by
      intro h
      exact Bool.false_ne_true (h.symm.trans ht)
    have hnotc : ¬ seenClash (trackRun w n).1 (w n).1 = true := by
      intro h
      exact Bool.false_ne_true (hnoclash.symm.trans h)
    have hstep : trackRun w (n + 1) = (seenOr (trackRun w n).1 (w n).1, true) := by
      simp [trackRun, trackStep, if_neg hnotdead, if_neg hnotc]
    constructor
    · rw [hstep]
    · intro i
      have hbit : (trackRun w (n + 1)).1 i = ((trackRun w n).1 i || (w n).1 i) := by
        simp [hstep, seenOr]
      rw [hbit, Bool.or_eq_true]
      constructor
      · intro h
        rcases h with hs | hb
        · obtain ⟨k, hk, hkbit⟩ := (ih.2 i).mp hs
          exact ⟨k, Nat.lt_succ_of_lt hk, hkbit⟩
        · exact ⟨n, Nat.lt_succ_self n, hb⟩
      · intro ⟨k, hk, hkbit⟩
        have hk' : k ≤ n := Nat.lt_succ_iff.mp hk
        rcases Nat.eq_or_lt_of_le hk' with heq | hlt
        · exact Or.inr (heq ▸ hkbit)
        · exact Or.inl ((ih.2 i).mpr ⟨k, hlt, hkbit⟩)

theorem all_seen_after {f s : Nat} (w : Nat → Letter f s) (hv : valid w)
    {n : Nat} (hn : lastPos w hv < n) : seenAll (trackRun w n).1 = true := by
  rw [seenAll_iff]
  intro i
  have hk : thePos (hv i) < n := Nat.lt_of_le_of_lt (pos_le_last w hv i) hn
  exact ((run_shape_valid w hv n).2 i).mpr ⟨thePos (hv i), hk, (thePos_spec (hv i)).1⟩

theorem guard_accepts_of_valid {f s : Nat} (w : Nat → Letter f s) (hv : valid w) :
    Accepts (guard f s) w := by
  refine ⟨trackRun w, ?_, ?_, ?_⟩
  · simp [guard, trackRun, trackStart]
  · intro n
    simp [guard, trackRun]
  · intro lower
    refine ⟨max lower (lastPos w hv + 1), le_max_left _ _, ?_⟩
    have hn : lastPos w hv < max lower (lastPos w hv + 1) := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    simp [guard, Bool.and_eq_true]
    exact ⟨(run_shape_valid w hv _).1, all_seen_after w hv hn⟩

theorem guard_iff {f s : Nat} (w : Nat → Letter f s) :
    Accepts (guard f s) w ↔ valid w := by
  constructor
  · intro ⟨path, h0, hs, hacc⟩
    have hall := always_alive_of_accepts w path h0 hs hacc
    have hrun := guard_path w path h0 hs
    obtain ⟨N, _, hN⟩ := hacc 0
    rw [hrun N, guard, Bool.and_eq_true] at hN
    have hseen := (seenAll_iff _).mp hN.2
    intro i
    obtain ⟨k, _, hkbit⟩ := (shape_of_alive w hall N i).mp (hseen i)
    refine ⟨k, hkbit, ?_⟩
    intro m hm
    exact at_most_one w hall i hm hkbit
  · exact guard_accepts_of_valid w

/-! ### Deterministic runs -/

def detRun {α σ : Type} (next : σ → α → σ) (s0 : σ) (w : Nat → α) : Nat → σ
  | 0 => s0
  | n + 1 => next (detRun next s0 w n) (w n)

theorem det_path {α σ : Type} (A : NBA α σ) (next : σ → α → σ) (s0 : σ)
    (hstep : ∀ s a t, A.step s a t = true ↔ t = next s a)
    (hstart : ∀ s, A.start s = true ↔ s = s0)
    {path : Nat → σ} {w : Nat → α}
    (h0 : A.start (path 0) = true)
    (hs : ∀ n, A.step (path n) (w n) (path (n + 1)) = true) :
    ∀ n, path n = detRun next s0 w n := by
  intro n
  induction n with
  | zero =>
    simpa [detRun] using (hstart (path 0)).mp h0
  | succ n ih =>
    have hs' := (hstep (path n) (w n) (path (n + 1))).mp (hs n)
    simpa [detRun, ih] using hs'

theorem detRun_accepts {α σ : Type} (A : NBA α σ) (next : σ → α → σ) (s0 : σ)
    (hstep : ∀ s a t, A.step s a t = true ↔ t = next s a)
    (hstart : ∀ s, A.start s = true ↔ s = s0) (w : Nat → α) :
    Accepts A w ↔ RunAccepts A.accept (detRun next s0 w) := by
  constructor
  · intro ⟨path, h0, hs, hacc⟩
    have hpath := det_path A next s0 hstep hstart h0 hs
    intro lower
    obtain ⟨v, hv, ha⟩ := hacc lower
    exact ⟨v, hv, by simpa [hpath] using ha⟩
  · intro hacc
    refine ⟨detRun next s0 w, (hstart _).mpr rfl, ?_, hacc⟩
    intro n
    exact (hstep _ _ _).mpr rfl

theorem letter_bit_pos {f s : Nat} (w : Nat → Letter f s) (hv : valid w)
    (i : Fin f) (n : Nat) : (w n).1 i = true ↔ n = thePos (hv i) := by
  constructor
  · intro h
    exact (thePos_spec (hv i)).2 n (by simpa [bit] using h)
  · intro h
    simpa [bit, h] using (thePos_spec (hv i)).1

theorem letter_bit_eq {f s : Nat} (w : Nat → Letter f s) (hv : valid w)
    (i : Fin f) (n : Nat) :
    (w n).1 i = decide (n = thePos (hv i)) := by
  cases hbit : (w n).1 i <;> cases hdec : decide (n = thePos (hv i))
  · rfl
  · exact hbit.symm.trans ((letter_bit_pos w hv i n).mpr (of_decide_eq_true hdec))
  · exact False.elim ((of_decide_eq_false hdec) ((letter_bit_pos w hv i n).mp hbit))
  · rfl

/-! ### Equality, successor, and membership checkers -/

inductive Flag where
  | wait
  | ok
  | bad
  deriving DecidableEq

instance : Fintype Flag where
  elems := {.wait, .ok, .bad}
  complete x := by cases x <;> simp

@[instance_reducible]
def enumerableFlag : Enumerable Flag where
  elems := [.wait, .ok, .bad]
  mem_elems x := by cases x <;> simp

@[simp] theorem Flag.wait_eq_ok : (Flag.wait = Flag.ok) ↔ False := by decide
@[simp] theorem Flag.wait_eq_bad : (Flag.wait = Flag.bad) ↔ False := by decide
@[simp] theorem Flag.ok_eq_wait : (Flag.ok = Flag.wait) ↔ False := by decide
@[simp] theorem Flag.ok_eq_bad : (Flag.ok = Flag.bad) ↔ False := by decide
@[simp] theorem Flag.bad_eq_wait : (Flag.bad = Flag.wait) ↔ False := by decide
@[simp] theorem Flag.bad_eq_ok : (Flag.bad = Flag.ok) ↔ False := by decide

inductive SuccSt where
  | wait
  | need
  | ok
  | bad
  deriving DecidableEq

instance : Fintype SuccSt where
  elems := {.wait, .need, .ok, .bad}
  complete x := by cases x <;> simp

@[instance_reducible]
def enumerableSuccSt : Enumerable SuccSt where
  elems := [.wait, .need, .ok, .bad]
  mem_elems x := by cases x <;> simp

@[simp] theorem SuccSt.wait_eq_need : (SuccSt.wait = SuccSt.need) ↔ False := by decide
@[simp] theorem SuccSt.wait_eq_ok : (SuccSt.wait = SuccSt.ok) ↔ False := by decide
@[simp] theorem SuccSt.wait_eq_bad : (SuccSt.wait = SuccSt.bad) ↔ False := by decide
@[simp] theorem SuccSt.need_eq_wait : (SuccSt.need = SuccSt.wait) ↔ False := by decide
@[simp] theorem SuccSt.need_eq_ok : (SuccSt.need = SuccSt.ok) ↔ False := by decide
@[simp] theorem SuccSt.need_eq_bad : (SuccSt.need = SuccSt.bad) ↔ False := by decide
@[simp] theorem SuccSt.ok_eq_wait : (SuccSt.ok = SuccSt.wait) ↔ False := by decide
@[simp] theorem SuccSt.ok_eq_need : (SuccSt.ok = SuccSt.need) ↔ False := by decide
@[simp] theorem SuccSt.ok_eq_bad : (SuccSt.ok = SuccSt.bad) ↔ False := by decide
@[simp] theorem SuccSt.bad_eq_wait : (SuccSt.bad = SuccSt.wait) ↔ False := by decide
@[simp] theorem SuccSt.bad_eq_need : (SuccSt.bad = SuccSt.need) ↔ False := by decide
@[simp] theorem SuccSt.bad_eq_ok : (SuccSt.bad = SuccSt.ok) ↔ False := by decide

def flagNext (bi bj : Bool) : Flag → Flag
  | .bad => .bad
  | .ok => if bi || bj then .bad else .ok
  | .wait => if bi && bj then .ok else if bi || bj then .bad else .wait

def eqPhase (p q n : Nat) : Flag :=
  if p = q then
    if n ≤ p then .wait else .ok
  else if p < q then
    if n ≤ p then .wait else .bad
  else if n ≤ q then .wait else .bad

@[simp] theorem decide_nat_eq_false {a b : Nat} (h : a ≠ b) : decide (a = b) = false :=
  decide_eq_false_iff_not.mpr h

theorem eqPhase_zero (p q : Nat) : eqPhase p q 0 = .wait := by
  unfold eqPhase
  split_ifs <;> solve | rfl | simp_all

theorem eqPhase_step (p q n : Nat) :
    eqPhase p q (n + 1) =
      flagNext (decide (n = p)) (decide (n = q)) (eqPhase p q n) := by
  unfold eqPhase flagNext
  split_ifs <;> simp_all <;> omega

theorem eqPhase_ok (p q n : Nat) :
    eqPhase p q n = .ok ↔ p = q ∧ ¬ n ≤ p := by
  unfold eqPhase
  constructor
  · intro h
    split_ifs at h; simp_all
  · intro h
    split_ifs <;> solve | simp_all | rfl | (exfalso; omega)

def eqNext {f s : Nat} (i j : Fin f) (st : Flag) (a : Letter f s) : Flag :=
  flagNext (a.1 i) (a.1 j) st

def eqAuto {f s : Nat} (i j : Fin f) : NBA (Letter f s) Flag where
  step st a st' := decide (st' = eqNext i j st a)
  start st := decide (st = .wait)
  accept st := decide (st = .ok)

theorem eqAuto_step {f s : Nat} (i j : Fin f) (st : Flag) (a : Letter f s) (st' : Flag) :
    (eqAuto i j).step st a st' = true ↔ st' = eqNext i j st a := by
  simp [eqAuto]

theorem eqAuto_start {f s : Nat} (i j : Fin f) (st : Flag) :
    (eqAuto (s := s) i j).start st = true ↔ st = .wait := by
  simp [eqAuto]

theorem eq_run {f s : Nat} (w : Nat → Letter f s) (hv : valid w) (i j : Fin f) :
    ∀ n, detRun (eqNext i j) .wait w n =
      eqPhase (thePos (hv i)) (thePos (hv j)) n := by
  intro n
  induction n with
  | zero =>
    simp [detRun]
    exact (eqPhase_zero _ _).symm
  | succ n ih =>
    simp only [detRun, eqNext, ih, letter_bit_eq w hv i n, letter_bit_eq w hv j n]
    exact (eqPhase_step _ _ n).symm

theorem eqAuto_iff {f s : Nat} (i j : Fin f) (w : Nat → Letter f s) (hv : valid w) :
    Accepts (eqAuto i j) w ↔ sat (.eq i j) w := by
  rw [detRun_accepts (eqAuto i j) (eqNext i j) .wait (eqAuto_step i j) (eqAuto_start i j)]
  have hrun := eq_run w hv i j
  constructor
  · intro hacc
    obtain ⟨v, _, ha⟩ := hacc 0
    have hdec : decide (detRun (eqNext i j) .wait w v = .ok) = true := by
      simpa [eqAuto] using ha
    have hst : eqPhase (thePos (hv i)) (thePos (hv j)) v = .ok := by
      simpa [hrun] using of_decide_eq_true hdec
    obtain ⟨hpq, _⟩ := (eqPhase_ok _ _ _).mp hst
    refine ⟨thePos (hv i), ?_, ?_⟩
    · simpa [bit] using (thePos_spec (hv i)).1
    · simpa [bit, hpq.symm] using (thePos_spec (hv j)).1
  · intro ⟨n, hi, hj⟩
    have hp : n = thePos (hv i) := (thePos_spec (hv i)).2 n (by simpa [bit] using hi)
    have hq : n = thePos (hv j) := (thePos_spec (hv j)).2 n (by simpa [bit] using hj)
    have hpq : thePos (hv i) = thePos (hv j) := hp.symm.trans hq
    intro lower
    refine ⟨max lower (thePos (hv i) + 1), le_max_left _ _, ?_⟩
    have hnot : ¬ max lower (thePos (hv i) + 1) ≤ thePos (hv i) :=
      Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
    have hok := (eqPhase_ok _ _ _).mpr ⟨hpq, hnot⟩
    simp [eqAuto, hrun, hok]

def eqChecked {f s : Nat} (i j : Fin f) : NBA (Letter f s) (Track f × Flag × Fin 2) :=
  inter (guard f s) (eqAuto (s := s) i j)

theorem eqChecked_iff {f s : Nat} (i j : Fin f) (w : Nat → Letter f s) :
    Accepts (eqChecked i j) w ↔ valid w ∧ sat (.eq i j) w := by
  rw [eqChecked, accepts_inter, guard_iff]
  constructor
  · intro ⟨hv, ha⟩
    exact ⟨hv, (eqAuto_iff i j w hv).mp ha⟩
  · intro ⟨hv, hs⟩
    exact ⟨hv, (eqAuto_iff i j w hv).mpr hs⟩

def succFlag (bi bj : Bool) : SuccSt → SuccSt
  | .bad => .bad
  | .ok => if bi || bj then .bad else .ok
  | .need => if bj && !bi then .ok else .bad
  | .wait => if bi && bj then .bad else if bi then .need else if bj then .bad else .wait

def succPhase (p q n : Nat) : SuccSt :=
  if q = p + 1 then
    if n ≤ p then .wait else if n = p + 1 then .need else .ok
  else if q = p then
    if n ≤ p then .wait else .bad
  else if q < p then
    if n ≤ q then .wait else .bad
  else if n ≤ p then .wait else if n = p + 1 then .need else .bad

theorem succPhase_zero (p q : Nat) : succPhase p q 0 = .wait := by
  unfold succPhase
  split_ifs <;> solve | rfl | simp_all

theorem succPhase_step (p q n : Nat) :
    succPhase p q (n + 1) =
      succFlag (decide (n = p)) (decide (n = q)) (succPhase p q n) := by
  unfold succPhase succFlag
  split_ifs <;> simp_all <;> omega

theorem succPhase_ok (p q n : Nat) :
    succPhase p q n = .ok ↔ q = p + 1 ∧ ¬ n ≤ p ∧ n ≠ p + 1 := by
  unfold succPhase
  constructor
  · intro h
    split_ifs at h; simp_all
  · intro h
    split_ifs <;> simp_all

def succNext {f s : Nat} (i j : Fin f) (st : SuccSt) (a : Letter f s) : SuccSt :=
  succFlag (a.1 i) (a.1 j) st

def succAuto {f s : Nat} (i j : Fin f) : NBA (Letter f s) SuccSt where
  step st a st' := decide (st' = succNext i j st a)
  start st := decide (st = .wait)
  accept st := decide (st = .ok)

theorem succAuto_step {f s : Nat} (i j : Fin f) (st : SuccSt) (a : Letter f s) (st' : SuccSt) :
    (succAuto i j).step st a st' = true ↔ st' = succNext i j st a := by
  simp [succAuto]

theorem succAuto_start {f s : Nat} (i j : Fin f) (st : SuccSt) :
    (succAuto (s := s) i j).start st = true ↔ st = .wait := by
  simp [succAuto]

theorem succ_run {f s : Nat} (w : Nat → Letter f s) (hv : valid w) (i j : Fin f) :
    ∀ n, detRun (succNext i j) .wait w n =
      succPhase (thePos (hv i)) (thePos (hv j)) n := by
  intro n
  induction n with
  | zero =>
    simp [detRun]
    exact (succPhase_zero _ _).symm
  | succ n ih =>
    simp only [detRun, succNext, ih, letter_bit_eq w hv i n, letter_bit_eq w hv j n]
    exact (succPhase_step _ _ n).symm

theorem succAuto_iff {f s : Nat} (i j : Fin f) (w : Nat → Letter f s) (hv : valid w) :
    Accepts (succAuto i j) w ↔ sat (.succ i j) w := by
  rw [detRun_accepts (succAuto i j) (succNext i j) .wait (succAuto_step i j) (succAuto_start i j)]
  have hrun := succ_run w hv i j
  constructor
  · intro hacc
    obtain ⟨v, _, ha⟩ := hacc 0
    have hdec : decide (detRun (succNext i j) .wait w v = .ok) = true := by
      simpa [succAuto] using ha
    have hst : succPhase (thePos (hv i)) (thePos (hv j)) v = .ok := by
      simpa [hrun] using of_decide_eq_true hdec
    obtain ⟨hpq, _, _⟩ := (succPhase_ok _ _ _).mp hst
    refine ⟨thePos (hv i), ?_, ?_⟩
    · simpa [bit] using (thePos_spec (hv i)).1
    · simpa [bit, hpq] using (thePos_spec (hv j)).1
  · intro ⟨n, hi, hj⟩
    have hp : n = thePos (hv i) := (thePos_spec (hv i)).2 n (by simpa [bit] using hi)
    have hq : n + 1 = thePos (hv j) := (thePos_spec (hv j)).2 (n + 1) (by simpa [bit] using hj)
    have hpq : thePos (hv j) = thePos (hv i) + 1 := by
      rw [← hq, hp]
    intro lower
    refine ⟨max lower (thePos (hv i) + 2), le_max_left _ _, ?_⟩
    have hnot : ¬ max lower (thePos (hv i) + 2) ≤ thePos (hv i) :=
      Nat.not_le_of_gt (Nat.lt_of_lt_of_le (by omega : thePos (hv i) < thePos (hv i) + 2)
        (le_max_right _ _))
    have hne : max lower (thePos (hv i) + 2) ≠ thePos (hv i) + 1 := by omega
    have hok := (succPhase_ok _ _ _).mpr ⟨hpq, hnot, hne⟩
    simp [succAuto, hrun, hok]

def succChecked {f s : Nat} (i j : Fin f) : NBA (Letter f s) (Track f × SuccSt × Fin 2) :=
  inter (guard f s) (succAuto (s := s) i j)

theorem succChecked_iff {f s : Nat} (i j : Fin f) (w : Nat → Letter f s) :
    Accepts (succChecked i j) w ↔ valid w ∧ sat (.succ i j) w := by
  rw [succChecked, accepts_inter, guard_iff]
  constructor
  · intro ⟨hv, ha⟩
    exact ⟨hv, (succAuto_iff i j w hv).mp ha⟩
  · intro ⟨hv, hs⟩
    exact ⟨hv, (succAuto_iff i j w hv).mpr hs⟩

def memFlag (bi bX : Bool) : Flag → Flag
  | .bad => .bad
  | .ok => if bi then .bad else .ok
  | .wait => if bi then (if bX then .ok else .bad) else .wait

theorem memFlag_off (bX bX' : Bool) (st : Flag) :
    memFlag false bX st = memFlag false bX' st := by
  cases st <;> rfl

def memPhase (on : Bool) (p n : Nat) : Flag :=
  if on = true then
    if n ≤ p then .wait else .ok
  else
    if n ≤ p then .wait else .bad

theorem memPhase_zero (on : Bool) (p : Nat) : memPhase on p 0 = .wait := by
  unfold memPhase
  split_ifs <;> solve | rfl | simp_all

theorem memPhase_step (on : Bool) (p n : Nat) :
    memPhase on p (n + 1) =
      memFlag (decide (n = p)) (if n = p then on else false) (memPhase on p n) := by
  unfold memPhase memFlag
  split_ifs <;> simp_all <;> omega

theorem memPhase_ok (on : Bool) (p n : Nat) :
    memPhase on p n = .ok ↔ on = true ∧ ¬ n ≤ p := by
  unfold memPhase
  constructor
  · intro h
    split_ifs at h; simp_all
  · intro h
    split_ifs <;> simp_all

def memNext {f s : Nat} (i : Fin f) (X : Fin s) (st : Flag) (a : Letter f s) : Flag :=
  memFlag (a.1 i) (a.2 X) st

def memAuto {f s : Nat} (i : Fin f) (X : Fin s) : NBA (Letter f s) Flag where
  step st a st' := decide (st' = memNext i X st a)
  start st := decide (st = .wait)
  accept st := decide (st = .ok)

theorem memAuto_step {f s : Nat} (i : Fin f) (X : Fin s) (st : Flag) (a : Letter f s)
    (st' : Flag) : (memAuto i X).step st a st' = true ↔ st' = memNext i X st a := by
  simp [memAuto]

theorem memAuto_start {f s : Nat} (i : Fin f) (X : Fin s) (st : Flag) :
    (memAuto (s := s) i X).start st = true ↔ st = .wait := by
  simp [memAuto]

theorem mem_run {f s : Nat} (w : Nat → Letter f s) (hv : valid w) (i : Fin f) (X : Fin s) :
    ∀ n, detRun (memNext i X) .wait w n =
      memPhase (setBit w X (thePos (hv i))) (thePos (hv i)) n := by
  intro n
  induction n with
  | zero =>
    simp [detRun]
    exact (memPhase_zero _ _).symm
  | succ n ih =>
    rw [detRun, memNext, ih, letter_bit_eq w hv i n, memPhase_step]
    by_cases hn : n = thePos (hv i)
    · simp [hn, setBit]
    · rw [decide_nat_eq_false hn]
      exact memFlag_off _ _ _

theorem memAuto_iff {f s : Nat} (i : Fin f) (X : Fin s) (w : Nat → Letter f s)
    (hv : valid w) : Accepts (memAuto i X) w ↔ sat (.mem i X) w := by
  rw [detRun_accepts (memAuto i X) (memNext i X) .wait (memAuto_step i X) (memAuto_start i X)]
  have hrun := mem_run w hv i X
  constructor
  · intro hacc
    obtain ⟨v, _, ha⟩ := hacc 0
    have hdec : decide (detRun (memNext i X) .wait w v = .ok) = true := by
      simpa [memAuto] using ha
    have hst : memPhase (setBit w X (thePos (hv i))) (thePos (hv i)) v = .ok := by
      simpa [hrun] using of_decide_eq_true hdec
    obtain ⟨hon, _⟩ := (memPhase_ok _ _ _).mp hst
    refine ⟨thePos (hv i), ?_, ?_⟩
    · simpa [bit] using (thePos_spec (hv i)).1
    · simpa [setBit] using hon
  · intro ⟨n, hi, hX⟩
    have hp : n = thePos (hv i) := (thePos_spec (hv i)).2 n (by simpa [bit] using hi)
    have hon : setBit w X (thePos (hv i)) = true := by simpa [setBit, hp] using hX
    intro lower
    refine ⟨max lower (thePos (hv i) + 1), le_max_left _ _, ?_⟩
    have hnot : ¬ max lower (thePos (hv i) + 1) ≤ thePos (hv i) :=
      Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
    have hok := (memPhase_ok _ _ _).mpr ⟨hon, hnot⟩
    simp [memAuto, hrun, hok]

def memChecked {f s : Nat} (i : Fin f) (X : Fin s) :
    NBA (Letter f s) (Track f × Flag × Fin 2) :=
  inter (guard f s) (memAuto (s := s) i X)

theorem memChecked_iff {f s : Nat} (i : Fin f) (X : Fin s) (w : Nat → Letter f s) :
    Accepts (memChecked i X) w ↔ valid w ∧ sat (.mem i X) w := by
  rw [memChecked, accepts_inter, guard_iff]
  constructor
  · intro ⟨hv, ha⟩
    exact ⟨hv, (memAuto_iff i X w hv).mp ha⟩
  · intro ⟨hv, hs⟩
    exact ⟨hv, (memAuto_iff i X w hv).mpr hs⟩

/-! ### Monadic second-order sentences

`compileMSO` sends each formula to a Büchi automaton on the same alphabet.
Individual quantifiers are projected through the exactly-one guard, and set
quantifiers are projected directly. Negation is complementation intersected
with the guard, so an invalid word is not accepted by a negated formula.
J. Richard Büchi, *On a Decision Method in Restricted Second Order Arithmetic*
(1962).
-/

def rankGuessEquiv (σ : Type) [Fintype σ] :
    RankGuess σ ≃ ((σ → Option (Fin (2 * Fintype.card σ + 1))) × (σ → Bool)) where
  toFun s := (s.rank, s.owe)
  invFun p := ⟨p.1, p.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by cases p; rfl

/-- A rank guess whose domain is `Fin n`, so the formula-state recursion does not
mention a `Fintype` instance in its own type. `notStateEquiv` identifies it
with `RankGuess`. -/
abbrev NotGuess (n : Nat) :=
  (Fin n → Option (Fin (2 * n + 1))) × (Fin n → Bool)

abbrev NotState (f n : Nat) := NotGuess n × Track f × Fin 2

noncomputable def mcard {f s : Nat} : MSO f s → Nat
  | .bot => 1
  | .eq _ _ => Fintype.card (Track f × Flag × Fin 2)
  | .succ _ _ => Fintype.card (Track f × SuccSt × Fin 2)
  | .mem _ _ => Fintype.card (Track f × Flag × Fin 2)
  | .and φ ψ => mcard φ * (mcard ψ * 2)
  | .or φ ψ => mcard φ + mcard ψ
  | .not φ => Fintype.card (NotState f (mcard φ))
  | .exInd φ => mcard φ
  | .exSet φ => mcard φ

@[reducible]
noncomputable def MState {f s : Nat} : MSO f s → Type
  | .bot => Unit
  | .eq _ _ => Track f × Flag × Fin 2
  | .succ _ _ => Track f × SuccSt × Fin 2
  | .mem _ _ => Track f × Flag × Fin 2
  | .and φ ψ => MState φ × MState ψ × Fin 2
  | .or φ ψ => MState φ ⊕ MState ψ
  | .not φ => NotState f (mcard φ)
  | .exInd φ => MState φ
  | .exSet φ => MState φ

@[instance_reducible]
noncomputable def fintypeMState {f s : Nat} : (φ : MSO f s) → Fintype (MState φ)
  | .bot => inferInstance
  | .eq _ _ => (inferInstance : Fintype (Track f × Flag × Fin 2))
  | .succ _ _ => (inferInstance : Fintype (Track f × SuccSt × Fin 2))
  | .mem _ _ => (inferInstance : Fintype (Track f × Flag × Fin 2))
  | .and φ ψ =>
      letI := fintypeMState φ
      letI := fintypeMState ψ
      (inferInstance : Fintype (MState φ × MState ψ × Fin 2))
  | .or φ ψ =>
      letI := fintypeMState φ
      letI := fintypeMState ψ
      (inferInstance : Fintype (MState φ ⊕ MState ψ))
  | .not φ => (inferInstance : Fintype (NotState f (mcard φ)))
  | .exInd φ => fintypeMState φ
  | .exSet φ => fintypeMState φ

@[instance_reducible]
noncomputable def decidableEqMState {f s : Nat} : (φ : MSO f s) → DecidableEq (MState φ)
  | .bot => inferInstance
  | .eq _ _ => (inferInstance : DecidableEq (Track f × Flag × Fin 2))
  | .succ _ _ => (inferInstance : DecidableEq (Track f × SuccSt × Fin 2))
  | .mem _ _ => (inferInstance : DecidableEq (Track f × Flag × Fin 2))
  | .and φ ψ =>
      letI := decidableEqMState φ
      letI := decidableEqMState ψ
      (inferInstance : DecidableEq (MState φ × MState ψ × Fin 2))
  | .or φ ψ =>
      letI := decidableEqMState φ
      letI := decidableEqMState ψ
      (inferInstance : DecidableEq (MState φ ⊕ MState ψ))
  | .not φ => (inferInstance : DecidableEq (NotState f (mcard φ)))
  | .exInd φ => decidableEqMState φ
  | .exSet φ => decidableEqMState φ

noncomputable instance {f s : Nat} (φ : MSO f s) : Fintype (MState φ) :=
  fintypeMState φ

noncomputable instance {f s : Nat} (φ : MSO f s) : DecidableEq (MState φ) :=
  decidableEqMState φ

theorem mcard_eq {f s : Nat} (φ : MSO f s) : Fintype.card (MState φ) = mcard φ := by
  induction φ with
  | bot => exact Fintype.card_unit
  | eq _ _ => rfl
  | succ _ _ => rfl
  | mem _ _ => rfl
  | and φ ψ ihφ ihψ =>
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, ihφ, ihψ]
      rfl
  | or φ ψ ihφ ihψ =>
      rw [Fintype.card_sum, ihφ, ihψ]
      rfl
  | not _ _ => rfl
  | exInd _ ih => exact ih
  | exSet _ ih => exact ih

noncomputable def notStateEquiv {f s : Nat} (φ : MSO f s) :
    NotState f (mcard φ) ≃
      (@RankGuess (MState φ) (fintypeMState φ) × Track f × Fin 2) :=
  let eσ : Fin (mcard φ) ≃ MState φ := (Fintype.equivFinOfCardEq (mcard_eq φ)).symm
  let eIdx : Fin (2 * mcard φ + 1) ≃ Fin (2 * Fintype.card (MState φ) + 1) :=
    finCongr (congrArg (fun k => 2 * k + 1) (mcard_eq φ).symm)
  let eGuess :=
    Equiv.prodCongr
      (Equiv.arrowCongr eσ (Equiv.optionCongr eIdx))
      (Equiv.arrowCongr eσ (Equiv.refl Bool))
  (Equiv.prodCongr eGuess (Equiv.refl (Track f × Fin 2))).trans
    (Equiv.prodCongr (@rankGuessEquiv (MState φ) (fintypeMState φ)).symm
      (Equiv.refl (Track f × Fin 2)))

def mapState {α σ τ : Type} (e : σ ≃ τ) (A : NBA α σ) : NBA α τ where
  step t a t' := A.step (e.symm t) a (e.symm t')
  start t := A.start (e.symm t)
  accept t := A.accept (e.symm t)

theorem accepts_mapState {α σ τ : Type} (e : σ ≃ τ) (A : NBA α σ) (w : Nat → α) :
    Accepts (mapState e A) w ↔ Accepts A w := by
  constructor
  · intro ⟨path, h0, hs, ha⟩
    exact ⟨fun n => e.symm (path n), h0, hs, ha⟩
  · intro ⟨path, h0, hs, ha⟩
    refine ⟨fun n => e (path n), ?_, ?_, ?_⟩
    · simpa [mapState, Equiv.symm_apply_apply] using h0
    · intro n
      simpa [mapState, Equiv.symm_apply_apply] using hs n
    · intro lower
      obtain ⟨visit, hv, hacc⟩ := ha lower
      exact ⟨visit, hv, by simpa [mapState, Equiv.symm_apply_apply] using hacc⟩

noncomputable def compileMSO {f s : Nat} : (φ : MSO f s) → NBA (Letter f s) (MState φ)
  | .bot =>
      { step := fun _ _ _ => false
        start := fun _ => true
        accept := fun _ => true }
  | .eq i j => eqChecked i j
  | .succ i j => succChecked i j
  | .mem i X => memChecked i X
  | .and φ ψ => inter (compileMSO φ) (compileMSO ψ)
  | .or φ ψ => union (compileMSO φ) (compileMSO ψ)
  | .not φ =>
      mapState (notStateEquiv φ).symm
        (inter (@complement (Letter f s) (MState φ) (fintypeMState φ) (compileMSO φ))
          (guard f s))
  | .exInd φ => project (relabel (compileMSO φ) packInd)
  | .exSet φ => project (relabel (compileMSO φ) packSet)

/-- Acceptance is truth in the standard assignment model: a word is valid when
each free individual occurs at exactly one position, and `sat` reads `=`,
`succ`, and membership on those positions. -/
theorem compileMSO_iff {f s : Nat} (φ : MSO f s) (w : Nat → Letter f s) :
    Accepts (compileMSO φ) w ↔ valid w ∧ sat φ w := by
  induction φ with
  | bot =>
    constructor
    · intro ⟨_, _, hstep, _⟩
      simp [compileMSO] at hstep
    · intro ⟨_, hf⟩
      exact False.elim hf
  | eq i j =>
    exact eqChecked_iff i j w
  | succ i j =>
    exact succChecked_iff i j w
  | mem i X =>
    exact memChecked_iff i X w
  | and φ ψ ihφ ihψ =>
    unfold compileMSO
    rw [accepts_inter, sat]
    constructor
    · intro ⟨ha, hb⟩
      obtain ⟨hv, hsφ⟩ := (ihφ w).mp ha
      obtain ⟨_, hsψ⟩ := (ihψ w).mp hb
      exact ⟨hv, hsφ, hsψ⟩
    · intro ⟨hv, hsφ, hsψ⟩
      exact ⟨(ihφ w).mpr ⟨hv, hsφ⟩, (ihψ w).mpr ⟨hv, hsψ⟩⟩
  | or φ ψ ihφ ihψ =>
    unfold compileMSO
    rw [accepts_union, sat]
    constructor
    · intro h
      rcases h with ha | hb
      · obtain ⟨hv, hs⟩ := (ihφ w).mp ha
        exact ⟨hv, Or.inl hs⟩
      · obtain ⟨hv, hs⟩ := (ihψ w).mp hb
        exact ⟨hv, Or.inr hs⟩
    · intro ⟨hv, hs⟩
      rcases hs with hs | hs
      · exact Or.inl ((ihφ w).mpr ⟨hv, hs⟩)
      · exact Or.inr ((ihψ w).mpr ⟨hv, hs⟩)
  | not φ ih =>
    unfold compileMSO
    rw [accepts_mapState, accepts_inter, accepts_complement, guard_iff, sat]
    constructor
    · intro ⟨hc, hv⟩
      exact ⟨hv, fun hs => hc ((ih w).mpr ⟨hv, hs⟩)⟩
    · intro ⟨hv, hs⟩
      exact ⟨fun hacc => hs ((ih w).mp hacc).2, hv⟩
  | exInd φ ih =>
    unfold compileMSO
    rw [accepts_project, sat]
    constructor
    · intro ⟨labelling, hacc⟩
      rw [accepts_relabel] at hacc
      have hword : (fun n => packInd (w n, labelling n)) = envInd w labelling :=
        funext fun _ => rfl
      rw [hword] at hacc
      obtain ⟨hv, hs⟩ := (ih (envInd w labelling)).mp hacc
      obtain ⟨hb, hw⟩ := (valid_envInd w labelling).mp hv
      exact ⟨hw, labelling, hb, hs⟩
    · intro ⟨hw, b, hb, hs⟩
      refine ⟨b, ?_⟩
      rw [accepts_relabel]
      have hword : (fun n => packInd (w n, b n)) = envInd w b := funext fun _ => rfl
      rw [hword]
      exact (ih (envInd w b)).mpr ⟨(valid_envInd w b).mpr ⟨hb, hw⟩, hs⟩
  | exSet φ ih =>
    unfold compileMSO
    rw [accepts_project, sat]
    constructor
    · intro ⟨labelling, hacc⟩
      rw [accepts_relabel] at hacc
      have hword : (fun n => packSet (w n, labelling n)) = envSet w labelling :=
        funext fun _ => rfl
      rw [hword] at hacc
      obtain ⟨hv, hs⟩ := (ih (envSet w labelling)).mp hacc
      exact ⟨(valid_envSet w labelling).mp hv, labelling, hs⟩
    · intro ⟨hw, b, hs⟩
      refine ⟨b, ?_⟩
      rw [accepts_relabel]
      have hword : (fun n => packSet (w n, b n)) = envSet w b := funext fun _ => rfl
      rw [hword]
      exact (ih (envSet w b)).mpr ⟨(valid_envSet w b).mpr hw, hs⟩

def canonicalLetter : Letter 0 0 := ⟨Fin.elim0, Fin.elim0⟩

def canonicalWord : Nat → Letter 0 0 := fun _ => canonicalLetter

@[instance_reducible]
def enumerableLetter0 : Enumerable (Letter 0 0) where
  elems := [canonicalLetter]
  mem_elems p := by
    cases p with
    | mk a b =>
      have ha : a = Fin.elim0 := funext fun i => i.elim0
      have hb : b = Fin.elim0 := funext fun i => i.elim0
      simp [canonicalLetter, ha, hb]

theorem word0_unique (w : Nat → Letter 0 0) (n : Nat) : w n = canonicalWord n := by
  cases w n with
  | mk a b =>
    have ha : a = Fin.elim0 := funext fun i => i.elim0
    have hb : b = Fin.elim0 := funext fun i => i.elim0
    simp [canonicalWord, canonicalLetter, ha, hb]

theorem valid0 (w : Nat → Letter 0 0) : valid w := fun i => i.elim0

@[instance_reducible]
noncomputable def enumerableOfFintype (α : Type) [Fintype α] : Enumerable α where
  elems := Finset.univ.toList
  mem_elems a := by simp

noncomputable def decideMSO (φ : MSO 0 0) : Bool :=
  @decideNonempty (Letter 0 0) (MState φ) (compileMSO φ)
    enumerableLetter0 (enumerableOfFintype (MState φ)) (fintypeMState φ) (decidableEqMState φ)

/-- A closed sentence is true in `(ℕ, succ)` exactly when `decideMSO` returns
true. Quantifiers range over exactly-one individual predicates and over arbitrary
set predicates. J. Richard Büchi, *On a Decision Method in Restricted Second
Order Arithmetic* (1962). -/
theorem decideMSO_iff (φ : MSO 0 0) :
    decideMSO φ = true ↔ sat φ canonicalWord := by
  rw [decideMSO]
  rw [@decideNonempty_iff (Letter 0 0) (MState φ) (compileMSO φ)
    enumerableLetter0 (enumerableOfFintype (MState φ)) (fintypeMState φ) (decidableEqMState φ)]
  constructor
  · intro ⟨w, hw⟩
    obtain ⟨_, hs⟩ := (compileMSO_iff φ w).mp hw
    exact (sat_congr (word0_unique w)).mp hs
  · intro hs
    exact ⟨canonicalWord, (compileMSO_iff φ canonicalWord).mpr ⟨valid0 canonicalWord, hs⟩⟩

structure MSOBubble where
  decide : MSO 0 0 → Bool
  agrees : ∀ φ, decide φ = true ↔ sat φ canonicalWord

noncomputable def msoBubble : MSOBubble where
  decide := decideMSO
  agrees := decideMSO_iff

theorem msoBubble_iff (φ : MSO 0 0) :
    msoBubble.decide φ = true ↔ sat φ canonicalWord :=
  msoBubble.agrees φ

theorem exactlyOne_at (k : Nat) : exactlyOne (fun n => decide (n = k)) := by
  refine ⟨k, by simp, ?_⟩
  intro m hm
  exact of_decide_eq_true hm

theorem control_mso_bot : decideMSO .bot = false := by
  refine Bool.eq_false_iff.mpr ?_
  intro h
  have hsat := (decideMSO_iff .bot).mp h
  simp [sat] at hsat

theorem control_mso_not_bot : decideMSO (.not .bot) = true := by
  rw [decideMSO_iff]
  simp [sat]

theorem control_mso_succ :
    decideMSO (.exInd (.exInd (.succ (1 : Fin 2) 0))) = true := by
  rw [decideMSO_iff]
  let b : Nat → Bool := fun n => decide (n = 0)
  let c : Nat → Bool := fun n => decide (n = 1)
  refine ⟨b, exactlyOne_at 0, c, exactlyOne_at 1, 0, ?_, ?_⟩
  · have h1 := congrFun (bit_envInd_succ (envInd canonicalWord b) c (0 : Fin 1)) 0
    have hidx : Fin.succ (0 : Fin 1) = (1 : Fin 2) := by decide
    rw [hidx] at h1
    have h2 := congrFun (bit_envInd_zero canonicalWord b) 0
    have h3 : b 0 = true := by simp [b]
    exact h1.trans (h2.trans h3)
  · have h := congrFun (bit_envInd_zero (envInd canonicalWord b) c) 1
    simpa [c] using h

theorem control_mso_succ_self : decideMSO (.exInd (.succ 0 0)) = false := by
  refine Bool.eq_false_iff.mpr ?_
  intro h
  obtain ⟨b, hb, n, hn, hn1⟩ := (decideMSO_iff _).mp h
  have hbn : b n = true := (congrFun (bit_envInd_zero canonicalWord b) n).symm.trans hn
  have hbn1 : b (n + 1) = true :=
    (congrFun (bit_envInd_zero canonicalWord b) (n + 1)).symm.trans hn1
  obtain ⟨_, _, huniq⟩ := hb
  exact Nat.ne_of_lt (Nat.lt_succ_self n)
    ((huniq n hbn).trans (huniq (n + 1) hbn1).symm)

theorem control_mso_mem :
    decideMSO (.exSet (.exInd (.mem 0 0))) = true := by
  rw [decideMSO_iff]
  let bX : Nat → Bool := fun _ => true
  let bx : Nat → Bool := fun n => decide (n = 0)
  refine ⟨bX, bx, exactlyOne_at 0, 0, ?_, ?_⟩
  · have h := congrFun (bit_envInd_zero (envSet canonicalWord bX) bx) 0
    simpa [bx] using h
  · have hset := congrFun (setBit_envInd (envSet canonicalWord bX) bx 0) 0
    have hzero := congrFun (setBit_envSet_zero canonicalWord bX) 0
    have h3 : bX 0 = true := by simp [bX]
    exact hset.trans (hzero.trans h3)

theorem control_mso_not_eq : decideMSO (.exInd (.not (.eq 0 0))) = false := by
  refine Bool.eq_false_iff.mpr ?_
  intro h
  obtain ⟨b, hb, hnot⟩ := (decideMSO_iff _).mp h
  apply hnot
  obtain ⟨n, hn, _⟩ := hb
  refine ⟨n, ?_, ?_⟩
  · exact (congrFun (bit_envInd_zero canonicalWord b) n).symm.trans hn
  · exact (congrFun (bit_envInd_zero canonicalWord b) n).symm.trans hn

/-! ## Executable compiler

States are codes. `decodeTrack`, `decodeFlag`, and `decodeSucc` read those
codes; the inverse equalities stay in theorems. `execCompile` pulls the existing
checkers, product, union, projection, and `finComplement` along those readings.
-/

@[reducible] def trackCount (f : Nat) : Nat := 2 ^ f * 2

theorem trackCount_pos (f : Nat) : 0 < trackCount f :=
  Nat.mul_pos (Nat.two_pow_pos f) (by decide)

theorem flagSlots_pos : 0 < 3 * 2 := by decide

theorem succSlots_pos : 0 < 4 * 2 := by decide

def encodeBit (b : Bool) : Fin 2 := bif b then 1 else 0

def decodeBit (i : Fin 2) : Bool := decide (i.val = 1)

theorem decode_encodeBit (b : Bool) : decodeBit (encodeBit b) = b := by
  cases b <;> rfl

theorem encode_decodeBit (i : Fin 2) : encodeBit (decodeBit i) = i := by
  cases i using Fin.cases with
  | zero =>
    apply Fin.ext
    rfl
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      apply Fin.ext
      rfl
    | succ i => exact i.elim0

def encodeFlag : Flag → Fin 3
  | .wait => 0
  | .ok => 1
  | .bad => 2

def decodeFlag (i : Fin 3) : Flag :=
  if i.val = 0 then .wait else if i.val = 1 then .ok else .bad

theorem decode_encodeFlag (s : Flag) : decodeFlag (encodeFlag s) = s := by
  cases s <;> rfl

theorem encode_decodeFlag (i : Fin 3) : encodeFlag (decodeFlag i) = i := by
  cases i using Fin.cases with
  | zero =>
    apply Fin.ext
    rfl
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      apply Fin.ext
      rfl
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        apply Fin.ext
        rfl
      | succ i => exact i.elim0

def encodeSucc : SuccSt → Fin 4
  | .wait => 0
  | .need => 1
  | .ok => 2
  | .bad => 3

def decodeSucc (i : Fin 4) : SuccSt :=
  if i.val = 0 then .wait else if i.val = 1 then .need
  else if i.val = 2 then .ok else .bad

theorem decode_encodeSucc (s : SuccSt) : decodeSucc (encodeSucc s) = s := by
  cases s <;> rfl

theorem encode_decodeSucc (i : Fin 4) : encodeSucc (decodeSucc i) = i := by
  cases i using Fin.cases with
  | zero =>
    apply Fin.ext
    rfl
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      apply Fin.ext
      rfl
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        apply Fin.ext
        rfl
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          apply Fin.ext
          rfl
        | succ i => exact i.elim0

def encodeBits (f : Nat) (b : Fin f → Bool) : Fin (2 ^ f) :=
  ⟨packDigits 2 f (fun q => bif b q then 1 else 0),
    packDigits_lt (fun q => bif b q then 1 else 0) (by decide : 1 ≤ 2)
      (fun q => by cases b q <;> decide)⟩

def decodeBits (f : Nat) (i : Fin (2 ^ f)) : Fin f → Bool :=
  fun q => decide ((i.val / 2 ^ (q : Nat)) % 2 = 1)

theorem decode_encodeBits {f : Nat} (b : Fin f → Bool) :
    decodeBits f (encodeBits f b) = b := by
  funext q
  have hd :=
    packDigits_digit (fun i => bif b i then 1 else 0) (by decide : 1 ≤ 2)
      (fun i => by cases b i <;> decide) q
  cases hb : b q with
  | false =>
    rw [hb] at hd
    simp only [decodeBits, encodeBits]
    exact decide_eq_false (by rw [hd]; decide)
  | true =>
    rw [hb] at hd
    simp only [decodeBits, encodeBits]
    exact decide_eq_true (by rw [hd]; rfl)

theorem encode_decodeBits {f : Nat} (i : Fin (2 ^ f)) :
    encodeBits f (decodeBits f i) = i := by
  apply Fin.ext
  have hpack := pack_of_digits (by decide : 1 ≤ 2) i.isLt
  have hfun :
      (fun q : Fin f => bif decodeBits f i q then 1 else 0) =
        fun q : Fin f => (i.val / 2 ^ (q : Nat)) % 2 := by
    funext q
    have hlt : (i.val / 2 ^ (q : Nat)) % 2 < 2 := Nat.mod_lt _ (by decide)
    cases hdig : (i.val / 2 ^ (q : Nat)) % 2 with
    | zero => simp [decodeBits, hdig]
    | succ d =>
      have hd0 : d = 0 := by omega
      simp [decodeBits, hdig, hd0]
  simp only [encodeBits]
  rw [hfun]
  exact hpack

def encodeTrack (f : Nat) (t : Track f) : Fin (trackCount f) :=
  joinFin (encodeBits f t.1, encodeBit t.2)

def decodeTrack (f : Nat) (i : Fin (trackCount f)) : Track f :=
  let p := splitFin Nat.two_pos i
  (decodeBits f p.1, decodeBit p.2)

theorem decode_encodeTrack {f : Nat} (t : Track f) :
    decodeTrack f (encodeTrack f t) = t := by
  cases t with
  | mk bits alive =>
    dsimp only [decodeTrack, encodeTrack]
    rw [splitFin_joinFin Nat.two_pos]
    exact Prod.ext (decode_encodeBits bits) (decode_encodeBit alive)

def encodeChecked {f k : Nat} {α : Type} (encodeK : α → Fin k)
    (t : Track f × α × Fin 2) : Fin (trackCount f * (k * 2)) :=
  joinFin (encodeTrack f t.1, joinFin (encodeK t.2.1, t.2.2))

def decodeChecked {f k : Nat} {α : Type} (hk : 0 < k * 2) (decodeK : Fin k → α)
    (i : Fin (trackCount f * (k * 2))) : Track f × α × Fin 2 :=
  let outer := splitFin hk i
  let inner := splitFin Nat.two_pos outer.2
  (decodeTrack f outer.1, decodeK inner.1, inner.2)

theorem decode_encodeChecked {f k : Nat} {α : Type} (hk : 0 < k * 2)
    (decodeK : Fin k → α) (encodeK : α → Fin k)
    (hde : ∀ a, decodeK (encodeK a) = a) (t : Track f × α × Fin 2) :
    decodeChecked hk decodeK (encodeChecked encodeK t) = t := by
  cases t with
  | mk tr rest =>
    cases rest with
    | mk a ph =>
      dsimp only [decodeChecked, encodeChecked]
      rw [splitFin_joinFin hk]
      rw [splitFin_joinFin Nat.two_pos]
      exact Prod.ext (decode_encodeTrack tr) (Prod.ext (hde a) rfl)

def encodeProd {m n : Nat} (p : Fin m × Fin n × Fin 2) : Fin (m * (n * 2)) :=
  joinFin (p.1, joinFin (p.2.1, p.2.2))

def decodeProd {m n : Nat} (hn : 0 < n * 2) (i : Fin (m * (n * 2))) :
    Fin m × Fin n × Fin 2 :=
  let outer := splitFin hn i
  let inner := splitFin Nat.two_pos outer.2
  (outer.1, inner.1, inner.2)

theorem decode_encodeProd {m n : Nat} (hn : 0 < n * 2) (p : Fin m × Fin n × Fin 2) :
    decodeProd hn (encodeProd p) = p := by
  cases p with
  | mk a rest =>
    cases rest with
    | mk b ph =>
      dsimp only [decodeProd, encodeProd]
      rw [splitFin_joinFin hn]
      rw [splitFin_joinFin Nat.two_pos]

def pull {α σ τ : Type} (A : NBA α σ) (decode : τ → σ) : NBA α τ where
  step t a t' := A.step (decode t) a (decode t')
  start t := A.start (decode t)
  accept t := A.accept (decode t)

theorem accepts_pull {α σ τ : Type} (A : NBA α σ) (decode : τ → σ) (encode : σ → τ)
    (hde : ∀ s, decode (encode s) = s) (w : Nat → α) :
    Accepts (pull A decode) w ↔ Accepts A w :=
  accepts_recode A decode encode hde (pull A decode)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) w

def guardExec (f s : Nat) : NBA (Letter f s) (Fin (trackCount f)) :=
  pull (guard f s) (decodeTrack f)

theorem guardExec_iff {f s : Nat} (w : Nat → Letter f s) :
    Accepts (guardExec f s) w ↔ valid w := by
  rw [guardExec,
    accepts_pull (guard f s) (decodeTrack f) (encodeTrack f) decode_encodeTrack w]
  exact guard_iff w

@[reducible] def execCount {f s : Nat} : MSO f s → Nat
  | .bot => 1
  | .eq _ _ => trackCount f * (3 * 2)
  | .succ _ _ => trackCount f * (4 * 2)
  | .mem _ _ => trackCount f * (3 * 2)
  | .and φ ψ => execCount φ * (execCount ψ * 2)
  | .or φ ψ => execCount φ + execCount ψ
  | .not φ => guessCard (execCount φ) * (trackCount f * 2)
  | .exInd φ => execCount φ
  | .exSet φ => execCount φ

theorem execCount_pos {f s : Nat} : (φ : MSO f s) → 0 < execCount φ
  | .bot => Nat.one_pos
  | .eq _ _ => Nat.mul_pos (trackCount_pos f) flagSlots_pos
  | .succ _ _ => Nat.mul_pos (trackCount_pos f) succSlots_pos
  | .mem _ _ => Nat.mul_pos (trackCount_pos f) flagSlots_pos
  | .and φ ψ => Nat.mul_pos (execCount_pos φ) (Nat.mul_pos (execCount_pos ψ) Nat.two_pos)
  | .or φ ψ => Nat.lt_of_lt_of_le (execCount_pos φ) (Nat.le_add_right _ (execCount ψ))
  | .not φ =>
      Nat.mul_pos (guessCard_pos (execCount φ))
        (Nat.mul_pos (trackCount_pos f) Nat.two_pos)
  | .exInd φ => execCount_pos φ
  | .exSet φ => execCount_pos φ

def execCompile {f s : Nat} : (φ : MSO f s) → NBA (Letter f s) (Fin (execCount φ))
  | .bot =>
      { step := fun _ _ _ => false
        start := fun _ => true
        accept := fun _ => true }
  | .eq i j =>
      pull (eqChecked i j) (decodeChecked flagSlots_pos decodeFlag)
  | .succ i j =>
      pull (succChecked i j) (decodeChecked succSlots_pos decodeSucc)
  | .mem i X =>
      pull (memChecked i X) (decodeChecked flagSlots_pos decodeFlag)
  | .and φ ψ =>
      pull (inter (execCompile φ) (execCompile ψ))
        (decodeProd (Nat.mul_pos (execCount_pos ψ) Nat.two_pos))
  | .or φ ψ => pull (union (execCompile φ) (execCompile ψ)) decodeSum
  | .not φ =>
      pull (inter (finComplement (execCompile φ)) (guardExec f s))
        (decodeProd (Nat.mul_pos (trackCount_pos f) Nat.two_pos))
  | .exInd φ => project (relabel (execCompile φ) packInd)
  | .exSet φ => project (relabel (execCompile φ) packSet)

theorem execCompile_iff {f s : Nat} (φ : MSO f s) (w : Nat → Letter f s) :
    Accepts (execCompile φ) w ↔ valid w ∧ sat φ w := by
  induction φ with
  | bot =>
    constructor
    · intro ⟨_, _, hstep, _⟩
      simp [execCompile] at hstep
    · intro ⟨_, hf⟩
      exact False.elim hf
  | eq i j =>
    unfold execCompile
    rw [accepts_pull (eqChecked i j) (decodeChecked flagSlots_pos decodeFlag)
      (encodeChecked encodeFlag)
      (decode_encodeChecked flagSlots_pos decodeFlag encodeFlag decode_encodeFlag) w]
    exact eqChecked_iff i j w
  | succ i j =>
    unfold execCompile
    rw [accepts_pull (succChecked i j) (decodeChecked succSlots_pos decodeSucc)
      (encodeChecked encodeSucc)
      (decode_encodeChecked succSlots_pos decodeSucc encodeSucc decode_encodeSucc) w]
    exact succChecked_iff i j w
  | mem i X =>
    unfold execCompile
    rw [accepts_pull (memChecked i X) (decodeChecked flagSlots_pos decodeFlag)
      (encodeChecked encodeFlag)
      (decode_encodeChecked flagSlots_pos decodeFlag encodeFlag decode_encodeFlag) w]
    exact memChecked_iff i X w
  | and φ ψ ihφ ihψ =>
    unfold execCompile
    rw [accepts_pull (inter (execCompile φ) (execCompile ψ))
        (decodeProd (Nat.mul_pos (execCount_pos ψ) Nat.two_pos)) encodeProd
        (decode_encodeProd (Nat.mul_pos (execCount_pos ψ) Nat.two_pos)) w,
      accepts_inter, sat]
    constructor
    · intro ⟨ha, hb⟩
      obtain ⟨hv, hsφ⟩ := (ihφ w).mp ha
      obtain ⟨_, hsψ⟩ := (ihψ w).mp hb
      exact ⟨hv, hsφ, hsψ⟩
    · intro ⟨hv, hsφ, hsψ⟩
      exact ⟨(ihφ w).mpr ⟨hv, hsφ⟩, (ihψ w).mpr ⟨hv, hsψ⟩⟩
  | or φ ψ ihφ ihψ =>
    unfold execCompile
    rw [accepts_pull (union (execCompile φ) (execCompile ψ)) decodeSum encodeSum
        decodeSum_encodeSum w, accepts_union, sat]
    constructor
    · intro h
      rcases h with ha | hb
      · obtain ⟨hv, hs⟩ := (ihφ w).mp ha
        exact ⟨hv, Or.inl hs⟩
      · obtain ⟨hv, hs⟩ := (ihψ w).mp hb
        exact ⟨hv, Or.inr hs⟩
    · intro ⟨hv, hs⟩
      rcases hs with hs | hs
      · exact Or.inl ((ihφ w).mpr ⟨hv, hs⟩)
      · exact Or.inr ((ihψ w).mpr ⟨hv, hs⟩)
  | not φ ih =>
    unfold execCompile
    rw [accepts_pull _ _ encodeProd (decode_encodeProd _) w,
      accepts_inter, accepts_finComplement, guardExec_iff, sat]
    constructor
    · intro ⟨hn, hv⟩
      exact ⟨hv, fun hs => hn ((ih w).mpr ⟨hv, hs⟩)⟩
    · intro ⟨hv, hs⟩
      exact ⟨fun hacc => hs ((ih w).mp hacc).2, hv⟩
  | exInd φ ih =>
    unfold execCompile
    rw [accepts_project, sat]
    constructor
    · intro ⟨labelling, hacc⟩
      rw [accepts_relabel] at hacc
      have hword : (fun n => packInd (w n, labelling n)) = envInd w labelling :=
        funext fun _ => rfl
      rw [hword] at hacc
      obtain ⟨hv, hs⟩ := (ih (envInd w labelling)).mp hacc
      obtain ⟨hb, hw⟩ := (valid_envInd w labelling).mp hv
      exact ⟨hw, labelling, hb, hs⟩
    · intro ⟨hw, b, hb, hs⟩
      refine ⟨b, ?_⟩
      rw [accepts_relabel]
      have hword : (fun n => packInd (w n, b n)) = envInd w b := funext fun _ => rfl
      rw [hword]
      exact (ih (envInd w b)).mpr ⟨(valid_envInd w b).mpr ⟨hb, hw⟩, hs⟩
  | exSet φ ih =>
    unfold execCompile
    rw [accepts_project, sat]
    constructor
    · intro ⟨labelling, hacc⟩
      rw [accepts_relabel] at hacc
      have hword : (fun n => packSet (w n, labelling n)) = envSet w labelling :=
        funext fun _ => rfl
      rw [hword] at hacc
      obtain ⟨hv, hs⟩ := (ih (envSet w labelling)).mp hacc
      exact ⟨(valid_envSet w labelling).mp hv, labelling, hs⟩
    · intro ⟨hw, b, hs⟩
      refine ⟨b, ?_⟩
      rw [accepts_relabel]
      have hword : (fun n => packSet (w n, b n)) = envSet w b := funext fun _ => rfl
      rw [hword]
      exact (ih (envSet w b)).mpr ⟨(valid_envSet w b).mpr hw, hs⟩

def execDecide (φ : MSO 0 0) : Bool :=
  @decideNonempty (Letter 0 0) (Fin (execCount φ)) (execCompile φ)
    enumerableLetter0 (enumerableFin (execCount φ)) inferInstance inferInstance

theorem execDecide_iff (φ : MSO 0 0) :
    execDecide φ = true ↔ sat φ canonicalWord := by
  rw [execDecide, decideNonempty_iff]
  constructor
  · intro ⟨w, hw⟩
    obtain ⟨_, hs⟩ := (execCompile_iff φ w).mp hw
    exact (sat_congr (word0_unique w)).mp hs
  · intro hs
    exact ⟨canonicalWord, (execCompile_iff φ canonicalWord).mpr ⟨valid0 canonicalWord, hs⟩⟩

def execBubble : MSOBubble where
  decide := execDecide
  agrees := execDecide_iff

theorem execBubble_iff (φ : MSO 0 0) :
    execBubble.decide φ = true ↔ sat φ canonicalWord :=
  execBubble.agrees φ

theorem execDecide_eq (φ : MSO 0 0) : execDecide φ = decideMSO φ :=
  bool_eq_of_true_iff ((execDecide_iff φ).trans (decideMSO_iff φ).symm)

theorem control_exec_bot : execDecide .bot = false := by
  rw [execDecide_eq]
  exact control_mso_bot

theorem control_exec_not_bot : execDecide (.not .bot) = true := by
  rw [execDecide_eq]
  exact control_mso_not_bot

/-- Kernel evaluation: the one-state rejector is empty. -/
theorem control_exec_bot_eval : execDecide .bot = false := by
  decide

set_option maxHeartbeats 2000000 in
/-- Kernel evaluation: the guarded complement of that rejector is nonempty. -/
theorem control_exec_not_bot_eval : execDecide (.not .bot) = true := by
  decide

theorem control_exec_succ :
    execDecide (.exInd (.exInd (.succ (1 : Fin 2) 0))) = true := by
  rw [execDecide_eq]
  exact control_mso_succ

theorem control_exec_succ_self : execDecide (.exInd (.succ 0 0)) = false := by
  rw [execDecide_eq]
  exact control_mso_succ_self

theorem control_exec_mem :
    execDecide (.exSet (.exInd (.mem 0 0))) = true := by
  rw [execDecide_eq]
  exact control_mso_mem

theorem control_exec_not_eq : execDecide (.exInd (.not (.eq 0 0))) = false := by
  rw [execDecide_eq]
  exact control_mso_not_eq

section CheckedLasso

open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A closed sentence holds of `(ℕ, succ)` exactly when some retained run of
`Lasso.check` on the Boolean compiler finishes accepted. The run does not
assume a valid certificate; coverage uses `accepts_exists_lasso`. -/
theorem execCompile_sat_iff_checkedLasso (φ : MSO 0 0) :
    sat φ canonicalWord ↔
      ∃ L : Lasso (Letter 0 0) (Fin (execCount φ)),
        (lassoChecker.run (lassoBudget L.stem L.loop)
          (Lasso.checkpoint (execCompile φ) L)).2 = .finished true := by
  constructor
  · intro hs
    have hacc : Accepts (execCompile φ) canonicalWord :=
      (execCompile_iff φ canonicalWord).mpr ⟨valid0 canonicalWord, hs⟩
    obtain ⟨L, hL⟩ := accepts_exists_lasso (execCompile φ) hacc
    exact ⟨L, congrArg Prod.snd (lassoChecker_of_check (execCompile φ) L hL)⟩
  · intro ⟨L, hfin⟩
    have hcheck : L.check (execCompile φ) = true := by
      cases hL : L.check (execCompile φ) with
      | true => rfl
      | false =>
        have href := lassoChecker_of_refused (execCompile φ) L hL
        rw [href] at hfin
        cases hfin
    obtain ⟨_, hacc⟩ := Lasso.check_accepts (execCompile φ) L hcheck
    obtain ⟨_, hs⟩ := (execCompile_iff φ _).mp hacc
    exact (sat_congr (word0_unique _)).mp hs

/-- One individual witness makes `¬⊥` true, so some retained lasso on the
compiled automaton finishes accepted. -/
theorem control_checked_exInd_not_bot :
    sat (.exInd (.not .bot)) canonicalWord ∧
      ∃ L : Lasso (Letter 0 0) (Fin (execCount (.exInd (.not .bot)))),
        (lassoChecker.run (lassoBudget L.stem L.loop)
          (Lasso.checkpoint (execCompile (.exInd (.not .bot))) L)).2 =
          .finished true := by
  have hs : sat (.exInd (.not .bot)) canonicalWord :=
    ⟨fun n => decide (n = 0), exactlyOne_at 0, fun h => h⟩
  exact ⟨hs, (execCompile_sat_iff_checkedLasso (.exInd (.not .bot))).mp hs⟩

/-- A one-edge certificate on the compiled `∃x. ⊥` automaton is refused.
The body is false, so the sentence does not hold. -/
def refusedExIndBot : Lasso (Letter 0 0) (Fin 1) where
  startState := 0
  stem := []
  loop := [(canonicalLetter, 0)]

theorem control_checked_exInd_bot :
    ¬ sat (.exInd .bot) canonicalWord ∧
      refusedExIndBot.check (execCompile (.exInd .bot)) = false ∧
      (lassoChecker.run (lassoBudget refusedExIndBot.stem refusedExIndBot.loop)
        (Lasso.checkpoint (execCompile (.exInd .bot)) refusedExIndBot)).2 =
        .faulted := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨_, _, hs⟩
    exact hs
  · decide
  · have hcheck : refusedExIndBot.check (execCompile (.exInd .bot)) = false := by
      decide
    exact lassoChecker_of_refused (execCompile (.exInd .bot)) refusedExIndBot hcheck

/-! ### Explicit lassos on the compiled positive fragment

The states are `encodeChecked` readings of the guard track, the equality or
successor flag, and the intersection phase. The automaton in each check is
`execCompile`. -/

def eqSelfFormula : MSO 0 0 := .exInd (.eq (0 : Fin 1) (0 : Fin 1))

def succXYFormula : MSO 0 0 := .exInd (.exInd (.succ (1 : Fin 2) (0 : Fin 2)))

def bit1 (b : Bool) : Fin 1 → Bool := fun _ => b

def bit2 (lo hi : Bool) : Fin 2 → Bool :=
  fun i => if i = 0 then lo else hi

def eqTrackWitness : Track 1 := trackStep (trackStart 1) (bit1 true)

def eqTrackBlank : Track 1 := trackStep eqTrackWitness (bit1 false)

def succTrackY : Track 2 := trackStep (trackStart 2) (bit2 false true)

def succTrackBoth : Track 2 := trackStep succTrackY (bit2 true false)

def succTrackBlank : Track 2 := trackStep succTrackBoth (bit2 false false)

def eqCode (track : Track 1) (flag : Flag) (ph : Fin 2) :
    Fin (execCount eqSelfFormula) :=
  encodeChecked encodeFlag (track, flag, ph)

def succCode (track : Track 2) (st : SuccSt) (ph : Fin 2) :
    Fin (execCount succXYFormula) :=
  encodeChecked encodeSucc (track, st, ph)

def eqSelfStart : Fin (execCount eqSelfFormula) := eqCode (trackStart 1) .wait 0

def eqSelfPivot : Fin (execCount eqSelfFormula) := eqCode eqTrackWitness .ok 0

def eqSelfPhase : Fin (execCount eqSelfFormula) := eqCode eqTrackBlank .ok 1

def succStart : Fin (execCount succXYFormula) := succCode (trackStart 2) .wait 0

def succAfterY : Fin (execCount succXYFormula) := succCode succTrackY .need 0

def succPivot : Fin (execCount succXYFormula) := succCode succTrackBoth .ok 0

def succBlankCode : Fin (execCount succXYFormula) := succCode succTrackBlank .ok 1

def succWrongTarget : Fin (execCount succXYFormula) := succCode (trackStart 2) .ok 0

/-- Stem reads the unique position where `x` holds. The loop is the blank
letter, and the phase returns to the accepting pivot. -/
def eqSelfLasso : Lasso (Letter 0 0) (Fin (execCount eqSelfFormula)) where
  startState := eqSelfStart
  stem := [(canonicalLetter, eqSelfPivot)]
  loop := [(canonicalLetter, eqSelfPhase), (canonicalLetter, eqSelfPivot)]

/-- Stem reads `x` at position 0 and `y` at position 1. The loop is the blank
letter on the accepting pivot. -/
def succLasso : Lasso (Letter 0 0) (Fin (execCount succXYFormula)) where
  startState := succStart
  stem := [(canonicalLetter, succAfterY), (canonicalLetter, succPivot)]
  loop := [(canonicalLetter, succBlankCode), (canonicalLetter, succPivot)]

/-- The accepting pivot is a real successor of itself only after the phase
step. One edge from that pivot does not close. -/
def succNonclosing : Lasso (Letter 0 0) (Fin (execCount succXYFormula)) where
  startState := succStart
  stem := [(canonicalLetter, succAfterY), (canonicalLetter, succPivot)]
  loop := [(canonicalLetter, succBlankCode)]

/-- From the start code, the accepting pivot is not a one-step successor. -/
def succWrongEdge : Lasso (Letter 0 0) (Fin (execCount succXYFormula)) where
  startState := succStart
  stem := []
  loop := [(canonicalLetter, succWrongTarget)]

def succAfterStem : LassoCheckpoint (Letter 0 0) (Fin (execCount succXYFormula)) :=
  atStem (execCompile succXYFormula) succPivot succStart [] succLasso.loop

def succAfterLoopEdge : LassoCheckpoint (Letter 0 0) (Fin (execCount succXYFormula)) :=
  atLoop (execCompile succXYFormula) succBlankCode succPivot [(canonicalLetter, succPivot)]

set_option maxHeartbeats 2000000

theorem control_exec_eq_lasso_check :
    eqSelfLasso.check (execCompile eqSelfFormula) = true := by
  decide

theorem control_exec_eq_lasso_run :
    lassoChecker.run (lassoBudget eqSelfLasso.stem eqSelfLasso.loop)
      (Lasso.checkpoint (execCompile eqSelfFormula) eqSelfLasso) =
      (eqSelfLasso.stem ++ eqSelfLasso.loop, .finished true) := by
  rfl

theorem control_exec_succ_lasso_check :
    succLasso.check (execCompile succXYFormula) = true := by
  decide

theorem control_exec_succ_lasso_run :
    lassoChecker.run (lassoBudget succLasso.stem succLasso.loop)
      (Lasso.checkpoint (execCompile succXYFormula) succLasso) =
      (succLasso.stem ++ succLasso.loop, .finished true) := by
  rfl

theorem control_exec_succ_nonclosing :
    succNonclosing.check (execCompile succXYFormula) = false ∧
      lassoChecker.run (lassoBudget succNonclosing.stem succNonclosing.loop)
        (Lasso.checkpoint (execCompile succXYFormula) succNonclosing) =
        (succNonclosing.stem ++ succNonclosing.loop, .faulted) := by
  refine ⟨?_, ?_⟩
  · decide
  · rfl

theorem control_exec_succ_wrong_edge :
    succWrongEdge.check (execCompile succXYFormula) = false ∧
      lassoChecker.run (lassoBudget succWrongEdge.stem succWrongEdge.loop)
        (Lasso.checkpoint (execCompile succXYFormula) succWrongEdge) =
        ([], .faulted) := by
  refine ⟨?_, ?_⟩
  · decide
  · rfl

/-- Three steps publish the successor stem and exhaust. Two further steps
publish the first loop edge. The joint list is that prefix, and the resumed
segment does not contain the stem. -/
theorem control_exec_succ_split :
    lassoChecker.run 3 (Lasso.checkpoint (execCompile succXYFormula) succLasso) =
      (succLasso.stem, .exhausted succAfterStem) ∧
      lassoChecker.run 2 succAfterStem =
        ([(canonicalLetter, succBlankCode)], .exhausted succAfterLoopEdge) ∧
      lassoChecker.run (3 + 2) (Lasso.checkpoint (execCompile succXYFormula) succLasso) =
        (succLasso.stem ++ [(canonicalLetter, succBlankCode)], .exhausted succAfterLoopEdge) ∧
      (lassoChecker.run 2 succAfterStem).1.length = 1 ∧
      (lassoChecker.run 3 (Lasso.checkpoint (execCompile succXYFormula) succLasso)).1.length = 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

end CheckedLasso

#print axioms execCompile_iff
#print axioms execDecide_iff
#print axioms execDecide
#print axioms execCompile
#print axioms execDecide_eq
#print axioms control_exec_bot_eval
#print axioms control_exec_not_bot_eval
#print axioms control_exec_succ
#print axioms control_exec_succ_self
#print axioms control_exec_mem
#print axioms control_exec_not_eq
#print axioms execCompile_sat_iff_checkedLasso
#print axioms control_checked_exInd_not_bot
#print axioms control_checked_exInd_bot
#print axioms control_exec_eq_lasso_check
#print axioms control_exec_eq_lasso_run
#print axioms control_exec_succ_lasso_check
#print axioms control_exec_succ_lasso_run
#print axioms control_exec_succ_nonclosing
#print axioms control_exec_succ_wrong_edge
#print axioms control_exec_succ_split

/-! ## From a Büchi automaton to a formula

`toMSO A` binds one set for each state of a finite nondeterministic Büchi
automaton. A word satisfies that formula when those sets are the positions of
an accepting run. Satisfaction is the `sat` relation above. Acceptance is
`Accepts` from `BuchiAutomaton`.
-/

def msoImp {f s : Nat} (φ ψ : MSO f s) : MSO f s := .or (.not φ) ψ

def allInd {f s : Nat} (φ : MSO (f + 1) s) : MSO f s := .not (.exInd (.not φ))

def allSet {f s : Nat} (φ : MSO f (s + 1)) : MSO f s := .not (.exSet (.not φ))

def finOr {f s : Nat} : {n : Nat} → (Fin n → MSO f s) → MSO f s
  | 0, _ => .bot
  | _ + 1, φ => .or (φ 0) (finOr (fun i => φ i.succ))

def finAnd {f s : Nat} : {n : Nat} → (Fin n → MSO f s) → MSO f s
  | 0, _ => .not .bot
  | _ + 1, φ => .and (φ 0) (finAnd (fun i => φ i.succ))

theorem sat_msoImp {f s : Nat} (φ ψ : MSO f s) (w : Nat → Letter f s) :
    sat (msoImp φ ψ) w ↔ sat φ w → sat ψ w := by
  constructor
  · intro h hs
    rw [msoImp, sat, sat] at h
    rcases h with hn | ht
    · exact absurd hs hn
    · exact ht
  · intro h
    rw [msoImp, sat, sat]
    by_cases hs : sat φ w
    · exact Or.inr (h hs)
    · exact Or.inl hs

theorem sat_allInd {f s : Nat} (φ : MSO (f + 1) s) (w : Nat → Letter f s) :
    sat (allInd φ) w ↔ ∀ b, exactlyOne b → sat φ (envInd w b) := by
  constructor
  · intro h b hb
    by_contra hn
    apply h
    refine ⟨b, hb, ?_⟩
    rw [sat]
    exact hn
  · intro h hex
    rcases hex with ⟨b, hb, hs⟩
    rw [sat] at hs
    exact hs (h b hb)

theorem sat_allSet {f s : Nat} (φ : MSO f (s + 1)) (w : Nat → Letter f s) :
    sat (allSet φ) w ↔ ∀ b, sat φ (envSet w b) := by
  constructor
  · intro h b
    by_contra hn
    apply h
    refine ⟨b, ?_⟩
    rw [sat]
    exact hn
  · intro h hex
    rcases hex with ⟨b, hs⟩
    rw [sat] at hs
    exact hs (h b)

theorem sat_finOr {f s : Nat} :
    ∀ {n : Nat} (φ : Fin n → MSO f s) (w : Nat → Letter f s),
      sat (finOr φ) w ↔ ∃ i, sat (φ i) w := by
  intro n
  induction n with
  | zero =>
      intro φ w
      constructor
      · intro h
        simp [finOr, sat] at h
      · intro ⟨i, _⟩
        exact i.elim0
  | succ n ih =>
      intro φ w
      constructor
      · intro h
        rw [finOr, sat] at h
        rcases h with h0 | hr
        · exact ⟨0, h0⟩
        · obtain ⟨i, hi⟩ := (ih (fun i => φ i.succ) w).mp hr
          exact ⟨i.succ, hi⟩
      · intro ⟨i, hi⟩
        rw [finOr, sat]
        induction i using Fin.cases with
        | zero => exact Or.inl hi
        | succ i => exact Or.inr ((ih (fun j => φ j.succ) w).mpr ⟨i, hi⟩)

theorem sat_finAnd {f s : Nat} :
    ∀ {n : Nat} (φ : Fin n → MSO f s) (w : Nat → Letter f s),
      sat (finAnd φ) w ↔ ∀ i, sat (φ i) w := by
  intro n
  induction n with
  | zero =>
      intro φ w
      constructor
      · intro _ i
        exact i.elim0
      · intro _
        simp [finAnd, sat]
  | succ n ih =>
      intro φ w
      constructor
      · intro h i
        rw [finAnd, sat] at h
        induction i using Fin.cases with
        | zero => exact h.1
        | succ i => exact (ih (fun j => φ j.succ) w).mp h.2 i
      · intro h
        rw [finAnd, sat]
        refine ⟨h 0, (ih (fun j => φ j.succ) w).mpr (fun i => h i.succ)⟩

theorem thePos_at (k : Nat) : thePos (exactlyOne_at k) = k :=
  ((thePos_spec (exactlyOne_at k)).2 k (by simp)).symm

theorem thePos_eq_of_true {b : Nat → Bool} (hb : exactlyOne b) {k : Nat}
    (hk : b k = true) : thePos hb = k :=
  ((thePos_spec hb).2 k hk).symm

theorem forall_ge_closed_iff (t u : Nat) :
    (∀ b : Nat → Bool,
      b t = true → (∀ m, b m = true → b (m + 1) = true) → b u = true) ↔ t ≤ u := by
  constructor
  · intro h
    by_contra hle
    have hlt : u < t := Nat.not_le.mp hle
    let b : Nat → Bool := fun m => decide (t ≤ m)
    have ht : b t = true := by simp [b]
    have hcl : ∀ m, b m = true → b (m + 1) = true := by
      intro m hm
      have htm : t ≤ m := of_decide_eq_true (by simpa [b] using hm)
      simp [b, Nat.le_succ_of_le htm]
    have hu : b u = true := h b ht hcl
    have htu : t ≤ u := of_decide_eq_true (by simpa [b] using hu)
    exact Nat.not_le.mpr hlt htu
  · intro hle b ht hcl
    obtain ⟨k, hk⟩ := Nat.le.dest hle
    have hb : b (t + k) = true := by
      clear hk
      induction k with
      | zero => exact ht
      | succ k ih => exact hcl (t + k) ih
    rw [hk] at hb
    exact hb

theorem no_pred_iff (b : Nat → Bool) (hb : exactlyOne b) :
    (¬ ∃ c : Nat → Bool, exactlyOne c ∧ ∃ n, c n = true ∧ b (n + 1) = true) ↔
      thePos hb = 0 := by
  constructor
  · intro h
    match hpos : thePos hb with
    | 0 => rfl
    | t + 1 =>
        exfalso
        apply h
        refine ⟨fun n => decide (n = t), exactlyOne_at t, t, by simp, ?_⟩
        have hbpos : b (thePos hb) = true := (thePos_spec hb).1
        simpa [hpos] using hbpos
  · intro h0 ⟨_, _, n, hn, hb1⟩
    have hpos : n + 1 = thePos hb := (thePos_spec hb).2 (n + 1) hb1
    rw [h0] at hpos
    exact Nat.succ_ne_zero n hpos

theorem sat_mem_singleton {g s : Nat} (V : Nat → Letter g s) (p : Fin g) (X : Fin s)
    (hp : exactlyOne (bit V p)) :
    sat (.mem p X) V ↔ setBit V X (thePos hp) = true := by
  constructor
  · intro ⟨t, ht, hX⟩
    have htpos : t = thePos hp := (thePos_spec hp).2 t ht
    simpa [htpos] using hX
  · intro hX
    exact ⟨thePos hp, (thePos_spec hp).1, hX⟩

theorem sat_eq_singleton {g s : Nat} (V : Nat → Letter g s) (p i : Fin g)
    (hp : exactlyOne (bit V p)) :
    sat (.eq p i) V ↔ bit V i (thePos hp) = true := by
  constructor
  · intro ⟨t, ht, hi⟩
    have htpos : t = thePos hp := (thePos_spec hp).2 t ht
    simpa [htpos] using hi
  · intro hi
    exact ⟨thePos hp, (thePos_spec hp).1, hi⟩

theorem sat_succ_pair {g s : Nat} (V : Nat → Letter g s) (p q : Fin g)
    (hp : exactlyOne (bit V p)) (hq : exactlyOne (bit V q)) :
    sat (.succ p q) V ↔ thePos hq = thePos hp + 1 := by
  constructor
  · intro ⟨t, hpbit, hqbit⟩
    have ht : t = thePos hp := (thePos_spec hp).2 t hpbit
    have ht1 : t + 1 = thePos hq := (thePos_spec hq).2 (t + 1) hqbit
    rw [← ht1, ht]
  · intro h
    refine ⟨thePos hp, (thePos_spec hp).1, ?_⟩
    rw [← h]
    exact (thePos_spec hq).1

theorem bit_p {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool) :
    bit (envInd (envInd w bp) bq) (1 : Fin (f + 2)) = bp := by
  have hidx : (1 : Fin (f + 2)) = (0 : Fin (f + 1)).succ := by
    apply Fin.ext
    rfl
  rw [hidx, bit_envInd_succ, bit_envInd_zero]

theorem bit_q {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool) :
    bit (envInd (envInd w bp) bq) 0 = bq :=
  bit_envInd_zero (envInd w bp) bq

theorem bit_free2 {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool) (i : Fin f) :
    bit (envInd (envInd w bp) bq) i.succ.succ = bit w i := by
  rw [bit_envInd_succ, bit_envInd_succ]

theorem setBit_envInd2 {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool) (X : Fin s) :
    setBit (envInd (envInd w bp) bq) X = setBit w X := by
  rw [setBit_envInd, setBit_envInd]

theorem exactly_bit_zero {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool)
    (hb : exactlyOne b) : exactlyOne (bit (envInd w b) 0) := by
  simpa [bit_envInd_zero] using hb

theorem pos_bit_zero {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool)
    (hb : exactlyOne b) :
    thePos (exactly_bit_zero w b hb) = thePos hb := by
  have ht : bit (envInd w b) 0 (thePos hb) = true := by
    simpa [bit_envInd_zero] using (thePos_spec hb).1
  exact ((thePos_spec (exactly_bit_zero w b hb)).2 _ ht).symm

theorem exactly_bit_p {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool)
    (hp : exactlyOne bp) : exactlyOne (bit (envInd (envInd w bp) bq) 1) := by
  simpa [bit_p w bp bq] using hp

theorem pos_bit_p {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool)
    (hp : exactlyOne bp) :
    thePos (exactly_bit_p w bp bq hp) = thePos hp := by
  have ht : bit (envInd (envInd w bp) bq) 1 (thePos hp) = true := by
    simpa [bit_p w bp bq] using (thePos_spec hp).1
  exact ((thePos_spec (exactly_bit_p w bp bq hp)).2 _ ht).symm

theorem exactly_bit_q {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool)
    (hq : exactlyOne bq) : exactlyOne (bit (envInd (envInd w bp) bq) 0) := by
  simpa [bit_q w bp bq] using hq

theorem pos_bit_q {f s : Nat} (w : Nat → Letter f s) (bp bq : Nat → Bool)
    (hq : exactlyOne bq) :
    thePos (exactly_bit_q w bp bq hq) = thePos hq := by
  have ht : bit (envInd (envInd w bp) bq) 0 (thePos hq) = true := by
    simpa [bit_q w bp bq] using (thePos_spec hq).1
  exact ((thePos_spec (exactly_bit_q w bp bq hq)).2 _ ht).symm

def isZero {f s : Nat} : MSO (f + 1) s :=
  .not (.exInd (.succ 0 1))

theorem sat_isZero {f s : Nat} (w : Nat → Letter f s) (b : Nat → Bool) (hb : exactlyOne b) :
    sat isZero (envInd w b) ↔ thePos hb = 0 := by
  rw [isZero, sat]
  constructor
  · intro h
    apply (no_pred_iff b hb).mp
    intro ⟨c, hc, n, hn, hb1⟩
    apply h
    refine ⟨c, hc, ?_⟩
    rw [sat]
    refine ⟨n, ?_, ?_⟩
    · exact (congrFun (bit_q w b c) n).trans hn
    · exact (congrFun (bit_p w b c) (n + 1)).trans hb1
  · intro h0 ⟨c, hc, hs⟩
    rw [sat] at hs
    obtain ⟨n, hn, hb1⟩ := hs
    apply (no_pred_iff b hb).mpr h0
    refine ⟨c, hc, n, ?_, ?_⟩
    · exact (congrFun (bit_q w b c) n).symm.trans hn
    · exact (congrFun (bit_p w b c) (n + 1)).symm.trans hb1

def succClosed {g s : Nat} : MSO g (s + 1) :=
  allInd (allInd
    (msoImp
      (.and (.mem (1 : Fin (g + 2)) 0) (.succ (1 : Fin (g + 2)) 0))
      (.mem (0 : Fin (g + 2)) 0)))

theorem sat_succClosed {g s : Nat} (V : Nat → Letter g (s + 1)) :
    sat succClosed V ↔ ∀ m, setBit V 0 m = true → setBit V 0 (m + 1) = true := by
  rw [succClosed, sat_allInd]
  constructor
  · intro h m hm
    let bx : Nat → Bool := fun n => decide (n = m)
    let by_ : Nat → Bool := fun n => decide (n = m + 1)
    have hbx : exactlyOne bx := exactlyOne_at m
    have hby : exactlyOne by_ := exactlyOne_at (m + 1)
    have hbody := (sat_allInd _ _).mp (h bx hbx) by_ hby
    rw [sat_msoImp] at hbody
    have hU :
        sat (.and (.mem (1 : Fin (g + 2)) 0) (.succ (1 : Fin (g + 2)) 0))
          (envInd (envInd V bx) by_) := by
      rw [sat]
      refine ⟨?_, ?_⟩
      · rw [sat_mem_singleton _ _ _ (exactly_bit_p V bx by_ hbx),
          pos_bit_p V bx by_ hbx, thePos_at, setBit_envInd2]
        exact hm
      · rw [sat_succ_pair _ _ _ (exactly_bit_p V bx by_ hbx) (exactly_bit_q V bx by_ hby),
          pos_bit_p V bx by_ hbx, pos_bit_q V bx by_ hby, thePos_at, thePos_at]
    have hmem := hbody hU
    rw [sat_mem_singleton _ _ _ (exactly_bit_q V bx by_ hby),
      pos_bit_q V bx by_ hby, thePos_at, setBit_envInd2] at hmem
    exact hmem
  · intro hcl bx hbx
    rw [sat_allInd]
    intro by_ hby
    rw [sat_msoImp]
    intro hant
    rw [sat] at hant
    rcases hant with ⟨hmem, hsucc⟩
    have hxp : exactlyOne (bit (envInd (envInd V bx) by_) 1) := exactly_bit_p V bx by_ hbx
    have hyp : exactlyOne (bit (envInd (envInd V bx) by_) 0) := exactly_bit_q V bx by_ hby
    have hposp : thePos hxp = thePos hbx := pos_bit_p V bx by_ hbx
    have hposq : thePos hyp = thePos hby := pos_bit_q V bx by_ hby
    have hmemS : setBit V 0 (thePos hbx) = true := by
      have hm := (sat_mem_singleton (envInd (envInd V bx) by_) (1 : Fin (g + 2)) 0 hxp).mp hmem
      rw [setBit_envInd2, hposp] at hm
      exact hm
    have hshift : thePos hby = thePos hbx + 1 := by
      have hs :=
        (sat_succ_pair (envInd (envInd V bx) by_) (1 : Fin (g + 2)) 0 hxp hyp).mp hsucc
      rw [hposp, hposq] at hs
      exact hs
    rw [sat_mem_singleton (envInd (envInd V bx) by_) 0 0 hyp, setBit_envInd2, hposq, hshift]
    exact hcl _ hmemS

def gePos {g s : Nat} (p q : Fin g) : MSO g s :=
  allSet (msoImp (.and (.mem p 0) succClosed) (.mem q 0))

theorem sat_gePos {g s : Nat} (W : Nat → Letter g s) (p q : Fin g)
    (hp : exactlyOne (bit W p)) (hq : exactlyOne (bit W q)) :
    sat (gePos p q) W ↔ thePos hp ≤ thePos hq := by
  rw [gePos, sat_allSet]
  constructor
  · intro h
    apply (forall_ge_closed_iff (thePos hp) (thePos hq)).mp
    intro bZ hbZ hcl
    have hV := h bZ
    rw [sat_msoImp] at hV
    have hbitp : bit (envSet W bZ) p = bit W p := bit_envSet W bZ p
    have hbitq : bit (envSet W bZ) q = bit W q := bit_envSet W bZ q
    have hpV : exactlyOne (bit (envSet W bZ) p) := by simpa [hbitp] using hp
    have hqV : exactlyOne (bit (envSet W bZ) q) := by simpa [hbitq] using hq
    have hposp : thePos hpV = thePos hp := by
      have ht : bit (envSet W bZ) p (thePos hp) = true := by
        simpa [hbitp] using (thePos_spec hp).1
      exact ((thePos_spec hpV).2 _ ht).symm
    have hposq : thePos hqV = thePos hq := by
      have ht : bit (envSet W bZ) q (thePos hq) = true := by
        simpa [hbitq] using (thePos_spec hq).1
      exact ((thePos_spec hqV).2 _ ht).symm
    have hant :
        sat (.and (.mem p 0) (succClosed (g := g) (s := s))) (envSet W bZ) := by
      rw [sat]
      refine ⟨?_, ?_⟩
      · rw [sat_mem_singleton _ _ _ hpV, hposp, setBit_envSet_zero]
        exact hbZ
      · rw [sat_succClosed, setBit_envSet_zero]
        exact hcl
    have hmem := hV hant
    rw [sat_mem_singleton _ _ _ hqV, hposq, setBit_envSet_zero] at hmem
    exact hmem
  · intro hle bZ
    rw [sat_msoImp]
    intro hant
    rw [sat] at hant
    rcases hant with ⟨hmem, hclosed⟩
    have hbitp : bit (envSet W bZ) p = bit W p := bit_envSet W bZ p
    have hbitq : bit (envSet W bZ) q = bit W q := bit_envSet W bZ q
    have hpV : exactlyOne (bit (envSet W bZ) p) := by simpa [hbitp] using hp
    have hqV : exactlyOne (bit (envSet W bZ) q) := by simpa [hbitq] using hq
    have hposp : thePos hpV = thePos hp := by
      have ht : bit (envSet W bZ) p (thePos hp) = true := by
        simpa [hbitp] using (thePos_spec hp).1
      exact ((thePos_spec hpV).2 _ ht).symm
    have hposq : thePos hqV = thePos hq := by
      have ht : bit (envSet W bZ) q (thePos hq) = true := by
        simpa [hbitq] using (thePos_spec hq).1
      exact ((thePos_spec hqV).2 _ ht).symm
    rw [sat_mem_singleton _ _ _ hpV, setBit_envSet_zero, hposp] at hmem
    rw [sat_succClosed, setBit_envSet_zero] at hclosed
    rw [sat_mem_singleton _ _ _ hqV, setBit_envSet_zero, hposq]
    exact (forall_ge_closed_iff (thePos hp) (thePos hq)).mpr hle _ hmem hclosed

def stateIx {s n : Nat} (i : Fin n) : Fin (s + n) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_left n s)⟩

def setFree {s n : Nat} (j : Fin s) : Fin (s + n) :=
  ⟨n + j.val, Nat.lt_of_lt_of_eq (Nat.add_lt_add_left j.isLt n) (Nat.add_comm n s)⟩

theorem stateIx_zero {s n : Nat} :
    stateIx (s := s) (0 : Fin (n + 1)) = 0 := by
  apply Fin.ext
  rfl

theorem stateIx_succ {s n : Nat} (i : Fin n) :
    stateIx (s := s) i.succ = (stateIx (s := s) i).succ := by
  apply Fin.ext
  rfl

theorem setFree_base {s : Nat} (j : Fin s) : setFree (n := 0) j = j := by
  apply Fin.ext
  change (0 + j.val) = j.val
  exact Nat.zero_add j.val

theorem setFree_succ {s n : Nat} (j : Fin s) :
    setFree (n := n + 1) j = (setFree (n := n) j).succ := by
  apply Fin.ext
  show (n + 1) + j.val = (n + j.val) + 1
  rw [Nat.add_assoc, Nat.add_comm 1 j.val, ← Nat.add_assoc]

def pushLabs {f s : Nat} (w : Nat → Letter f s) :
    {n : Nat} → (Fin n → Nat → Bool) → Nat → Letter f (s + n)
  | 0, _ => w
  | _ + 1, labs => envSet (pushLabs w (fun i => labs i.succ)) (labs 0)

def quantSets {f s : Nat} : {n : Nat} → MSO f (s + n) → MSO f s
  | 0, φ => φ
  | _ + 1, φ => quantSets (.exSet φ)

theorem setBit_push_state {f s : Nat} (w : Nat → Letter f s) :
    ∀ {n : Nat} (labs : Fin n → Nat → Bool) (i : Fin n),
      setBit (pushLabs w labs) (stateIx i) = labs i := by
  intro n
  induction n with
  | zero =>
      intro _ i
      exact i.elim0
  | succ n ih =>
      intro labs i
      induction i using Fin.cases with
      | zero =>
          rw [pushLabs, stateIx_zero, setBit_envSet_zero]
      | succ i =>
          rw [pushLabs, stateIx_succ, setBit_envSet_succ]
          exact ih (fun j => labs j.succ) i

theorem setBit_push_free {f s : Nat} (w : Nat → Letter f s) :
    ∀ {n : Nat} (labs : Fin n → Nat → Bool) (j : Fin s),
      setBit (pushLabs w labs) (setFree j) = setBit w j := by
  intro n
  induction n with
  | zero =>
      intro _ j
      rw [pushLabs, setFree_base]
  | succ n ih =>
      intro labs j
      rw [pushLabs, setFree_succ, setBit_envSet_succ]
      exact ih (fun i => labs i.succ) j

theorem bit_push {f s : Nat} (w : Nat → Letter f s) :
    ∀ {n : Nat} (labs : Fin n → Nat → Bool) (i : Fin f),
      bit (pushLabs w labs) i = bit w i := by
  intro n
  induction n with
  | zero =>
      intro _ i
      rw [pushLabs]
  | succ n ih =>
      intro labs i
      rw [pushLabs, bit_envSet]
      exact ih (fun j => labs j.succ) i

theorem sat_quantSets {f s : Nat} :
    ∀ {n : Nat} (φ : MSO f (s + n)) (w : Nat → Letter f s),
      sat (quantSets φ) w ↔ ∃ labs : Fin n → Nat → Bool, sat φ (pushLabs w labs) := by
  intro n
  induction n with
  | zero =>
      intro φ w
      constructor
      · intro h
        exact ⟨fun i => i.elim0, by simpa [quantSets, pushLabs] using h⟩
      · intro ⟨_, h⟩
        simpa [quantSets, pushLabs] using h
  | succ n ih =>
      intro φ w
      rw [quantSets, ih]
      constructor
      · intro ⟨tail, htail⟩
        rw [sat] at htail
        obtain ⟨b, hb⟩ := htail
        refine ⟨fun i => Fin.cases b tail i, ?_⟩
        have hpush :
            pushLabs w (fun i => Fin.cases b tail i) =
              envSet (pushLabs w tail) b := by
          rw [pushLabs]
          rfl
        simpa [hpush] using hb
      · intro ⟨labs, hlabs⟩
        refine ⟨fun i => labs i.succ, ?_⟩
        rw [sat]
        refine ⟨labs 0, ?_⟩
        have hpush :
            envSet (pushLabs w (fun i => labs i.succ)) (labs 0) = pushLabs w labs := by
          rw [pushLabs]
        simpa [hpush] using hlabs

def IsPartition {n : Nat} (labs : Fin n → Nat → Bool) : Prop :=
  ∀ t, ∃ i, labs i t = true ∧ ∀ j, j ≠ i → labs j t = false

noncomputable def labelAt {n : Nat} {labs : Fin n → Nat → Bool}
    (h : IsPartition labs) (t : Nat) : Fin n :=
  Classical.choose (h t)

theorem labelAt_eq_of_true {n : Nat} {labs : Fin n → Nat → Bool}
    (h : IsPartition labs) {t : Nat} {i : Fin n} (hi : labs i t = true) :
    labelAt h t = i := by
  rcases Classical.choose_spec (h t) with ⟨_, honly⟩
  by_contra hne
  exact Bool.false_ne_true ((honly i (Ne.symm hne)).symm.trans hi)

def labsOfRun {σ : Type} {n : Nat} (e : σ ≃ Fin n) (path : Nat → σ) :
    Fin n → Nat → Bool :=
  fun i t => decide (e (path t) = i)

theorem sat_mem0_push {f s n : Nat} (w : Nat → Letter f s)
    (labs : Fin n → Nat → Bool) (b : Nat → Bool) (hb : exactlyOne b) (i : Fin n) :
    sat (.mem 0 (stateIx i)) (envInd (pushLabs w labs) b) ↔
      labs i (thePos hb) = true := by
  rw [sat_mem_singleton _ _ _ (exactly_bit_zero (pushLabs w labs) b hb),
    pos_bit_zero, setBit_envInd, setBit_push_state]

theorem sat_mem_p_push {f s n : Nat} (w : Nat → Letter f s)
    (labs : Fin n → Nat → Bool) (bp bq : Nat → Bool) (hp : exactlyOne bp) (i : Fin n) :
    sat (.mem (1 : Fin (f + 2)) (stateIx i))
      (envInd (envInd (pushLabs w labs) bp) bq) ↔
      labs i (thePos hp) = true := by
  rw [sat_mem_singleton _ _ _ (exactly_bit_p (pushLabs w labs) bp bq hp),
    pos_bit_p, setBit_envInd2, setBit_push_state]

theorem sat_mem_q_push {f s n : Nat} (w : Nat → Letter f s)
    (labs : Fin n → Nat → Bool) (bp bq : Nat → Bool) (hq : exactlyOne bq) (i : Fin n) :
    sat (.mem 0 (stateIx i)) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      labs i (thePos hq) = true := by
  rw [sat_mem_singleton _ _ _ (exactly_bit_q (pushLabs w labs) bp bq hq),
    pos_bit_q, setBit_envInd2, setBit_push_state]

def oneState {f s n : Nat} (i : Fin n) : MSO (f + 1) (s + n) :=
  .and (.mem 0 (stateIx i))
    (finAnd fun j => if j = i then .not .bot else .not (.mem 0 (stateIx j)))

def uniqueState {f s n : Nat} : MSO (f + 1) (s + n) :=
  finOr fun i => oneState i

theorem sat_oneState {f s n : Nat} (w : Nat → Letter f s)
    (labs : Fin n → Nat → Bool) (b : Nat → Bool) (hb : exactlyOne b) (i : Fin n) :
    sat (oneState i) (envInd (pushLabs w labs) b) ↔
      labs i (thePos hb) = true ∧ ∀ j, j ≠ i → labs j (thePos hb) = false := by
  rw [oneState, sat]
  rw [sat_mem0_push w labs b hb i, sat_finAnd]
  constructor
  · intro ⟨hi, hall⟩
    refine ⟨hi, ?_⟩
    intro j hne
    have hj := hall j
    rw [if_neg hne, sat] at hj
    rw [sat_mem0_push w labs b hb j] at hj
    exact (bool_ne_iff_eq_not _ true).mp hj
  · intro ⟨hi, hall⟩
    refine ⟨hi, ?_⟩
    intro j
    by_cases hji : j = i
    · simp [hji, sat]
    · rw [if_neg hji, sat]
      rw [sat_mem0_push w labs b hb j]
      intro ht
      exact Bool.false_ne_true ((hall j hji).symm.trans ht)

theorem sat_partition_iff {f s n : Nat} (w : Nat → Letter f s)
    (labs : Fin n → Nat → Bool) :
    sat (allInd (uniqueState (f := f) (s := s) (n := n))) (pushLabs w labs) ↔
      IsPartition labs := by
  rw [sat_allInd]
  constructor
  · intro h t
    let b : Nat → Bool := fun k => decide (k = t)
    have hb : exactlyOne b := exactlyOne_at t
    have huniq := h b hb
    rw [uniqueState, sat_finOr] at huniq
    obtain ⟨i, hi⟩ := huniq
    have hpos : thePos hb = t := thePos_eq_of_true hb (by simp [b])
    rw [sat_oneState w labs b hb i, hpos] at hi
    exact ⟨i, hi.1, hi.2⟩
  · intro hpart b hb
    rw [uniqueState, sat_finOr]
    obtain ⟨i, hi, honly⟩ := hpart (thePos hb)
    refine ⟨i, ?_⟩
    rw [sat_oneState w labs b hb i]
    exact ⟨hi, honly⟩

def startAtom {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ) (e : σ ≃ Fin n)
    (i : Fin n) : MSO (f + 1) (s + n) :=
  match A.start (e.symm i) with
  | true => .mem 0 (stateIx i)
  | false => .bot

def startFormula {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ) (e : σ ≃ Fin n) :
    MSO f (s + n) :=
  allInd (msoImp isZero (finOr fun i => startAtom A e i))

theorem startAtom_of_true {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) (i : Fin n) (h : A.start (e.symm i) = true) :
    startAtom A e i = .mem 0 (stateIx i) := by
  unfold startAtom
  generalize hb : A.start (e.symm i) = b
  cases b with
  | false =>
      exfalso
      exact Bool.false_ne_true (hb.symm.trans h)
  | true => rfl

theorem startAtom_of_false {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) (i : Fin n) (h : A.start (e.symm i) = false) :
    startAtom A e i = .bot := by
  unfold startAtom
  generalize hb : A.start (e.symm i) = b
  cases b with
  | false => rfl
  | true =>
      exfalso
      exact Bool.false_ne_true (h.symm.trans hb)

theorem sat_startFormula_iff {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) (w : Nat → Letter f s) (labs : Fin n → Nat → Bool) :
    sat (startFormula A e) (pushLabs w labs) ↔
      ∃ i, labs i 0 = true ∧ A.start (e.symm i) = true := by
  rw [startFormula, sat_allInd]
  constructor
  · intro h
    let b : Nat → Bool := fun k => decide (k = 0)
    have hb : exactlyOne b := exactlyOne_at 0
    have hs := h b hb
    rw [sat_msoImp] at hs
    have hpos0 : thePos hb = 0 := thePos_eq_of_true hb (by simp [b])
    have hzero : sat isZero (envInd (pushLabs w labs) b) :=
      (sat_isZero (pushLabs w labs) b hb).mpr hpos0
    have hdisj := hs hzero
    rw [sat_finOr] at hdisj
    obtain ⟨i, hi⟩ := hdisj
    cases hstart : A.start (e.symm i) with
    | true =>
        rw [startAtom_of_true A e i hstart] at hi
        have hmem := (sat_mem0_push w labs b hb i).mp hi
        rw [hpos0] at hmem
        exact ⟨i, hmem, hstart⟩
    | false =>
        rw [startAtom_of_false A e i hstart, sat] at hi
        exact hi.elim
  · intro ⟨i, hil, hstart⟩ b hb
    rw [sat_msoImp]
    intro hzero
    have hpos : thePos hb = 0 := (sat_isZero (pushLabs w labs) b hb).mp hzero
    rw [sat_finOr]
    refine ⟨i, ?_⟩
    rw [startAtom_of_true A e i hstart]
    apply (sat_mem0_push w labs b hb i).mpr
    rw [hpos]
    exact hil

def letterBit {f s n : Nat} (i : Fin f) (on : Bool) : MSO (f + 2) (s + n) :=
  match on with
  | true => .eq 1 i.succ.succ
  | false => .not (.eq 1 i.succ.succ)

def letterSet {f s n : Nat} (j : Fin s) (on : Bool) : MSO (f + 2) (s + n) :=
  match on with
  | true => .mem 1 (setFree j)
  | false => .not (.mem 1 (setFree j))

def letterAt {f s n : Nat} (a : Letter f s) : MSO (f + 2) (s + n) :=
  .and (finAnd fun i => letterBit i (a.1 i)) (finAnd fun j => letterSet j (a.2 j))

theorem sat_letterBit {f s n : Nat} (w : Nat → Letter f s) (labs : Fin n → Nat → Bool)
    (bp bq : Nat → Bool) (hp : exactlyOne bp) (i : Fin f) (on : Bool) :
    sat (letterBit i on) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      bit w i (thePos hp) = on := by
  cases on with
  | true =>
      rw [letterBit,
        sat_eq_singleton _ _ _ (exactly_bit_p (pushLabs w labs) bp bq hp),
        pos_bit_p, bit_free2, bit_push]
  | false =>
      rw [letterBit, sat,
        sat_eq_singleton _ _ _ (exactly_bit_p (pushLabs w labs) bp bq hp),
        pos_bit_p, bit_free2, bit_push]
      constructor
      · intro h
        simpa using (bool_ne_iff_eq_not _ true).mp h
      · intro h ht
        exact Bool.false_ne_true (h.symm.trans ht)

theorem sat_letterSet {f s n : Nat} (w : Nat → Letter f s) (labs : Fin n → Nat → Bool)
    (bp bq : Nat → Bool) (hp : exactlyOne bp) (j : Fin s) (on : Bool) :
    sat (letterSet j on) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      setBit w j (thePos hp) = on := by
  cases on with
  | true =>
      rw [letterSet,
        sat_mem_singleton _ _ _ (exactly_bit_p (pushLabs w labs) bp bq hp),
        pos_bit_p, setBit_envInd2, setBit_push_free]
  | false =>
      rw [letterSet, sat,
        sat_mem_singleton _ _ _ (exactly_bit_p (pushLabs w labs) bp bq hp),
        pos_bit_p, setBit_envInd2, setBit_push_free]
      constructor
      · intro h
        simpa using (bool_ne_iff_eq_not _ true).mp h
      · intro h ht
        exact Bool.false_ne_true (h.symm.trans ht)

theorem sat_letterAt {f s n : Nat} (w : Nat → Letter f s) (labs : Fin n → Nat → Bool)
    (bp bq : Nat → Bool) (hp : exactlyOne bp) (a : Letter f s) :
    sat (letterAt a) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      w (thePos hp) = a := by
  rw [letterAt, sat, sat_finAnd, sat_finAnd]
  constructor
  · intro ⟨hbits, hsets⟩
    apply Prod.ext
    · funext i
      have hi := (sat_letterBit w labs bp bq hp i (a.1 i)).mp (hbits i)
      simpa [bit] using hi
    · funext j
      have hj := (sat_letterSet w labs bp bq hp j (a.2 j)).mp (hsets j)
      simpa [setBit] using hj
  · intro hwa
    refine ⟨?_, ?_⟩
    · intro i
      rw [sat_letterBit]
      simpa [bit] using congr_fun (congrArg Prod.fst hwa) i
    · intro j
      rw [sat_letterSet]
      simpa [setBit] using congr_fun (congrArg Prod.snd hwa) j

def transAtom {f s n : Nat} (i j : Fin n) (a : Letter f s) : MSO (f + 2) (s + n) :=
  .and (.mem 1 (stateIx i)) (.and (letterAt a) (.mem 0 (stateIx j)))

theorem sat_transAtom {f s n : Nat} (w : Nat → Letter f s) (labs : Fin n → Nat → Bool)
    (bp bq : Nat → Bool) (hp : exactlyOne bp) (hq : exactlyOne bq)
    (i j : Fin n) (a : Letter f s) :
    sat (transAtom i j a) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      labs i (thePos hp) = true ∧ w (thePos hp) = a ∧ labs j (thePos hq) = true := by
  rw [transAtom, sat]
  rw [sat_mem_p_push w labs bp bq hp i]
  rw [sat]
  rw [sat_letterAt w labs bp bq hp a]
  rw [sat_mem_q_push w labs bp bq hq j]

def stepAtom {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ) (e : σ ≃ Fin n)
    (i : Fin n) (a : Letter f s) (j : Fin n) : MSO (f + 2) (s + n) :=
  match A.step (e.symm i) a (e.symm j) with
  | true => transAtom i j a
  | false => .bot

theorem stepAtom_of_true {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ) (e : σ ≃ Fin n)
    (i : Fin n) (a : Letter f s) (j : Fin n)
    (h : A.step (e.symm i) a (e.symm j) = true) :
    stepAtom A e i a j = transAtom i j a := by
  unfold stepAtom
  generalize hb : A.step (e.symm i) a (e.symm j) = b
  cases b with
  | false =>
      exfalso
      exact Bool.false_ne_true (hb.symm.trans h)
  | true => rfl

theorem stepAtom_of_false {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ) (e : σ ≃ Fin n)
    (i : Fin n) (a : Letter f s) (j : Fin n)
    (h : A.step (e.symm i) a (e.symm j) = false) :
    stepAtom A e i a j = .bot := by
  unfold stepAtom
  generalize hb : A.step (e.symm i) a (e.symm j) = b
  cases b with
  | false => rfl
  | true =>
      exfalso
      exact Bool.false_ne_true (h.symm.trans hb)

theorem sat_stepAtom {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ) (e : σ ≃ Fin n)
    (w : Nat → Letter f s) (labs : Fin n → Nat → Bool) (bp bq : Nat → Bool)
    (i : Fin n) (a : Letter f s) (j : Fin n) :
    sat (stepAtom A e i a j) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      A.step (e.symm i) a (e.symm j) = true ∧
        sat (transAtom i j a) (envInd (envInd (pushLabs w labs) bp) bq) := by
  by_cases hstep : A.step (e.symm i) a (e.symm j) = true
  · rw [stepAtom_of_true A e i a j hstep]
    constructor
    · intro h
      exact ⟨hstep, h⟩
    · intro ⟨_, h⟩
      exact h
  · have hfalse : A.step (e.symm i) a (e.symm j) = false := Bool.eq_false_iff.mpr hstep
    rw [stepAtom_of_false A e i a j hfalse, sat]
    constructor
    · intro h
      exact h.elim
    · intro ⟨h, _⟩
      exact Bool.false_ne_true (hfalse.symm.trans h)

noncomputable def stepDisj {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) : MSO (f + 2) (s + n) :=
  finOr fun i =>
    finOr fun aIx : Fin (Fintype.card (Letter f s)) =>
      finOr fun j => stepAtom A e i ((Fintype.equivFin (Letter f s)).symm aIx) j

theorem sat_stepDisj_iff {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) (w : Nat → Letter f s) (labs : Fin n → Nat → Bool)
    (bp bq : Nat → Bool) (hp : exactlyOne bp) (hq : exactlyOne bq) :
    sat (stepDisj A e) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      ∃ i j, labs i (thePos hp) = true ∧ labs j (thePos hq) = true ∧
        A.step (e.symm i) (w (thePos hp)) (e.symm j) = true := by
  rw [stepDisj, sat_finOr]
  constructor
  · intro ⟨i, hi⟩
    rw [sat_finOr] at hi
    obtain ⟨aIx, ha⟩ := hi
    rw [sat_finOr] at ha
    obtain ⟨j, hj⟩ := ha
    let a := (Fintype.equivFin (Letter f s)).symm aIx
    rw [sat_stepAtom A e w labs bp bq i a j] at hj
    rcases hj with ⟨hstep, htrans⟩
    rw [sat_transAtom w labs bp bq hp hq i j a] at htrans
    rcases htrans with ⟨hil, hletter, hjl⟩
    refine ⟨i, j, hil, hjl, ?_⟩
    rw [← hletter] at hstep
    exact hstep
  · intro ⟨i, j, hil, hjl, hstep⟩
    let eL := Fintype.equivFin (Letter f s)
    have ha : eL.symm (eL (w (thePos hp))) = w (thePos hp) := eL.symm_apply_apply _
    refine ⟨i, ?_⟩
    rw [sat_finOr]
    refine ⟨eL (w (thePos hp)), ?_⟩
    rw [sat_finOr]
    refine ⟨j, ?_⟩
    rw [sat_stepAtom A e w labs bp bq i (eL.symm (eL (w (thePos hp)))) j]
    refine ⟨?_, ?_⟩
    · rw [ha]
      exact hstep
    · rw [sat_transAtom w labs bp bq hp hq i j (eL.symm (eL (w (thePos hp))))]
      exact ⟨hil, ha.symm, hjl⟩

noncomputable def stepFormula {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) : MSO f (s + n) :=
  allInd (allInd (msoImp (.succ 1 0) (stepDisj A e)))

theorem sat_stepFormula_iff {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) (w : Nat → Letter f s) (labs : Fin n → Nat → Bool) :
    sat (stepFormula A e) (pushLabs w labs) ↔
      ∀ t, ∃ i j, labs i t = true ∧ labs j (t + 1) = true ∧
        A.step (e.symm i) (w t) (e.symm j) = true := by
  rw [stepFormula, sat_allInd]
  constructor
  · intro h t
    let bp : Nat → Bool := fun k => decide (k = t)
    let bq : Nat → Bool := fun k => decide (k = t + 1)
    have hbp : exactlyOne bp := exactlyOne_at t
    have hbq : exactlyOne bq := exactlyOne_at (t + 1)
    have hinner := h bp hbp
    rw [sat_allInd] at hinner
    have hbody := hinner bq hbq
    rw [sat_msoImp] at hbody
    have hpt : thePos hbp = t := thePos_eq_of_true hbp (by simp [bp])
    have hqt : thePos hbq = t + 1 := thePos_eq_of_true hbq (by simp [bq])
    have hsucc :
        sat (.succ (1 : Fin (f + 2)) 0) (envInd (envInd (pushLabs w labs) bp) bq) := by
      have hpbit := exactly_bit_p (pushLabs w labs) bp bq hbp
      have hqbit := exactly_bit_q (pushLabs w labs) bp bq hbq
      apply (sat_succ_pair (envInd (envInd (pushLabs w labs) bp) bq)
        (1 : Fin (f + 2)) 0 hpbit hqbit).mpr
      rw [pos_bit_p (pushLabs w labs) bp bq hbp, pos_bit_q (pushLabs w labs) bp bq hbq,
        hpt, hqt]
    have hdisj := hbody hsucc
    have hrun := (sat_stepDisj_iff A e w labs bp bq hbp hbq).mp hdisj
    rw [hpt, hqt] at hrun
    exact hrun
  · intro h bp hbp
    rw [sat_allInd]
    intro bq hbq
    rw [sat_msoImp]
    intro hsucc
    have hpbit := exactly_bit_p (pushLabs w labs) bp bq hbp
    have hqbit := exactly_bit_q (pushLabs w labs) bp bq hbq
    have hshift := (sat_succ_pair (envInd (envInd (pushLabs w labs) bp) bq)
      (1 : Fin (f + 2)) 0 hpbit hqbit).mp hsucc
    rw [pos_bit_p (pushLabs w labs) bp bq hbp, pos_bit_q (pushLabs w labs) bp bq hbq] at hshift
    rw [sat_stepDisj_iff A e w labs bp bq hbp hbq, hshift]
    exact h (thePos hbp)

def acceptAtom {f s n : Nat} (acc : Fin n → Bool) (i : Fin n) : MSO (f + 2) (s + n) :=
  match acc i with
  | true => .mem 0 (stateIx i)
  | false => .bot

def infAccept {f s n : Nat} (acc : Fin n → Bool) : MSO f (s + n) :=
  allInd (.exInd (.and (gePos (1 : Fin (f + 2)) 0) (finOr fun i => acceptAtom acc i)))

theorem sat_acceptAtom {f s n : Nat} (w : Nat → Letter f s) (labs : Fin n → Nat → Bool)
    (bp bq : Nat → Bool) (hq : exactlyOne bq) (acc : Fin n → Bool) (i : Fin n) :
    sat (acceptAtom acc i) (envInd (envInd (pushLabs w labs) bp) bq) ↔
      acc i = true ∧ labs i (thePos hq) = true := by
  cases hacc : acc i with
  | true =>
      rw [acceptAtom, hacc, sat_mem_q_push]
      constructor
      · intro h
        exact ⟨rfl, h⟩
      · intro ⟨_, h⟩
        exact h
  | false =>
      rw [acceptAtom, hacc, sat]
      constructor
      · intro h
        exact h.elim
      · intro ⟨h, _⟩
        exact Bool.false_ne_true h

theorem sat_infAccept_iff {f s n : Nat} (w : Nat → Letter f s) (labs : Fin n → Nat → Bool)
    (acc : Fin n → Bool) :
    sat (infAccept acc) (pushLabs w labs) ↔
      ∀ t, ∃ u, t ≤ u ∧ ∃ i, labs i u = true ∧ acc i = true := by
  rw [infAccept, sat_allInd]
  constructor
  · intro h t
    let bp : Nat → Bool := fun k => decide (k = t)
    have hbp : exactlyOne bp := exactlyOne_at t
    obtain ⟨bq, hbq, hbody⟩ := h bp hbp
    rw [sat] at hbody
    rcases hbody with ⟨hge, hacc⟩
    have hpbit := exactly_bit_p (pushLabs w labs) bp bq hbp
    have hqbit := exactly_bit_q (pushLabs w labs) bp bq hbq
    have hle0 := (sat_gePos (envInd (envInd (pushLabs w labs) bp) bq)
      (1 : Fin (f + 2)) 0 hpbit hqbit).mp hge
    have hposp : thePos hpbit = thePos hbp := pos_bit_p (pushLabs w labs) bp bq hbp
    have hposq : thePos hqbit = thePos hbq := pos_bit_q (pushLabs w labs) bp bq hbq
    have hpt : thePos hbp = t := thePos_eq_of_true hbp (by simp [bp])
    have hle : t ≤ thePos hbq := by
      rw [hposp, hposq, hpt] at hle0
      exact hle0
    rw [sat_finOr] at hacc
    obtain ⟨i, hi⟩ := hacc
    have hacc' := (sat_acceptAtom w labs bp bq hbq acc i).mp hi
    exact ⟨thePos hbq, hle, i, hacc'.2, hacc'.1⟩
  · intro h bp hbp
    obtain ⟨u, hle, i, hil, hacc⟩ := h (thePos hbp)
    let bq : Nat → Bool := fun k => decide (k = u)
    have hbq : exactlyOne bq := exactlyOne_at u
    refine ⟨bq, hbq, ?_⟩
    rw [sat]
    refine ⟨?_, ?_⟩
    · have hpbit := exactly_bit_p (pushLabs w labs) bp bq hbp
      have hqbit := exactly_bit_q (pushLabs w labs) bp bq hbq
      apply (sat_gePos (envInd (envInd (pushLabs w labs) bp) bq)
        (1 : Fin (f + 2)) 0 hpbit hqbit).mpr
      rw [pos_bit_p (pushLabs w labs) bp bq hbp, pos_bit_q (pushLabs w labs) bp bq hbq]
      have hqu : thePos hbq = u := thePos_eq_of_true hbq (by simp [bq])
      rw [hqu]
      exact hle
    · rw [sat_finOr]
      refine ⟨i, (sat_acceptAtom w labs bp bq hbq acc i).mpr ?_⟩
      refine ⟨hacc, ?_⟩
      have hqu : thePos hbq = u := thePos_eq_of_true hbq (by simp [bq])
      rw [hqu]
      exact hil

/-- Sets coding a run of `A` on `w`: one label at each position, a start label at
time `0`, a transition on the letter actually read, and accepting labels beyond
every time. -/
def CodingRun {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ) (e : σ ≃ Fin n)
    (w : Nat → Letter f s) (labs : Fin n → Nat → Bool) : Prop :=
  IsPartition labs ∧
    (∃ i, labs i 0 = true ∧ A.start (e.symm i) = true) ∧
      (∀ t, ∃ i j, labs i t = true ∧ labs j (t + 1) = true ∧
        A.step (e.symm i) (w t) (e.symm j) = true) ∧
        (∀ t, ∃ u, t ≤ u ∧ ∃ i, labs i u = true ∧ A.accept (e.symm i) = true)

noncomputable def runMatrix {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) : MSO f (s + n) :=
  .and (allInd (uniqueState (f := f) (s := s) (n := n)))
    (.and (startFormula A e)
      (.and (stepFormula A e) (infAccept (fun i => A.accept (e.symm i)))))

theorem sat_runMatrix_iff {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) (w : Nat → Letter f s) (labs : Fin n → Nat → Bool) :
    sat (runMatrix A e) (pushLabs w labs) ↔ CodingRun A e w labs := by
  rw [runMatrix, sat, sat, sat]
  constructor
  · intro ⟨hpart, hstart, hstep, hinf⟩
    exact ⟨(sat_partition_iff w labs).mp hpart, (sat_startFormula_iff A e w labs).mp hstart,
      (sat_stepFormula_iff A e w labs).mp hstep,
      (sat_infAccept_iff w labs (fun i => A.accept (e.symm i))).mp hinf⟩
  · intro ⟨hpart, hstart, hstep, hinf⟩
    exact ⟨(sat_partition_iff w labs).mpr hpart, (sat_startFormula_iff A e w labs).mpr hstart,
      (sat_stepFormula_iff A e w labs).mpr hstep,
      (sat_infAccept_iff w labs (fun i => A.accept (e.symm i))).mpr hinf⟩

theorem accepts_iff_coding {f s n : Nat} {σ : Type} (A : NBA (Letter f s) σ)
    (e : σ ≃ Fin n) (w : Nat → Letter f s) :
    Accepts A w ↔ ∃ labs, CodingRun A e w labs := by
  constructor
  · intro ⟨path, hstart, hstep, hacc⟩
    refine ⟨labsOfRun e path, ?_, ?_, ?_, ?_⟩
    · intro t
      refine ⟨e (path t), ?_, ?_⟩
      · rw [labsOfRun, decide_eq_true_iff]
      · intro j hne
        rw [labsOfRun, decide_eq_false_iff_not]
        exact hne.symm
    · refine ⟨e (path 0), ?_, ?_⟩
      · rw [labsOfRun, decide_eq_true_iff]
      · rw [Equiv.symm_apply_apply]
        exact hstart
    · intro t
      refine ⟨e (path t), e (path (t + 1)), ?_, ?_, ?_⟩
      · rw [labsOfRun, decide_eq_true_iff]
      · rw [labsOfRun, decide_eq_true_iff]
      · rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hstep t
    · intro t
      obtain ⟨u, hle, hu⟩ := hacc t
      refine ⟨u, hle, e (path u), ?_, ?_⟩
      · rw [labsOfRun, decide_eq_true_iff]
      · rw [Equiv.symm_apply_apply]
        exact hu
  · intro ⟨labs, hpart, hstart, hstep, hinf⟩
    refine ⟨fun t => e.symm (labelAt hpart t), ?_, ?_, ?_⟩
    · obtain ⟨i, hil, hst⟩ := hstart
      simpa [labelAt_eq_of_true hpart hil] using hst
    · intro t
      obtain ⟨i, j, hil, hjl, hst⟩ := hstep t
      simpa [labelAt_eq_of_true hpart hil, labelAt_eq_of_true hpart hjl] using hst
    · intro lower
      obtain ⟨u, hle, i, hil, hu⟩ := hinf lower
      exact ⟨u, hle, by simpa [labelAt_eq_of_true hpart hil] using hu⟩

/-- A formula of monadic second-order logic of one successor for `A`. The bound
sets are the states of an accepting run. -/
noncomputable def toMSO {f s : Nat} {σ : Type} [Fintype σ] (A : NBA (Letter f s) σ) :
    MSO f s :=
  quantSets (runMatrix A (Fintype.equivFin σ))

theorem toMSO_iff {f s : Nat} {σ : Type} [Fintype σ] (A : NBA (Letter f s) σ)
    (w : Nat → Letter f s) : sat (toMSO A) w ↔ Accepts A w := by
  rw [toMSO, sat_quantSets, accepts_iff_coding A (Fintype.equivFin σ)]
  constructor
  · intro ⟨labs, h⟩
    exact ⟨labs, (sat_runMatrix_iff A (Fintype.equivFin σ) w labs).mp h⟩
  · intro ⟨labs, h⟩
    exact ⟨labs, (sat_runMatrix_iff A (Fintype.equivFin σ) w labs).mpr h⟩

def loopLetter : NBA (Letter 0 0) Unit where
  step _ _ _ := true
  start _ := true
  accept _ := true

def stuckLetter : NBA (Letter 0 0) Unit where
  step _ _ _ := false
  start _ := true
  accept _ := true

def seeOnce : NBA (Letter 0 1) (Fin 2) where
  start q := decide (q = 0)
  accept q := decide (q = 1)
  step q a q' :=
    match q, a.2 0, q' with
    | 0, false, 0 => true
    | 0, true, 1 => true
    | 1, _, 1 => true
    | _, _, _ => false

def seeWord : Nat → Letter 0 1 :=
  fun n => ⟨Fin.elim0, fun _ => decide (n = 0)⟩

def seePath : Nat → Fin 2 :=
  fun n => if n = 0 then 0 else 1

def neverWord : Nat → Letter 0 1 :=
  fun _ => ⟨Fin.elim0, fun _ => false⟩

theorem control_toMSO_loop : sat (toMSO loopLetter) canonicalWord := by
  rw [toMSO_iff]
  refine ⟨fun _ => (), rfl, fun _ => rfl, fun lower => ⟨lower, Nat.le_refl _, rfl⟩⟩

theorem control_toMSO_stuck : ¬ sat (toMSO stuckLetter) canonicalWord := by
  rw [toMSO_iff]
  intro ⟨_, _, hstep, _⟩
  exact Bool.false_ne_true (hstep 0)

theorem control_toMSO_see : sat (toMSO seeOnce) seeWord := by
  rw [toMSO_iff]
  refine ⟨seePath, ?_, ?_, ?_⟩
  · simp [seeOnce, seePath]
  · intro n
    by_cases hn : n = 0
    · simp [seeOnce, seeWord, seePath, hn]
    · simp [seeOnce, seeWord, seePath, hn]
  · intro lower
    refine ⟨lower + 1, Nat.le_succ _, ?_⟩
    simp [seeOnce, seePath]

theorem control_toMSO_never : ¬ sat (toMSO seeOnce) neverWord := by
  rw [toMSO_iff]
  intro ⟨path, hstart, hstep, hacc⟩
  have hpath : ∀ n, path n = 0 := by
    intro n
    induction n with
    | zero =>
        exact of_decide_eq_true (by simpa [seeOnce] using hstart)
    | succ n ih =>
        have hs := hstep n
        rw [ih] at hs
        match hq : path (n + 1) with
        | 0 => rfl
        | 1 =>
            rw [hq] at hs
            simp [seeOnce, neverWord] at hs
  obtain ⟨visit, _, hv⟩ := hacc 0
  simp [seeOnce, hpath visit] at hv

#print axioms compileMSO_iff
#print axioms decideMSO_iff
#print axioms msoBubble_iff
#print axioms control_mso_bot
#print axioms control_mso_not_bot
#print axioms control_mso_succ
#print axioms control_mso_succ_self
#print axioms control_mso_mem
#print axioms control_mso_not_eq
#print axioms toMSO_iff
#print axioms control_toMSO_loop
#print axioms control_toMSO_stuck
#print axioms control_toMSO_see
#print axioms control_toMSO_never


end Mettapedia.Logic.Arithmetic.ExS1S
