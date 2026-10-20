import Mathlib.Logic.Basic
import Mathlib.Computability.Halting

/-!
# Omniscience principles: constructive reverse mathematics

Constructive reverse mathematics classifies theorems by the logical
principles they imply over intuitionistic logic (H. Ishihara, *Reverse
mathematics in Bishop's constructive mathematics*, Philosophia Scientiae
CS 6, 2006; H. Diener, *Constructive Reverse Mathematics*, arXiv:1804.05495).
The basic scale is made of omniscience principles about Boolean sequences:

* `LPO`: every sequence has a `true` entry or is constantly `false`;
* `WLPO`: every sequence is constantly `false` or not;
* `LLPO`: for a sequence with at most one `true` entry, the even entries or
  the odd entries are all `false`;
* `MP` (Markov's principle): a sequence that is not constantly `false` has a
  `true` entry.

Lean's logic is classical, so every one of them is provable in Lean
(`lpo_of_em`, `lpo_classical`). The content is in the implications between
them. They are proved below without `Classical.choice` (for the excluded
middle) and without `propext`: `#print axioms` lists no axioms at all, which
certifies each proof as an intuitionistic argument.

* `wlpo_of_lpo`, `llpo_of_wlpo`, `llpo_of_lpo`, `mp_of_lpo`;
* `lpo_of_wlpo_of_mp` and `lpo_iff_wlpo_and_mp`: LPO is WLPO together with MP;
* `lpo_of_em`: excluded middle, as an explicit hypothesis, gives LPO.

The converse implications fail in suitable models of intuitionistic
mathematics (realizability, Kripke and topological models; see Diener's
survey and M. Hendtlass, R. Lubarsky, *Separating fragments of WLEM, LPO,
and MP*, J. Symbolic Logic 81 (2016)). Those models are
not formalized here. Lean's classical logic proves every principle, so it is
no model in which a principle fails.

Formalizations of the same principles elsewhere, consulted for their
statements: M. Escardó, TypeTopology (Agda), modules `Taboos.LPO`,
`Taboos.WLPO`, `Taboos.LLPO`, `Taboos.MarkovsPrinciple`; the Saarland Coq
developments on Markov's principle and omniscience (Forster, Kirst, Smolka,
CPP 2019; Cohen, Forster, Kirst, Da Rocha Paiva, Rahli, *Separating Markov's
principles*, LICS 2024).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics.Omniscience

/-- The limited principle of omniscience. -/
def LPO : Prop :=
  ∀ α : ℕ → Bool, (∃ n, α n = true) ∨ ∀ n, α n = false

/-- The weak limited principle of omniscience. -/
def WLPO : Prop :=
  ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ ¬ ∀ n, α n = false

/-- At most one entry is `true`. -/
def AtMostOneTrue (α : ℕ → Bool) : Prop :=
  ∀ m n, α m = true → α n = true → m = n

/-- The lesser limited principle of omniscience. -/
def LLPO : Prop :=
  ∀ α : ℕ → Bool, AtMostOneTrue α → (∀ n, α (2 * n) = false) ∨ ∀ n, α (2 * n + 1) = false

/-- Markov's principle. -/
def MP : Prop :=
  ∀ α : ℕ → Bool, ¬ (∀ n, α n = false) → ∃ n, α n = true

/-- A Boolean is `false` or `true`, intuitionistically. -/
private theorem bool_cases (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem ne_false_of_true {b : Bool} (h : b = true) : b ≠ false := by
  cases h
  exact Bool.noConfusion

/-- An even number is not odd, by structural recursion. -/
private theorem two_mul_ne_two_mul_add_one' : ∀ m n : ℕ, 2 * m ≠ 2 * n + 1
  | 0, _, h => Nat.noConfusion h
  | m + 1, 0, h => by
      have : Nat.succ (2 * m + 1) = Nat.succ 0 := h
      exact Nat.noConfusion (Nat.succ.inj this)
  | m + 1, n + 1, h => by
      have : Nat.succ (Nat.succ (2 * m)) = Nat.succ (Nat.succ (2 * n + 1)) := h
      exact two_mul_ne_two_mul_add_one' m n (Nat.succ.inj (Nat.succ.inj this))

/-- **LPO implies WLPO.** -/
theorem wlpo_of_lpo (lpo : LPO) : WLPO := by
  intro α
  rcases lpo α with ⟨n, hn⟩ | all
  · exact Or.inr fun all => ne_false_of_true hn (all n)
  · exact Or.inl all

/-- **WLPO implies LLPO.** -/
theorem llpo_of_wlpo (wlpo : WLPO) : LLPO := by
  intro α atMostOne
  rcases wlpo (fun n => α (2 * n)) with evens | notEvens
  · exact Or.inl evens
  · refine Or.inr fun n => ?_
    rcases bool_cases (α (2 * n + 1)) with h | h
    · exact h
    · refine absurd (fun m => ?_) notEvens
      rcases bool_cases (α (2 * m)) with h' | h'
      · exact h'
      · exact absurd (atMostOne _ _ h' h) (two_mul_ne_two_mul_add_one' m n)

/-- **LPO implies LLPO.** -/
theorem llpo_of_lpo (lpo : LPO) : LLPO :=
  llpo_of_wlpo (wlpo_of_lpo lpo)

/-- **LPO implies Markov's principle.** -/
theorem mp_of_lpo (lpo : LPO) : MP := by
  intro α notAll
  rcases lpo α with found | all
  · exact found
  · exact absurd all notAll

/-- **WLPO and Markov's principle together give LPO.** -/
theorem lpo_of_wlpo_of_mp (wlpo : WLPO) (mp : MP) : LPO := by
  intro α
  rcases wlpo α with all | notAll
  · exact Or.inr all
  · exact Or.inl (mp α notAll)

/-- **LPO is exactly WLPO and Markov's principle.** -/
theorem lpo_iff_wlpo_and_mp : LPO ↔ WLPO ∧ MP :=
  ⟨fun lpo => ⟨wlpo_of_lpo lpo, mp_of_lpo lpo⟩, fun ⟨wlpo, mp⟩ => lpo_of_wlpo_of_mp wlpo mp⟩

/-- Excluded middle, as an explicit hypothesis, gives LPO. -/
theorem lpo_of_em (em : ∀ p : Prop, p ∨ ¬ p) : LPO := by
  intro α
  rcases em (∃ n, α n = true) with found | none
  · exact Or.inl found
  · refine Or.inr fun n => ?_
    rcases bool_cases (α n) with h | h
    · exact h
    · exact absurd ⟨n, h⟩ none

/-- In Lean's classical logic LPO is a theorem; this proof uses
`Classical.choice`. -/
theorem lpo_classical : LPO :=
  lpo_of_em Classical.em

/-- Markov's principle in its double-negation form. -/
theorem mp_iff_dne_exists :
    MP ↔ ∀ α : ℕ → Bool, ¬ ¬ (∃ n, α n = true) → ∃ n, α n = true := by
  constructor
  · intro mp α notNot
    refine mp α fun all => notNot fun ⟨n, hn⟩ => ne_false_of_true hn (all n)
  · intro dne α notAll
    refine dne α fun none => notAll fun n => ?_
    rcases bool_cases (α n) with h | h
    · exact h
    · exact absurd ⟨n, h⟩ none

/-! ## The computable reading: Markov's principle holds, LPO and WLPO fail

Read each principle uniformly over computable sequences: one computable
procedure must produce the disjunct (for LPO, WLPO) or the witness (for MP)
from a code of the sequence. This is the reading of Kleene realizability.

* `computableMP`: the unbounded search for a `true` entry is one partial
  computable procedure, and it succeeds on every computable sequence that is
  not constantly `false`. Its termination is argued classically, as in the
  standard realizability argument for Markov's principle.
* `not_computableLPO`, `not_computableWLPO`: no computable procedure decides
  LPO or WLPO uniformly, since either would decide the halting problem
  (Mathlib's `ComputablePred.halting_problem`), through the s-m-n function
  `Nat.Partrec.Code.curry`.

With the soundness of realizability for Heyting arithmetic (not formalized
here), this gives the classical separation `HA + MP ⊬ LPO`.
-/

open Nat.Partrec

/-- The code `c` computes the Boolean sequence `α`, with `true` as `1`. -/
def ComputesSeq (c : Code) (α : ℕ → Bool) : Prop :=
  ∀ n, c.eval n = Part.some (bif α n then 1 else 0)

/-- The computable reading of LPO. -/
def ComputableLPO : Prop :=
  ∃ F : Code → Bool, Computable F ∧
    ∀ c α, ComputesSeq c α → (F c = true ↔ ∃ n, α n = true)

/-- The computable reading of WLPO. -/
def ComputableWLPO : Prop :=
  ∃ F : Code → Bool, Computable F ∧
    ∀ c α, ComputesSeq c α → (F c = true ↔ ∀ n, α n = false)

/-- The computable reading of Markov's principle. -/
def ComputableMP : Prop :=
  ∃ G : Code →. ℕ, Partrec G ∧
    ∀ c α, ComputesSeq c α → ¬ (∀ n, α n = false) → ∃ n ∈ G c, α n = true

/-- `1` when code `p.1` halts on input `0` within `p.2` steps. -/
def haltBit (p : Code × ℕ) : ℕ :=
  bif (Code.evaln p.2 p.1 0).isSome then 1 else 0

theorem haltBit_primrec : Primrec haltBit :=
  Primrec.cond (Primrec.option_isSome.comp (Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.snd Primrec.fst) (Primrec.const 0))))
    (Primrec.const 1) (Primrec.const 0)

/-- Codes of the halting-time sequences, computed uniformly. -/
theorem exists_halting_codes : ∃ h : Code → Code, Computable h ∧
    ∀ d, ComputesSeq (h d) fun n => (Code.evaln n d 0).isSome := by
  have uncurried : Primrec fun m : ℕ =>
      haltBit (Denumerable.ofNat Code (Nat.unpair m).1, (Nat.unpair m).2) :=
    haltBit_primrec.comp (Primrec.pair
      ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair))
  obtain ⟨e, he⟩ := Code.exists_code.mp (Partrec.nat_iff.mp uncurried.to_comp.partrec)
  refine ⟨fun d => Code.curry e (Encodable.encode d),
    (Code.primrec₂_curry.comp (Primrec.const e) Primrec.encode).to_comp, fun d n => ?_⟩
  rw [Code.eval_curry, he]
  simp [haltBit, Denumerable.ofNat_encode]

theorem halts_iff_exists_haltBit (d : Code) :
    (Code.eval d 0).Dom ↔ ∃ n, (Code.evaln n d 0).isSome = true := by
  constructor
  · intro dom
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp (Part.get_mem dom)
    rw [Option.mem_def] at hk
    exact ⟨k, by simp [hk]⟩
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hn
    exact Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound hx⟩

/-- **LPO has no computable reading.** -/
theorem not_computableLPO : ¬ ComputableLPO := by
  classical
  rintro ⟨F, hF, spec⟩
  obtain ⟨h, hh, codes⟩ := exists_halting_codes
  apply ComputablePred.halting_problem 0
  refine ⟨inferInstance, (hF.comp hh).of_eq fun d => ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  show _ ↔ (Code.eval d 0).Dom
  rw [spec _ _ (codes d), halts_iff_exists_haltBit]

/-- **WLPO has no computable reading.** -/
theorem not_computableWLPO : ¬ ComputableWLPO := by
  classical
  rintro ⟨F, hF, spec⟩
  obtain ⟨h, hh, codes⟩ := exists_halting_codes
  apply ComputablePred.halting_problem 0
  refine ⟨inferInstance, (Primrec.not.to_comp.comp (hF.comp hh)).of_eq fun d => ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  show _ ↔ (Code.eval d 0).Dom
  rw [halts_iff_exists_haltBit]
  have := spec _ _ (codes d)
  cases hFd : F (h d)
  · simp only [Bool.not_false, true_iff]
    rw [hFd] at this
    by_contra none
    push Not at none
    exact Bool.false_ne_true (this.mpr fun n => by simpa using none n)
  · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists]
    rw [hFd] at this
    intro n
    simpa using this.mp rfl n

/-- **Markov's principle has a computable reading.** -/
theorem computableMP : ComputableMP := by
  classical
  refine ⟨fun c => Nat.rfind fun n => (c.eval n).map fun v => v == 1, ?_, ?_⟩
  · exact Partrec.rfind (Code.eval_part.map
      (Primrec.beq.comp Primrec.snd (Primrec.const 1)).to₂.to_comp)
  · intro c α computes notAll
    have found : ∃ n, α n = true := by
      by_contra none
      push Not at none
      exact notAll fun n => by simpa using none n
    obtain ⟨m, hm⟩ := found
    obtain ⟨n₀, mem, _⟩ := Nat.rfind_min' (p := fun n => (bif α n then 1 else 0) == 1) (m := m)
      (by simp [hm])
    refine ⟨n₀, ?_, ?_⟩
    · have same : (fun n => (c.eval n).map fun v => v == 1) =
          fun n => Part.some ((bif α n then 1 else 0) == 1) := by
        funext n
        simp [computes n]
      show n₀ ∈ Nat.rfind fun n => (c.eval n).map fun v => v == 1
      rw [same]
      exact mem
    · have := Nat.rfind_spec mem
      cases h : α n₀ <;> simp_all

/-- **In the computable reading, Markov's principle holds and LPO fails.** -/
theorem computableMP_and_not_computableLPO : ComputableMP ∧ ¬ ComputableLPO :=
  ⟨computableMP, not_computableLPO⟩

/-! ## Examples -/

/-- Positive example of `AtMostOneTrue`: the sequence true only at `3`. -/
example : AtMostOneTrue fun n => decide (n = 3) := by
  intro m n hm hn
  simp only [decide_eq_true_eq] at hm hn
  rw [hm, hn]

/-- Negative example: the constantly true sequence has two true entries. -/
example : ¬ AtMostOneTrue fun _ => true := by
  intro h
  exact absurd (h 0 1 rfl rfl) (by decide)

/-- Each principle's disjunction, for a sequence where it can be decided by
hand: the constantly false sequence. -/
example : (∃ n : ℕ, (fun _ : ℕ => false) n = true) ∨ ∀ n : ℕ, (fun _ : ℕ => false) n = false :=
  Or.inr fun _ => rfl

#print axioms wlpo_of_lpo
#print axioms llpo_of_wlpo
#print axioms mp_of_lpo
#print axioms lpo_of_wlpo_of_mp
#print axioms lpo_iff_wlpo_and_mp
#print axioms lpo_of_em
#print axioms mp_iff_dne_exists
#print axioms lpo_classical
#print axioms not_computableLPO
#print axioms not_computableWLPO
#print axioms computableMP

end Mettapedia.Logic.ReverseMathematics.Omniscience
