import Mettapedia.Logic.ReverseMathematics.Syntax

/-!
# The systems RCA₀ and ACA₀ and their ω-models

The axioms are formulas of `L₂` (or of an extension by a signature):

* `basicAxioms`: the eight basic axioms of Simpson §I.2 about `0`, `1`, `+`,
  `·` and `<`.
* `indInstance φ`: the induction instance
  `(φ(0) ∧ ∀n (φ(n) → φ(n+1))) → ∀n φ(n)`, where number variable `0` of `φ`
  is the induction variable and the others are parameters.
* `comprehension φ`: `∃X ∀n (n ∈ X ↔ φ(n))`, where `X` is not free in `φ`.
* `deltaComprehension φ ψ`: `∀n (φ(n) ↔ ψ(n)) → ∃X ∀n (n ∈ X ↔ φ(n))`.
* `setInduction`: the second-order induction axiom.

`RCA0` is the basic axioms with `Σ⁰₁` induction and `Δ⁰₁` comprehension
(Simpson §II.1); `ACA0` is the basic axioms with
the induction axiom and arithmetical comprehension (Simpson §III.1).

## ω-models

In an ω-model the numbers are the standard ones, so the basic axioms and
every induction instance hold (`satisfies_basicAxioms`,
`satisfies_indInstance`, `satisfies_setInduction`). What remains is
comprehension:

* `models_RCA0_iff`: `S` is an ω-model of `RCA₀` exactly when it is nonempty
  and closed under sets `Δ⁰₁`-definable with parameters from `S`.
* `models_ACA0_iff`: `S` is an ω-model of `ACA₀` exactly when it is nonempty
  and closed under sets arithmetically definable with parameters from `S`.
* `models_RCA0_of_models_ACA0`: every ω-model of `ACA₀` is an ω-model of
  `RCA₀`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Formula Term

variable {σ : Signature}

/-! ## The axioms -/

/-- The basic axioms (Simpson §I.2): `n+1 ≠ 0`, `m+1 = n+1 → m = n`,
`m+0 = m`, `m+(n+1) = (m+n)+1`, `m·0 = 0`, `m·(n+1) = m·n+m`, `¬ m < 0`,
`m < n+1 ↔ (m < n ∨ m = n)`. -/
def basicAxioms : Set (Formula σ) :=
  { all (not (eq (add (var 0) one) zero)),
    all (all (imp (eq (add (var 1) one) (add (var 0) one)) (eq (var 1) (var 0)))),
    all (eq (add (var 0) zero) (var 0)),
    all (all (eq (add (var 1) (add (var 0) one)) (add (add (var 1) (var 0)) one))),
    all (eq (mul (var 0) zero) zero),
    all (all (eq (mul (var 1) (add (var 0) one)) (add (mul (var 1) (var 0)) (var 1)))),
    all (not (lt (var 0) zero)),
    all (all (iff (lt (var 1) (add (var 0) one)) (or (lt (var 1) (var 0)) (eq (var 1) (var 0))))) }

/-- The induction instance of `φ` in its number variable `0`. -/
def indInstance (φ : Formula σ) : Formula σ :=
  imp (and (all (imp (eq (var 0) zero) φ))
        (all (imp φ (all (imp (eq (var 0) (add (var 1) one)) (φ.renameNum (liftRen Nat.succ)))))))
    (all φ)

/-- The comprehension instance of `φ` in its number variable `0`; the new set
variable does not occur in `φ`. -/
def comprehension (φ : Formula σ) : Formula σ :=
  exSet (all (iff (mem (var 0) 0) (φ.renameSet Nat.succ)))

/-- The `Δ⁰₁` comprehension instance for the pair `(φ, ψ)`. -/
def deltaComprehension (φ ψ : Formula σ) : Formula σ :=
  imp (all (iff φ ψ)) (comprehension φ)

/-- The second-order induction axiom. -/
def setInduction : Formula σ :=
  allSet (imp (and (mem zero 0) (all (imp (mem (var 0) 0) (mem (add (var 0) one) 0))))
    (all (mem (var 0) 0)))

/-- The `Σ⁰₁` induction scheme. -/
def sigma1Induction : Set (Formula σ) :=
  {χ | ∃ φ, IsSigma 1 φ ∧ χ = indInstance φ}

/-- The `Δ⁰₁` comprehension scheme. -/
def delta1Comprehension : Set (Formula σ) :=
  {χ | ∃ φ ψ, IsSigma 1 φ ∧ IsPi 1 ψ ∧ χ = deltaComprehension φ ψ}

/-- The `Σ⁰₁` comprehension scheme. -/
def sigma1Comprehension : Set (Formula σ) :=
  {χ | ∃ φ, IsSigma 1 φ ∧ χ = comprehension φ}

/-- The arithmetical comprehension scheme. -/
def arithComprehension : Set (Formula σ) :=
  {χ | ∃ φ, IsArithmetical φ ∧ χ = comprehension φ}

/-- `RCA₀`: basic axioms, `Σ⁰₁` induction, `Δ⁰₁` comprehension. -/
def RCA0 : Set (Formula σ) :=
  basicAxioms ∪ sigma1Induction ∪ delta1Comprehension

/-- `ACA₀`: basic axioms, the induction axiom, arithmetical comprehension. -/
def ACA0 : Set (Formula σ) :=
  basicAxioms ∪ {setInduction} ∪ arithComprehension

/-! ## Meaning in an ω-model -/

theorem holds_indInstance (S : Set (Set ℕ)) (φ : Formula σ) (v : ℕ → ℕ) (V : ℕ → Set ℕ) :
    Holds S (indInstance φ) v V ↔
      ((Holds S φ (Env.cons 0 v) V ∧
          ∀ n, Holds S φ (Env.cons n v) V → Holds S φ (Env.cons (n + 1) v) V) →
        ∀ n, Holds S φ (Env.cons n v) V) := by
  simp only [indInstance, Holds, Term.eval, Env.cons_zero, Env.cons_succ,
    holds_renameNum, Env.cons_comp_liftRen, Env.cons_comp_succ]
  constructor
  · intro h ⟨base, step⟩
    exact h ⟨fun z same => same ▸ base, fun n holds m same => same ▸ step n holds⟩
  · intro h ⟨base, step⟩
    exact h ⟨base 0 rfl, fun n holds => step n holds (n + 1) rfl⟩

/-- **Every induction instance holds in every ω-model.** -/
theorem satisfies_indInstance (S : Set (Set ℕ)) (φ : Formula σ) :
    Satisfies S (indInstance φ) := by
  intro v V _
  rw [holds_indInstance]
  rintro ⟨base, step⟩ n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih

theorem holds_comprehension (S : Set (Set ℕ)) (φ : Formula σ) (v : ℕ → ℕ) (V : ℕ → Set ℕ) :
    Holds S (comprehension φ) v V ↔ ∃ X ∈ S, ∀ n, n ∈ X ↔ Holds S φ (Env.cons n v) V := by
  simp only [comprehension, Holds, holds_iff, holds_renameSet, Term.eval, Env.cons_zero,
    Env.cons_comp_succ]

theorem holds_deltaComprehension (S : Set (Set ℕ)) (φ ψ : Formula σ) (v : ℕ → ℕ)
    (V : ℕ → Set ℕ) :
    Holds S (deltaComprehension φ ψ) v V ↔
      ((∀ n, Holds S φ (Env.cons n v) V ↔ Holds S ψ (Env.cons n v) V) →
        ∃ X ∈ S, ∀ n, n ∈ X ↔ Holds S φ (Env.cons n v) V) := by
  simp only [deltaComprehension, Holds, holds_iff]
  rw [← holds_comprehension]

/-- **The second-order induction axiom holds in every ω-model.** -/
theorem satisfies_setInduction (S : Set (Set ℕ)) : Satisfies S (setInduction : Formula σ) := by
  intro v V _
  simp only [setInduction, Holds, Term.eval, Env.cons_zero]
  rintro X _ ⟨base, step⟩ n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih

/-- **The basic axioms hold in every ω-model.** -/
theorem satisfies_basicAxioms (S : Set (Set ℕ)) :
    ∀ φ ∈ (basicAxioms : Set (Formula σ)), Satisfies S φ := by
  intro φ member v V _
  simp only [basicAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Holds, Term.eval, Formula.not, Formula.iff, Nat.mul_add] <;> omega

/-- Closure under sets `Δ⁰₁`-definable with parameters from the ω-model. -/
def DeltaOneClosed (σ : Signature) (S : Set (Set ℕ)) : Prop :=
  ∀ (φ ψ : Formula σ), IsSigma 1 φ → IsPi 1 ψ → ∀ (v : ℕ → ℕ) (V : ℕ → Set ℕ),
    (∀ j, V j ∈ S) →
    (∀ n, Holds S φ (Env.cons n v) V ↔ Holds S ψ (Env.cons n v) V) →
    ∃ X ∈ S, ∀ n, n ∈ X ↔ Holds S φ (Env.cons n v) V

/-- Closure under sets arithmetically definable with parameters from the
ω-model. -/
def ArithClosed (σ : Signature) (S : Set (Set ℕ)) : Prop :=
  ∀ (φ : Formula σ), IsArithmetical φ → ∀ (v : ℕ → ℕ) (V : ℕ → Set ℕ),
    (∀ j, V j ∈ S) → ∃ X ∈ S, ∀ n, n ∈ X ↔ Holds S φ (Env.cons n v) V

/-- **ω-models of RCA₀ are the nonempty families closed under
`Δ⁰₁`-definability.** -/
theorem models_RCA0_iff (S : Set (Set ℕ)) :
    Models S (RCA0 : Set (Formula σ)) ↔ S.Nonempty ∧ DeltaOneClosed σ S := by
  constructor
  · rintro ⟨nonempty, sat⟩
    refine ⟨nonempty, fun φ ψ hφ hψ v V inS equiv => ?_⟩
    have := sat (deltaComprehension φ ψ) (Or.inr ⟨φ, ψ, hφ, hψ, rfl⟩) v V inS
    exact (holds_deltaComprehension S φ ψ v V).mp this equiv
  · rintro ⟨nonempty, closed⟩
    refine ⟨nonempty, fun χ member => ?_⟩
    rcases member with (basic | ⟨φ, _, rfl⟩) | ⟨φ, ψ, hφ, hψ, rfl⟩
    · exact satisfies_basicAxioms S χ basic
    · exact satisfies_indInstance S φ
    · intro v V inS
      exact (holds_deltaComprehension S φ ψ v V).mpr (closed φ ψ hφ hψ v V inS)

/-- **ω-models of ACA₀ are the nonempty families closed under arithmetical
definability.** -/
theorem models_ACA0_iff (S : Set (Set ℕ)) :
    Models S (ACA0 : Set (Formula σ)) ↔ S.Nonempty ∧ ArithClosed σ S := by
  constructor
  · rintro ⟨nonempty, sat⟩
    refine ⟨nonempty, fun φ hφ v V inS => ?_⟩
    exact (holds_comprehension S φ v V).mp (sat (comprehension φ) (Or.inr ⟨φ, hφ, rfl⟩) v V inS)
  · rintro ⟨nonempty, closed⟩
    refine ⟨nonempty, fun χ member => ?_⟩
    rcases member with (basic | single) | ⟨φ, hφ, rfl⟩
    · exact satisfies_basicAxioms S χ basic
    · rw [Set.mem_singleton_iff] at single
      subst single
      exact satisfies_setInduction S
    · intro v V inS
      exact (holds_comprehension S φ v V).mpr (closed φ hφ v V inS)

/-- **Every ω-model of ACA₀ is an ω-model of RCA₀.** -/
theorem models_RCA0_of_models_ACA0 {S : Set (Set ℕ)} (h : Models S (ACA0 : Set (Formula σ))) :
    Models S (RCA0 : Set (Formula σ)) := by
  obtain ⟨nonempty, closed⟩ := (models_ACA0_iff S).mp h
  exact (models_RCA0_iff S).mpr
    ⟨nonempty, fun φ _ hφ _ v V inS _ => closed φ hφ.isArithmetical v V inS⟩

/-! ## Examples -/

/-- Positive example: the full power set is an ω-model of ACA₀, hence of
RCA₀. -/
theorem univ_models_ACA0 : Models (Set.univ : Set (Set ℕ)) (ACA0 : Set (Formula σ)) :=
  (models_ACA0_iff _).mpr ⟨⟨∅, trivial⟩, fun φ _ v V _ =>
    ⟨{n | Holds Set.univ φ (Env.cons n v) V}, trivial, fun _ => Iff.rfl⟩⟩

theorem univ_models_RCA0 : Models (Set.univ : Set (Set ℕ)) (RCA0 : Set (Formula σ)) :=
  models_RCA0_of_models_ACA0 univ_models_ACA0

/-- The `Σ⁰₁` and `Π⁰₁` forms of `n = n`, with a vacuous quantifier. -/
def trivialSigma : Formula σ := ex (eq (var 1) (var 1))

def trivialPi : Formula σ := all (eq (var 1) (var 1))

/-- Negative example: `{∅}` is not an ω-model of RCA₀, because `Δ⁰₁`
comprehension for `n = n` asks for the set of all numbers. -/
theorem singleton_empty_not_models_RCA0 :
    ¬ Models ({∅} : Set (Set ℕ)) (RCA0 : Set (Formula σ)) := by
  intro h
  obtain ⟨_, closed⟩ := (models_RCA0_iff _).mp h
  obtain ⟨X, member, spec⟩ := closed trivialSigma trivialPi
    (isSigma_one_iff.mpr ⟨_, .eq _ _, rfl⟩) (isPi_one_iff.mpr ⟨_, .eq _ _, rfl⟩)
    (fun _ => 0) (fun _ => ∅) (fun _ => rfl)
    (fun n => by simp [trivialSigma, trivialPi, Holds])
  rw [Set.mem_singleton_iff] at member
  subst member
  exact (spec 0).mpr ⟨0, rfl⟩

#print axioms models_RCA0_iff
#print axioms models_ACA0_iff
#print axioms models_RCA0_of_models_ACA0
#print axioms satisfies_indInstance

end Mettapedia.Logic.ReverseMathematics
