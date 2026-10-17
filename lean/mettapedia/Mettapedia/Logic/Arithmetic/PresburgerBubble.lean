import Mathlib.ModelTheory.Arithmetic.Presburger.Definability

/-!
# Presburger bubble

Decidable fragment of the first-order theory of the standard model `(ℕ, 0, 1, +, <)`.
Order and divisibility are included as atomic predicates because both are definable
from addition: `a < b` if and only if `∃ z, a + (z + 1) = b`, and `m ∣ t` if and
only if `∃ z, t = m * z` whenever `m ≠ 0`. The underlying language of functions is
the language `(0, 1, +)` studied by Mojżesz Presburger in *Über die Vollständigkeit
eines gewissen Systems der Arithmetik ganzer Zahlen, in welchem die Addition als
einzige Operation hervortritt* (1929). Ultimate periodicity of one-variable
definable sets is the one-dimensional form of the semilinear characterisation in
Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger Formulas, and
Languages* (1966), and Samuel Eilenberg and M. P. Schützenberger, *Rational Sets
in Commutative Monoids* (1969).

## What this bubble decides

Every closed sentence of `(ℕ, 0, 1, +, <)`. `Formula.eliminate` removes quantifiers
from the inside outward and returns a quantifier-free sentence. `Formula.decideClosed`
evaluates that sentence, so `presburgerBubble_iff_sat` identifies the verdict
`some true` with truth in the standard model. A formula that still has a free
variable receives `none`.

## Quantifier elimination

David C. Cooper, *Theorem Proving in Arithmetic without Multiplication* (1972).
For a quantifier-free `φ : Formula (n + 1)` and every environment `e : Fin n → ℕ`,
`Formula.cooper` returns a quantifier-free formula of arity `n` with the same
existential closure. Parameters are the variables that remain free, and a nested
quantifier is the same step applied to the inner formula first. The one-variable
bound `Formula.exists_iff_below` remains the certificate search used by the
witness checker.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.PresburgerBubble

/-- Coefficients of a linear term in `n` variables, variable `0` outermost. -/
inductive Coeff : Nat → Type where
  | nil : Coeff 0
  | cons : {n : Nat} → Nat → Coeff n → Coeff (n + 1)
  deriving DecidableEq, Repr

/-- `const + Σ coeffᵢ · envᵢ`. -/
structure LinTerm (n : Nat) where
  coeff : Coeff n
  const : Nat
  deriving DecidableEq, Repr

/-- Extend an environment by a value for the outermost variable. -/
def envCons {n : Nat} (x : Nat) (env : Fin n → Nat) : Fin (n + 1) → Nat :=
  Fin.cases x env

/-- The unique environment for a closed term. -/
def env0 : Fin 0 → Nat := Fin.elim0

/-- The environment that sends the single variable to `x`. -/
abbrev env1 (x : Nat) : Fin 1 → Nat := envCons x env0

def Coeff.dot : {n : Nat} → Coeff n → (Fin n → Nat) → Nat
  | _, .nil, _ => 0
  | _, .cons c cs, env => c * env 0 + cs.dot (fun i => env i.succ)

def LinTerm.eval {n : Nat} (t : LinTerm n) (env : Fin n → Nat) : Nat :=
  t.coeff.dot env + t.const

@[simp] theorem dot_nil (env : Fin 0 → Nat) : Coeff.dot .nil env = 0 := rfl

@[simp] theorem dot_cons {n : Nat} (c : Nat) (cs : Coeff n) (env : Fin (n + 1) → Nat) :
    Coeff.dot (.cons c cs) env = c * env 0 + cs.dot (fun i => env i.succ) := rfl

@[simp] theorem eval_mk {n : Nat} (coeff : Coeff n) (const : Nat) (env : Fin n → Nat) :
    LinTerm.eval ⟨coeff, const⟩ env = coeff.dot env + const := rfl

@[simp] theorem envCons_zero {n : Nat} (x : Nat) (env : Fin n → Nat) :
    envCons x env 0 = x := rfl

@[simp] theorem eval_one (c k x : Nat) :
    (LinTerm.mk (.cons c .nil) k).eval (env1 x) = c * x + k := by
  simp [LinTerm.eval, env1, envCons, Coeff.dot]

@[simp] theorem eval_closed (k : Nat) :
    (LinTerm.mk .nil k).eval env0 = k := by
  simp [LinTerm.eval, Coeff.dot]

/-- Atomic predicates. Divisibility by `0` is never true. -/
inductive Atom (n : Nat) where
  | eq (left right : LinTerm n)
  | lt (left right : LinTerm n)
  | dvd (modulus : Nat) (term : LinTerm n)
  deriving DecidableEq, Repr

def Atom.sat {n : Nat} : Atom n → (Fin n → Nat) → Prop
  | .eq left right, env => left.eval env = right.eval env
  | .lt left right, env => left.eval env < right.eval env
  | .dvd modulus term, env => modulus ≠ 0 ∧ modulus ∣ term.eval env

def Atom.holds {n : Nat} : Atom n → (Fin n → Nat) → Bool
  | .eq left right, env => left.eval env == right.eval env
  | .lt left right, env => left.eval env < right.eval env
  | .dvd modulus term, env =>
      (modulus != 0) && (modulus ∣ term.eval env)

theorem Atom.holds_iff {n : Nat} (a : Atom n) (env : Fin n → Nat) :
    a.holds env = true ↔ a.sat env := by
  cases a with
  | eq left right =>
      simp [holds, sat]
  | lt left right =>
      simp [holds, sat]
  | dvd modulus term =>
      simp [holds, sat]

/-- First-order formulas. `ex` binds the outermost variable. -/
inductive Formula : Nat → Type where
  | bot : {n : Nat} → Formula n
  | atom : {n : Nat} → Atom n → Formula n
  | conj : {n : Nat} → Formula n → Formula n → Formula n
  | neg : {n : Nat} → Formula n → Formula n
  | ex : {n : Nat} → Formula (n + 1) → Formula n
  deriving DecidableEq, Repr

def Formula.sat : {n : Nat} → Formula n → (Fin n → Nat) → Prop
  | _, .bot, _ => False
  | _, .atom a, env => a.sat env
  | _, .conj left right, env => left.sat env ∧ right.sat env
  | _, .neg body, env => ¬ body.sat env
  | _, .ex body, env => ∃ x, body.sat (envCons x env)

def Formula.quantifierFree : {n : Nat} → (φ : Formula n) → Bool
  | _, .bot => true
  | _, .atom _ => true
  | _, .conj left right =>
      Formula.quantifierFree left && Formula.quantifierFree right
  | _, .neg body => Formula.quantifierFree body
  | _, .ex _ => false
  termination_by structural _ φ => φ

def Formula.decideQF : {n : Nat} → (φ : Formula n) → (Fin n → Nat) → Bool
  | _, .bot, _ => false
  | _, .atom a, env => a.holds env
  | _, .conj left right, env =>
      Formula.decideQF left env && Formula.decideQF right env
  | _, .neg body, env => !Formula.decideQF body env
  | _, .ex _, _ => false
  termination_by structural _ φ => φ

theorem Formula.decideQF_iff {n : Nat} :
    (φ : Formula n) → (hq : φ.quantifierFree = true) → (env : Fin n → Nat) →
      (φ.decideQF env = true ↔ φ.sat env)
  | .bot, _, env => by simp [decideQF, sat]
  | .atom a, _, env => by simp [decideQF, sat, Atom.holds_iff]
  | .conj left right, hq, env => by
      have hleft : left.quantifierFree = true := by
        simp only [quantifierFree, Bool.and_eq_true] at hq
        exact hq.1
      have hright : right.quantifierFree = true := by
        simp only [quantifierFree, Bool.and_eq_true] at hq
        exact hq.2
      simp only [decideQF, sat, Bool.and_eq_true]
      exact and_congr (decideQF_iff left hleft env) (decideQF_iff right hright env)
  | .neg body, hq, env => by
      have hbody : body.quantifierFree = true := by
        simpa [quantifierFree] using hq
      simp only [decideQF, sat]
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact (decideQF_iff body hbody env).not
  | .ex _, hq, _ => by simp [quantifierFree] at hq

/-! ## One-variable ultimate periodicity -/

/-- These bounds ignore the arity: equality and order have period `1`, and
divisibility by `m ≠ 0` has period `m`. -/
def Atom.period1 : {n : Nat} → Atom n → Nat
  | _, .eq _ _ => 1
  | _, .lt _ _ => 1
  | _, .dvd modulus _ => if modulus = 0 then 1 else modulus

def Atom.threshold1 : {n : Nat} → Atom n → Nat
  | _, .eq left right => max left.const right.const + 1
  | _, .lt left right => max left.const right.const + 1
  | _, .dvd _ _ => 0

theorem Atom.period1_pos (a : Atom 1) : 0 < a.period1 := by
  cases a with
  | eq _ _ =>
      simp [period1]
  | lt _ _ =>
      simp [period1]
  | dvd modulus _ =>
      cases modulus with
      | zero =>
          simp [period1]
      | succ modulus =>
          simp only [period1, Nat.succ_ne_zero, ite_false]
          exact Nat.succ_pos modulus

/-- Variable index, so the recursion is structural and reduces in the kernel.
A fixed index `Formula 1` is compiled by well-founded recursion and does not. -/
def Formula.period1 : {n : Nat} → (φ : Formula n) → Nat
  | _, .bot => 1
  | _, .atom a => a.period1
  | _, .conj left right => Nat.lcm (Formula.period1 left) (Formula.period1 right)
  | _, .neg body => Formula.period1 body
  | _, .ex _ => 1
  termination_by structural _ φ => φ

def Formula.threshold1 : {n : Nat} → (φ : Formula n) → Nat
  | _, .bot => 0
  | _, .atom a => a.threshold1
  | _, .conj left right =>
      max (Formula.threshold1 left) (Formula.threshold1 right)
  | _, .neg body => Formula.threshold1 body
  | _, .ex _ => 0
  termination_by structural _ φ => φ

theorem Nat.pos_lcm {a b : Nat} (ha : 0 < a) (hb : 0 < b) : 0 < Nat.lcm a b := by
  have hg : Nat.gcd a b ≠ 0 := by
    intro hzero
    have hboth : a = 0 ∧ b = 0 := Nat.gcd_eq_zero_iff.mp hzero
    omega
  have hmul : 0 < a * b := Nat.mul_pos ha hb
  have hdiv : Nat.gcd a b ∣ a * b :=
    Nat.dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_mul_right a b)
  have hquot : 0 < a * b / Nat.gcd a b :=
    Nat.div_pos (Nat.le_of_dvd hmul hdiv) (Nat.pos_of_ne_zero hg)
  simpa [Nat.lcm] using hquot

theorem Formula.period1_pos : (φ : Formula 1) → 0 < φ.period1
  | .bot => by simp [period1]
  | .atom a => by simpa [period1] using a.period1_pos
  | .conj left right => by
      simpa [period1] using Nat.pos_lcm (period1_pos left) (period1_pos right)
  | .neg body => by simpa [period1] using period1_pos body
  | .ex _ => by simp [period1]

theorem periodic_step {P : Nat → Prop} {threshold step : Nat}
    (h : ∀ x, threshold ≤ x → (P x ↔ P (x + step))) :
    ∀ mult x, threshold ≤ x → (P x ↔ P (x + step * mult)) := by
  intro mult x hx
  induction mult with
  | zero => simp
  | succ mult inductionHypothesis =>
      have hgrow : threshold ≤ x + step * mult :=
        Nat.le_trans hx (Nat.le_add_right _ _)
      rw [inductionHypothesis, Nat.mul_succ, ← Nat.add_assoc]
      exact h _ hgrow

theorem periodic_of_dvd {P : Nat → Prop} {threshold step quantity : Nat}
    (hdvd : step ∣ quantity)
    (h : ∀ x, threshold ≤ x → (P x ↔ P (x + step))) :
    ∀ x, threshold ≤ x → (P x ↔ P (x + quantity)) := by
  intro x hx
  obtain ⟨mult, rfl⟩ := hdvd
  have hshift := periodic_step h mult x hx
  simpa [Nat.mul_comm] using hshift

theorem mul_add_lt_of_coeff_lt {c₁ c₂ k₁ k₂ x : Nat}
    (hcoeff : c₁ < c₂) (hx : max k₁ k₂ + 1 ≤ x) :
    c₁ * x + k₁ < c₂ * x + k₂ := by
  have hsucc : c₁ + 1 ≤ c₂ := Nat.succ_le_of_lt hcoeff
  have hk : k₁ < x + k₂ := by
    have hmax : max k₁ k₂ < x := Nat.lt_of_succ_le hx
    exact lt_of_le_of_lt (Nat.le_max_left k₁ k₂)
      (lt_of_lt_of_le hmax (Nat.le_add_right x k₂))
  have hsplit : c₁ * x + x = (c₁ + 1) * x := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one]
  have hmul : (c₁ + 1) * x ≤ c₂ * x := Nat.mul_le_mul_right x hsucc
  calc
    c₁ * x + k₁ < c₁ * x + (x + k₂) := Nat.add_lt_add_left hk _
    _ = c₁ * x + x + k₂ := by rw [← Nat.add_assoc]
    _ = (c₁ + 1) * x + k₂ := by rw [hsplit]
    _ ≤ c₂ * x + k₂ := Nat.add_le_add_right hmul _

theorem eq_periodic (c₁ k₁ c₂ k₂ : Nat) :
    ∀ x, max k₁ k₂ + 1 ≤ x →
      ((c₁ * x + k₁ = c₂ * x + k₂) ↔
        (c₁ * (x + 1) + k₁ = c₂ * (x + 1) + k₂)) := by
  intro x hx
  by_cases hcoeff : c₁ = c₂
  · subst hcoeff
    simp
  · cases Nat.lt_or_gt_of_ne hcoeff with
    | inl hlt =>
        exact iff_of_false
          (ne_of_lt (mul_add_lt_of_coeff_lt hlt hx))
          (ne_of_lt (mul_add_lt_of_coeff_lt hlt (Nat.le_trans hx (Nat.le_succ x))))
    | inr hgt =>
        have hx' : max k₂ k₁ + 1 ≤ x := by simpa [Nat.max_comm] using hx
        exact iff_of_false
          (ne_of_gt (mul_add_lt_of_coeff_lt hgt hx'))
          (ne_of_gt (mul_add_lt_of_coeff_lt hgt (Nat.le_trans hx' (Nat.le_succ x))))

theorem lt_periodic (c₁ k₁ c₂ k₂ : Nat) :
    ∀ x, max k₁ k₂ + 1 ≤ x →
      ((c₁ * x + k₁ < c₂ * x + k₂) ↔
        (c₁ * (x + 1) + k₁ < c₂ * (x + 1) + k₂)) := by
  intro x hx
  cases Nat.lt_trichotomy c₁ c₂ with
  | inl hlt =>
      exact iff_of_true
        (mul_add_lt_of_coeff_lt hlt hx)
        (mul_add_lt_of_coeff_lt hlt (Nat.le_trans hx (Nat.le_succ x)))
  | inr hrest =>
      cases hrest with
      | inl heq =>
          subst heq
          simp
      | inr hgt =>
          have hx' : max k₂ k₁ + 1 ≤ x := by simpa [Nat.max_comm] using hx
          exact iff_of_false
            (lt_asymm (mul_add_lt_of_coeff_lt hgt hx'))
            (lt_asymm (mul_add_lt_of_coeff_lt hgt (Nat.le_trans hx' (Nat.le_succ x))))

theorem dvd_shift (modulus coeff const : Nat) (hmodulus : 0 < modulus) (x : Nat) :
    (modulus ∣ coeff * x + const) ↔
      (modulus ∣ coeff * (x + modulus) + const) := by
  have hsum : coeff * (x + modulus) + const =
      coeff * x + const + coeff * modulus := by
    calc
      coeff * (x + modulus) + const = coeff * x + coeff * modulus + const := by
        rw [Nat.mul_add]
      _ = coeff * x + const + coeff * modulus := by
        omega
  have hmodMul : coeff * modulus = modulus * coeff := Nat.mul_comm _ _
  constructor
  · intro ⟨q, hq⟩
    rw [hsum, hq, hmodMul, ← Nat.mul_add]
    exact ⟨q + coeff, rfl⟩
  · intro ⟨q, hq⟩
    rw [hsum] at hq
    have hle : coeff * modulus ≤ modulus * q := by
      have : coeff * x + const + coeff * modulus = modulus * q := hq
      omega
    have hcoeff : coeff ≤ q :=
      Nat.le_of_mul_le_mul_left (by simpa [hmodMul] using hle) hmodulus
    refine ⟨q - coeff, ?_⟩
    have hrest : coeff * x + const = modulus * q - modulus * coeff := by
      omega
    rw [hrest, ← Nat.mul_sub_left_distrib]

theorem Atom.ultimately_periodic (a : Atom 1) :
    ∀ x, a.threshold1 ≤ x →
      (a.sat (env1 x) ↔ a.sat (env1 (x + a.period1))) := by
  cases a with
  | eq left right =>
      obtain ⟨c₁, k₁, rfl⟩ : ∃ c k, left = ⟨.cons c .nil, k⟩ := by
        cases left with
        | mk coeff const =>
            cases coeff with
            | cons c tail =>
                cases tail with
                | nil => exact ⟨c, const, rfl⟩
      obtain ⟨c₂, k₂, rfl⟩ : ∃ c k, right = ⟨.cons c .nil, k⟩ := by
        cases right with
        | mk coeff const =>
            cases coeff with
            | cons c tail =>
                cases tail with
                | nil => exact ⟨c, const, rfl⟩
      intro x hx
      simpa [sat, threshold1, period1, env1] using eq_periodic c₁ k₁ c₂ k₂ x hx
  | lt left right =>
      obtain ⟨c₁, k₁, rfl⟩ : ∃ c k, left = ⟨.cons c .nil, k⟩ := by
        cases left with
        | mk coeff const =>
            cases coeff with
            | cons c tail =>
                cases tail with
                | nil => exact ⟨c, const, rfl⟩
      obtain ⟨c₂, k₂, rfl⟩ : ∃ c k, right = ⟨.cons c .nil, k⟩ := by
        cases right with
        | mk coeff const =>
            cases coeff with
            | cons c tail =>
                cases tail with
                | nil => exact ⟨c, const, rfl⟩
      intro x hx
      simpa [sat, threshold1, period1, env1] using lt_periodic c₁ k₁ c₂ k₂ x hx
  | dvd modulus term =>
      obtain ⟨c, k, rfl⟩ : ∃ c k, term = ⟨.cons c .nil, k⟩ := by
        cases term with
        | mk coeff const =>
            cases coeff with
            | cons c tail =>
                cases tail with
                | nil => exact ⟨c, const, rfl⟩
      intro x _hx
      cases modulus with
      | zero =>
          simp [sat, period1]
      | succ modulus =>
          have hperiod :
              (Atom.dvd (modulus + 1) (LinTerm.mk (.cons c .nil) k)).period1 =
                modulus + 1 := by
            simp [period1]
          rw [hperiod]
          simpa [sat, env1] using
            dvd_shift (modulus + 1) c k (Nat.succ_pos modulus) x

theorem Formula.qf_ultimately_periodic :
    (φ : Formula 1) → (hq : φ.quantifierFree = true) →
      ∀ x, φ.threshold1 ≤ x →
        (φ.sat (env1 x) ↔ φ.sat (env1 (x + φ.period1)))
  | .bot, _, x, _ => by simp [sat]
  | .atom a, _, x, hx => by
      simpa [sat, threshold1, period1] using
        a.ultimately_periodic x (by simpa [threshold1] using hx)
  | .conj left right, hq, x, hx => by
      have hleft : left.quantifierFree = true := by
        simp only [quantifierFree, Bool.and_eq_true] at hq
        exact hq.1
      have hright : right.quantifierFree = true := by
        simp only [quantifierFree, Bool.and_eq_true] at hq
        exact hq.2
      have hxLeft : left.threshold1 ≤ x := by
        have hmax : left.threshold1 ≤ (left.conj right).threshold1 := by
          simp [threshold1]
        exact le_trans hmax hx
      have hxRight : right.threshold1 ≤ x := by
        have hmax : right.threshold1 ≤ (left.conj right).threshold1 := by
          simp [threshold1]
        exact le_trans hmax hx
      have hleftStep :=
        periodic_of_dvd (Nat.dvd_lcm_left left.period1 right.period1)
          (qf_ultimately_periodic left hleft) x hxLeft
      have hrightStep :=
        periodic_of_dvd (Nat.dvd_lcm_right left.period1 right.period1)
          (qf_ultimately_periodic right hright) x hxRight
      simp only [sat, period1]
      exact and_congr hleftStep hrightStep
  | .neg body, hq, x, hx => by
      have hbody : body.quantifierFree = true := by
        simpa [quantifierFree] using hq
      have hxBody : body.threshold1 ≤ x := by
        simpa [threshold1] using hx
      have hstep := qf_ultimately_periodic body hbody x hxBody
      simp only [sat, period1]
      exact not_congr hstep
  | .ex _, hq, _, _ => by simp [quantifierFree] at hq

theorem Formula.exists_iff_below (φ : Formula 1) (hq : φ.quantifierFree = true) :
    (∃ x, φ.sat (env1 x)) ↔
      ∃ x, x < φ.threshold1 + φ.period1 ∧ φ.sat (env1 x) := by
  constructor
  · intro hsat
    have hwitness : ∀ x, φ.sat (env1 x) →
        ∃ y, y < φ.threshold1 + φ.period1 ∧ φ.sat (env1 y) ∧ y ≤ x := by
      intro x
      induction x using Nat.strong_induction_on with
      | h x inductionHypothesis =>
          intro hxsat
          by_cases hsmall : x < φ.threshold1 + φ.period1
          · exact ⟨x, hsmall, hxsat, le_rfl⟩
          · have hlarge : φ.threshold1 + φ.period1 ≤ x := Nat.le_of_not_lt hsmall
            have hthreshold : φ.threshold1 ≤ x - φ.period1 := by
              omega
            have hback : φ.sat (env1 ((x - φ.period1) + φ.period1)) := by
              simpa [Nat.sub_add_cancel (le_trans (Nat.le_add_left _ _) hlarge)] using hxsat
            have hsmaller : φ.sat (env1 (x - φ.period1)) :=
              (qf_ultimately_periodic φ hq (x - φ.period1) hthreshold).mpr hback
            have hlt : x - φ.period1 < x :=
              Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.add_pos_right _ (period1_pos φ)) hlarge)
                (period1_pos φ)
            obtain ⟨y, hy, hysat, hyle⟩ := inductionHypothesis _ hlt hsmaller
            exact ⟨y, hy, hysat, le_trans hyle (Nat.sub_le _ _)⟩
    obtain ⟨x, hx⟩ := hsat
    obtain ⟨y, hy, hysat, _⟩ := hwitness x hx
    exact ⟨y, hy, hysat⟩
  · intro ⟨x, _, hx⟩
    exact ⟨x, hx⟩

/-! ## Linear combinations of parameter terms -/

def Coeff.head : {n : Nat} → Coeff (n + 1) → Nat
  | _, .cons c _ => c

def Coeff.tail : {n : Nat} → Coeff (n + 1) → Coeff n
  | _, .cons _ cs => cs

def Coeff.scale : {n : Nat} → Nat → Coeff n → Coeff n
  | _, _, .nil => .nil
  | _, k, .cons c cs => .cons (k * c) (Coeff.scale k cs)

def Coeff.add : {n : Nat} → Coeff n → Coeff n → Coeff n
  | _, .nil, .nil => .nil
  | _, .cons a as, .cons b bs => .cons (a + b) (Coeff.add as bs)

def LinTerm.param {n : Nat} (t : LinTerm (n + 1)) : LinTerm n where
  coeff := t.coeff.tail
  const := t.const

def LinTerm.addConst {n : Nat} (t : LinTerm n) (k : Nat) : LinTerm n where
  coeff := t.coeff
  const := t.const + k

def LinTerm.scale {n : Nat} (k : Nat) (t : LinTerm n) : LinTerm n where
  coeff := Coeff.scale k t.coeff
  const := k * t.const

def LinTerm.add {n : Nat} (a b : LinTerm n) : LinTerm n where
  coeff := Coeff.add a.coeff b.coeff
  const := a.const + b.const

theorem Coeff.dot_scale : {n : Nat} → (k : Nat) → (cs : Coeff n) → (env : Fin n → Nat) →
    Coeff.dot (Coeff.scale k cs) env = k * Coeff.dot cs env
  | _, _, .nil, _ => by simp [Coeff.scale, Coeff.dot]
  | _, k, .cons c cs, env => by
      simp only [Coeff.scale, dot_cons, dot_scale, Nat.mul_add, Nat.mul_assoc]

theorem Coeff.dot_add : {n : Nat} → (a b : Coeff n) → (env : Fin n → Nat) →
    Coeff.dot (Coeff.add a b) env = Coeff.dot a env + Coeff.dot b env
  | _, .nil, .nil, _ => by simp [Coeff.add, Coeff.dot]
  | _, .cons a as, .cons b bs, env => by
      simp only [Coeff.add, dot_cons, dot_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm]

theorem LinTerm.eval_param {n : Nat} (t : LinTerm (n + 1)) (x : Nat) (env : Fin n → Nat) :
    t.eval (envCons x env) = t.coeff.head * x + t.param.eval env := by
  rcases t with ⟨coeff, const⟩
  cases coeff with
  | cons c cs =>
      simp only [eval_mk, param, Coeff.head, Coeff.tail, dot_cons, envCons_zero]
      have htail : cs.dot (fun i => envCons x env i.succ) = cs.dot env := by
        congr 1
      simp only [htail, Nat.add_assoc]

theorem LinTerm.eval_addConst {n : Nat} (t : LinTerm n) (k : Nat) (env : Fin n → Nat) :
    (t.addConst k).eval env = t.eval env + k := by
  simp [LinTerm.addConst, LinTerm.eval, Nat.add_assoc]

theorem LinTerm.eval_scale {n : Nat} (k : Nat) (t : LinTerm n) (env : Fin n → Nat) :
    (t.scale k).eval env = k * t.eval env := by
  simp only [LinTerm.scale, LinTerm.eval, Coeff.dot_scale, Nat.mul_add]

theorem LinTerm.eval_add {n : Nat} (a b : LinTerm n) (env : Fin n → Nat) :
    (a.add b).eval env = a.eval env + b.eval env := by
  simp only [LinTerm.add, LinTerm.eval, Coeff.dot_add, Nat.add_assoc, Nat.add_left_comm]

theorem lt_of_head_lt {c₁ c₂ t₁ t₂ x : Nat} (h : c₁ < c₂) :
    (c₁ * x + t₁ < c₂ * x + t₂) ↔ t₁ < (c₂ - c₁) * x + t₂ := by
  have hc : c₂ = c₁ + (c₂ - c₁) := by omega
  have hsum : c₂ * x = c₁ * x + (c₂ - c₁) * x := by
    calc
      c₂ * x = (c₁ + (c₂ - c₁)) * x := by conv_lhs => rw [hc]
      _ = c₁ * x + (c₂ - c₁) * x := Nat.add_mul _ _ _
  rw [hsum, Nat.add_assoc, Nat.add_lt_add_iff_left]

theorem lt_of_head_gt {c₁ c₂ t₁ t₂ x : Nat} (h : c₂ < c₁) :
    (c₁ * x + t₁ < c₂ * x + t₂) ↔ (c₁ - c₂) * x + t₁ < t₂ := by
  have hc : c₁ = c₂ + (c₁ - c₂) := by omega
  have hsum : c₁ * x = c₂ * x + (c₁ - c₂) * x := by
    calc
      c₁ * x = (c₂ + (c₁ - c₂)) * x := by conv_lhs => rw [hc]
      _ = c₂ * x + (c₁ - c₂) * x := Nat.add_mul _ _ _
  rw [hsum, Nat.add_assoc, Nat.add_lt_add_iff_left]

theorem lt_of_head_eq {c t₁ t₂ x : Nat} :
    (c * x + t₁ < c * x + t₂) ↔ t₁ < t₂ := by
  exact Nat.add_lt_add_iff_left

theorem eq_iff_both_lt_succ (a b : Nat) :
    a = b ↔ a < b + 1 ∧ b < a + 1 := by
  omega

theorem ne_iff_lt_or_gt (a b : Nat) :
    a ≠ b ↔ a < b ∨ b < a := by
  omega

theorem dvd_add_right_iff {m a b : Nat} (hb : m ∣ b) :
    m ∣ a + b ↔ m ∣ a := by
  constructor
  · intro hab
    obtain ⟨q, hq⟩ := hab
    obtain ⟨p, hp⟩ := hb
    have hle : b ≤ a + b := Nat.le_add_left _ _
    refine ⟨q - p, ?_⟩
    have hsub : a = m * q - m * p := by omega
    rw [hsub, ← Nat.mul_sub_left_distrib]
  · intro ha
    exact Nat.dvd_add ha hb

theorem dvd_mul_residue {m c nShift j k t : Nat} (hm : m ∣ nShift) :
    (m ∣ c * (nShift * k + j) + t) ↔ (m ∣ c * j + t) := by
  have hperiod : m ∣ c * nShift * k :=
    Nat.dvd_trans hm (by
      have : nShift ∣ nShift * (c * k) := Nat.dvd_mul_right _ _
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this)
  have hsplit : c * (nShift * k + j) + t = c * j + t + c * nShift * k := by
    simp only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.mul_assoc]
  rw [hsplit]
  exact dvd_add_right_iff hperiod

theorem exists_mod_split {period : Nat} (hperiod : 0 < period) {P : Nat → Prop} :
    (∃ x, P x) ↔ ∃ j, j < period ∧ ∃ k, P (period * k + j) := by
  constructor
  · intro ⟨x, hx⟩
    refine ⟨x % period, Nat.mod_lt _ hperiod, x / period, ?_⟩
    have hsplit := Nat.div_add_mod x period
    have hcomm : period * (x / period) + x % period = x := by
      simpa [Nat.mul_comm] using hsplit
    simpa [hcomm] using hx
  · intro ⟨j, _, k, hk⟩
    exact ⟨period * k + j, hk⟩

theorem div_le_iff_le_mul {c a k : Nat} (hc : 0 < c) :
    (a + (c - 1)) / c ≤ k ↔ a ≤ c * k := by
  have hstep : (a + (c - 1)) / c ≤ k ↔ (a + (c - 1)) / c < k + 1 := by
    omega
  rw [hstep, Nat.div_lt_iff_lt_mul hc]
  have hmul : (k + 1) * c = c * k + c := by
    rw [Nat.succ_mul, Nat.mul_comm k c]
  omega

/-- Least `k` such that `α < coeff * k + β`. -/
def firstGe (coeff α β : Nat) : Nat :=
  if α < β then 0 else (α - β + coeff) / coeff

theorem firstGe_spec {coeff α β k : Nat} (hcoeff : 0 < coeff) :
    α < coeff * k + β ↔ firstGe coeff α β ≤ k := by
  by_cases hlt : α < β
  · simp only [firstGe, hlt, ite_true, Nat.zero_le, iff_true]
    exact lt_of_lt_of_le hlt (Nat.le_add_left β _)
  · simp only [firstGe, hlt, ite_false]
    have hβ : β ≤ α := Nat.le_of_not_lt hlt
    have hstrict : α < coeff * k + β ↔ α - β + 1 ≤ coeff * k := by
      omega
    have hceil :=
      (div_le_iff_le_mul (a := α - β + 1) (c := coeff) (k := k) hcoeff).symm
    have hsum : (α - β + 1) + (coeff - 1) = α - β + coeff := by
      omega
    rw [hstrict, hceil, hsum]

/-! ## Cooper elimination

David C. Cooper, *Theorem Proving in Arithmetic without Multiplication* (1972).
A quantifier-free formula is put in disjunctive normal form. Equality is two
strict inequalities, and the negation of a strict inequality is one strict
inequality. Each inequality is monotone in the outermost variable, and each
divisibility constraint is periodic of period the least common multiple of the
moduli. In a residue class it is therefore enough to test the value zero, or
the least value that meets one lower bound. Substituting that test point
removes the variable. Nested quantifiers are removed from the inside outward.
-/

theorem lowerMoved_iff {scale other α β α' β' slack k : Nat} (hscale : 0 < scale)
    (hk : scale * k + β = α + (slack + 1)) :
    α' < other * k + β' ↔
      scale * α' + other * β < other * (α + (slack + 1)) + scale * β' := by
  have hmul :=
    Nat.mul_lt_mul_left (a := scale) (b := α') (c := other * k + β') hscale
  rw [← hmul, Nat.mul_add]
  have hrhs : other * (α + (slack + 1)) = scale * (other * k) + other * β := by
    rw [← hk, Nat.mul_add]
    rw [← Nat.mul_assoc, Nat.mul_comm other scale, Nat.mul_assoc]
  rw [hrhs]
  have hassoc :
      scale * (other * k) + other * β + scale * β' =
        scale * (other * k) + scale * β' + other * β := by
    omega
  rw [hassoc]
  exact (Nat.add_lt_add_iff_right (k := other * β)).symm

theorem upperMoved_iff {scale slope α β γ δ slack k : Nat} (hscale : 0 < scale)
    (hk : scale * k + β = α + (slack + 1)) :
    slope * k + γ < δ ↔
      slope * (α + (slack + 1)) + scale * γ < scale * δ + slope * β := by
  have hmul :=
    (Nat.mul_lt_mul_left (a := scale) (b := slope * k + γ) (c := δ) hscale).symm
  rw [hmul, Nat.mul_add]
  have hre : scale * (slope * k) = slope * (scale * k) := by
    rw [← Nat.mul_assoc, Nat.mul_comm scale slope, Nat.mul_assoc]
  rw [hre]
  have hbase : slope * (α + (slack + 1)) = slope * (scale * k) + slope * β := by
    rw [← hk, Nat.mul_add]
  rw [hbase]
  have hassoc :
      slope * (scale * k) + slope * β + scale * γ =
        slope * (scale * k) + scale * γ + slope * β := by
    omega
  rw [hassoc]
  exact (Nat.add_lt_add_iff_right (k := slope * β)).symm

/-- A literal is an atom or its negation. -/
inductive Lit (n : Nat) where
  | pos : Atom n → Lit n
  | neg : Atom n → Lit n

def Lit.sat {n : Nat} : Lit n → (Fin n → Nat) → Prop
  | .pos a, env => a.sat env
  | .neg a, env => ¬ a.sat env

def Lit.formula {n : Nat} : Lit n → Formula n
  | .pos a => .atom a
  | .neg a => .neg (.atom a)

theorem Lit.formula_qf {n : Nat} (l : Lit n) : l.formula.quantifierFree = true := by
  cases l <;> simp [Lit.formula, Formula.quantifierFree]

theorem Lit.formula_iff {n : Nat} (l : Lit n) (env : Fin n → Nat) :
    l.formula.sat env ↔ l.sat env := by
  cases l <;> simp [Lit.formula, Lit.sat, Formula.sat]

/-- A constraint on the outermost variable, with parameter terms beside it. -/
inductive Constraint (n : Nat) where
  | param : Lit n → Constraint n
  | lower : Nat → LinTerm n → LinTerm n → Constraint n
  | upper : Nat → LinTerm n → LinTerm n → Constraint n
  | dvd : Nat → Nat → LinTerm n → Constraint n
  | ndvd : Nat → Nat → LinTerm n → Constraint n

def Constraint.wf {n : Nat} : Constraint n → Prop
  | .param _ => True
  | .lower coeff _ _ => 0 < coeff
  | .upper coeff _ _ => 0 < coeff
  | .dvd modulus _ _ => 0 < modulus
  | .ndvd modulus _ _ => 0 < modulus

def Constraint.holds {n : Nat} : Constraint n → Nat → (Fin n → Nat) → Prop
  | .param lit, _, env => lit.sat env
  | .lower coeff left right, x, env => left.eval env < coeff * x + right.eval env
  | .upper coeff left right, x, env => coeff * x + left.eval env < right.eval env
  | .dvd modulus coeff term, x, env =>
      modulus ≠ 0 ∧ modulus ∣ coeff * x + term.eval env
  | .ndvd modulus coeff term, x, env =>
      modulus ≠ 0 ∧ ¬ modulus ∣ coeff * x + term.eval env

def holdsAll {n : Nat} (cs : List (Constraint n)) (x : Nat) (env : Fin n → Nat) : Prop :=
  ∀ c ∈ cs, c.holds x env

def holdsSome {n : Nat} (clauses : List (List (Constraint n))) (x : Nat)
    (env : Fin n → Nat) : Prop :=
  ∃ clause ∈ clauses, holdsAll clause x env

def expandLt {n : Nat} (left right : LinTerm (n + 1)) : List (Constraint n) :=
  if left.coeff.head < right.coeff.head then
    [.lower (right.coeff.head - left.coeff.head) left.param right.param]
  else if right.coeff.head < left.coeff.head then
    [.upper (left.coeff.head - right.coeff.head) left.param right.param]
  else
    [.param (.pos (.lt left.param right.param))]

theorem expandLt_wf {n : Nat} (left right : LinTerm (n + 1)) :
    ∀ c ∈ expandLt left right, c.wf := by
  by_cases hlt : left.coeff.head < right.coeff.head
  · simp only [expandLt, hlt, ite_true, List.mem_singleton, forall_eq, Constraint.wf]
    omega
  · by_cases hgt : right.coeff.head < left.coeff.head
    · simp only [expandLt, hlt, hgt, ite_false, ite_true, List.mem_singleton, forall_eq,
        Constraint.wf]
      omega
    · simp only [expandLt, hlt, hgt, ite_false, List.mem_singleton, forall_eq, Constraint.wf]

theorem expandLt_iff {n : Nat} (left right : LinTerm (n + 1)) (x : Nat) (env : Fin n → Nat) :
    holdsAll (expandLt left right) x env ↔
      left.eval (envCons x env) < right.eval (envCons x env) := by
  have hl := LinTerm.eval_param left x env
  have hr := LinTerm.eval_param right x env
  by_cases hlt : left.coeff.head < right.coeff.head
  · simp only [holdsAll, expandLt, hlt, ite_true, List.mem_singleton, forall_eq, Constraint.holds,
      hl, hr]
    exact (lt_of_head_lt hlt).symm
  · by_cases hgt : right.coeff.head < left.coeff.head
    · simp only [holdsAll, expandLt, hlt, hgt, ite_false, ite_true, List.mem_singleton, forall_eq,
        Constraint.holds, hl, hr]
      exact (lt_of_head_gt hgt).symm
    · have heq : left.coeff.head = right.coeff.head := by omega
      simp only [holdsAll, expandLt, hlt, hgt, ite_false, List.mem_singleton, forall_eq,
        Constraint.holds, Lit.sat, Atom.sat]
      rw [hl, hr, heq]
      exact lt_of_head_eq.symm

theorem param_addConst {n : Nat} (t : LinTerm (n + 1)) (k : Nat) :
    (t.addConst k).param = t.param.addConst k :=
  rfl

def expandDvd {n : Nat} (positive : Bool) (modulus : Nat) (term : LinTerm (n + 1)) :
    List (List (Constraint n)) :=
  if modulus = 0 then
    if positive then [] else [[]]
  else if term.coeff.head = 0 then
    [[.param (if positive then .pos (.dvd modulus term.param) else .neg (.dvd modulus term.param))]]
  else if positive then
    [[.dvd modulus term.coeff.head term.param]]
  else
    [[.ndvd modulus term.coeff.head term.param]]

theorem expandDvd_wf {n : Nat} (positive : Bool) (modulus : Nat) (term : LinTerm (n + 1)) :
    ∀ clause ∈ expandDvd positive modulus term, ∀ c ∈ clause, c.wf := by
  by_cases hzero : modulus = 0
  · by_cases hp : positive = true
    · simp only [expandDvd, hzero, hp, ite_true, List.not_mem_nil, false_implies, implies_true]
    · simp only [expandDvd, hzero, hp, ite_true, Bool.false_eq_true, ite_false, List.mem_singleton,
        forall_eq]
      intro c hc
      exact (List.not_mem_nil hc).elim
  · have hpos : 0 < modulus := Nat.pos_of_ne_zero hzero
    by_cases hhead : term.coeff.head = 0
    · simp only [expandDvd, hzero, hhead, ite_false, ite_true, List.mem_singleton, forall_eq,
        Constraint.wf]
    · by_cases hp : positive = true
      · simp only [expandDvd, hzero, hhead, hp, ite_false, ite_true, List.mem_singleton, forall_eq,
          Constraint.wf, hpos]
      · simp only [expandDvd, hzero, hhead, hp, Bool.false_eq_true, ite_false, List.mem_singleton,
          forall_eq, Constraint.wf, hpos]

theorem expandDvd_iff {n : Nat} (positive : Bool) (modulus : Nat) (term : LinTerm (n + 1))
    (x : Nat) (env : Fin n → Nat) :
    holdsSome (expandDvd positive modulus term) x env ↔
      (if positive then (Atom.dvd modulus term).sat (envCons x env)
        else ¬ (Atom.dvd modulus term).sat (envCons x env)) := by
  have ht := LinTerm.eval_param term x env
  by_cases hzero : modulus = 0
  · cases positive <;>
      simp [expandDvd, holdsSome, holdsAll, Atom.sat, hzero, ht]
  · by_cases hhead : term.coeff.head = 0
    · cases positive <;>
        simp [expandDvd, holdsSome, holdsAll, Constraint.holds, Lit.sat, Atom.sat, hzero, hhead, ht]
    · cases positive <;>
        simp [expandDvd, holdsSome, holdsAll, Constraint.holds, Atom.sat, hzero, hhead, ht]

def expandAtom {n : Nat} (positive : Bool) (a : Atom (n + 1)) : List (List (Constraint n)) :=
  match a with
  | .eq left right =>
      if positive then
        [expandLt left (right.addConst 1) ++ expandLt right (left.addConst 1)]
      else
        [expandLt left right, expandLt right left]
  | .lt left right =>
      if positive then [expandLt left right] else [expandLt right (left.addConst 1)]
  | .dvd modulus term => expandDvd positive modulus term

theorem forall_append {n : Nat} {p : Constraint n → Prop} (l r : List (Constraint n)) :
    (∀ c ∈ l ++ r, p c) ↔ (∀ c ∈ l, p c) ∧ (∀ c ∈ r, p c) := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append.mpr (Or.inl hc)),
      fun c hc => h c (List.mem_append.mpr (Or.inr hc))⟩
  · intro h c hc
    rcases List.mem_append.mp hc with hl | hr
    · exact h.1 c hl
    · exact h.2 c hr

theorem expandAtom_wf {n : Nat} (positive : Bool) (a : Atom (n + 1)) :
    ∀ clause ∈ expandAtom positive a, ∀ c ∈ clause, c.wf := by
  cases a with
  | eq left right =>
      by_cases hp : positive = true
      · simp only [expandAtom, hp, ite_true, List.mem_singleton, forall_eq]
        intro c hc
        rcases List.mem_append.mp hc with hleft | hright
        · exact expandLt_wf left (right.addConst 1) c hleft
        · exact expandLt_wf right (left.addConst 1) c hright
      · simp only [expandAtom, hp, Bool.false_eq_true, ite_false, List.forall_mem_cons]
        exact ⟨expandLt_wf left right, expandLt_wf right left,
          fun _ hx => (List.not_mem_nil hx).elim⟩
  | lt left right =>
      by_cases hp : positive = true
      · simp only [expandAtom, hp, ite_true, List.mem_singleton, forall_eq]
        exact expandLt_wf left right
      · simp only [expandAtom, hp, Bool.false_eq_true, ite_false, List.mem_singleton, forall_eq]
        exact expandLt_wf right (left.addConst 1)
  | dvd modulus term =>
      simpa [expandAtom] using expandDvd_wf positive modulus term

theorem expandAtom_iff {n : Nat} (positive : Bool) (a : Atom (n + 1)) (x : Nat)
    (env : Fin n → Nat) :
    holdsSome (expandAtom positive a) x env ↔
      (if positive then a.sat (envCons x env) else ¬ a.sat (envCons x env)) := by
  cases a with
  | dvd modulus term =>
      simpa [expandAtom] using expandDvd_iff positive modulus term x env
  | lt left right =>
      by_cases hp : positive = true
      · simp only [expandAtom, hp, ite_true, holdsSome, List.mem_singleton, exists_eq_left, Atom.sat]
        exact expandLt_iff left right x env
      · simp only [expandAtom, hp, Bool.false_eq_true, ite_false, holdsSome, List.mem_singleton,
          exists_eq_left, Atom.sat]
        have hnot : ¬ left.eval (envCons x env) < right.eval (envCons x env) ↔
            right.eval (envCons x env) < left.eval (envCons x env) + 1 := by
          omega
        rw [hnot]
        have hadd := LinTerm.eval_addConst left 1 (envCons x env)
        rw [← hadd]
        exact expandLt_iff right (left.addConst 1) x env
  | eq left right =>
      by_cases hp : positive = true
      · simp only [expandAtom, hp, ite_true, holdsSome, List.mem_singleton, exists_eq_left, Atom.sat,
          holdsAll]
        rw [forall_append (p := fun c => c.holds x env)]
        have hleft := expandLt_iff left (right.addConst 1) x env
        have hright := expandLt_iff right (left.addConst 1) x env
        simp only [holdsAll] at hleft hright
        rw [hleft, hright]
        have haddL := LinTerm.eval_addConst right 1 (envCons x env)
        have haddR := LinTerm.eval_addConst left 1 (envCons x env)
        rw [haddL, haddR]
        exact (eq_iff_both_lt_succ _ _).symm
      · simp only [expandAtom, hp, Bool.false_eq_true, ite_false, holdsSome, Atom.sat]
        have hleft := expandLt_iff left right x env
        have hright := expandLt_iff right left x env
        constructor
        · rintro ⟨clause, hmem, hholds⟩
          simp only [List.mem_cons] at hmem
          intro heq
          rcases hmem with rfl | rfl | hnil
          · exact Nat.lt_irrefl _ (heq ▸ hleft.mp hholds)
          · exact Nat.lt_irrefl _ (heq ▸ hright.mp hholds)
          · exact (List.not_mem_nil hnil).elim
        · intro hne
          rcases (ne_iff_lt_or_gt _ _).mp hne with hlt | hgt
          · exact ⟨expandLt left right, List.mem_cons_self, hleft.mpr hlt⟩
          · exact ⟨expandLt right left,
              List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), hright.mpr hgt⟩

def expandLit {n : Nat} : Lit (n + 1) → List (List (Constraint n))
  | .pos a => expandAtom true a
  | .neg a => expandAtom false a

theorem expandLit_wf {n : Nat} (l : Lit (n + 1)) :
    ∀ clause ∈ expandLit l, ∀ c ∈ clause, c.wf := by
  cases l with
  | pos a => simpa [expandLit] using expandAtom_wf true a
  | neg a => simpa [expandLit] using expandAtom_wf false a

theorem expandLit_iff {n : Nat} (l : Lit (n + 1)) (x : Nat) (env : Fin n → Nat) :
    holdsSome (expandLit l) x env ↔ l.sat (envCons x env) := by
  cases l with
  | pos a =>
      simpa [expandLit, Lit.sat] using expandAtom_iff true a x env
  | neg a =>
      simpa [expandLit, Lit.sat] using expandAtom_iff false a x env

def dnfBind {n : Nat} (left right : List (List (Constraint n))) : List (List (Constraint n)) :=
  left.flatMap fun clause => right.map fun rest => clause ++ rest

theorem dnfBind_iff {n : Nat} (left right : List (List (Constraint n))) (x : Nat)
    (env : Fin n → Nat) :
    holdsSome (dnfBind left right) x env ↔ holdsSome left x env ∧ holdsSome right x env := by
  constructor
  · rintro ⟨clause, hmem, hall⟩
    rw [dnfBind, List.mem_flatMap] at hmem
    rcases hmem with ⟨base, hbase, hclause⟩
    rw [List.mem_map] at hclause
    rcases hclause with ⟨rest, hrest, rfl⟩
    obtain ⟨hL, hR⟩ :=
      (forall_append (p := fun c => c.holds x env) base rest).mp hall
    exact ⟨⟨base, hbase, hL⟩, ⟨rest, hrest, hR⟩⟩
  · rintro ⟨⟨base, hbase, hL⟩, ⟨rest, hrest, hR⟩⟩
    refine ⟨base ++ rest, ?_, (forall_append (p := fun c => c.holds x env) base rest).mpr ⟨hL, hR⟩⟩
    rw [dnfBind, List.mem_flatMap]
    exact ⟨base, hbase, List.mem_map.mpr ⟨rest, hrest, rfl⟩⟩

/-- Cartesian product of clause lists: every pair is concatenated. -/
def clauseProd {α : Type} (left right : List (List α)) : List (List α) :=
  left.flatMap fun clause => right.map fun rest => clause ++ rest

theorem forall_append_pred {α : Type} {p : α → Prop} (l r : List α) :
    (∀ a ∈ l ++ r, p a) ↔ (∀ a ∈ l, p a) ∧ (∀ a ∈ r, p a) := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append.mpr (Or.inl ha)),
      fun a ha => h a (List.mem_append.mpr (Or.inr ha))⟩
  · intro h a ha
    rcases List.mem_append.mp ha with hl | hr
    · exact h.1 a hl
    · exact h.2 a hr

theorem clauseProd_iff {α : Type} {p : α → Prop} (left right : List (List α)) :
    (∃ clause ∈ clauseProd left right, ∀ a ∈ clause, p a) ↔
      (∃ clause ∈ left, ∀ a ∈ clause, p a) ∧ (∃ clause ∈ right, ∀ a ∈ clause, p a) := by
  constructor
  · rintro ⟨clause, hmem, hall⟩
    rw [clauseProd, List.mem_flatMap] at hmem
    rcases hmem with ⟨base, hbase, hclause⟩
    rw [List.mem_map] at hclause
    rcases hclause with ⟨rest, hrest, rfl⟩
    obtain ⟨hL, hR⟩ := (forall_append_pred (p := p) base rest).mp hall
    exact ⟨⟨base, hbase, hL⟩, ⟨rest, hrest, hR⟩⟩
  · rintro ⟨⟨base, hbase, hL⟩, ⟨rest, hrest, hR⟩⟩
    refine ⟨base ++ rest, ?_, (forall_append_pred (p := p) base rest).mpr ⟨hL, hR⟩⟩
    rw [clauseProd, List.mem_flatMap]
    exact ⟨base, hbase, List.mem_map.mpr ⟨rest, hrest, rfl⟩⟩

def litsHold {n : Nat} (lits : List (Lit n)) (env : Fin n → Nat) : Prop :=
  ∀ lit ∈ lits, lit.sat env

def litsSome {n : Nat} (clauses : List (List (Lit n))) (env : Fin n → Nat) : Prop :=
  ∃ clause ∈ clauses, litsHold clause env

theorem litsSome_append {n : Nat} (left right : List (List (Lit n))) (env : Fin n → Nat) :
    litsSome (left ++ right) env ↔ litsSome left env ∨ litsSome right env := by
  constructor
  · rintro ⟨clause, hmem, hhold⟩
    rcases List.mem_append.mp hmem with hl | hr
    · exact Or.inl ⟨clause, hl, hhold⟩
    · exact Or.inr ⟨clause, hr, hhold⟩
  · rintro (⟨clause, hmem, hhold⟩ | ⟨clause, hmem, hhold⟩)
    · exact ⟨clause, List.mem_append.mpr (Or.inl hmem), hhold⟩
    · exact ⟨clause, List.mem_append.mpr (Or.inr hmem), hhold⟩

/-- Disjunctive normal form. `positive = false` builds the negation.
An empty clause list is false. A list containing the empty clause is true. -/
def toDnf {n : Nat} (positive : Bool) : Formula n → List (List (Lit n))
  | .bot =>
      match positive with
      | true => []
      | false => [[]]
  | .atom a =>
      match positive with
      | true => [[.pos a]]
      | false => [[.neg a]]
  | .conj left right =>
      match positive with
      | true => clauseProd (toDnf true left) (toDnf true right)
      | false => toDnf false left ++ toDnf false right
  | .neg body =>
      toDnf (match positive with | true => false | false => true) body
  | .ex _ => []
  termination_by structural φ => φ

theorem toDnf_iff {n : Nat} (positive : Bool) :
    (φ : Formula n) → (hq : φ.quantifierFree = true) → (env : Fin n → Nat) →
      litsSome (toDnf positive φ) env ↔
        match positive with
        | true => φ.sat env
        | false => ¬ φ.sat env
  | .bot, _, _ => by
      cases positive
      · simp only [toDnf, litsSome, litsHold, List.mem_singleton, exists_eq_left, Formula.sat,
          List.not_mem_nil, false_implies, implies_true]
        exact ⟨fun _ h => h.elim, fun _ => trivial⟩
      · simp only [toDnf, litsSome, Formula.sat, List.not_mem_nil, false_and, exists_false]
  | .atom a, _, env => by
      cases positive
      · simp only [toDnf, litsSome, litsHold, List.mem_singleton, exists_eq_left, forall_eq, Lit.sat,
          Formula.sat]
      · simp only [toDnf, litsSome, litsHold, List.mem_singleton, exists_eq_left, forall_eq, Lit.sat,
          Formula.sat]
  | .conj left right, hq, env => by
      have hleft : left.quantifierFree = true := by
        simp only [Formula.quantifierFree, Bool.and_eq_true] at hq
        exact hq.1
      have hright : right.quantifierFree = true := by
        simp only [Formula.quantifierFree, Bool.and_eq_true] at hq
        exact hq.2
      cases positive
      · simp only [toDnf, Formula.sat]
        rw [litsSome_append, toDnf_iff false left hleft env, toDnf_iff false right hright env]
        constructor
        · rintro (hnl | hnr) ⟨hl, hr⟩
          · exact hnl hl
          · exact hnr hr
        · intro hboth
          by_cases hl : left.sat env
          · exact Or.inr (fun hr => hboth ⟨hl, hr⟩)
          · exact Or.inl hl
      · simp only [toDnf, litsSome, litsHold, Formula.sat]
        have hL := toDnf_iff true left hleft env
        have hR := toDnf_iff true right hright env
        simp only [litsSome, litsHold] at hL hR
        rw [clauseProd_iff (p := fun (lit : Lit n) => lit.sat env), hL, hR]
  | .neg body, hq, env => by
      have hbody : body.quantifierFree = true := by
        simpa [Formula.quantifierFree] using hq
      cases positive
      · simp only [toDnf, Formula.sat]
        rw [toDnf_iff true body hbody env]
        exact Classical.not_not.symm
      · simp only [toDnf, Formula.sat]
        exact toDnf_iff false body hbody env
  | .ex _, hq, _ => by
      simp [Formula.quantifierFree] at hq

def expandClause {n : Nat} : List (Lit (n + 1)) → List (List (Constraint n))
  | [] => [[]]
  | lit :: rest => dnfBind (expandLit lit) (expandClause rest)
  termination_by structural lits => lits

theorem expandClause_wf {n : Nat} :
    (lits : List (Lit (n + 1))) → ∀ clause ∈ expandClause lits, ∀ c ∈ clause, c.wf
  | [] => by
      simp only [expandClause, List.mem_singleton, forall_eq]
      intro c hc
      exact (List.not_mem_nil hc).elim
  | lit :: rest => by
      intro clause hmem c hc
      rw [expandClause, dnfBind, List.mem_flatMap] at hmem
      rcases hmem with ⟨base, hbase, htail⟩
      rw [List.mem_map] at htail
      rcases htail with ⟨restClause, hrest, rfl⟩
      rcases List.mem_append.mp hc with hleft | hright
      · exact expandLit_wf lit base hbase c hleft
      · exact expandClause_wf rest restClause hrest c hright

theorem expandClause_iff {n : Nat} :
    (lits : List (Lit (n + 1))) → (x : Nat) → (env : Fin n → Nat) →
      holdsSome (expandClause lits) x env ↔ ∀ lit ∈ lits, lit.sat (envCons x env)
  | [], _, _ => by
      simp only [expandClause, holdsSome, List.mem_singleton, exists_eq_left, holdsAll,
        List.not_mem_nil, false_implies, implies_true]
  | lit :: rest, x, env => by
      simp only [expandClause]
      rw [dnfBind_iff, expandLit_iff, expandClause_iff rest x env, List.forall_mem_cons]

/-- Quantifier-free matrix as a disjunction of constraint clauses. -/
def matrixConstraints {n : Nat} (φ : Formula (n + 1)) : List (List (Constraint n)) :=
  (toDnf true φ).flatMap expandClause

theorem flatMap_holds {n : Nat} (clauses : List (List (Lit (n + 1)))) (x : Nat)
    (env : Fin n → Nat) :
    holdsSome (clauses.flatMap expandClause) x env ↔
      ∃ clause ∈ clauses, holdsSome (expandClause clause) x env := by
  constructor
  · rintro ⟨row, hmem, hholds⟩
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨clause, hclause, hrow⟩
    exact ⟨clause, hclause, row, hrow, hholds⟩
  · rintro ⟨clause, hclause, row, hrow, hholds⟩
    exact ⟨row, List.mem_flatMap.mpr ⟨clause, hclause, hrow⟩, hholds⟩

theorem matrixConstraints_wf {n : Nat} (φ : Formula (n + 1)) :
    ∀ clause ∈ matrixConstraints φ, ∀ c ∈ clause, c.wf := by
  intro clause hmem c hc
  rw [matrixConstraints, List.mem_flatMap] at hmem
  rcases hmem with ⟨lits, _, hclause⟩
  exact expandClause_wf lits clause hclause c hc

theorem matrixConstraints_iff {n : Nat} (φ : Formula (n + 1)) (hq : φ.quantifierFree = true)
    (x : Nat) (env : Fin n → Nat) :
    holdsSome (matrixConstraints φ) x env ↔ φ.sat (envCons x env) := by
  simp only [matrixConstraints]
  rw [flatMap_holds]
  constructor
  · rintro ⟨clause, hclause, hholds⟩
    have hlit : litsHold clause (envCons x env) := (expandClause_iff clause x env).mp hholds
    exact (toDnf_iff true φ hq (envCons x env)).mp ⟨clause, hclause, hlit⟩
  · intro hsat
    obtain ⟨clause, hclause, hlit⟩ := (toDnf_iff true φ hq (envCons x env)).mpr hsat
    exact ⟨clause, hclause, (expandClause_iff clause x env).mpr hlit⟩

/-! ### Test points

In one residue class the divisibility literals do not depend on the quotient.
Order literals are monotone, so a satisfying quotient is either zero or the
least quotient that meets one lower bound. That quotient is named by a slack
below the scaled period, and the slack is a divisibility atom.
-/

theorem mul_pred_cancel {m b : Nat} (hm : 0 < m) : b * (m - 1) + b = b * m := by
  have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  calc
    b * (m - 1) + b = b * (m - 1) + b * 1 := by rw [Nat.mul_one]
    _ = b * (m - 1 + 1) := (Nat.mul_add b (m - 1) 1).symm
    _ = b * m := by rw [hsucc]

theorem residue_mod_congr {m am bm : Nat} (hm : 0 < m) (ham : am < m) (hbm : bm < m) :
    (am + bm * (m - 1)) % m = 0 ↔ am = bm := by
  have hsplit : bm * (m - 1) + bm = bm * m := mul_pred_cancel hm
  by_cases hle : bm ≤ am
  · have hrestore : am - bm + bm = am := Nat.sub_add_cancel hle
    have hrewrite : am + bm * (m - 1) = am - bm + m * bm := by
      calc
        am + bm * (m - 1) = (am - bm + bm) + bm * (m - 1) := by rw [hrestore]
        _ = am - bm + (bm + bm * (m - 1)) := by rw [Nat.add_assoc]
        _ = am - bm + (bm * (m - 1) + bm) := by rw [Nat.add_comm bm (bm * (m - 1))]
        _ = am - bm + bm * m := by rw [hsplit]
        _ = am - bm + m * bm := by rw [Nat.mul_comm]
    rw [hrewrite, Nat.add_mul_mod_self_left]
    have hsmall : am - bm < m := Nat.lt_of_le_of_lt (Nat.sub_le am bm) ham
    rw [Nat.mod_eq_of_lt hsmall, Nat.sub_eq_zero_iff_le]
    exact ⟨fun hle2 => Nat.le_antisymm hle2 hle, fun heq => Nat.le_of_eq heq⟩
  · have hlt : am < bm := Nat.lt_of_not_ge hle
    have hbm0 : 0 < bm := Nat.lt_of_le_of_lt (Nat.zero_le am) hlt
    have hpred : (bm - 1) + 1 = bm := Nat.sub_add_cancel (Nat.succ_le_of_lt hbm0)
    have hmul : m * (bm - 1) + m = m * bm := by
      calc
        m * (bm - 1) + m = m * (bm - 1) + m * 1 := by rw [Nat.mul_one]
        _ = m * (bm - 1 + 1) := (Nat.mul_add m (bm - 1) 1).symm
        _ = m * bm := by rw [hpred]
    have hsubmul : bm * (m - 1) = bm * m - bm :=
      (Nat.sub_eq_of_eq_add hsplit.symm).symm
    have hbmLe : bm ≤ bm * m :=
      Nat.le_trans (Nat.le_of_eq (Nat.mul_one bm).symm)
        (Nat.mul_le_mul_left bm (Nat.succ_le_of_lt hm))
    have hdlt : bm - am < m := Nat.lt_of_le_of_lt (Nat.sub_le bm am) hbm
    have hcancel : am + (bm * m - bm) + (bm - am) = bm * m := by
      have h1 : am + (bm - am) = bm := Nat.add_sub_of_le (Nat.le_of_lt hlt)
      have h2 : bm + (bm * m - bm) = bm * m := Nat.add_sub_of_le hbmLe
      calc
        am + (bm * m - bm) + (bm - am) = am + ((bm * m - bm) + (bm - am)) := by
          rw [← Nat.add_assoc]
        _ = am + ((bm - am) + (bm * m - bm)) := by
          rw [Nat.add_comm (bm * m - bm) (bm - am)]
        _ = am + (bm - am) + (bm * m - bm) := by rw [Nat.add_assoc]
        _ = bm + (bm * m - bm) := by rw [h1]
        _ = bm * m := h2
    have hsum : am + (bm * m - bm) = bm * m - (bm - am) :=
      (Nat.sub_eq_of_eq_add hcancel.symm).symm
    have htail : m * (bm - 1) + (m - (bm - am)) = m * bm - (bm - am) := by
      have hrestore : (m - (bm - am)) + (bm - am) = m := Nat.sub_add_cancel (Nat.le_of_lt hdlt)
      have hjoin : m * (bm - 1) + (m - (bm - am)) + (bm - am) = m * bm := by
        calc
          m * (bm - 1) + (m - (bm - am)) + (bm - am) =
              m * (bm - 1) + ((m - (bm - am)) + (bm - am)) := by rw [Nat.add_assoc]
          _ = m * (bm - 1) + m := by rw [hrestore]
          _ = m * bm := hmul
      exact (Nat.sub_eq_of_eq_add hjoin.symm).symm
    have hrewrite : am + bm * (m - 1) = m * (bm - 1) + (m - (bm - am)) := by
      calc
        am + bm * (m - 1) = am + (bm * m - bm) := by rw [hsubmul]
        _ = bm * m - (bm - am) := hsum
        _ = m * bm - (bm - am) := by rw [Nat.mul_comm bm m]
        _ = m * (bm - 1) + (m - (bm - am)) := htail.symm
    rw [hrewrite, Nat.add_comm, Nat.add_mul_mod_self_left]
    have hspan : m - (bm - am) < m :=
      Nat.sub_lt_of_pos_le (Nat.sub_pos_of_lt hlt) (Nat.le_of_lt hdlt)
    rw [Nat.mod_eq_of_lt hspan]
    exact iff_of_false (Nat.ne_of_gt (Nat.sub_pos_of_lt hdlt)) (Nat.ne_of_lt hlt)

theorem dvd_congr {m a b : Nat} (hm : 0 < m) :
    m ∣ a + b * (m - 1) ↔ a % m = b % m := by
  have hpred : (m - 1) % m = m - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt_of_pos_le Nat.one_pos (Nat.succ_le_of_lt hm))
  have hbmod : (b * (m - 1)) % m = ((b % m) * (m - 1)) % m := by
    rw [Nat.mul_mod, hpred]
  have hshift : (a + b * (m - 1)) % m = (a % m + (b % m) * (m - 1)) % m := by
    rw [Nat.add_mod, hbmod]
    conv_lhs => rw [← Nat.mod_mod a m]
    exact (Nat.add_mod (a % m) ((b % m) * (m - 1)) m).symm
  rw [Nat.dvd_iff_mod_eq_zero, hshift]
  exact residue_mod_congr hm (Nat.mod_lt a hm) (Nat.mod_lt b hm)

theorem exists_mul_of_modEq {m a b : Nat} (_hm : 0 < m) (hle : b ≤ a)
    (hmod : a % m = b % m) : ∃ k, m * k + b = a := by
  have ha : m * (a / m) + a % m = a := Nat.div_add_mod a m
  have hb : m * (b / m) + b % m = b := Nat.div_add_mod b m
  refine ⟨a / m - b / m, ?_⟩
  have hdiff : a - b = m * (a / m - b / m) := by
    conv_lhs => rw [← ha, ← hb, hmod]
    rw [Nat.add_sub_add_right]
    exact (Nat.mul_sub m (a / m) (b / m)).symm
  calc
    m * (a / m - b / m) + b = a - b + b := by rw [hdiff]
    _ = a := Nat.sub_add_cancel hle

theorem upper_downward {slope γ δ k k' : Nat} (hk : k ≤ k') (h : slope * k' + γ < δ) :
    slope * k + γ < δ := by
  exact lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left slope hk) γ) h

theorem lower_upward {scale α β k k' : Nat} (hk : k ≤ k') (h : α < scale * k + β) :
    α < scale * k' + β :=
  lt_of_lt_of_le h (Nat.add_le_add_right (Nat.mul_le_mul_left scale hk) β)

theorem firstGe_pos_of_le {coeff α β : Nat} (hcoeff : 0 < coeff) (hβ : β ≤ α) :
    0 < firstGe coeff α β := by
  have hnot : ¬ α < β := Nat.not_lt.mpr hβ
  simp only [firstGe, hnot, ite_false]
  exact Nat.div_pos (by omega) hcoeff

theorem binding_slack {coeff α β : Nat} (hcoeff : 0 < coeff) (hβ : β ≤ α) :
    ∃ slack, slack < coeff ∧
      coeff * firstGe coeff α β + β = α + (slack + 1) := by
  set k := firstGe coeff α β
  have hkpos : 0 < k := firstGe_pos_of_le hcoeff hβ
  have hlt : α < coeff * k + β := (firstGe_spec hcoeff).mpr (Nat.le_refl k)
  have hprev : ¬ α < coeff * (k - 1) + β := by
    intro hsmall
    have hle : k ≤ k - 1 := (firstGe_spec (k := k - 1) hcoeff).mp hsmall
    omega
  have hupper : coeff * k + β ≤ α + coeff := by
    have hle : coeff * (k - 1) + β ≤ α := Nat.le_of_not_lt hprev
    have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
    have hmul : coeff * (k - 1) + coeff = coeff * k := by
      calc
        coeff * (k - 1) + coeff = coeff * (k - 1) + coeff * 1 := by rw [Nat.mul_one]
        _ = coeff * (k - 1 + 1) := (Nat.mul_add coeff (k - 1) 1).symm
        _ = coeff * k := by rw [hsucc]
    omega
  refine ⟨coeff * k + β - α - 1, ?_, ?_⟩
  · omega
  · omega

def finConj {n : Nat} : List (Formula n) → Formula n
  | [] => .neg .bot
  | f :: fs => .conj f (finConj fs)
  termination_by structural fs => fs

def finDisj {n : Nat} : List (Formula n) → Formula n
  | [] => .bot
  | f :: fs => .neg (.conj (.neg f) (.neg (finDisj fs)))
  termination_by structural fs => fs

theorem finConj_iff {n : Nat} (fs : List (Formula n)) (env : Fin n → Nat) :
    (finConj fs).sat env ↔ ∀ f ∈ fs, f.sat env := by
  induction fs with
  | nil =>
      simp only [finConj, Formula.sat]
      exact ⟨fun _ f hf => (List.not_mem_nil hf).elim, fun _ h => False.elim h⟩
  | cons f fs ih =>
      simp only [finConj, Formula.sat, List.forall_mem_cons, ih]

theorem finDisj_iff {n : Nat} (fs : List (Formula n)) (env : Fin n → Nat) :
    (finDisj fs).sat env ↔ ∃ f ∈ fs, f.sat env := by
  induction fs with
  | nil =>
      simp only [finDisj, Formula.sat, List.not_mem_nil, false_and, exists_false]
  | cons head tail ih =>
      simp only [finDisj, Formula.sat]
      constructor
      · intro h
        by_cases hh : head.sat env
        · exact ⟨head, List.mem_cons_self, hh⟩
        · have htail : (finDisj tail).sat env :=
            Classical.not_not.mp (fun hn => h ⟨hh, hn⟩)
          obtain ⟨f, hf, hsat⟩ := ih.mp htail
          exact ⟨f, List.mem_cons_of_mem head hf, hsat⟩
      · rintro ⟨f, hfmem, hsat⟩
        intro hboth
        rcases List.mem_cons.mp hfmem with rfl | htail
        · exact hboth.1 hsat
        · exact hboth.2 ((ih.mpr ⟨f, htail, hsat⟩))

def listLcm : List Nat → Nat
  | [] => 1
  | a :: as => Nat.lcm a (listLcm as)

theorem listLcm_pos : (l : List Nat) → (∀ a ∈ l, 0 < a) → 0 < listLcm l
  | [], _ => Nat.one_pos
  | a :: as, h => by
      have ha : 0 < a := h a List.mem_cons_self
      have hrest : ∀ b ∈ as, 0 < b := fun b hb => h b (List.mem_cons_of_mem _ hb)
      simpa [listLcm] using Nat.pos_lcm ha (listLcm_pos as hrest)

theorem mem_listLcm_dvd {a : Nat} {l : List Nat} (ha : a ∈ l) : a ∣ listLcm l := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | hmem
      · simpa [listLcm] using Nat.dvd_lcm_left a (listLcm bs)
      · exact Nat.dvd_trans (ih hmem) (by simpa [listLcm] using Nat.dvd_lcm_right b (listLcm bs))

def constraintModulus {n : Nat} : Constraint n → Nat
  | .dvd modulus _ _ => modulus
  | .ndvd modulus _ _ => modulus
  | _ => 1

theorem constraintModulus_pos {n : Nat} (c : Constraint n) (hc : c.wf) :
    0 < constraintModulus c := by
  cases c with
  | param _ => simp [constraintModulus]
  | lower coeff _ _ =>
      simp only [constraintModulus]
      exact Nat.one_pos
  | upper coeff _ _ =>
      simp only [constraintModulus]
      exact Nat.one_pos
  | dvd modulus _ _ =>
      simpa [constraintModulus, Constraint.wf] using hc
  | ndvd modulus _ _ =>
      simpa [constraintModulus, Constraint.wf] using hc

def modulusOf {n : Nat} (cs : List (Constraint n)) : Nat :=
  listLcm (cs.map constraintModulus)

theorem modulusOf_pos {n : Nat} (cs : List (Constraint n)) (hcs : ∀ c ∈ cs, c.wf) :
    0 < modulusOf cs := by
  have hmap : ∀ a ∈ cs.map constraintModulus, 0 < a := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨c, hc, rfl⟩
    exact constraintModulus_pos c (hcs c hc)
  simpa [modulusOf] using listLcm_pos (cs.map constraintModulus) hmap

theorem modulus_dvd_constraint {n : Nat} {cs : List (Constraint n)} {c : Constraint n}
    (hc : c ∈ cs) : constraintModulus c ∣ modulusOf cs := by
  simpa [modulusOf] using mem_listLcm_dvd (List.mem_map.mpr ⟨c, hc, rfl⟩)

def isLower {n : Nat} : Constraint n → Bool
  | .lower _ _ _ => true
  | _ => false

def guardForm {n : Nat} (left right : LinTerm n) : Formula n :=
  .atom (.lt left (right.addConst 1))

def congForm {n : Nat} (modulus : Nat) (α β : LinTerm n) (slack : Nat) : Formula n :=
  .atom (.dvd modulus ((α.addConst (slack + 1)).add (β.scale (modulus - 1))))

def movedLower {n : Nat} (scale other : Nat) (α β α' β' : LinTerm n) (slack : Nat) : Formula n :=
  .atom (.lt ((α'.scale scale).add (β.scale other))
    (((α.addConst (slack + 1)).scale other).add (β'.scale scale)))

def movedUpper {n : Nat} (scale slope : Nat) (α β γ δ : LinTerm n) (slack : Nat) : Formula n :=
  .atom (.lt (((α.addConst (slack + 1)).scale slope).add (γ.scale scale))
    ((δ.scale scale).add (β.scale slope)))

def zeroLiteral {n : Nat} (j : Nat) : Constraint n → Formula n
  | .param lit => lit.formula
  | .lower coeff left right => .atom (.lt left (right.addConst (coeff * j)))
  | .upper coeff left right => .atom (.lt (left.addConst (coeff * j)) right)
  | .dvd modulus coeff term => .atom (.dvd modulus (term.addConst (coeff * j)))
  | .ndvd modulus coeff term => .neg (.atom (.dvd modulus (term.addConst (coeff * j))))

def atSlack {n : Nat} (coeff : Nat) (left right : LinTerm n) (period residue slack : Nat) :
    Constraint n → Formula n
  | .param lit => lit.formula
  | .dvd modulus head term => .atom (.dvd modulus (term.addConst (head * residue)))
  | .ndvd modulus head term => .neg (.atom (.dvd modulus (term.addConst (head * residue))))
  | .lower other left' right' =>
      movedLower (coeff * period) (other * period) left (right.addConst (coeff * residue))
        left' (right'.addConst (other * residue)) slack
  | .upper other left' right' =>
      movedUpper (coeff * period) (other * period) left (right.addConst (coeff * residue))
        (left'.addConst (other * residue)) right' slack

def strictForm {n : Nat} (period residue coeff : Nat) (left right : LinTerm n) (slack : Nat)
    (cs : List (Constraint n)) : Formula n :=
  let scale := coeff * period
  let β := right.addConst (coeff * residue)
  finConj
    (guardForm β (left.addConst (slack + 1)) ::
      congForm scale left β slack ::
        cs.map (atSlack coeff left right period residue slack))

def residueChoices {n : Nat} (period residue : Nat) (cs : List (Constraint n)) : List (Formula n) :=
  finConj (cs.map (zeroLiteral residue)) ::
    ((cs.filter isLower).flatMap fun bound =>
      match bound with
      | .lower coeff left right =>
          (List.range (coeff * period)).map fun slack =>
            strictForm period residue coeff left right slack cs
      | _ => [])

def cooperClause {n : Nat} (cs : List (Constraint n)) : Formula n :=
  let period := modulusOf cs
  finDisj ((List.range period).map fun residue => finDisj (residueChoices period residue cs))

theorem scaled_head {coeff period residue k t : Nat} :
    coeff * (period * k + residue) + t =
      (coeff * period) * k + (t + coeff * residue) := by
  calc
    coeff * (period * k + residue) + t
        = coeff * (period * k) + coeff * residue + t := by rw [Nat.mul_add]
    _ = (coeff * period) * k + coeff * residue + t := by rw [Nat.mul_assoc]
    _ = (coeff * period) * k + (coeff * residue + t) := by rw [Nat.add_assoc]
    _ = (coeff * period) * k + (t + coeff * residue) := by rw [Nat.add_comm (coeff * residue)]

theorem holds_lower_iff_scaled {n : Nat} (coeff : Nat) (left right : LinTerm n)
    (period residue k : Nat) (env : Fin n → Nat) :
    left.eval env < coeff * (period * k + residue) + right.eval env ↔
      left.eval env < (coeff * period) * k +
        (right.addConst (coeff * residue)).eval env := by
  rw [LinTerm.eval_addConst, scaled_head]

theorem holds_upper_iff_scaled {n : Nat} (coeff : Nat) (left right : LinTerm n)
    (period residue k : Nat) (env : Fin n → Nat) :
    coeff * (period * k + residue) + left.eval env < right.eval env ↔
      (coeff * period) * k + (left.addConst (coeff * residue)).eval env <
        right.eval env := by
  rw [LinTerm.eval_addConst, scaled_head]

theorem zeroLiteral_iff {n : Nat} (j : Nat) (c : Constraint n) (hc : c.wf)
    (env : Fin n → Nat) :
    (zeroLiteral j c).sat env ↔ c.holds j env := by
  cases c with
  | param lit =>
      exact Lit.formula_iff lit env
  | lower coeff left right =>
      simp only [zeroLiteral, Formula.sat, Atom.sat, Constraint.holds]
      rw [LinTerm.eval_addConst, Nat.add_comm]
  | upper coeff left right =>
      simp only [zeroLiteral, Formula.sat, Atom.sat, Constraint.holds]
      rw [LinTerm.eval_addConst, Nat.add_comm]
  | dvd modulus coeff term =>
      simp only [zeroLiteral, Formula.sat, Atom.sat, Constraint.holds]
      rw [LinTerm.eval_addConst, Nat.add_comm]
  | ndvd modulus coeff term =>
      have hm : modulus ≠ 0 := Nat.ne_of_gt hc
      simp only [zeroLiteral, Formula.sat, Atom.sat, Constraint.holds]
      constructor
      · intro hn
        refine ⟨hm, fun hdiv => hn ⟨hm, ?_⟩⟩
        rw [LinTerm.eval_addConst, Nat.add_comm]
        exact hdiv
      · rintro ⟨_, hnot⟩ ⟨_, hdiv⟩
        apply hnot
        rw [LinTerm.eval_addConst, Nat.add_comm] at hdiv
        exact hdiv

theorem guardForm_iff {n : Nat} (left right : LinTerm n) (env : Fin n → Nat) :
    (guardForm left right).sat env ↔ left.eval env ≤ right.eval env := by
  simp only [guardForm, Formula.sat, Atom.sat, LinTerm.eval_addConst]
  exact Nat.lt_succ_iff

theorem congForm_iff {n : Nat} (modulus : Nat) (α β : LinTerm n) (slack : Nat)
    (hm : 0 < modulus) (env : Fin n → Nat) :
    (congForm modulus α β slack).sat env ↔
      (α.eval env + (slack + 1)) % modulus = β.eval env % modulus := by
  have hterm :
      (((α.addConst (slack + 1)).add (β.scale (modulus - 1))).eval env) =
        (α.eval env + (slack + 1)) + β.eval env * (modulus - 1) := by
    rw [LinTerm.eval_add, LinTerm.eval_addConst, LinTerm.eval_scale, Nat.mul_comm]
  simp only [congForm, Formula.sat, Atom.sat]
  rw [hterm]
  constructor
  · intro ⟨_, hdiv⟩
    exact (dvd_congr hm).mp hdiv
  · intro hmod
    exact ⟨Nat.ne_of_gt hm, (dvd_congr hm).mpr hmod⟩

theorem atSlack_iff {n : Nat} (coeff period residue slack k : Nat)
    (left right : LinTerm n) (env : Fin n → Nat) (c : Constraint n) (hc : c.wf)
    (hcoeff : 0 < coeff) (hperiod : 0 < period)
    (hk : (coeff * period) * k + (right.addConst (coeff * residue)).eval env =
      left.eval env + (slack + 1))
    (hmod : constraintModulus c ∣ period) :
    (atSlack coeff left right period residue slack c).sat env ↔
      c.holds (period * k + residue) env := by
  cases c with
  | param lit =>
      exact Lit.formula_iff lit env
  | dvd modulus head term =>
      simp only [atSlack, Formula.sat, Atom.sat, Constraint.holds, LinTerm.eval_addConst]
      constructor
      · intro ⟨hne, hdiv⟩
        refine ⟨hne, (dvd_mul_residue (m := modulus) (c := head) (nShift := period)
          (j := residue) (k := k) (t := term.eval env) hmod).mpr ?_⟩
        rw [Nat.add_comm] at hdiv
        exact hdiv
      · intro ⟨hne, hdiv⟩
        refine ⟨hne, ?_⟩
        have hres := (dvd_mul_residue (m := modulus) (c := head) (nShift := period)
          (j := residue) (k := k) (t := term.eval env) hmod).mp hdiv
        rw [Nat.add_comm] at hres
        exact hres
  | ndvd modulus head term =>
      have hm : modulus ≠ 0 := Nat.ne_of_gt hc
      simp only [atSlack, Formula.sat, Atom.sat, Constraint.holds, LinTerm.eval_addConst]
      constructor
      · intro hn
        refine ⟨hm, fun hdiv => hn ⟨hm, ?_⟩⟩
        have hres := (dvd_mul_residue (m := modulus) (c := head) (nShift := period)
          (j := residue) (k := k) (t := term.eval env) hmod).mp hdiv
        rw [Nat.add_comm]
        exact hres
      · intro ⟨_, hnot⟩ ⟨_, hdiv⟩
        apply hnot
        rw [Nat.add_comm] at hdiv
        exact (dvd_mul_residue (m := modulus) (c := head) (nShift := period)
          (j := residue) (k := k) (t := term.eval env) hmod).mpr hdiv
  | lower other left' right' =>
      have hscale : 0 < coeff * period := Nat.mul_pos hcoeff hperiod
      have hmove :=
        lowerMoved_iff (scale := coeff * period) (other := other * period)
          (α := left.eval env) (β := (right.addConst (coeff * residue)).eval env)
          (α' := left'.eval env) (β' := (right'.addConst (other * residue)).eval env)
          (slack := slack) (k := k) hscale hk
      have hform :
          (atSlack coeff left right period residue slack (.lower other left' right')).sat env ↔
            (coeff * period) * left'.eval env +
                (other * period) * (right.addConst (coeff * residue)).eval env <
              (other * period) * (left.eval env + (slack + 1)) +
                (coeff * period) * (right'.addConst (other * residue)).eval env := by
        simp only [atSlack, movedLower, Formula.sat, Atom.sat, LinTerm.eval_add,
          LinTerm.eval_scale, LinTerm.eval_addConst]
      have hpoint := holds_lower_iff_scaled other left' right' period residue k env
      exact hform.trans (hmove.symm.trans hpoint.symm)
  | upper other left' right' =>
      have hscale : 0 < coeff * period := Nat.mul_pos hcoeff hperiod
      have hmove :=
        upperMoved_iff (scale := coeff * period) (slope := other * period)
          (α := left.eval env) (β := (right.addConst (coeff * residue)).eval env)
          (γ := (left'.addConst (other * residue)).eval env) (δ := right'.eval env)
          (slack := slack) (k := k) hscale hk
      have hform :
          (atSlack coeff left right period residue slack (.upper other left' right')).sat env ↔
            (other * period) * (left.eval env + (slack + 1)) +
                (coeff * period) * (left'.addConst (other * residue)).eval env <
              (coeff * period) * right'.eval env +
                (other * period) * (right.addConst (coeff * residue)).eval env := by
        simp only [atSlack, movedUpper, Formula.sat, Atom.sat, LinTerm.eval_add,
          LinTerm.eval_scale, LinTerm.eval_addConst]
      have hpoint := holds_upper_iff_scaled other left' right' period residue k env
      exact hform.trans (hmove.symm.trans hpoint.symm)

theorem strictForm_iff {n : Nat} (period residue coeff slack : Nat)
    (left right : LinTerm n) (cs : List (Constraint n)) (env : Fin n → Nat)
    (hcs : ∀ c ∈ cs, c.wf) (hcoeff : 0 < coeff) (hperiod : 0 < period)
    (hdivs : ∀ c ∈ cs, constraintModulus c ∣ period) :
    (strictForm period residue coeff left right slack cs).sat env ↔
      ∃ k,
        (coeff * period) * k + (right.addConst (coeff * residue)).eval env =
          left.eval env + (slack + 1) ∧
        holdsAll cs (period * k + residue) env := by
  have hscale : 0 < coeff * period := Nat.mul_pos hcoeff hperiod
  constructor
  · intro hsat
    rw [strictForm, finConj_iff] at hsat
    have hguardLe :=
      (guardForm_iff (right.addConst (coeff * residue)) (left.addConst (slack + 1)) env).mp
        (hsat _ List.mem_cons_self)
    have hguard : (right.addConst (coeff * residue)).eval env ≤
        left.eval env + (slack + 1) := by
      rw [LinTerm.eval_addConst right (coeff * residue),
        ← LinTerm.eval_addConst left (slack + 1)]
      rw [LinTerm.eval_addConst right (coeff * residue)] at hguardLe
      exact hguardLe
    have hcong :=
      (congForm_iff (coeff * period) left (right.addConst (coeff * residue)) slack hscale env).mp
        (hsat _ (List.mem_cons_of_mem _ List.mem_cons_self))
    obtain ⟨k, hk⟩ := exists_mul_of_modEq hscale hguard hcong
    refine ⟨k, hk, ?_⟩
    intro c hc
    exact (atSlack_iff coeff period residue slack k left right env c (hcs c hc)
      hcoeff hperiod hk (hdivs c hc)).mp
      (hsat _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨c, hc, rfl⟩))))
  · rintro ⟨k, hk, hholds⟩
    rw [strictForm, finConj_iff]
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · apply (guardForm_iff (right.addConst (coeff * residue))
        (left.addConst (slack + 1)) env).mpr
      conv_rhs => rw [LinTerm.eval_addConst]
      exact Nat.le_trans
        (Nat.le_add_left ((right.addConst (coeff * residue)).eval env) ((coeff * period) * k))
        (Nat.le_of_eq hk)
    · rcases List.mem_cons.mp hf with rfl | hf
      · apply (congForm_iff (coeff * period) left (right.addConst (coeff * residue))
          slack hscale env).mpr
        rw [← hk, Nat.add_comm ((coeff * period) * k)]
        exact Nat.add_mul_mod_self_left
          ((right.addConst (coeff * residue)).eval env) (coeff * period) k
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
        exact (atSlack_iff coeff period residue slack k left right env c (hcs c hc)
          hcoeff hperiod hk (hdivs c hc)).mpr (hholds c hc)

theorem mem_strict_residueChoices {n : Nat} (period residue coeff slack : Nat)
    (left right : LinTerm n) (cs : List (Constraint n))
    (hc : Constraint.lower coeff left right ∈ cs) (hslack : slack < coeff * period) :
    strictForm period residue coeff left right slack cs ∈
      residueChoices period residue cs := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨.lower coeff left right, ?_, ?_⟩)
  · exact List.mem_filter.mpr ⟨hc, rfl⟩
  · exact List.mem_map.mpr ⟨slack, List.mem_range.mpr hslack, rfl⟩

theorem residueChoices_spec {n : Nat} (period residue : Nat) (cs : List (Constraint n))
    (env : Fin n → Nat) (hcs : ∀ c ∈ cs, c.wf) :
    (finDisj (residueChoices period residue cs)).sat env ↔
      holdsAll cs residue env ∨
        ∃ coeff left right slack,
          Constraint.lower coeff left right ∈ cs ∧ slack < coeff * period ∧
            (strictForm period residue coeff left right slack cs).sat env := by
  constructor
  · intro hsat
    obtain ⟨f, hf, hfSat⟩ := (finDisj_iff _ env).mp hsat
    rcases List.mem_cons.mp hf with rfl | htail
    · refine Or.inl ?_
      rw [finConj_iff] at hfSat
      intro c hc
      exact (zeroLiteral_iff residue c (hcs c hc) env).mp
        (hfSat _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    · refine Or.inr ?_
      obtain ⟨bound, hbound, hfmatch⟩ := List.mem_flatMap.mp htail
      obtain ⟨hmem, _⟩ := List.mem_filter.mp hbound
      cases bound with
      | param _ => exact (List.not_mem_nil hfmatch).elim
      | upper _ _ _ => exact (List.not_mem_nil hfmatch).elim
      | dvd _ _ _ => exact (List.not_mem_nil hfmatch).elim
      | ndvd _ _ _ => exact (List.not_mem_nil hfmatch).elim
      | lower coeff left right =>
          obtain ⟨slack, hslack, rfl⟩ := List.mem_map.mp hfmatch
          exact ⟨coeff, left, right, slack, hmem, List.mem_range.mp hslack, hfSat⟩
  · intro h
    apply (finDisj_iff _ env).mpr
    rcases h with hzero | ⟨coeff, left, right, slack, hc, hslack, hstrict⟩
    · refine ⟨finConj (cs.map (zeroLiteral residue)), List.mem_cons_self, ?_⟩
      rw [finConj_iff]
      intro f hf
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
      exact (zeroLiteral_iff residue c (hcs c hc) env).mpr (hzero c hc)
    · exact ⟨strictForm period residue coeff left right slack cs,
        mem_strict_residueChoices period residue coeff slack left right cs hc hslack, hstrict⟩

def listMax : List Nat → Nat
  | [] => 0
  | a :: as => max a (listMax as)

theorem listMax_le {l : List Nat} {k : Nat} (h : ∀ a ∈ l, a ≤ k) : listMax l ≤ k := by
  induction l with
  | nil =>
      simp only [listMax]
      exact Nat.zero_le _
  | cons a as ih =>
      simp only [listMax]
      exact Nat.max_le.mpr
        ⟨h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

theorem le_listMax_of_mem {a : Nat} {l : List Nat} (h : a ∈ l) : a ≤ listMax l := by
  induction l with
  | nil => cases h
  | cons b bs ih =>
      simp only [listMax]
      rcases List.mem_cons.mp h with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem listMax_mem_of_pos {l : List Nat} (h : 0 < listMax l) : listMax l ∈ l := by
  induction l with
  | nil =>
      simp only [listMax] at h
      exact absurd h (Nat.lt_irrefl 0)
  | cons a as ih =>
      simp only [listMax] at h ⊢
      by_cases hle : listMax as ≤ a
      · rw [Nat.max_eq_left hle]
        exact List.mem_cons_self
      · have hgt : a < listMax as := Nat.lt_of_not_ge hle
        rw [Nat.max_eq_right (Nat.le_of_lt hgt)]
        exact List.mem_cons_of_mem _
          (ih (Nat.lt_of_le_of_lt (Nat.zero_le a) hgt))

def lowerQuotient {n : Nat} (period residue : Nat) (env : Fin n → Nat) :
    Constraint n → Nat
  | .lower coeff left right =>
      firstGe (coeff * period) (left.eval env) ((right.addConst (coeff * residue)).eval env)
  | _ => 0

theorem lowerQuotient_le_of_holds {n : Nat} (period residue k : Nat) (c : Constraint n)
    (env : Fin n → Nat) (hc : c.wf) (hperiod : 0 < period)
    (h : c.holds (period * k + residue) env) :
    lowerQuotient period residue env c ≤ k := by
  cases c with
  | lower coeff left right =>
      simp only [lowerQuotient]
      exact (firstGe_spec (Nat.mul_pos hc hperiod)).mp
        ((holds_lower_iff_scaled coeff left right period residue k env).mp h)
  | param _ =>
      simp only [lowerQuotient]
      exact Nat.zero_le _
  | upper _ _ _ =>
      simp only [lowerQuotient]
      exact Nat.zero_le _
  | dvd _ _ _ =>
      simp only [lowerQuotient]
      exact Nat.zero_le _
  | ndvd _ _ _ =>
      simp only [lowerQuotient]
      exact Nat.zero_le _

theorem holdsAll_down {n : Nat} (period residue k k' : Nat) (cs : List (Constraint n))
    (env : Fin n → Nat) (hcs : ∀ c ∈ cs, c.wf) (hperiod : 0 < period)
    (hk : holdsAll cs (period * k + residue) env) (hk' : k' ≤ k)
    (hlower : ∀ c ∈ cs, lowerQuotient period residue env c ≤ k')
    (hdivs : ∀ c ∈ cs, constraintModulus c ∣ period) :
    holdsAll cs (period * k' + residue) env := by
  intro c hc
  cases c with
  | param lit =>
      exact hk (.param lit) hc
  | lower coeff left right =>
      have hq : firstGe (coeff * period) (left.eval env)
          ((right.addConst (coeff * residue)).eval env) ≤ k' :=
        hlower (.lower coeff left right) hc
      exact (holds_lower_iff_scaled coeff left right period residue k' env).mpr
        ((firstGe_spec (Nat.mul_pos (hcs _ hc) hperiod)).mpr hq)
  | upper coeff left right =>
      have hbig := (holds_upper_iff_scaled coeff left right period residue k env).mp
        (hk (.upper coeff left right) hc)
      have hsmall := upper_downward (k := k') (k' := k) hk' hbig
      exact (holds_upper_iff_scaled coeff left right period residue k' env).mpr hsmall
  | dvd modulus head term =>
      have hdivp : modulus ∣ period := hdivs (.dvd modulus head term) hc
      have hhold := hk (.dvd modulus head term) hc
      refine ⟨hhold.1, (dvd_mul_residue (m := modulus) (c := head) (nShift := period)
        (j := residue) (k := k') (t := term.eval env) hdivp).mpr ?_⟩
      exact (dvd_mul_residue (m := modulus) (c := head) (nShift := period)
        (j := residue) (k := k) (t := term.eval env) hdivp).mp hhold.2
  | ndvd modulus head term =>
      have hdivp : modulus ∣ period := hdivs (.ndvd modulus head term) hc
      have hhold := hk (.ndvd modulus head term) hc
      refine ⟨hhold.1, fun hdiv => hhold.2 ?_⟩
      exact (dvd_mul_residue (m := modulus) (c := head) (nShift := period)
        (j := residue) (k := k) (t := term.eval env) hdivp).mpr
        ((dvd_mul_residue (m := modulus) (c := head) (nShift := period)
          (j := residue) (k := k') (t := term.eval env) hdivp).mp hdiv)

theorem cooperClause_iff {n : Nat} (cs : List (Constraint n))
    (hcs : ∀ c ∈ cs, c.wf) (env : Fin n → Nat) :
    (∃ x, holdsAll cs x env) ↔ (cooperClause cs).sat env := by
  have hperiod : 0 < modulusOf cs := modulusOf_pos cs hcs
  have hdivs : ∀ c ∈ cs, constraintModulus c ∣ modulusOf cs :=
    fun _ hc => modulus_dvd_constraint hc
  constructor
  · intro ⟨x, hx⟩
    obtain ⟨j, hj, k, hk⟩ :=
      (exists_mod_split (P := fun y => holdsAll cs y env) hperiod).mp ⟨x, hx⟩
    apply (finDisj_iff _ env).mpr
    refine ⟨finDisj (residueChoices (modulusOf cs) j cs),
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
    apply (residueChoices_spec (modulusOf cs) j cs env hcs).mpr
    let quotients := cs.map (lowerQuotient (modulusOf cs) j env)
    let kStar := listMax quotients
    have hquot : ∀ q ∈ quotients, q ≤ k := by
      intro q hq
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
      exact lowerQuotient_le_of_holds (modulusOf cs) j k c env (hcs c hc) hperiod (hk c hc)
    have hkStar : kStar ≤ k := listMax_le hquot
    have hlow : ∀ c ∈ cs, lowerQuotient (modulusOf cs) j env c ≤ kStar :=
      fun c hc => le_listMax_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have hdown :=
      holdsAll_down (modulusOf cs) j k kStar cs env hcs hperiod hk hkStar hlow hdivs
    by_cases hzero : kStar = 0
    · refine Or.inl ?_
      rw [hzero, Nat.mul_zero, Nat.zero_add] at hdown
      exact hdown
    · have hpos : 0 < kStar := Nat.pos_of_ne_zero hzero
      have hstarMem : kStar ∈ quotients := listMax_mem_of_pos hpos
      obtain ⟨bound, hbound, hstar⟩ := List.mem_map.mp hstarMem
      cases bound with
      | param _ =>
          simp only [lowerQuotient] at hstar
          exact absurd hstar.symm (Nat.ne_of_gt hpos)
      | upper _ _ _ =>
          simp only [lowerQuotient] at hstar
          exact absurd hstar.symm (Nat.ne_of_gt hpos)
      | dvd _ _ _ =>
          simp only [lowerQuotient] at hstar
          exact absurd hstar.symm (Nat.ne_of_gt hpos)
      | ndvd _ _ _ =>
          simp only [lowerQuotient] at hstar
          exact absurd hstar.symm (Nat.ne_of_gt hpos)
      | lower coeff left right =>
          have hcoeff : 0 < coeff := hcs _ hbound
          have hscale : 0 < coeff * modulusOf cs := Nat.mul_pos hcoeff hperiod
          have hfirst : firstGe (coeff * modulusOf cs) (left.eval env)
              ((right.addConst (coeff * j)).eval env) = kStar := by
            simpa [lowerQuotient] using hstar
          have hβ : (right.addConst (coeff * j)).eval env ≤ left.eval env := by
            have hnot : ¬ left.eval env < (right.addConst (coeff * j)).eval env := by
              intro hlt
              have hge : firstGe (coeff * modulusOf cs) (left.eval env)
                  ((right.addConst (coeff * j)).eval env) = 0 := by
                simp only [firstGe, hlt, ite_true]
              rw [hge] at hfirst
              exact Nat.ne_of_gt hpos hfirst.symm
            exact Nat.le_of_not_lt hnot
          obtain ⟨slack, hslack, heq⟩ := binding_slack hscale hβ
          rw [hfirst] at heq
          refine Or.inr ⟨coeff, left, right, slack, hbound, hslack, ?_⟩
          apply (strictForm_iff (modulusOf cs) j coeff slack left right cs env hcs
            hcoeff hperiod hdivs).mpr
          exact ⟨kStar, heq, hdown⟩
  · intro hsat
    rw [cooperClause, finDisj_iff] at hsat
    obtain ⟨f, hf, hfSat⟩ := hsat
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
    rcases (residueChoices_spec (modulusOf cs) j cs env hcs).mp hfSat with
      hzero | ⟨coeff, left, right, slack, hbound, _, hstrict⟩
    · exact ⟨j, hzero⟩
    · have hcoeff : 0 < coeff := hcs _ hbound
      obtain ⟨k, _, hholds⟩ := (strictForm_iff (modulusOf cs) j coeff slack left right cs env
        hcs hcoeff hperiod hdivs).mp hstrict
      exact ⟨modulusOf cs * k + j, hholds⟩

theorem finDisj_qf {n : Nat} :
    (fs : List (Formula n)) → (∀ f ∈ fs, f.quantifierFree = true) →
      (finDisj fs).quantifierFree = true
  | [], _ => by simp [finDisj, Formula.quantifierFree]
  | f :: fs, h => by
      have hf := h f List.mem_cons_self
      have hfs := finDisj_qf fs fun g hg => h g (List.mem_cons_of_mem _ hg)
      simp [finDisj, Formula.quantifierFree, hf, hfs]

theorem finConj_qf {n : Nat} :
    (fs : List (Formula n)) → (∀ f ∈ fs, f.quantifierFree = true) →
      (finConj fs).quantifierFree = true
  | [], _ => by simp [finConj, Formula.quantifierFree]
  | f :: fs, h => by
      have hf := h f List.mem_cons_self
      have hfs := finConj_qf fs fun g hg => h g (List.mem_cons_of_mem _ hg)
      simp [finConj, Formula.quantifierFree, hf, hfs]

theorem zeroLiteral_qf {n : Nat} (j : Nat) (c : Constraint n) :
    (zeroLiteral j c).quantifierFree = true := by
  cases c with
  | param lit => simp [zeroLiteral, Lit.formula_qf]
  | lower _ _ _ => simp [zeroLiteral, Formula.quantifierFree]
  | upper _ _ _ => simp [zeroLiteral, Formula.quantifierFree]
  | dvd _ _ _ => simp [zeroLiteral, Formula.quantifierFree]
  | ndvd _ _ _ => simp [zeroLiteral, Formula.quantifierFree]

theorem atSlack_qf {n : Nat} (coeff : Nat) (left right : LinTerm n)
    (period residue slack : Nat) (c : Constraint n) :
    (atSlack coeff left right period residue slack c).quantifierFree = true := by
  cases c with
  | param lit => simp [atSlack, Lit.formula_qf]
  | lower _ _ _ => simp [atSlack, movedLower, Formula.quantifierFree]
  | upper _ _ _ => simp [atSlack, movedUpper, Formula.quantifierFree]
  | dvd _ _ _ => simp [atSlack, Formula.quantifierFree]
  | ndvd _ _ _ => simp [atSlack, Formula.quantifierFree]

theorem strictForm_qf {n : Nat} (period residue coeff : Nat) (left right : LinTerm n)
    (slack : Nat) (cs : List (Constraint n)) :
    (strictForm period residue coeff left right slack cs).quantifierFree = true := by
  refine finConj_qf _ ?_
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · simp [guardForm, Formula.quantifierFree]
  · rcases List.mem_cons.mp hf with rfl | hf
    · simp [congForm, Formula.quantifierFree]
    · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hf
      exact atSlack_qf coeff left right period residue slack c

theorem residueChoices_qf {n : Nat} (period residue : Nat) (cs : List (Constraint n))
    (f : Formula n) (hf : f ∈ residueChoices period residue cs) :
    f.quantifierFree = true := by
  rcases List.mem_cons.mp hf with rfl | htail
  · exact finConj_qf _ fun g hg => by
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
      exact zeroLiteral_qf residue c
  · obtain ⟨bound, _, hfmatch⟩ := List.mem_flatMap.mp htail
    cases bound with
    | param _ => exact (List.not_mem_nil hfmatch).elim
    | upper _ _ _ => exact (List.not_mem_nil hfmatch).elim
    | dvd _ _ _ => exact (List.not_mem_nil hfmatch).elim
    | ndvd _ _ _ => exact (List.not_mem_nil hfmatch).elim
    | lower coeff left right =>
        obtain ⟨slack, _, rfl⟩ := List.mem_map.mp hfmatch
        exact strictForm_qf period residue coeff left right slack cs

theorem cooperClause_qf {n : Nat} (cs : List (Constraint n)) :
    (cooperClause cs).quantifierFree = true := by
  unfold cooperClause
  refine finDisj_qf _ ?_
  intro f hf
  obtain ⟨residue, _, rfl⟩ := List.mem_map.mp hf
  exact finDisj_qf _ fun g hg => residueChoices_qf (modulusOf cs) residue cs g hg

def Formula.cooper {n : Nat} (φ : Formula (n + 1)) : Formula n :=
  finDisj ((matrixConstraints φ).map cooperClause)

theorem Formula.cooper_qf {n : Nat} (φ : Formula (n + 1)) :
    (Formula.cooper φ).quantifierFree = true := by
  rw [Formula.cooper]
  refine finDisj_qf _ ?_
  intro f hf
  obtain ⟨clause, _, rfl⟩ := List.mem_map.mp hf
  exact cooperClause_qf clause

theorem Formula.cooper_iff {n : Nat} (φ : Formula (n + 1)) (hq : φ.quantifierFree = true)
    (env : Fin n → Nat) :
    (Formula.cooper φ).sat env ↔ ∃ x, φ.sat (envCons x env) := by
  constructor
  · intro hsat
    rw [Formula.cooper, finDisj_iff] at hsat
    obtain ⟨clauseForm, hmem, hclause⟩ := hsat
    obtain ⟨clause, hclauseMem, rfl⟩ := List.mem_map.mp hmem
    have hwf := matrixConstraints_wf φ clause hclauseMem
    obtain ⟨x, hx⟩ := (cooperClause_iff clause hwf env).mpr hclause
    exact ⟨x, (matrixConstraints_iff φ hq x env).mp ⟨clause, hclauseMem, hx⟩⟩
  · intro ⟨x, hx⟩
    obtain ⟨clause, hclause, hholds⟩ := (matrixConstraints_iff φ hq x env).mpr hx
    have hwf := matrixConstraints_wf φ clause hclause
    rw [Formula.cooper]
    apply (finDisj_iff _ env).mpr
    exact ⟨cooperClause clause, List.mem_map.mpr ⟨clause, hclause, rfl⟩,
      (cooperClause_iff clause hwf env).mp ⟨x, hholds⟩⟩

def Formula.eliminate : {n : Nat} → (φ : Formula n) → Formula n
  | _, .bot => .bot
  | _, .atom a => .atom a
  | _, .conj a b => .conj (Formula.eliminate a) (Formula.eliminate b)
  | _, .neg a => .neg (Formula.eliminate a)
  | _, .ex body => Formula.cooper (Formula.eliminate body)
  termination_by structural _ φ => φ

theorem Formula.eliminate_qf : {n : Nat} → (φ : Formula n) → φ.eliminate.quantifierFree = true
  | _, .bot => by simp [Formula.eliminate, Formula.quantifierFree]
  | _, .atom _ => by simp [Formula.eliminate, Formula.quantifierFree]
  | _, .conj a b => by
      simp [Formula.eliminate, Formula.quantifierFree, Formula.eliminate_qf a,
        Formula.eliminate_qf b]
  | _, .neg a => by
      simp [Formula.eliminate, Formula.quantifierFree, Formula.eliminate_qf a]
  | _, .ex body => by
      simp only [Formula.eliminate]
      exact Formula.cooper_qf body.eliminate

theorem Formula.eliminate_iff : {n : Nat} → (φ : Formula n) → (env : Fin n → Nat) →
    φ.eliminate.sat env ↔ φ.sat env
  | _, .bot, _ => by simp [Formula.eliminate, Formula.sat]
  | _, .atom _, env => by simp [Formula.eliminate, Formula.sat]
  | _, .conj a b, env => by
      simp only [Formula.eliminate, Formula.sat]
      exact and_congr (Formula.eliminate_iff a env) (Formula.eliminate_iff b env)
  | _, .neg a, env => by
      simp only [Formula.eliminate, Formula.sat]
      exact not_congr (Formula.eliminate_iff a env)
  | _, .ex body, env => by
      simp only [Formula.eliminate, Formula.sat]
      rw [Formula.cooper_iff body.eliminate (Formula.eliminate_qf body) env]
      exact exists_congr fun x => Formula.eliminate_iff body (envCons x env)


/-- Largest `x < bound` accepted by `p`, if any. -/
def firstBelow : Nat → (Nat → Bool) → Option Nat
  | 0, _ => none
  | bound + 1, p =>
      if p bound then some bound else firstBelow bound p

theorem firstBelow_spec {bound witness : Nat} {p : Nat → Bool}
    (h : firstBelow bound p = some witness) :
    witness < bound ∧ p witness = true := by
  induction bound generalizing witness with
  | zero => simp [firstBelow] at h
  | succ bound inductionHypothesis =>
      by_cases hp : p bound = true
      · have hsome : firstBelow (bound + 1) p = some bound := by
          simp [firstBelow, hp]
        rw [hsome] at h
        cases h
        exact ⟨Nat.lt_succ_self bound, hp⟩
      · have hrec : firstBelow (bound + 1) p = firstBelow bound p := by
          simp [firstBelow, hp]
        rw [hrec] at h
        obtain ⟨hlt, htrue⟩ := inductionHypothesis h
        exact ⟨Nat.lt_succ_of_lt hlt, htrue⟩

theorem exists_firstBelow {bound : Nat} {p : Nat → Bool} :
    (∃ x, x < bound ∧ p x = true) ↔ ∃ witness, firstBelow bound p = some witness := by
  induction bound with
  | zero => simp [firstBelow]
  | succ bound inductionHypothesis =>
      constructor
      · intro ⟨x, hx, hp⟩
        by_cases hhead : p bound = true
        · exact ⟨bound, by simp [firstBelow, hhead]⟩
        · have hxlt : x < bound := by
            have hxle : x ≤ bound := Nat.le_of_lt_succ hx
            have hne : x ≠ bound := by
              intro heq
              have : p bound = true := by simpa [heq] using hp
              exact hhead this
            omega
          obtain ⟨witness, hwitness⟩ := inductionHypothesis.mp ⟨x, hxlt, hp⟩
          exact ⟨witness, by simp [firstBelow, hhead, hwitness]⟩
      · intro ⟨witness, hwitness⟩
        obtain ⟨hlt, hp⟩ := firstBelow_spec hwitness
        exact ⟨witness, hlt, hp⟩

def searchSat (φ : Formula 1) (bound : Nat) : Bool :=
  (firstBelow bound (fun x => φ.decideQF (env1 x))).isSome

def witnessOf (φ : Formula 1) : Option Nat :=
  firstBelow (φ.threshold1 + φ.period1) (fun x => φ.decideQF (env1 x))

/-- Re-evaluate a quantifier-free matrix at a proposed witness. -/
def checkWitness (φ : Formula 1) (witness : Nat) : Bool :=
  φ.decideQF (env1 witness)

theorem searchSat_iff (φ : Formula 1) (hq : φ.quantifierFree = true) (bound : Nat) :
    searchSat φ bound = true ↔ ∃ x, x < bound ∧ φ.sat (env1 x) := by
  simp only [searchSat, Option.isSome_iff_exists]
  constructor
  · intro ⟨witness, hwitness⟩
    obtain ⟨hlt, hdecide⟩ := firstBelow_spec hwitness
    exact ⟨witness, hlt, (Formula.decideQF_iff φ hq (env1 witness)).mp hdecide⟩
  · intro ⟨x, hx, hsat⟩
    have hdecide : φ.decideQF (env1 x) = true :=
      (Formula.decideQF_iff φ hq (env1 x)).mpr hsat
    exact (exists_firstBelow).mp ⟨x, hx, hdecide⟩

theorem checkWitness_sound (φ : Formula 1) (hq : φ.quantifierFree = true)
    (witness : Nat) (h : checkWitness φ witness = true) :
    φ.sat (env1 witness) :=
  (Formula.decideQF_iff φ hq (env1 witness)).mp h

theorem checkWitness_complete (φ : Formula 1) (hq : φ.quantifierFree = true)
    (witness : Nat) (h : φ.sat (env1 witness)) :
    checkWitness φ witness = true :=
  (Formula.decideQF_iff φ hq (env1 witness)).mpr h

/-- Boolean verdict on every closed sentence. A formula with a free variable returns `none`. -/
def Formula.decideClosed : {n : Nat} → Formula n → Option Bool
  | 0, φ => some (φ.eliminate.decideQF env0)
  | _ + 1, _ => none

theorem Formula.decideClosed_iff (φ : Formula 0) {b : Bool}
    (h : φ.decideClosed = some b) : (b = true) ↔ φ.sat env0 := by
  simp only [Formula.decideClosed, Option.some.injEq] at h
  subst h
  rw [Formula.decideQF_iff _ (Formula.eliminate_qf φ) env0, Formula.eliminate_iff]

/-- A witness below the computed bound is accepted by the cheap checker. -/
theorem witnessOf_spec (φ : Formula 1) (hq : φ.quantifierFree = true) (witness : Nat)
    (h : witnessOf φ = some witness) :
    checkWitness φ witness = true ∧ φ.sat (env1 witness) := by
  obtain ⟨_, hdecide⟩ := firstBelow_spec h
  exact ⟨hdecide, checkWitness_sound φ hq witness hdecide⟩

theorem exists_iff_witnessOf (φ : Formula 1) (hq : φ.quantifierFree = true) :
    (∃ x, φ.sat (env1 x)) ↔ ∃ witness, witnessOf φ = some witness := by
  constructor
  · intro hsat
    have hbelow := (Formula.exists_iff_below φ hq).mp hsat
    have hdecide : ∃ x, x < φ.threshold1 + φ.period1 ∧
        φ.decideQF (env1 x) = true := by
      obtain ⟨x, hx, hsatx⟩ := hbelow
      exact ⟨x, hx, (Formula.decideQF_iff φ hq (env1 x)).mpr hsatx⟩
    simpa [witnessOf] using (exists_firstBelow).mp hdecide
  · intro ⟨witness, hsome⟩
    exact ⟨witness, (witnessOf_spec φ hq witness hsome).2⟩

/-! ## Definable order and divisibility -/

theorem lt_iff_exists_add_succ (a b : Nat) :
    a < b ↔ ∃ z, a + (z + 1) = b := by
  constructor
  · intro hlt
    refine ⟨b - (a + 1), ?_⟩
    omega
  · intro ⟨z, hz⟩
    omega

theorem dvd_iff_exists_mul (modulus value : Nat) (hmodulus : modulus ≠ 0) :
    modulus ∣ value ↔ ∃ z, value = modulus * z := by
  have _used : modulus ≠ 0 := hmodulus
  constructor
  · intro hdiv
    exact ⟨value / modulus, (Nat.mul_div_cancel' hdiv).symm⟩
  · intro ⟨z, hz⟩
    exact ⟨z, hz⟩

/-! ## The bubble -/

/-- Presentation and standard interpretation.
`decide` returns a Boolean for every closed sentence and `none` when a variable is free. -/
structure Bubble where
  name : String
  decide : Formula 0 → Option Bool

def presburgerBubble : Bubble where
  name := "Presburger"
  decide := Formula.decideClosed

theorem presburgerBubble_decides (φ : Formula 0) {b : Bool}
    (h : presburgerBubble.decide φ = some b) :
    (b = true) ↔ φ.sat env0 :=
  Formula.decideClosed_iff φ h

theorem presburgerBubble_iff_sat (φ : Formula 0) :
    presburgerBubble.decide φ = some true ↔ φ.sat env0 := by
  have hdecide : presburgerBubble.decide φ = some (φ.eliminate.decideQF env0) := by
    simp [presburgerBubble, Formula.decideClosed]
  rw [hdecide, Option.some.injEq, Formula.decideQF_iff _ (Formula.eliminate_qf φ) env0,
    Formula.eliminate_iff]

theorem decide_true_of_sat {φ : Formula 0} (h : φ.sat env0) :
    presburgerBubble.decide φ = some true :=
  (presburgerBubble_iff_sat φ).mpr h

theorem decide_false_of_unsat {φ : Formula 0} (h : ¬ φ.sat env0) :
    presburgerBubble.decide φ = some false := by
  have hbit : φ.eliminate.decideQF env0 = false := by
    cases hval : φ.eliminate.decideQF env0 with
    | false => rfl
    | true =>
        exact False.elim (h ((Formula.eliminate_iff φ env0).mp
          ((Formula.decideQF_iff _ (Formula.eliminate_qf φ) env0).mp hval)))
  simp [presburgerBubble, Formula.decideClosed, hbit]

/-! ## Semilinear sets in the standard model -/

theorem qf_arity1_semilinear (φ : Formula 1) (hq : φ.quantifierFree = true) :
    IsSemilinearSet {x : Nat | φ.sat (env1 x)} := by
  refine (Nat.isSemilinearSet_iff_ultimately_periodic).2 ?_
  refine ⟨φ.threshold1, φ.period1, Formula.period1_pos φ, ?_⟩
  intro x hx
  simpa [Set.mem_ofPred_eq] using Formula.qf_ultimately_periodic φ hq x hx

theorem multiplication_graph_not_presburger_definable :
    ¬ (∅ : Set Nat).Definable FirstOrder.Language.presburger
        {v : Fin 3 → Nat | v 0 = v 1 * v 2} :=
  FirstOrder.Language.presburger.mul_not_definable (A := ∅)

/-! ## Controls -/

def closedEq (left right : Nat) : Formula 0 :=
  .atom (.eq ⟨.nil, left⟩ ⟨.nil, right⟩)

def exEqConst (target : Nat) : Formula 0 :=
  .ex (.atom (.eq ⟨.cons 1 .nil, 0⟩ ⟨.cons 0 .nil, target⟩))

def exSuccEqZero : Formula 0 :=
  .ex (.atom (.eq ⟨.cons 1 .nil, 1⟩ ⟨.cons 0 .nil, 0⟩))

def exEven : Formula 0 :=
  .ex (.atom (.dvd 2 ⟨.cons 1 .nil, 0⟩))

def exOddByDouble : Formula 0 :=
  .ex (.atom (.dvd 2 ⟨.cons 2 .nil, 1⟩))

def forallRefl : Formula 0 :=
  .neg (.ex (.neg (.atom (.eq ⟨.cons 1 .nil, 0⟩ ⟨.cons 1 .nil, 0⟩))))

def existsIrrefl : Formula 0 :=
  .ex (.neg (.atom (.eq ⟨.cons 1 .nil, 0⟩ ⟨.cons 1 .nil, 0⟩)))

def exTwoOrThree : Formula 0 :=
  .ex (.neg (.conj
    (.neg (.atom (.eq ⟨.cons 1 .nil, 0⟩ ⟨.cons 0 .nil, 2⟩)))
    (.neg (.atom (.eq ⟨.cons 1 .nil, 0⟩ ⟨.cons 0 .nil, 3⟩)))))

def nestedExists : Formula 0 :=
  .ex (.ex (.bot : Formula 2))

def nestedExistsZero : Formula 0 :=
  .ex (.ex (.atom (.eq ⟨.cons 1 (.cons 0 .nil), 0⟩ ⟨.cons 0 (.cons 0 .nil), 0⟩)))

def nestedEven : Formula 0 :=
  .ex (.ex (.atom (.dvd 2 ⟨.cons 1 (.cons 0 .nil), 0⟩)))

def nestedDoubleOdd : Formula 0 :=
  .ex (.ex (.atom (.dvd 2 ⟨.cons 2 (.cons 0 .nil), 1⟩)))

theorem exEqConst_sat (target : Nat) : (exEqConst target).sat env0 := by
  refine ⟨target, ?_⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot]

theorem exSuccEqZero_unsat : ¬ exSuccEqZero.sat env0 := by
  intro ⟨_, hx⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot] at hx

theorem exEven_sat : exEven.sat env0 := by
  refine ⟨0, ?_⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot]

theorem exOddByDouble_unsat : ¬ exOddByDouble.sat env0 := by
  intro ⟨_, hx⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot] at hx

theorem forallRefl_sat : forallRefl.sat env0 := by
  intro ⟨_, hx⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot] at hx

theorem existsIrrefl_unsat : ¬ existsIrrefl.sat env0 := by
  intro ⟨_, hx⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot] at hx

theorem exTwoOrThree_sat : exTwoOrThree.sat env0 := by
  refine ⟨2, ?_⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot]

theorem nestedExists_unsat : ¬ nestedExists.sat env0 := by
  intro ⟨_, h⟩
  obtain ⟨_, hbot⟩ := h
  exact hbot

theorem nestedExistsZero_sat : nestedExistsZero.sat env0 := by
  refine ⟨0, 0, ?_⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot]

theorem nestedEven_sat : nestedEven.sat env0 := by
  refine ⟨0, 0, ?_⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot]

theorem nestedDoubleOdd_unsat : ¬ nestedDoubleOdd.sat env0 := by
  intro ⟨_, ⟨_, hx⟩⟩
  simp [Formula.sat, Atom.sat, LinTerm.eval, envCons, Coeff.dot] at hx

theorem control_zero_eq_zero :
    presburgerBubble.decide (closedEq 0 0) = some true := rfl

theorem control_zero_eq_one :
    presburgerBubble.decide (closedEq 0 1) = some false := rfl

theorem control_exists_one :
    presburgerBubble.decide (exEqConst 1) = some true :=
  decide_true_of_sat (exEqConst_sat 1)

theorem control_exists_one_witness :
    witnessOf (.atom (.eq ⟨.cons 1 .nil, 0⟩ ⟨.cons 0 .nil, 1⟩)) = some 1 := rfl

theorem control_bad_witness_rejected :
    checkWitness (.atom (.eq ⟨.cons 1 .nil, 1⟩ ⟨.cons 0 .nil, 0⟩)) 0 = false := rfl

theorem control_succ_eq_zero :
    presburgerBubble.decide exSuccEqZero = some false :=
  decide_false_of_unsat exSuccEqZero_unsat

theorem control_exists_even :
    presburgerBubble.decide exEven = some true :=
  decide_true_of_sat exEven_sat

theorem control_no_even_successor :
    presburgerBubble.decide exOddByDouble = some false :=
  decide_false_of_unsat exOddByDouble_unsat

theorem control_forall_refl :
    presburgerBubble.decide forallRefl = some true :=
  decide_true_of_sat forallRefl_sat

theorem control_exists_irrefl :
    presburgerBubble.decide existsIrrefl = some false :=
  decide_false_of_unsat existsIrrefl_unsat

theorem control_two_or_three :
    presburgerBubble.decide exTwoOrThree = some true :=
  decide_true_of_sat exTwoOrThree_sat

theorem control_conjunction_of_mixed :
    presburgerBubble.decide (.conj (closedEq 0 0) (closedEq 0 1)) = some false := rfl

theorem control_nested_exists_false :
    presburgerBubble.decide nestedExists = some false :=
  decide_false_of_unsat nestedExists_unsat

theorem control_nested_exists_zero :
    presburgerBubble.decide nestedExistsZero = some true :=
  decide_true_of_sat nestedExistsZero_sat

theorem control_nested_even :
    presburgerBubble.decide nestedEven = some true :=
  decide_true_of_sat nestedEven_sat

theorem control_nested_double_odd :
    presburgerBubble.decide nestedDoubleOdd = some false :=
  decide_false_of_unsat nestedDoubleOdd_unsat

theorem control_zero_eq_zero_sat :
    (closedEq 0 0).sat env0 := by
  simpa [presburgerBubble, Bubble.decide] using
    (presburgerBubble_decides (closedEq 0 0) control_zero_eq_zero).mp rfl

theorem control_zero_eq_one_unsat :
    ¬ (closedEq 0 1).sat env0 := by
  intro hsat
  have hdecide :=
    (presburgerBubble_decides (closedEq 0 1) control_zero_eq_one).mpr hsat
  simp at hdecide

end Mettapedia.Logic.Arithmetic.PresburgerBubble

#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula.cooper_iff
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula.eliminate_iff
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula.decideClosed_iff
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.presburgerBubble_decides
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.presburgerBubble_iff_sat
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula.exists_iff_below
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.qf_arity1_semilinear
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.multiplication_graph_not_presburger_definable
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.checkWitness_sound
#print axioms Mettapedia.Logic.Arithmetic.PresburgerBubble.exists_iff_witnessOf
