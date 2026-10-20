import Mathlib.Computability.Partrec
import Mathlib.Data.Set.Basic

/-!
# The language of second-order arithmetic and its ω-models

The language `L₂` of second-order arithmetic has number terms built from
`0`, `1`, `+` and `·`, atomic formulas `t = u`, `t < u` and `t ∈ X`, the
propositional connectives, quantifiers over numbers and quantifiers over sets
(Simpson, *Subsystems of Second Order Arithmetic*, §I.2). Variables are de
Bruijn indices, with separate index spaces for numbers and sets.

A `Signature` adds binary function symbols with a fixed meaning on `ℕ`.
`Signature.arith` adds nothing, so `Formula Signature.arith` is exactly
`L₂`. `Signature.primrec` adds every primitive recursive binary function.
Over ω-models this extension is definitional (each primitive recursive graph
is `Σ⁰₁`-definable in `L₂`, Simpson §II.3), and it makes coding visible in the
syntax. Theorems that need only computable meanings are stated for every
`Signature.IsComputable` signature.

Bounded quantifiers `∀ x < t` and `∃ x < t` are primitive, so the arithmetical
hierarchy is syntactic:

* `IsBounded`: `Σ⁰₀ = Π⁰₀`, only bounded number quantifiers and no set
  quantifiers; set variables may occur free as parameters.
* `IsSigma n`, `IsPi n`: a block of `n` alternating unbounded number
  quantifiers in front of a bounded matrix (Simpson's prenex classes).
* `IsArithmetical`: no set quantifiers.

An ω-model is a family `S : Set (Set ℕ)`: the numbers are the standard ones
and set quantifiers range over `S` (Simpson §I.2 and Chapter VIII).
`Holds S φ v V` is satisfaction under a number environment `v` and a set
environment `V`; `Satisfies S φ` is satisfaction of the universal closure;
`Models S T` requires a nonempty family satisfying every formula in `T`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

/-- Extra binary function symbols with a fixed meaning on the naturals. -/
structure Signature where
  Fn : Type
  interp : Fn → ℕ → ℕ → ℕ

namespace Signature

/-- No extra symbols: the language `L₂` of Simpson §I.2. -/
def arith : Signature := ⟨Empty, fun f => Empty.elim f⟩

/-- Every primitive recursive binary function as a symbol. -/
def primrec : Signature := ⟨{f : ℕ → ℕ → ℕ // Primrec₂ f}, fun f => f.1⟩

/-- Every extra symbol denotes a computable function. -/
def IsComputable (σ : Signature) : Prop :=
  ∀ f, Computable₂ (σ.interp f)

theorem arith_isComputable : arith.IsComputable := fun f => Empty.elim f

theorem primrec_isComputable : primrec.IsComputable := fun f => f.2.to_comp

/-- Negative example: a signature naming a non-computable function is not
computable. -/
theorem not_isComputable_of {σ : Signature} (f : σ.Fn) (h : ¬ Computable₂ (σ.interp f)) :
    ¬ σ.IsComputable := fun computable => h (computable f)

end Signature

/-- Extending an environment by a new innermost variable. -/
def Env.cons {α : Type*} (a : α) (f : ℕ → α) : ℕ → α
  | 0 => a
  | n + 1 => f n

@[simp] theorem Env.cons_zero {α : Type*} (a : α) (f : ℕ → α) : Env.cons a f 0 = a := rfl

@[simp] theorem Env.cons_succ {α : Type*} (a : α) (f : ℕ → α) (n : ℕ) :
    Env.cons a f (n + 1) = f n := rfl

theorem Env.cons_comp_succ {α : Type*} (a : α) (f : ℕ → α) : Env.cons a f ∘ Nat.succ = f :=
  rfl

/-- Lifting a renaming under a binder. -/
def liftRen (ρ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ρ n + 1

theorem Env.cons_comp_liftRen {α : Type*} (a : α) (f : ℕ → α) (ρ : ℕ → ℕ) :
    Env.cons a f ∘ liftRen ρ = Env.cons a (f ∘ ρ) := by
  funext n
  cases n <;> rfl

variable {σ : Signature}

/-- Number terms. -/
inductive Term (σ : Signature) : Type
  | var : ℕ → Term σ
  | zero : Term σ
  | one : Term σ
  | add : Term σ → Term σ → Term σ
  | mul : Term σ → Term σ → Term σ
  | app : σ.Fn → Term σ → Term σ → Term σ

namespace Term

/-- The value of a term. -/
def eval (v : ℕ → ℕ) : Term σ → ℕ
  | var i => v i
  | zero => 0
  | one => 1
  | add t u => t.eval v + u.eval v
  | mul t u => t.eval v * u.eval v
  | app f t u => σ.interp f (t.eval v) (u.eval v)

/-- Renaming the number variables of a term. -/
def rename (ρ : ℕ → ℕ) : Term σ → Term σ
  | var i => var (ρ i)
  | zero => zero
  | one => one
  | add t u => add (t.rename ρ) (u.rename ρ)
  | mul t u => mul (t.rename ρ) (u.rename ρ)
  | app f t u => app f (t.rename ρ) (u.rename ρ)

theorem eval_rename (ρ : ℕ → ℕ) (v : ℕ → ℕ) (t : Term σ) :
    (t.rename ρ).eval v = t.eval (v ∘ ρ) := by
  induction t with
  | var i => rfl
  | zero => rfl
  | one => rfl
  | add t u ht hu => simp [rename, eval, ht, hu]
  | mul t u ht hu => simp [rename, eval, ht, hu]
  | app f t u ht hu => simp [rename, eval, ht, hu]

end Term

/-- Formulas of second-order arithmetic. Number binders (`ballLt`, `bexLt`,
`all`, `ex`) bind number variable `0` in their body; the bound of `ballLt t φ`
lives outside the binder. Set binders (`allSet`, `exSet`) bind set variable
`0`. -/
inductive Formula (σ : Signature) : Type
  | eq : Term σ → Term σ → Formula σ
  | lt : Term σ → Term σ → Formula σ
  | mem : Term σ → ℕ → Formula σ
  | falsum : Formula σ
  | imp : Formula σ → Formula σ → Formula σ
  | and : Formula σ → Formula σ → Formula σ
  | or : Formula σ → Formula σ → Formula σ
  | ballLt : Term σ → Formula σ → Formula σ
  | bexLt : Term σ → Formula σ → Formula σ
  | all : Formula σ → Formula σ
  | ex : Formula σ → Formula σ
  | allSet : Formula σ → Formula σ
  | exSet : Formula σ → Formula σ

namespace Formula

/-- Negation. -/
def not (φ : Formula σ) : Formula σ := imp φ falsum

/-- The biconditional. -/
def iff (φ ψ : Formula σ) : Formula σ := and (imp φ ψ) (imp ψ φ)

/-- Satisfaction in the ω-model `S` under a number environment `v` and a set
environment `V`. -/
def Holds (S : Set (Set ℕ)) : Formula σ → (ℕ → ℕ) → (ℕ → Set ℕ) → Prop
  | eq t u, v, _ => t.eval v = u.eval v
  | lt t u, v, _ => t.eval v < u.eval v
  | mem t j, v, V => t.eval v ∈ V j
  | falsum, _, _ => False
  | imp φ ψ, v, V => Holds S φ v V → Holds S ψ v V
  | and φ ψ, v, V => Holds S φ v V ∧ Holds S ψ v V
  | or φ ψ, v, V => Holds S φ v V ∨ Holds S ψ v V
  | ballLt t φ, v, V => ∀ n < t.eval v, Holds S φ (Env.cons n v) V
  | bexLt t φ, v, V => ∃ n < t.eval v, Holds S φ (Env.cons n v) V
  | all φ, v, V => ∀ n, Holds S φ (Env.cons n v) V
  | ex φ, v, V => ∃ n, Holds S φ (Env.cons n v) V
  | allSet φ, v, V => ∀ X ∈ S, Holds S φ v (Env.cons X V)
  | exSet φ, v, V => ∃ X ∈ S, Holds S φ v (Env.cons X V)

@[simp] theorem holds_not (S : Set (Set ℕ)) (φ : Formula σ) (v : ℕ → ℕ) (V : ℕ → Set ℕ) :
    Holds S (not φ) v V ↔ ¬ Holds S φ v V := Iff.rfl

@[simp] theorem holds_iff (S : Set (Set ℕ)) (φ ψ : Formula σ) (v : ℕ → ℕ) (V : ℕ → Set ℕ) :
    Holds S (iff φ ψ) v V ↔ (Holds S φ v V ↔ Holds S ψ v V) := by
  simp only [iff, Holds]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ## Renaming -/

/-- Renaming the free number variables. -/
def renameNum (ρ : ℕ → ℕ) : Formula σ → Formula σ
  | eq t u => eq (t.rename ρ) (u.rename ρ)
  | lt t u => lt (t.rename ρ) (u.rename ρ)
  | mem t j => mem (t.rename ρ) j
  | falsum => falsum
  | imp φ ψ => imp (φ.renameNum ρ) (ψ.renameNum ρ)
  | and φ ψ => and (φ.renameNum ρ) (ψ.renameNum ρ)
  | or φ ψ => or (φ.renameNum ρ) (ψ.renameNum ρ)
  | ballLt t φ => ballLt (t.rename ρ) (φ.renameNum (liftRen ρ))
  | bexLt t φ => bexLt (t.rename ρ) (φ.renameNum (liftRen ρ))
  | all φ => all (φ.renameNum (liftRen ρ))
  | ex φ => ex (φ.renameNum (liftRen ρ))
  | allSet φ => allSet (φ.renameNum ρ)
  | exSet φ => exSet (φ.renameNum ρ)

/-- Renaming the free set variables. -/
def renameSet (ρ : ℕ → ℕ) : Formula σ → Formula σ
  | eq t u => eq t u
  | lt t u => lt t u
  | mem t j => mem t (ρ j)
  | falsum => falsum
  | imp φ ψ => imp (φ.renameSet ρ) (ψ.renameSet ρ)
  | and φ ψ => and (φ.renameSet ρ) (ψ.renameSet ρ)
  | or φ ψ => or (φ.renameSet ρ) (ψ.renameSet ρ)
  | ballLt t φ => ballLt t (φ.renameSet ρ)
  | bexLt t φ => bexLt t (φ.renameSet ρ)
  | all φ => all (φ.renameSet ρ)
  | ex φ => ex (φ.renameSet ρ)
  | allSet φ => allSet (φ.renameSet (liftRen ρ))
  | exSet φ => exSet (φ.renameSet (liftRen ρ))

theorem holds_renameNum (S : Set (Set ℕ)) (φ : Formula σ) :
    ∀ (ρ : ℕ → ℕ) (v : ℕ → ℕ) (V : ℕ → Set ℕ),
      Holds S (φ.renameNum ρ) v V ↔ Holds S φ (v ∘ ρ) V := by
  induction φ with
  | eq t u => intro ρ v V; simp [renameNum, Holds, Term.eval_rename]
  | lt t u => intro ρ v V; simp [renameNum, Holds, Term.eval_rename]
  | mem t j => intro ρ v V; simp [renameNum, Holds, Term.eval_rename]
  | falsum => intro ρ v V; rfl
  | imp φ ψ hφ hψ => intro ρ v V; simp only [renameNum, Holds, hφ, hψ]
  | and φ ψ hφ hψ => intro ρ v V; simp only [renameNum, Holds, hφ, hψ]
  | or φ ψ hφ hψ => intro ρ v V; simp only [renameNum, Holds, hφ, hψ]
  | ballLt t φ hφ =>
      intro ρ v V
      simp only [renameNum, Holds, hφ, Env.cons_comp_liftRen, Term.eval_rename]
  | bexLt t φ hφ =>
      intro ρ v V
      simp only [renameNum, Holds, hφ, Env.cons_comp_liftRen, Term.eval_rename]
  | all φ hφ => intro ρ v V; simp only [renameNum, Holds, hφ, Env.cons_comp_liftRen]
  | ex φ hφ => intro ρ v V; simp only [renameNum, Holds, hφ, Env.cons_comp_liftRen]
  | allSet φ hφ => intro ρ v V; simp only [renameNum, Holds, hφ]
  | exSet φ hφ => intro ρ v V; simp only [renameNum, Holds, hφ]

theorem holds_renameSet (S : Set (Set ℕ)) (φ : Formula σ) :
    ∀ (ρ : ℕ → ℕ) (v : ℕ → ℕ) (V : ℕ → Set ℕ),
      Holds S (φ.renameSet ρ) v V ↔ Holds S φ v (V ∘ ρ) := by
  induction φ with
  | eq t u => intro ρ v V; rfl
  | lt t u => intro ρ v V; rfl
  | mem t j => intro ρ v V; rfl
  | falsum => intro ρ v V; rfl
  | imp φ ψ hφ hψ => intro ρ v V; simp only [renameSet, Holds, hφ, hψ]
  | and φ ψ hφ hψ => intro ρ v V; simp only [renameSet, Holds, hφ, hψ]
  | or φ ψ hφ hψ => intro ρ v V; simp only [renameSet, Holds, hφ, hψ]
  | ballLt t φ hφ => intro ρ v V; simp only [renameSet, Holds, hφ]
  | bexLt t φ hφ => intro ρ v V; simp only [renameSet, Holds, hφ]
  | all φ hφ => intro ρ v V; simp only [renameSet, Holds, hφ]
  | ex φ hφ => intro ρ v V; simp only [renameSet, Holds, hφ]
  | allSet φ hφ => intro ρ v V; simp only [renameSet, Holds, hφ, Env.cons_comp_liftRen]
  | exSet φ hφ => intro ρ v V; simp only [renameSet, Holds, hφ, Env.cons_comp_liftRen]

/-! ## The arithmetical hierarchy -/

/-- `Σ⁰₀ = Π⁰₀`: only bounded number quantifiers, no set quantifiers. -/
inductive IsBounded : Formula σ → Prop
  | eq (t u : Term σ) : IsBounded (eq t u)
  | lt (t u : Term σ) : IsBounded (lt t u)
  | mem (t : Term σ) (j : ℕ) : IsBounded (mem t j)
  | falsum : IsBounded falsum
  | imp {φ ψ : Formula σ} : IsBounded φ → IsBounded ψ → IsBounded (imp φ ψ)
  | and {φ ψ : Formula σ} : IsBounded φ → IsBounded ψ → IsBounded (and φ ψ)
  | or {φ ψ : Formula σ} : IsBounded φ → IsBounded ψ → IsBounded (or φ ψ)
  | ballLt (t : Term σ) {φ : Formula σ} : IsBounded φ → IsBounded (ballLt t φ)
  | bexLt (t : Term σ) {φ : Formula σ} : IsBounded φ → IsBounded (bexLt t φ)

/-- The prenex classes: `InClass true n` is `Σ⁰ₙ`, `InClass false n` is `Π⁰ₙ`. -/
inductive InClass : Bool → ℕ → Formula σ → Prop
  | bounded (b : Bool) {φ : Formula σ} : IsBounded φ → InClass b 0 φ
  | ex {n : ℕ} {φ : Formula σ} : InClass false n φ → InClass true (n + 1) (ex φ)
  | all {n : ℕ} {φ : Formula σ} : InClass true n φ → InClass false (n + 1) (all φ)

/-- `Σ⁰ₙ` formulas. -/
def IsSigma (n : ℕ) (φ : Formula σ) : Prop := InClass true n φ

/-- `Π⁰ₙ` formulas. -/
def IsPi (n : ℕ) (φ : Formula σ) : Prop := InClass false n φ

/-- Arithmetical formulas: no set quantifiers. -/
inductive IsArithmetical : Formula σ → Prop
  | eq (t u : Term σ) : IsArithmetical (eq t u)
  | lt (t u : Term σ) : IsArithmetical (lt t u)
  | mem (t : Term σ) (j : ℕ) : IsArithmetical (mem t j)
  | falsum : IsArithmetical falsum
  | imp {φ ψ : Formula σ} : IsArithmetical φ → IsArithmetical ψ → IsArithmetical (imp φ ψ)
  | and {φ ψ : Formula σ} : IsArithmetical φ → IsArithmetical ψ → IsArithmetical (and φ ψ)
  | or {φ ψ : Formula σ} : IsArithmetical φ → IsArithmetical ψ → IsArithmetical (or φ ψ)
  | ballLt (t : Term σ) {φ : Formula σ} : IsArithmetical φ → IsArithmetical (ballLt t φ)
  | bexLt (t : Term σ) {φ : Formula σ} : IsArithmetical φ → IsArithmetical (bexLt t φ)
  | all {φ : Formula σ} : IsArithmetical φ → IsArithmetical (all φ)
  | ex {φ : Formula σ} : IsArithmetical φ → IsArithmetical (ex φ)

theorem IsBounded.isArithmetical {φ : Formula σ} (h : IsBounded φ) : IsArithmetical φ := by
  induction h with
  | eq t u => exact .eq t u
  | lt t u => exact .lt t u
  | mem t j => exact .mem t j
  | falsum => exact .falsum
  | imp _ _ hφ hψ => exact .imp hφ hψ
  | and _ _ hφ hψ => exact .and hφ hψ
  | or _ _ hφ hψ => exact .or hφ hψ
  | ballLt t _ hφ => exact .ballLt t hφ
  | bexLt t _ hφ => exact .bexLt t hφ

theorem InClass.isArithmetical {b : Bool} {n : ℕ} {φ : Formula σ} (h : InClass b n φ) :
    IsArithmetical φ := by
  induction h with
  | bounded _ hφ => exact hφ.isArithmetical
  | ex _ hφ => exact .ex hφ
  | all _ hφ => exact .all hφ

theorem IsSigma.isArithmetical {n : ℕ} {φ : Formula σ} (h : IsSigma n φ) : IsArithmetical φ :=
  InClass.isArithmetical h

theorem IsPi.isArithmetical {n : ℕ} {φ : Formula σ} (h : IsPi n φ) : IsArithmetical φ :=
  InClass.isArithmetical h

/-- A `Σ⁰₁` formula is an unbounded existential over a bounded matrix. -/
theorem isSigma_one_iff {φ : Formula σ} : IsSigma 1 φ ↔ ∃ θ, IsBounded θ ∧ φ = ex θ := by
  constructor
  · intro h
    unfold IsSigma at h
    cases h with
    | ex hθ =>
        cases hθ with
        | bounded _ hb => exact ⟨_, hb, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact InClass.ex (InClass.bounded false hθ)

/-- A `Π⁰₁` formula is an unbounded universal over a bounded matrix. -/
theorem isPi_one_iff {φ : Formula σ} : IsPi 1 φ ↔ ∃ θ, IsBounded θ ∧ φ = all θ := by
  constructor
  · intro h
    unfold IsPi at h
    cases h with
    | all hθ =>
        cases hθ with
        | bounded _ hb => exact ⟨_, hb, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact InClass.all (InClass.bounded true hθ)

theorem IsBounded.renameNum {φ : Formula σ} (h : IsBounded φ) :
    ∀ ρ : ℕ → ℕ, IsBounded (φ.renameNum ρ) := by
  induction h with
  | eq t u => intro ρ; exact .eq _ _
  | lt t u => intro ρ; exact .lt _ _
  | mem t j => intro ρ; exact .mem _ _
  | falsum => intro ρ; exact .falsum
  | imp _ _ hφ hψ => intro ρ; exact .imp (hφ ρ) (hψ ρ)
  | and _ _ hφ hψ => intro ρ; exact .and (hφ ρ) (hψ ρ)
  | or _ _ hφ hψ => intro ρ; exact .or (hφ ρ) (hψ ρ)
  | ballLt t _ hφ => intro ρ; exact .ballLt _ (hφ _)
  | bexLt t _ hφ => intro ρ; exact .bexLt _ (hφ _)

theorem IsBounded.renameSet {φ : Formula σ} (h : IsBounded φ) :
    ∀ ρ : ℕ → ℕ, IsBounded (φ.renameSet ρ) := by
  induction h with
  | eq t u => intro ρ; exact .eq _ _
  | lt t u => intro ρ; exact .lt _ _
  | mem t j => intro ρ; exact .mem _ _
  | falsum => intro ρ; exact .falsum
  | imp _ _ hφ hψ => intro ρ; exact .imp (hφ ρ) (hψ ρ)
  | and _ _ hφ hψ => intro ρ; exact .and (hφ ρ) (hψ ρ)
  | or _ _ hφ hψ => intro ρ; exact .or (hφ ρ) (hψ ρ)
  | ballLt t _ hφ => intro ρ; exact .ballLt _ (hφ _)
  | bexLt t _ hφ => intro ρ; exact .bexLt _ (hφ _)

/-- Every set variable that occurs free has index below `k`. -/
inductive SetVarsBelow : ℕ → Formula σ → Prop
  | eq (k : ℕ) (t u : Term σ) : SetVarsBelow k (eq t u)
  | lt (k : ℕ) (t u : Term σ) : SetVarsBelow k (lt t u)
  | mem {k j : ℕ} (t : Term σ) : j < k → SetVarsBelow k (mem t j)
  | falsum (k : ℕ) : SetVarsBelow k falsum
  | imp {k : ℕ} {φ ψ : Formula σ} : SetVarsBelow k φ → SetVarsBelow k ψ →
      SetVarsBelow k (imp φ ψ)
  | and {k : ℕ} {φ ψ : Formula σ} : SetVarsBelow k φ → SetVarsBelow k ψ →
      SetVarsBelow k (and φ ψ)
  | or {k : ℕ} {φ ψ : Formula σ} : SetVarsBelow k φ → SetVarsBelow k ψ →
      SetVarsBelow k (or φ ψ)
  | ballLt {k : ℕ} (t : Term σ) {φ : Formula σ} : SetVarsBelow k φ → SetVarsBelow k (ballLt t φ)
  | bexLt {k : ℕ} (t : Term σ) {φ : Formula σ} : SetVarsBelow k φ → SetVarsBelow k (bexLt t φ)
  | all {k : ℕ} {φ : Formula σ} : SetVarsBelow k φ → SetVarsBelow k (all φ)
  | ex {k : ℕ} {φ : Formula σ} : SetVarsBelow k φ → SetVarsBelow k (ex φ)
  | allSet {k : ℕ} {φ : Formula σ} : SetVarsBelow (k + 1) φ → SetVarsBelow k (allSet φ)
  | exSet {k : ℕ} {φ : Formula σ} : SetVarsBelow (k + 1) φ → SetVarsBelow k (exSet φ)

/-- A number bounding the free set variables. -/
def setBound : Formula σ → ℕ
  | eq _ _ => 0
  | lt _ _ => 0
  | mem _ j => j + 1
  | falsum => 0
  | imp φ ψ => max φ.setBound ψ.setBound
  | and φ ψ => max φ.setBound ψ.setBound
  | or φ ψ => max φ.setBound ψ.setBound
  | ballLt _ φ => φ.setBound
  | bexLt _ φ => φ.setBound
  | all φ => φ.setBound
  | ex φ => φ.setBound
  | allSet φ => φ.setBound - 1
  | exSet φ => φ.setBound - 1

theorem SetVarsBelow.mono {k : ℕ} {φ : Formula σ} (h : SetVarsBelow k φ) :
    ∀ {m : ℕ}, k ≤ m → SetVarsBelow m φ := by
  induction h with
  | eq k t u => intro m _; exact .eq m t u
  | lt k t u => intro m _; exact .lt m t u
  | mem t hj => intro m hm; exact .mem t (lt_of_lt_of_le hj hm)
  | falsum k => intro m _; exact .falsum m
  | imp _ _ hφ hψ => intro m hm; exact .imp (hφ hm) (hψ hm)
  | and _ _ hφ hψ => intro m hm; exact .and (hφ hm) (hψ hm)
  | or _ _ hφ hψ => intro m hm; exact .or (hφ hm) (hψ hm)
  | ballLt t _ hφ => intro m hm; exact .ballLt t (hφ hm)
  | bexLt t _ hφ => intro m hm; exact .bexLt t (hφ hm)
  | all _ hφ => intro m hm; exact .all (hφ hm)
  | ex _ hφ => intro m hm; exact .ex (hφ hm)
  | allSet _ hφ => intro m hm; exact .allSet (hφ (Nat.succ_le_succ hm))
  | exSet _ hφ => intro m hm; exact .exSet (hφ (Nat.succ_le_succ hm))

/-- `setBound` bounds the free set variables. -/
theorem setVarsBelow_setBound (φ : Formula σ) : SetVarsBelow φ.setBound φ := by
  induction φ with
  | eq t u => exact .eq _ t u
  | lt t u => exact .lt _ t u
  | mem t j => exact .mem t (Nat.lt_succ_self j)
  | falsum => exact .falsum _
  | imp φ ψ hφ hψ =>
      exact .imp (hφ.mono (le_max_left _ _)) (hψ.mono (le_max_right _ _))
  | and φ ψ hφ hψ =>
      exact .and (hφ.mono (le_max_left _ _)) (hψ.mono (le_max_right _ _))
  | or φ ψ hφ hψ =>
      exact .or (hφ.mono (le_max_left _ _)) (hψ.mono (le_max_right _ _))
  | ballLt t φ hφ => exact .ballLt t hφ
  | bexLt t φ hφ => exact .bexLt t hφ
  | all φ hφ => exact .all hφ
  | ex φ hφ => exact .ex hφ
  | allSet φ hφ => exact .allSet (hφ.mono (by simp only [setBound]; omega))
  | exSet φ hφ => exact .exSet (hφ.mono (by simp only [setBound]; omega))

/-- Satisfaction depends only on the set variables below a bound. -/
theorem holds_congr_set (S : Set (Set ℕ)) {k : ℕ} {φ : Formula σ} (h : SetVarsBelow k φ) :
    ∀ (v : ℕ → ℕ) (V W : ℕ → Set ℕ), (∀ j < k, V j = W j) →
      (Holds S φ v V ↔ Holds S φ v W) := by
  induction h with
  | eq k t u => intro v V W _; rfl
  | lt k t u => intro v V W _; rfl
  | mem t hj => intro v V W agree; simp only [Holds, agree _ hj]
  | falsum k => intro v V W _; rfl
  | imp _ _ hφ hψ => intro v V W agree; simp only [Holds, hφ v V W agree, hψ v V W agree]
  | and _ _ hφ hψ => intro v V W agree; simp only [Holds, hφ v V W agree, hψ v V W agree]
  | or _ _ hφ hψ => intro v V W agree; simp only [Holds, hφ v V W agree, hψ v V W agree]
  | ballLt t _ hφ =>
      intro v V W agree
      simp only [Holds]
      exact forall_congr' fun n => imp_congr_right fun _ => hφ _ V W agree
  | bexLt t _ hφ =>
      intro v V W agree
      simp only [Holds]
      exact exists_congr fun n => and_congr_right fun _ => hφ _ V W agree
  | all _ hφ =>
      intro v V W agree
      simp only [Holds]
      exact forall_congr' fun n => hφ _ V W agree
  | ex _ hφ =>
      intro v V W agree
      simp only [Holds]
      exact exists_congr fun n => hφ _ V W agree
  | allSet _ hφ =>
      intro v V W agree
      simp only [Holds]
      refine forall_congr' fun X => imp_congr_right fun _ => hφ v _ _ fun j hj => ?_
      cases j with
      | zero => rfl
      | succ j => exact agree j (by omega)
  | exSet _ hφ =>
      intro v V W agree
      simp only [Holds]
      refine exists_congr fun X => and_congr_right fun _ => hφ v _ _ fun j hj => ?_
      cases j with
      | zero => rfl
      | succ j => exact agree j (by omega)

/-- Satisfaction of an arithmetical formula does not depend on the ω-model. -/
theorem IsArithmetical.holds_iff {φ : Formula σ} (h : IsArithmetical φ) (S T : Set (Set ℕ)) :
    ∀ (v : ℕ → ℕ) (V : ℕ → Set ℕ), Holds S φ v V ↔ Holds T φ v V := by
  induction h with
  | eq t u => intro v V; rfl
  | lt t u => intro v V; rfl
  | mem t j => intro v V; rfl
  | falsum => intro v V; rfl
  | imp _ _ hφ hψ => intro v V; simp only [Holds, hφ v V, hψ v V]
  | and _ _ hφ hψ => intro v V; simp only [Holds, hφ v V, hψ v V]
  | or _ _ hφ hψ => intro v V; simp only [Holds, hφ v V, hψ v V]
  | ballLt t _ hφ =>
      intro v V
      simp only [Holds]
      exact forall_congr' fun n => imp_congr_right fun _ => hφ _ V
  | bexLt t _ hφ =>
      intro v V
      simp only [Holds]
      exact exists_congr fun n => and_congr_right fun _ => hφ _ V
  | all _ hφ => intro v V; simp only [Holds]; exact forall_congr' fun n => hφ _ V
  | ex _ hφ => intro v V; simp only [Holds]; exact exists_congr fun n => hφ _ V

end Formula

/-! ## ω-models -/

open Formula

/-- The universal closure of `φ` holds in the ω-model `S`: every assignment
of numbers to the number variables and of members of `S` to the set
variables satisfies `φ`. -/
def Satisfies (S : Set (Set ℕ)) (φ : Formula σ) : Prop :=
  ∀ (v : ℕ → ℕ) (V : ℕ → Set ℕ), (∀ j, V j ∈ S) → Holds S φ v V

/-- `S` is an ω-model of the theory `T`: a nonempty family satisfying every
formula of `T` (Simpson §VIII.1). -/
def Models (S : Set (Set ℕ)) (T : Set (Formula σ)) : Prop :=
  S.Nonempty ∧ ∀ φ ∈ T, Satisfies S φ

theorem Models.mono {S : Set (Set ℕ)} {T U : Set (Formula σ)} (h : Models S U) (sub : T ⊆ U) :
    Models S T :=
  ⟨h.1, fun φ member => h.2 φ (sub member)⟩

/-! ## Examples -/

section Examples

open Term

/-- `∀ x < y, x < y`: bounded, and true everywhere. -/
def boundedExample : Formula Signature.arith := ballLt (var 0) (lt (var 0) (var 1))

/-- Positive example of `IsBounded`, `IsSigma 0` and `IsArithmetical`. -/
example : IsBounded boundedExample := .ballLt _ (.lt _ _)

example : IsSigma 0 boundedExample := InClass.bounded true (.ballLt _ (.lt _ _))

/-- Negative example: an unbounded quantifier is not bounded. -/
example : ¬ IsBounded (all (eq (var 0) (var 0)) : Formula Signature.arith) := by
  intro h
  cases h

/-- Positive example: `∃ x, x ∈ X₀` is `Σ⁰₁`. -/
example : IsSigma 1 (ex (mem (var 0) 0) : Formula Signature.arith) :=
  isSigma_one_iff.mpr ⟨_, .mem _ _, rfl⟩

/-- Negative example: `∃ x, x ∈ X₀` is not `Π⁰₁`. -/
example : ¬ IsPi 1 (ex (mem (var 0) 0) : Formula Signature.arith) := by
  intro h
  obtain ⟨θ, _, same⟩ := isPi_one_iff.mp h
  cases same

/-- Negative example: a set quantifier is not arithmetical. -/
example : ¬ IsArithmetical (exSet (mem zero 0) : Formula Signature.arith) := by
  intro h
  cases h

/-- Positive example of `Holds`: the bounded sentence holds at every
assignment. -/
example (S : Set (Set ℕ)) (v : ℕ → ℕ) (V : ℕ → Set ℕ) : Holds S boundedExample v V :=
  fun _ lt => lt

/-- Set quantifiers range over the ω-model: `∃ X, 0 ∈ X` holds in `{univ}`
and fails in `{∅}`. -/
example : Satisfies ({Set.univ} : Set (Set ℕ))
    (exSet (mem zero 0) : Formula Signature.arith) :=
  fun _ _ _ => ⟨Set.univ, rfl, trivial⟩

example : ¬ Satisfies ({∅} : Set (Set ℕ)) (exSet (mem zero 0) : Formula Signature.arith) := by
  intro h
  obtain ⟨X, member, zeroIn⟩ := h (fun _ => 0) (fun _ => ∅) (fun _ => rfl)
  rw [Set.mem_singleton_iff] at member
  subst member
  exact zeroIn

/-- Negative example of `Models`: the empty family is not an ω-model of
anything, not even of the empty theory. -/
example : ¬ Models (∅ : Set (Set ℕ)) (∅ : Set (Formula Signature.arith)) :=
  fun h => Set.not_nonempty_empty h.1

end Examples

end Mettapedia.Logic.ReverseMathematics
