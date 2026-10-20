import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHead
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Environment Machine with Closures and Stratified Normal Forms (`smalltt`-Style NbE)

This module implements the Normalization-by-Evaluation (NbE) semantic domain and
closure-based environment machine for `ParameterizedPiSigmaId` (following Coquand 1996,
Abel 2013, Kovács's `smalltt`, and Jang et al. McTT 2025):

1. **Semantic Domain with Defunctionalized Closures (`Val`, `Clos`, `Env`)**:
   - `Val Head n`: semantic values in ambient target scope `n`.
   - `Clos Head n`: defunctionalized lexical closures `Clos.mk env body` pairing an
     environment `env : Env Head m n` with an unevaluated binder body `body : Tm Head (m + 1)`.
   - `Env Head m n`: lexical environments mapping source indices `Fin m` to semantic
     values `Val Head n` without eager syntactic shifting or substitution.

2. **Exact Syntactic Realization (`toTm`, `toSub`) and Binder-Opening Identity**:
   - Every value `v : Val Head n` realizes to `v.toTm : Tm Head n`, and every environment
     `env : Env Head m n` realizes to a simultaneous substitution `env.toSub : Sub Head m n`.
   - Crucially, weakening `env` by `wk` and extending with `.var 0` realizes to the exact
     lifted substitution: `((env.rename wk).snoc (.var 0)).toSub = liftSub env.toSub`
     (`Env.toSub_snoc_wk_var0`), and opening a closure realizes to environment extension:
     `inst0 v.toTm (Clos.mk env body).toTm = subst (env.snoc v).toSub body`
     (`Clos.inst0_toTm`).

3. **Stratified Normal and Neutral Forms (`Nf`, `Ne`)**:
   - `Nf Head n` and `Ne Head n` syntactically forbid β-redexes (`app (lam ..)`,
     `fst (pair ..)`, `snd (pair ..)`).
   - Theorem `Nf.step_empty_eq_none` proves that every `nf : Nf Head n` is in normal form
     with respect to structural β-reduction (`ExecutableReduction.step`).

4. **Certified Closure Evaluation (`eval`) and Readback (`quoteVal`, `nbeNormNf`)**:
   - `eval` evaluates `t : Tm Head m` in `env : Env Head m n` using $O(1)$ closure creation
     for `lam`, `pi`, and `sigma`, $O(1)$ environment extension for β-redexes, $O(1)$
     pair projection for `fst`/`snd`, and root/δ-unfolding via `RootEvaluator R`,
     returning a certified reduction path `Reduces R (subst env.toSub t) v.toTm`.
   - `quoteVal` forces all remaining closures under binders and produces a stratified
     normal form `nf : Nf Head n` with a certified reduction `Reduces R v.toTm nf.toTm`.
   - `nbeReducer` and `nbeWhnfReducer` package the machine as verified instances of
     `ExecutableReduction.Reducer R`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NbE

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Normalization

/-! ## 1. Stratified Normal and Neutral Forms -/

mutual

/-- Stratified β-normal forms in scope `n`. Function application and pair projections
are restricted to neutral spines (`Ne Head n`), making β-redexes unrepresentable. -/
inductive Nf (Head : Type) : Nat → Type where
  | ne {n : Nat} : Ne Head n → Nf Head n
  | head {n : Nat} : Head → Nf Head n
  | pi {n : Nat} : Nf Head n → Nf Head (n + 1) → Nf Head n
  | sigma {n : Nat} : Nf Head n → Nf Head (n + 1) → Nf Head n
  | id {n : Nat} : Nf Head n → Nf Head n → Nf Head n → Nf Head n
  | lam {n : Nat} : Nf Head (n + 1) → Nf Head n
  | pair {n : Nat} : Nf Head n → Nf Head n → Nf Head n
  | refl {n : Nat} : Nf Head n → Nf Head n

/-- Stratified neutral forms in scope `n`: variables or unexpanded constants
eliminated by normal arguments or projections. -/
inductive Ne (Head : Type) : Nat → Type where
  | var {n : Nat} : Fin n → Ne Head n
  | const {n : Nat} : DeclName → Ne Head n
  | app {n : Nat} : Ne Head n → Nf Head n → Ne Head n
  | fst {n : Nat} : Ne Head n → Ne Head n
  | snd {n : Nat} : Ne Head n → Ne Head n

end

namespace Nf

variable {Head : Type}

mutual

/-- Embed a stratified normal form back into a scoped term `Tm Head n`. -/
def toTm {n : Nat} : Nf Head n → Tm Head n
  | .ne ntm => Ne.toTm ntm
  | .head h => .head h
  | .pi A B => .pi (toTm A) (toTm B)
  | .sigma A B => .sigma (toTm A) (toTm B)
  | .id A a b => .id (toTm A) (toTm a) (toTm b)
  | .lam body => .lam (toTm body)
  | .pair a b => .pair (toTm a) (toTm b)
  | .refl a => .refl (toTm a)

/-- Embed a stratified neutral form back into a scoped term `Tm Head n`. -/
def _root_.Mettapedia.TypeTheory.NbE.Ne.toTm {n : Nat} : Ne Head n → Tm Head n
  | .var i => .var i
  | .const c => .const c
  | .app fn arg => .app (Ne.toTm fn) (Nf.toTm arg)
  | .fst p => .fst (Ne.toTm p)
  | .snd p => .snd (Ne.toTm p)

end

/-- A neutral form never embeds to a lambda abstraction. -/
theorem _root_.Mettapedia.TypeTheory.NbE.Ne.toTm_ne_lam {n : Nat}
    (ntm : Ne Head n) (body : Tm Head (n + 1)) :
    ntm.toTm ≠ .lam body := by
  cases ntm <;> intro h <;> cases h

/-- A neutral form never embeds to a pair constructor. -/
theorem _root_.Mettapedia.TypeTheory.NbE.Ne.toTm_ne_pair {n : Nat}
    (ntm : Ne Head n) (a b : Tm Head n) :
    ntm.toTm ≠ .pair a b := by
  cases ntm <;> intro h <;> cases h

mutual

/-- `Nf.toTm` is injective: distinct normal forms denote distinct terms. -/
theorem toTm_injective {n : Nat} :
    ∀ {x y : Nf Head n}, x.toTm = y.toTm → x = y
  | .ne nx, .ne ny, h => congrArg Nf.ne (Ne.toTm_injective h)
  | .ne nx, .head _, h => by cases nx <;> cases h
  | .ne nx, .pi _ _, h => by cases nx <;> cases h
  | .ne nx, .sigma _ _, h => by cases nx <;> cases h
  | .ne nx, .id _ _ _, h => by cases nx <;> cases h
  | .ne nx, .lam _, h => False.elim (Ne.toTm_ne_lam nx _ h)
  | .ne nx, .pair _ _, h => False.elim (Ne.toTm_ne_pair nx _ _ h)
  | .ne nx, .refl _, h => by cases nx <;> cases h
  | .head _, .ne ny, h => by cases ny <;> cases h
  | .pi _ _, .ne ny, h => by cases ny <;> cases h
  | .sigma _ _, .ne ny, h => by cases ny <;> cases h
  | .id _ _ _, .ne ny, h => by cases ny <;> cases h
  | .lam _, .ne ny, h => False.elim (Ne.toTm_ne_lam ny _ h.symm)
  | .pair _ _, .ne ny, h => False.elim (Ne.toTm_ne_pair ny _ _ h.symm)
  | .refl _, .ne ny, h => by cases ny <;> cases h
  | .head hx, .head hy, h => by cases h; rfl
  | .pi A₁ B₁, .pi A₂ B₂, h => by
      simp only [toTm, Tm.pi.injEq] at h
      rw [toTm_injective h.1, toTm_injective h.2]
  | .sigma A₁ B₁, .sigma A₂ B₂, h => by
      simp only [toTm, Tm.sigma.injEq] at h
      rw [toTm_injective h.1, toTm_injective h.2]
  | .id A₁ a₁ b₁, .id A₂ a₂ b₂, h => by
      simp only [toTm, Tm.id.injEq] at h
      rw [toTm_injective h.1, toTm_injective h.2.1, toTm_injective h.2.2]
  | .lam b₁, .lam b₂, h => by
      simp only [toTm, Tm.lam.injEq] at h
      rw [toTm_injective h]
  | .pair a₁ b₁, .pair a₂ b₂, h => by
      simp only [toTm, Tm.pair.injEq] at h
      rw [toTm_injective h.1, toTm_injective h.2]
  | .refl a₁, .refl a₂, h => by
      simp only [toTm, Tm.refl.injEq] at h
      rw [toTm_injective h]

/-- `Ne.toTm` is injective. -/
theorem _root_.Mettapedia.TypeTheory.NbE.Ne.toTm_injective {n : Nat} :
    ∀ {x y : Ne Head n}, x.toTm = y.toTm → x = y
  | .var i, .var j, h => by cases h; rfl
  | .const c₁, .const c₂, h => by cases h; rfl
  | .app f₁ a₁, .app f₂ a₂, h => by
      simp only [Ne.toTm, Tm.app.injEq] at h
      rw [Ne.toTm_injective h.1, Nf.toTm_injective h.2]
  | .fst p₁, .fst p₂, h => by
      simp only [Ne.toTm, Tm.fst.injEq] at h
      rw [Ne.toTm_injective h]
  | .snd p₁, .snd p₂, h => by
      simp only [Ne.toTm, Tm.snd.injEq] at h
      rw [Ne.toTm_injective h]

end

instance instDecidableEqNf [DecidableEq Head] {n : Nat} : DecidableEq (Nf Head n) :=
  fun x y => decidable_of_iff (x.toTm = y.toTm) ⟨toTm_injective, congrArg toTm⟩

instance instDecidableEqNe [DecidableEq Head] {n : Nat} : DecidableEq (Ne Head n) :=
  fun x y => decidable_of_iff (x.toTm = y.toTm) ⟨Ne.toTm_injective, congrArg Ne.toTm⟩

mutual

/-- Rename free variables in a normal form. -/
def rename {n m : Nat} (ρ : Ren n m) : Nf Head n → Nf Head m
  | .ne ntm => .ne (Ne.rename ρ ntm)
  | .head h => .head h
  | .pi A B => .pi (rename ρ A) (rename (liftRen ρ) B)
  | .sigma A B => .sigma (rename ρ A) (rename (liftRen ρ) B)
  | .id A a b => .id (rename ρ A) (rename ρ a) (rename ρ b)
  | .lam body => .lam (rename (liftRen ρ) body)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .refl a => .refl (rename ρ a)

/-- Rename free variables in a neutral form. -/
def _root_.Mettapedia.TypeTheory.NbE.Ne.rename {n m : Nat} (ρ : Ren n m) : Ne Head n → Ne Head m
  | .var i => .var (ρ i)
  | .const c => .const c
  | .app fn arg => .app (Ne.rename ρ fn) (Nf.rename ρ arg)
  | .fst p => .fst (Ne.rename ρ p)
  | .snd p => .snd (Ne.rename ρ p)

end

mutual

/-- Every stratified normal form has zero structural β-steps (`step` returns `none`
under an empty root evaluator). -/
theorem step_empty_eq_none (R : Rules Head) :
    ∀ {n : Nat} (nf : Nf Head n),
      ExecutableReduction.step R (fun _ => none) nf.toTm = none
  | _, .ne ntm => Ne.step_empty_eq_none R ntm
  | _, .head _ => rfl
  | _, .pi A B => by
      simp [toTm, ExecutableReduction.step, step_empty_eq_none R A, step_empty_eq_none R B]
  | _, .sigma A B => by
      simp [toTm, ExecutableReduction.step, step_empty_eq_none R A, step_empty_eq_none R B]
  | _, .id A a b => by
      simp [toTm, ExecutableReduction.step, step_empty_eq_none R A,
        step_empty_eq_none R a, step_empty_eq_none R b]
  | _, .lam body => by
      simp [toTm, ExecutableReduction.step, step_empty_eq_none R body]
  | _, .pair a b => by
      simp [toTm, ExecutableReduction.step, step_empty_eq_none R a, step_empty_eq_none R b]
  | _, .refl a => by
      simp [toTm, ExecutableReduction.step, step_empty_eq_none R a]

/-- Every stratified neutral form has zero structural β-steps. -/
theorem _root_.Mettapedia.TypeTheory.NbE.Ne.step_empty_eq_none (R : Rules Head) :
    ∀ {n : Nat} (ntm : Ne Head n),
      ExecutableReduction.step R (fun _ => none) ntm.toTm = none
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .app fn arg => by
      have hFn := Ne.step_empty_eq_none R fn
      have hArg := Nf.step_empty_eq_none R arg
      cases hTm : fn.toTm with
      | lam body => exact False.elim (Ne.toTm_ne_lam fn body hTm)
      | _ =>
          simp [Ne.toTm, ExecutableReduction.step, hTm] at hFn ⊢
          simp [hFn, hArg]
  | _, .fst p => by
      have hP := Ne.step_empty_eq_none R p
      cases hTm : p.toTm with
      | pair a b => exact False.elim (Ne.toTm_ne_pair p a b hTm)
      | _ =>
          simp [Ne.toTm, ExecutableReduction.step, hTm] at hP ⊢
          simp [hP]
  | _, .snd p => by
      have hP := Ne.step_empty_eq_none R p
      cases hTm : p.toTm with
      | pair a b => exact False.elim (Ne.toTm_ne_pair p a b hTm)
      | _ =>
          simp [Ne.toTm, ExecutableReduction.step, hTm] at hP ⊢
          simp [hP]

end

end Nf

/-! ## 2. Semantic Values, Defunctionalized Closures, and Lexical Environments -/

mutual

/-- Semantic values of the NbE environment machine in target scope `n`.
Binders (`lam`, `pi`, `sigma`) hold explicit lexical closures (`Clos Head n`). -/
inductive Val (Head : Type) : Nat → Type where
  | var {n : Nat} : Fin n → Val Head n
  | const {n : Nat} : DeclName → Val Head n
  | app {n : Nat} : Val Head n → Val Head n → Val Head n
  | fst {n : Nat} : Val Head n → Val Head n
  | snd {n : Nat} : Val Head n → Val Head n
  | head {n : Nat} : Head → Val Head n
  | pi {n : Nat} : Val Head n → Clos Head n → Val Head n
  | sigma {n : Nat} : Val Head n → Clos Head n → Val Head n
  | id {n : Nat} : Val Head n → Val Head n → Val Head n → Val Head n
  | lam {n : Nat} : Clos Head n → Val Head n
  | pair {n : Nat} : Val Head n → Val Head n → Val Head n
  | refl {n : Nat} : Val Head n → Val Head n

/-- A defunctionalized closure in target scope `n`: pairs a lexical environment
`env : Env Head m n` for source scope `m` with an unevaluated binder body
`body : Tm Head (m + 1)`. -/
inductive Clos (Head : Type) : Nat → Type where
  | mk {m n : Nat} (env : Env Head m n) (body : Tm Head (m + 1)) : Clos Head n

/-- A lexical environment mapping source scope `m` to semantic values in target scope `n`. -/
inductive Env (Head : Type) : Nat → Nat → Type where
  | nil {n : Nat} : Env Head 0 n
  | snoc {m n : Nat} : Env Head m n → Val Head n → Env Head (m + 1) n

end

namespace Val

variable {Head : Type}

/-- Look up a de Bruijn index `i : Fin m` in a lexical environment `Env Head m n`. -/
def _root_.Mettapedia.TypeTheory.NbE.Env.lookup {m n : Nat} :
    Env Head m n → Fin m → Val Head n
  | .nil, i => Fin.elim0 i
  | .snoc env v, i => Fin.cases v (fun j => env.lookup j) i

mutual

/-- Rename target-scope variables inside a semantic value `Val Head n`. -/
def rename {n k : Nat} (ρ : Ren n k) : Val Head n → Val Head k
  | .var i => .var (ρ i)
  | .const c => .const c
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .fst p => .fst (rename ρ p)
  | .snd p => .snd (rename ρ p)
  | .head h => .head h
  | .pi A B => .pi (rename ρ A) (Clos.rename ρ B)
  | .sigma A B => .sigma (rename ρ A) (Clos.rename ρ B)
  | .id A a b => .id (rename ρ A) (rename ρ a) (rename ρ b)
  | .lam body => .lam (Clos.rename ρ body)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .refl a => .refl (rename ρ a)

/-- Rename target-scope variables inside a closure `Clos Head n`. -/
def _root_.Mettapedia.TypeTheory.NbE.Clos.rename {n k : Nat} (ρ : Ren n k) :
    Clos Head n → Clos Head k
  | .mk env body => .mk (Env.rename ρ env) body

/-- Rename target-scope variables inside a lexical environment `Env Head m n`. -/
def _root_.Mettapedia.TypeTheory.NbE.Env.rename {m n k : Nat} (ρ : Ren n k) :
    Env Head m n → Env Head m k
  | .nil => .nil
  | .snoc env v => .snoc (Env.rename ρ env) (Val.rename ρ v)

end

mutual

/-- Realize a semantic value `Val Head n` as a syntactic term `Tm Head n`. -/
def toTm {n : Nat} : Val Head n → Tm Head n
  | .var i => .var i
  | .const c => .const c
  | .app f a => .app (toTm f) (toTm a)
  | .fst p => .fst (toTm p)
  | .snd p => .snd (toTm p)
  | .head h => .head h
  | .pi A B => .pi (toTm A) (Clos.toTm B)
  | .sigma A B => .sigma (toTm A) (Clos.toTm B)
  | .id A a b => .id (toTm A) (toTm a) (toTm b)
  | .lam body => .lam (Clos.toTm body)
  | .pair a b => .pair (toTm a) (toTm b)
  | .refl a => .refl (toTm a)

/-- Realize a closure `Clos Head n` as a syntactic binder body `Tm Head (n + 1)`. -/
def _root_.Mettapedia.TypeTheory.NbE.Clos.toTm {n : Nat} :
    Clos Head n → Tm Head (n + 1)
  | .mk env body => subst (liftSub (Env.toSub env)) body

/-- Realize a lexical environment `Env Head m n` as a syntactic substitution `Sub Head m n`. -/
def _root_.Mettapedia.TypeTheory.NbE.Env.toSub {m n : Nat} :
    Env Head m n → Sub Head m n
  | .nil => Fin.elim0
  | .snoc env v => Fin.cases (Val.toTm v) (Env.toSub env)

end

/-- Looking up `i` in `env` and realizing to a term equals applying `env.toSub` to `i`. -/
@[simp] theorem _root_.Mettapedia.TypeTheory.NbE.Env.lookup_toTm :
    ∀ {m n : Nat} (env : Env Head m n) (i : Fin m),
      (env.lookup i).toTm = env.toSub i
  | _, _, .nil, i => Fin.elim0 i
  | _, _, .snoc env v, i => by
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simp [Env.lookup, Env.toSub, Env.lookup_toTm env j]

mutual

/-- Realizing a renamed semantic value equals renaming its realization. -/
@[simp] theorem toTm_rename {n k : Nat} (ρ : Ren n k) :
    ∀ (v : Val Head n),
      (v.rename ρ).toTm =
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename ρ v.toTm
  | .var i => rfl
  | .const c => rfl
  | .app f a => by
      simp [rename, toTm, toTm_rename ρ f, toTm_rename ρ a,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .fst p => by
      simp [rename, toTm, toTm_rename ρ p,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .snd p => by
      simp [rename, toTm, toTm_rename ρ p,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .head h => rfl
  | .pi A B => by
      simp [rename, toTm, toTm_rename ρ A, Clos.toTm_rename ρ B,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .sigma A B => by
      simp [rename, toTm, toTm_rename ρ A, Clos.toTm_rename ρ B,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .id A a b => by
      simp [rename, toTm, toTm_rename ρ A, toTm_rename ρ a, toTm_rename ρ b,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .lam body => by
      simp [rename, toTm, Clos.toTm_rename ρ body,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .pair a b => by
      simp [rename, toTm, toTm_rename ρ a, toTm_rename ρ b,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]
  | .refl a => by
      simp [rename, toTm, toTm_rename ρ a,
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename]

/-- Realizing a renamed closure equals renaming its realization under `liftRen`. -/
@[simp] theorem _root_.Mettapedia.TypeTheory.NbE.Clos.toTm_rename {n k : Nat} (ρ : Ren n k) :
    ∀ (c : Clos Head n),
      (c.rename ρ).toTm =
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename (liftRen ρ) c.toTm
  | .mk env body => by
      simp only [Clos.rename, Clos.toTm, rename_subst]
      apply subst_ext
      intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        have hEnv := Env.toSub_rename ρ env j
        simp only [liftSub_succ, hEnv]
        exact (rename_liftSub ρ env.toSub j.succ).symm

/-- Realizing a renamed environment equals renaming each entry of `env.toSub`. -/
@[simp] theorem _root_.Mettapedia.TypeTheory.NbE.Env.toSub_rename {m n k : Nat} (ρ : Ren n k) :
    ∀ (env : Env Head m n) (i : Fin m),
      (env.rename ρ).toSub i =
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename ρ (env.toSub i)
  | .nil, i => Fin.elim0 i
  | .snoc env v, i => by
      refine Fin.cases ?_ ?_ i
      · exact Val.toTm_rename ρ v
      · intro j
        exact Env.toSub_rename ρ env j

end

end Val

namespace Env

variable {Head : Type}

/-- Weakening an environment by `wk` and extending with the fresh variable `.var 0`
realizes to the exact lifted substitution `liftSub env.toSub`. -/
@[simp] theorem toSub_snoc_wk_var0 {m n : Nat} (env : Env Head m n) :
    ((env.rename wk).snoc (.var 0)).toSub = liftSub env.toSub := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [Env.toSub, Env.toSub_rename]

/-- The canonical identity environment `idEnv n : Env Head n n` mapping `i : Fin n`
to `Val.var i`. -/
def idEnv : (n : Nat) → Env Head n n
  | 0 => .nil
  | n + 1 => .snoc ((idEnv n).rename wk) (.var 0)

/-- The identity environment realizes to the identity substitution `ids`. -/
@[simp] theorem toSub_idEnv (n : Nat) :
    (idEnv (Head := Head) n).toSub = ids := by
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ k ih =>
      rw [idEnv, toSub_snoc_wk_var0, ih, liftSub_ids]

end Env

namespace Clos

variable {Head : Type}

/-- Opening a realized closure `(Clos.mk env body).toTm` at `v.toTm` via `inst0`
equals substituting `(env.snoc v).toSub` into `body`. -/
theorem inst0_toTm {m n : Nat} (env : Env Head m n) (body : Tm Head (m + 1))
    (v : Val Head n) :
    inst0 v.toTm (Clos.mk env body).toTm = subst (env.snoc v).toSub body := by
  unfold Clos.toTm inst0
  rw [subst_comp]
  apply subst_ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    change inst0 v.toTm
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename wk (env.toSub j)) =
      env.toSub j
    exact inst0_rename_wk v.toTm (env.toSub j)

/-- Consequently, a β-redex `(.app (.lam c.toTm) v.toTm)` steps in a single
`StepCore.betaPi` step to `subst (env.snoc v).toSub body`. -/
theorem betaPi_toTm (R : Rules Head) {m n : Nat} (env : Env Head m n)
    (body : Tm Head (m + 1)) (v : Val Head n) :
    StepCore R.computation R.headEq
      (.app (Val.lam (.mk env body)).toTm v.toTm)
      (subst (env.snoc v).toSub body) := by
  rw [← inst0_toTm env body v]
  exact StepCore.betaPi (Clos.mk env body).toTm v.toTm

end Clos

/-! ## 3. Multi-Step Congruence Helpers for `Reduces` -/

section ReducesCongr

variable {Head : Type} (R : Rules Head)

theorem reduces_congr {m n : Nat} (f : Tm Head m → Tm Head n)
    (hf : ∀ {x y : Tm Head m},
      StepCore R.computation R.headEq x y →
      StepCore R.computation R.headEq (f x) (f y))
    {t u : Tm Head m} (h : Reduces R t u) :
    Reduces R (f t) (f u) := by
  induction h with
  | refl => exact .refl
  | tail _ hStep ih => exact ih.tail (hf hStep)

theorem reduces_to_conv {n : Nat} {t u : Tm Head n}
    (h : Reduces R t u) : Conv R.headEq t u R.computation := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hStep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hStep)

variable {n : Nat}

theorem reduces_pi {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (hA : Reduces R A A') (hB : Reduces R B B') :
    Reduces R (.pi A B) (.pi A' B') :=
  (reduces_congr R (fun x => .pi x B) (fun s => .congPiDom s) hA).trans
    (reduces_congr R (fun y => .pi A' y) (fun s => .congPiCod s) hB)

theorem reduces_sigma {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (hA : Reduces R A A') (hB : Reduces R B B') :
    Reduces R (.sigma A B) (.sigma A' B') :=
  (reduces_congr R (fun x => .sigma x B) (fun s => .congSigmaDom s) hA).trans
    (reduces_congr R (fun y => .sigma A' y) (fun s => .congSigmaCod s) hB)

theorem reduces_id {A A' a a' b b' : Tm Head n}
    (hA : Reduces R A A') (ha : Reduces R a a') (hb : Reduces R b b') :
    Reduces R (.id A a b) (.id A' a' b') :=
  ((reduces_congr R (fun x => .id x a b) (fun s => .congIdTy s) hA).trans
    (reduces_congr R (fun y => .id A' y b) (fun s => .congIdLeft s) ha)).trans
    (reduces_congr R (fun z => .id A' a' z) (fun s => .congIdRight s) hb)

theorem reduces_app {f f' a a' : Tm Head n}
    (hf : Reduces R f f') (ha : Reduces R a a') :
    Reduces R (.app f a) (.app f' a') :=
  (reduces_congr R (fun x => .app x a) (fun s => .congAppFun s) hf).trans
    (reduces_congr R (fun y => .app f' y) (fun s => .congAppArg s) ha)

theorem reduces_pair {a a' b b' : Tm Head n}
    (ha : Reduces R a a') (hb : Reduces R b b') :
    Reduces R (.pair a b) (.pair a' b') :=
  (reduces_congr R (fun x => .pair x b) (fun s => .congPairFst s) ha).trans
    (reduces_congr R (fun y => .pair a' y) (fun s => .congPairSnd s) hb)

theorem reduces_lam {b b' : Tm Head (n + 1)}
    (hb : Reduces R b b') :
    Reduces R (.lam b) (.lam b') :=
  reduces_congr R (fun x => .lam x) (fun s => .congLam s) hb

theorem reduces_fst {p p' : Tm Head n}
    (hp : Reduces R p p') :
    Reduces R (.fst p) (.fst p') :=
  reduces_congr R (fun x => .fst x) (fun s => .congFst s) hp

theorem reduces_snd {p p' : Tm Head n}
    (hp : Reduces R p p') :
    Reduces R (.snd p) (.snd p') :=
  reduces_congr R (fun x => .snd x) (fun s => .congSnd s) hp

theorem reduces_refl {a a' : Tm Head n}
    (ha : Reduces R a a') :
    Reduces R (.refl a) (.refl a') :=
  reduces_congr R (fun x => .refl x) (fun s => .congRefl s) ha

end ReducesCongr

/-! ## 4. Certified Closure-Based Evaluator (`eval`) and Readback (`quoteVal`) -/

section Machine

variable {Head : Type} (R : Rules Head) (root : ExecutableReduction.RootEvaluator R)

/-- Result of evaluating `t : Tm Head m` in lexical environment `env : Env Head m n`:
a semantic value `val : Val Head n` together with a proof that `subst env.toSub t`
reduces to `val.toTm`. -/
structure EvalResult {m n : Nat} (env : Env Head m n) (t : Tm Head m) where
  val : Val Head n
  reduces : Reduces R (subst env.toSub t) val.toTm

/-- Result of quoting a semantic value `v : Val Head n` to a stratified normal form
`nf : Nf Head n`, together with a proof that `v.toTm` reduces to `nf.toTm`. -/
structure QuoteResult {n : Nat} (v : Val Head n) where
  nf : Nf Head n
  reduces : Reduces R v.toTm nf.toTm

/-- Certified closure-based environment evaluator (`smalltt`-style).
- Variables look up their value in `env` in $O(1)$.
- Lambda abstractions form a closure `Val.lam (.mk env body)` in $O(1)$ without
  traversing `body` or performing syntactic substitution.
- `pi` and `sigma` evaluate their domain and form a closure `.mk env B` for their codomain.
- Function application `app f a` evaluates `f` and `a`; when `f` evaluates to a closure
  `Val.lam (.mk env' body')`, it extends `env'` with the argument value and evaluates
  `body'` directly in `env'.snoc va`.
- Projections `fst` and `snd` project pair values `.pair va vb` in $O(1)$.
- Constants unfold via `root` (δ-unfolding) when declared. -/
def eval : Nat → {m n : Nat} → (env : Env Head m n) → (t : Tm Head m) →
    Option (EvalResult R env t)
  | 0, _, _, _, _ => none
  | fuel + 1, _, _, env, t =>
      match t with
      | .var i =>
          some ⟨env.lookup i, by simp [subst, Env.lookup_toTm]; exact .refl⟩
      | .const name =>
          match root (.const name) with
          | none => some ⟨.const name, .refl⟩
          | some next => do
              let res ← eval fuel (Env.idEnv _) next.val
              have hStep : StepCore R.computation R.headEq (.const name)
                  (subst (Env.idEnv _).toSub next.val) := by
                simpa [Env.toSub_idEnv, subst_ids] using StepCore.root next.property
              return ⟨res.val, .head hStep res.reduces⟩
      | .head h =>
          some ⟨.head h, .refl⟩
      | .pi A B => do
          let resA ← eval fuel env A
          return ⟨.pi resA.val (.mk env B),
            reduces_pi R resA.reduces .refl⟩
      | .sigma A B => do
          let resA ← eval fuel env A
          return ⟨.sigma resA.val (.mk env B),
            reduces_sigma R resA.reduces .refl⟩
      | .id A a b => do
          let resA ← eval fuel env A
          let resa ← eval fuel env a
          let resb ← eval fuel env b
          return ⟨.id resA.val resa.val resb.val,
            reduces_id R resA.reduces resa.reduces resb.reduces⟩
      | .lam body =>
          some ⟨.lam (.mk env body), .refl⟩
      | .app f a => do
          let resF ← eval fuel env f
          let resA ← eval fuel env a
          let appRed : Reduces R (subst env.toSub (.app f a)) (.app resF.val.toTm resA.val.toTm) :=
            reduces_app R resF.reduces resA.reduces
          match hF : resF.val with
          | .lam (.mk env' body') => do
              let resBeta ← eval fuel (env'.snoc resA.val) body'
              have hBetaStep : StepCore R.computation R.headEq
                  (.app (Val.lam (.mk env' body')).toTm resA.val.toTm)
                  (subst (env'.snoc resA.val).toSub body') :=
                Clos.betaPi_toTm R env' body' resA.val
              return ⟨resBeta.val,
                appRed.trans (hF ▸ .head hBetaStep resBeta.reduces)⟩
          | _ =>
              let spineTm := Tm.app resF.val.toTm resA.val.toTm
              match root spineTm with
              | none => return ⟨.app resF.val resA.val, appRed⟩
              | some next => do
                  let resRoot ← eval fuel (Env.idEnv _) next.val
                  have hRootStep : StepCore R.computation R.headEq spineTm
                      (subst (Env.idEnv _).toSub next.val) := by
                    simpa [Env.toSub_idEnv, subst_ids] using StepCore.root next.property
                  return ⟨resRoot.val,
                    appRed.trans (.head hRootStep resRoot.reduces)⟩
      | .pair a b => do
          let resa ← eval fuel env a
          let resb ← eval fuel env b
          return ⟨.pair resa.val resb.val,
            reduces_pair R resa.reduces resb.reduces⟩
      | .fst p => do
          let resP ← eval fuel env p
          let fstRed : Reduces R (subst env.toSub (.fst p)) (.fst resP.val.toTm) :=
            reduces_fst R resP.reduces
          match hP : resP.val with
          | .pair va vb =>
              have hStep : StepCore R.computation R.headEq
                  (.fst (Val.pair va vb).toTm) va.toTm :=
                StepCore.betaSigmaFst va.toTm vb.toTm
              return ⟨va, fstRed.trans (hP ▸ .single hStep)⟩
          | _ =>
              return ⟨.fst resP.val, fstRed⟩
      | .snd p => do
          let resP ← eval fuel env p
          let sndRed : Reduces R (subst env.toSub (.snd p)) (.snd resP.val.toTm) :=
            reduces_snd R resP.reduces
          match hP : resP.val with
          | .pair va vb =>
              have hStep : StepCore R.computation R.headEq
                  (.snd (Val.pair va vb).toTm) vb.toTm :=
                StepCore.betaSigmaSnd va.toTm vb.toTm
              return ⟨vb, sndRed.trans (hP ▸ .single hStep)⟩
          | _ =>
              return ⟨.snd resP.val, sndRed⟩
      | .refl a => do
          let resa ← eval fuel env a
          return ⟨.refl resa.val, reduces_refl R resa.reduces⟩

/-- Readback (`quoteVal`) from semantic values `Val Head n` to stratified normal forms
`Nf Head n`. Entering a binder (`lam`, `pi`, `sigma`) weakens the closure's lexical
environment by `wk`, extends it with `.var 0`, evaluates the body, and quotes the
resulting value in scope `n + 1`. -/
def quoteVal : Nat → {n : Nat} → (v : Val Head n) → Option (QuoteResult R v)
  | 0, _, _ => none
  | fuel + 1, _, v =>
      match v with
      | .var i => some ⟨.ne (.var i), .refl⟩
      | .const c => some ⟨.ne (.const c), .refl⟩
      | .head h => some ⟨.head h, .refl⟩
      | .pi A (.mk env B) => do
          let qA ← quoteVal fuel A
          let evalB ← eval R root fuel ((env.rename wk).snoc (.var 0)) B
          let qB ← quoteVal fuel evalB.val
          have hBRed : Reduces R (Clos.mk env B).toTm qB.nf.toTm := by
            have hSub : ((env.rename wk).snoc (.var 0)).toSub = liftSub env.toSub :=
              Env.toSub_snoc_wk_var0 env
            have hEval : Reduces R (Clos.mk env B).toTm evalB.val.toTm := by
              simpa [Clos.toTm, hSub] using evalB.reduces
            exact hEval.trans qB.reduces
          return ⟨.pi qA.nf qB.nf, reduces_pi R qA.reduces hBRed⟩
      | .sigma A (.mk env B) => do
          let qA ← quoteVal fuel A
          let evalB ← eval R root fuel ((env.rename wk).snoc (.var 0)) B
          let qB ← quoteVal fuel evalB.val
          have hBRed : Reduces R (Clos.mk env B).toTm qB.nf.toTm := by
            have hSub : ((env.rename wk).snoc (.var 0)).toSub = liftSub env.toSub :=
              Env.toSub_snoc_wk_var0 env
            have hEval : Reduces R (Clos.mk env B).toTm evalB.val.toTm := by
              simpa [Clos.toTm, hSub] using evalB.reduces
            exact hEval.trans qB.reduces
          return ⟨.sigma qA.nf qB.nf, reduces_sigma R qA.reduces hBRed⟩
      | .id A a b => do
          let qA ← quoteVal fuel A
          let qa ← quoteVal fuel a
          let qb ← quoteVal fuel b
          return ⟨.id qA.nf qa.nf qb.nf,
            reduces_id R qA.reduces qa.reduces qb.reduces⟩
      | .lam (.mk env body) => do
          let evalBody ← eval R root fuel ((env.rename wk).snoc (.var 0)) body
          let qBody ← quoteVal fuel evalBody.val
          have hBodyRed : Reduces R (Clos.mk env body).toTm qBody.nf.toTm := by
            have hSub : ((env.rename wk).snoc (.var 0)).toSub = liftSub env.toSub :=
              Env.toSub_snoc_wk_var0 env
            have hEval : Reduces R (Clos.mk env body).toTm evalBody.val.toTm := by
              simpa [Clos.toTm, hSub] using evalBody.reduces
            exact hEval.trans qBody.reduces
          return ⟨.lam qBody.nf, reduces_lam R hBodyRed⟩
      | .pair a b => do
          let qa ← quoteVal fuel a
          let qb ← quoteVal fuel b
          return ⟨.pair qa.nf qb.nf, reduces_pair R qa.reduces qb.reduces⟩
      | .refl a => do
          let qa ← quoteVal fuel a
          return ⟨.refl qa.nf, reduces_refl R qa.reduces⟩
      | .app f a => do
          let qf ← quoteVal fuel f
          let qa ← quoteVal fuel a
          let appRed : Reduces R (.app f.toTm a.toTm) (.app qf.nf.toTm qa.nf.toTm) :=
            reduces_app R qf.reduces qa.reduces
          match hF : qf.nf with
          | .ne neF =>
              have hAppRed : Reduces R (.app f.toTm a.toTm) (Nf.ne (.app neF qa.nf)).toTm := by
                simpa [hF, Nf.toTm, Ne.toTm] using appRed
              return ⟨.ne (.app neF qa.nf), hAppRed⟩
          | .lam nfBody => do
              let resBeta ← eval R root fuel (Env.idEnv _) (inst0 qa.nf.toTm nfBody.toTm)
              let qBeta ← quoteVal fuel resBeta.val
              have hAppRed : Reduces R (.app f.toTm a.toTm) (.app (Nf.lam nfBody).toTm qa.nf.toTm) := by
                simpa [hF] using appRed
              have hStep : StepCore R.computation R.headEq
                  (.app (Nf.lam nfBody).toTm qa.nf.toTm)
                  (subst (Env.idEnv _).toSub (inst0 qa.nf.toTm nfBody.toTm)) := by
                simpa [Nf.toTm, Env.toSub_idEnv, subst_ids] using
                  StepCore.betaPi nfBody.toTm qa.nf.toTm
              return ⟨qBeta.nf,
                hAppRed.trans ((Relation.ReflTransGen.head hStep resBeta.reduces).trans qBeta.reduces)⟩
          | _ => none
      | .fst p => do
          let qp ← quoteVal fuel p
          let fstRed : Reduces R (.fst p.toTm) (.fst qp.nf.toTm) :=
            reduces_fst R qp.reduces
          match hP : qp.nf with
          | .ne neP =>
              have hFstRed : Reduces R (.fst p.toTm) (Nf.ne (.fst neP)).toTm := by
                simpa [hP, Nf.toTm, Ne.toTm] using fstRed
              return ⟨.ne (.fst neP), hFstRed⟩
          | .pair nfA nfB =>
              have hFstRed : Reduces R (.fst p.toTm) (.fst (Nf.pair nfA nfB).toTm) := by
                simpa [hP] using fstRed
              have hStep : StepCore R.computation R.headEq
                  (.fst (Nf.pair nfA nfB).toTm) nfA.toTm :=
                StepCore.betaSigmaFst nfA.toTm nfB.toTm
              return ⟨nfA, hFstRed.trans (.single hStep)⟩
          | _ => none
      | .snd p => do
          let qp ← quoteVal fuel p
          let sndRed : Reduces R (.snd p.toTm) (.snd qp.nf.toTm) :=
            reduces_snd R qp.reduces
          match hP : qp.nf with
          | .ne neP =>
              have hSndRed : Reduces R (.snd p.toTm) (Nf.ne (.snd neP)).toTm := by
                simpa [hP, Nf.toTm, Ne.toTm] using sndRed
              return ⟨.ne (.snd neP), hSndRed⟩
          | .pair nfA nfB =>
              have hSndRed : Reduces R (.snd p.toTm) (.snd (Nf.pair nfA nfB).toTm) := by
                simpa [hP] using sndRed
              have hStep : StepCore R.computation R.headEq
                  (.snd (Nf.pair nfA nfB).toTm) nfB.toTm :=
                StepCore.betaSigmaSnd nfA.toTm nfB.toTm
              return ⟨nfB, hSndRed.trans (.single hStep)⟩
          | _ => none

/-- Full NbE normalization (`nbeNorm`): evaluates `t : Tm Head n` in the identity
environment `Env.idEnv n` and quotes the resulting value to a stratified normal form
`nf : Nf Head n`, bundled with a proof that `Reduces R t nf.toTm`. -/
def nbeNorm (fuel : Nat) {n : Nat} (t : Tm Head n) :
    Option {nf : Nf Head n // Reduces R t nf.toTm} := do
  let evaluated ← eval R root fuel (Env.idEnv n) t
  let quoted ← quoteVal R root fuel evaluated.val
  have hRed : Reduces R t quoted.nf.toTm := by
    have hEval : Reduces R t evaluated.val.toTm := by
      simpa [Env.toSub_idEnv, subst_ids] using evaluated.reduces
    exact hEval.trans quoted.reduces
  return ⟨quoted.nf, hRed⟩

/-- Extract the stratified normal form `Nf Head n` produced by `nbeNorm`. -/
def nbeNormNf (fuel : Nat) {n : Nat} (t : Tm Head n) : Option (Nf Head n) :=
  (nbeNorm R root fuel t).map Subtype.val

/-- Extract the underlying term `Tm Head n` of the NbE normal form. -/
def nbeNormTm (fuel : Nat) {n : Nat} (t : Tm Head n) : Option (Tm Head n) :=
  (nbeNormNf R root fuel t).map Nf.toTm

/-- **Soundness of `nbeNormNf` for Multi-Step Reduction (`Reduces`)**:
Whenever `nbeNormNf` returns `some nf`, `t` reduces to `nf.toTm` in `Reduces R`
and `nf.toTm` contains no structural β-redexes. -/
theorem nbeNormNf_sound {fuel n : Nat} {t : Tm Head n} {nf : Nf Head n}
    (hNorm : nbeNormNf R root fuel t = some nf) :
    Reduces R t nf.toTm ∧
      ExecutableReduction.step R (fun _ => none) nf.toTm = none := by
  unfold nbeNormNf at hNorm
  cases h : nbeNorm R root fuel t with
  | none => simp [h] at hNorm
  | some res =>
      simp only [h, Option.map_some, Option.some.injEq] at hNorm
      subst hNorm
      exact ⟨res.property, Nf.step_empty_eq_none R res.val⟩

/-- **Soundness of `nbeNormNf` for Declarative Conversion (`Conv`)**:
Whenever `nbeNormNf` returns `some nf`, `t` is declaratively convertible to `nf.toTm`. -/
theorem nbeNormNf_conv {fuel n : Nat} {t : Tm Head n} {nf : Nf Head n}
    (hNorm : nbeNormNf R root fuel t = some nf) :
    Conv R.headEq t nf.toTm R.computation :=
  reduces_to_conv R (nbeNormNf_sound R root hNorm).1

/-- Eager weak-head NbE evaluation (`nbeEagerWhnf`): evaluates `t : Tm Head n` in `Env.idEnv n`
to a semantic value `v : Val Head n` (evaluating application arguments before root unfolding)
without forcing closures under binders, returning `v.toTm` together with `Reduces R t v.toTm`. -/
def nbeEagerWhnf (fuel : Nat) {n : Nat} (t : Tm Head n) :
    Option (ExecutableReduction.Result R t) := do
  let evaluated ← eval R root fuel (Env.idEnv n) t
  have hEval : Reduces R t evaluated.val.toTm := by
    simpa [Env.toSub_idEnv, subst_ids] using evaluated.reduces
  return ⟨evaluated.val.toTm, hEval⟩

/-- The full NbE machine packaged as a verified `ExecutableReduction.Reducer R`. -/
def nbeReducer : ExecutableReduction.Reducer R :=
  fun fuel {_} t => do
    let res ← nbeNorm R root fuel t
    return ⟨res.val.toTm, res.property⟩

/-- The eager weak-head NbE closure machine packaged as a verified `ExecutableReduction.Reducer R`
(useful when declaration-root unfolding inspects already-evaluated constructor spines). -/
def nbeEagerWhnfReducer : ExecutableReduction.Reducer R :=
  fun fuel {_} t => nbeEagerWhnf R root fuel t

end Machine

/-! ## 5. Call-by-Name Weak-Head Closure Machine (`WhEntry`, `WhEnv`, `WhVal`, `whEval`)

To guarantee that weak-head evaluation terminates on every term that possesses a
weak-head normal form (`WhRed R roles t w ∧ Whnf R roles w`), we pair the closure
machine with call-by-name environment entries (`WhEntry`):
- Bound variables are stored as `.boundVar i`, and unevaluated arguments are stored
  as thunks `.clos env tm`.
- Type formers (`.pi`, `.sigma`, `.id`) and constructors (`.lam`, `.pair`, `.refl`, `.head`)
  return immediately in 1 step as weak-head values holding their lexical environment `env`.
- β-redexes `.app (.lam env' body') a` extend `env'` with `.clos env a` in $O(1)$ without
  evaluating `a` or running syntactic substitution.
- Pair projections `.fst` and `.snd` evaluate only the projected component of `.pair ca cb`.
-/

mutual

/-- Entry in a call-by-name lexical environment `WhEnv Head m n`: either a target-scope
bound variable `.boundVar i` or a thunked closure `.clos env tm`. -/
inductive WhEntry (Head : Type) : Nat → Type where
  | boundVar {n : Nat} : Fin n → WhEntry Head n
  | clos {k n : Nat} : WhEnv Head k n → Tm Head k → WhEntry Head n

/-- Call-by-name lexical environment mapping source scope `m` to entries in target scope `n`. -/
inductive WhEnv (Head : Type) : Nat → Nat → Type where
  | nil {n : Nat} : WhEnv Head 0 n
  | snoc {m n : Nat} : WhEnv Head m n → WhEntry Head n → WhEnv Head (m + 1) n

end

namespace WhEnv

variable {Head : Type}

/-- Look up a de Bruijn index `i : Fin m` in `WhEnv Head m n`. -/
def lookup {m n : Nat} : WhEnv Head m n → Fin m → WhEntry Head n
  | .nil, i => Fin.elim0 i
  | .snoc env e, i => Fin.cases e (fun j => env.lookup j) i

mutual

/-- Realize a `WhEntry Head n` as a syntactic term `Tm Head n`. -/
def _root_.Mettapedia.TypeTheory.NbE.WhEntry.toTm {n : Nat} : WhEntry Head n → Tm Head n
  | .boundVar i => .var i
  | .clos env tm => subst (WhEnv.toSub env) tm

/-- Realize a `WhEnv Head m n` as a simultaneous substitution `Sub Head m n`. -/
def toSub {m n : Nat} : WhEnv Head m n → Sub Head m n
  | .nil => Fin.elim0
  | .snoc env e => Fin.cases (WhEntry.toTm e) (WhEnv.toSub env)

end

@[simp] theorem lookup_toTm :
    ∀ {m n : Nat} (env : WhEnv Head m n) (i : Fin m),
      (env.lookup i).toTm = env.toSub i
  | _, _, .nil, i => Fin.elim0 i
  | _, _, .snoc env e, i => by
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simp [lookup, toSub, lookup_toTm env j]

/-- Build a `WhEnv Head m n` from a renaming `ρ : Ren m n`. -/
def ofRen : {m n : Nat} → Ren m n → WhEnv Head m n
  | 0, _, _ => .nil
  | _ + 1, _, ρ => .snoc (ofRen (fun j => ρ j.succ)) (.boundVar (ρ 0))

@[simp] theorem lookup_ofRen :
    ∀ {m n : Nat} (ρ : Ren m n) (i : Fin m),
      (ofRen (Head := Head) ρ).lookup i = .boundVar (ρ i)
  | 0, _, _, i => Fin.elim0 i
  | _ + 1, _, ρ, i => by
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simp [ofRen, lookup, lookup_ofRen]

/-- Canonical identity environment `idEnv n : WhEnv Head n n` mapping `i` to `.boundVar i`. -/
def idEnv (n : Nat) : WhEnv Head n n :=
  ofRen idRen

@[simp] theorem lookup_idEnv {n : Nat} (i : Fin n) :
    (idEnv (Head := Head) n).lookup i = .boundVar i := by
  simp [idEnv, idRen]

@[simp] theorem toSub_idEnv (n : Nat) :
    (idEnv (Head := Head) n).toSub = ids := by
  funext i
  rw [← lookup_toTm, lookup_idEnv]
  rfl

/-- Opening a realized binder body `subst (liftSub env.toSub) body` at `e.toTm` via `inst0`
equals substituting `(env.snoc e).toSub` into `body`. -/
theorem inst0_liftSub_toSub {m n : Nat} (env : WhEnv Head m n)
    (body : Tm Head (m + 1)) (e : WhEntry Head n) :
    inst0 e.toTm (subst (liftSub env.toSub) body) =
      subst (env.snoc e).toSub body := by
  unfold inst0
  rw [subst_comp]
  apply subst_ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    change inst0 e.toTm
        (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename wk (env.toSub j)) =
      env.toSub j
    exact inst0_rename_wk e.toTm (env.toSub j)

end WhEnv

/-- Weak-head semantic values in target scope `n`. -/
inductive WhVal (Head : Type) (n : Nat) : Type where
  | var : Fin n → WhVal Head n
  | const : DeclName → WhVal Head n
  | head : Head → WhVal Head n
  | app : WhVal Head n → WhEntry Head n → WhVal Head n
  | fst : WhVal Head n → WhVal Head n
  | snd : WhVal Head n → WhVal Head n
  | pi {m : Nat} : WhEnv Head m n → Tm Head m → Tm Head (m + 1) → WhVal Head n
  | sigma {m : Nat} : WhEnv Head m n → Tm Head m → Tm Head (m + 1) → WhVal Head n
  | id {m : Nat} : WhEnv Head m n → Tm Head m → Tm Head m → Tm Head m → WhVal Head n
  | lam {m : Nat} : WhEnv Head m n → Tm Head (m + 1) → WhVal Head n
  | pair : WhEntry Head n → WhEntry Head n → WhVal Head n
  | refl : WhEntry Head n → WhVal Head n

namespace WhVal

variable {Head : Type}

/-- Realize a weak-head semantic value `WhVal Head n` as a syntactic term `Tm Head n`. -/
def toTm {n : Nat} : WhVal Head n → Tm Head n
  | .var i => .var i
  | .const c => .const c
  | .head h => .head h
  | .app f a => .app f.toTm a.toTm
  | .fst p => .fst p.toTm
  | .snd p => .snd p.toTm
  | .pi env A B => .pi (subst env.toSub A) (subst (liftSub env.toSub) B)
  | .sigma env A B => .sigma (subst env.toSub A) (subst (liftSub env.toSub) B)
  | .id env A a b => .id (subst env.toSub A) (subst env.toSub a) (subst env.toSub b)
  | .lam env body => .lam (subst (liftSub env.toSub) body)
  | .pair a b => .pair a.toTm b.toTm
  | .refl a => .refl a.toTm

theorem betaPi_toTm (R : Rules Head) {m n : Nat} (env : WhEnv Head m n)
    (body : Tm Head (m + 1)) (e : WhEntry Head n) :
    StepCore R.computation R.headEq
      (.app (WhVal.lam env body).toTm e.toTm)
      (subst (env.snoc e).toSub body) := by
  rw [← WhEnv.inst0_liftSub_toSub env body e]
  exact StepCore.betaPi (subst (liftSub env.toSub) body) e.toTm

theorem toTm_eq_lam_iff {n : Nat} {v : WhVal Head n} {body₀ : Tm Head (n + 1)} :
    v.toTm = .lam body₀ ↔
      ∃ (m : Nat) (env' : WhEnv Head m n) (body' : Tm Head (m + 1)),
        v = .lam env' body' ∧ subst (liftSub env'.toSub) body' = body₀ := by
  constructor
  · intro h
    cases v <;> simp [toTm] at h
    rename_i m env' body'
    exact ⟨m, env', body', rfl, h⟩
  · rintro ⟨m, env', body', rfl, h⟩
    simpa [toTm] using h

theorem toTm_eq_pair_iff {n : Nat} {v : WhVal Head n} {a₀ b₀ : Tm Head n} :
    v.toTm = .pair a₀ b₀ ↔
      ∃ (ca cb : WhEntry Head n),
        v = .pair ca cb ∧ ca.toTm = a₀ ∧ cb.toTm = b₀ := by
  constructor
  · intro h
    cases v <;> simp [toTm] at h
    rename_i ca cb
    exact ⟨ca, cb, rfl, h.1, h.2⟩
  · rintro ⟨ca, cb, rfl, h₁, h₂⟩
    simp [toTm, h₁, h₂]

end WhVal

section WhMachine

variable {Head : Type} (R : Rules Head) (root : ExecutableReduction.RootEvaluator R)

/-- Call-by-name weak-head closure evaluator (`whEval`). -/
def whEval : Nat → {m n : Nat} → (env : WhEnv Head m n) → (t : Tm Head m) →
    Option (WhVal Head n)
  | 0, _, _, _, _ => none
  | fuel + 1, _, n, env, t =>
      match t with
      | .var i =>
          match env.lookup i with
          | .boundVar j => some (.var j)
          | .clos env' tm' => whEval fuel env' tm'
      | .const name =>
          match root (Tm.const (Head := Head) (n := n) name) with
          | none => some (.const name)
          | some next => whEval fuel (WhEnv.idEnv n) next.val
      | .head h => some (.head h)
      | .pi A B => some (.pi env A B)
      | .sigma A B => some (.sigma env A B)
      | .id A a b => some (.id env A a b)
      | .lam body => some (.lam env body)
      | .pair a b => some (.pair (.clos env a) (.clos env b))
      | .refl a => some (.refl (.clos env a))
      | .app f a => do
          let valF ← whEval fuel env f
          match valF with
          | .lam env' body' =>
              whEval fuel (env'.snoc (.clos env a)) body'
          | _ =>
              match root (Tm.app valF.toTm (WhEntry.clos env a).toTm) with
              | none => return .app valF (.clos env a)
              | some next => whEval fuel (WhEnv.idEnv n) next.val
      | .fst p => do
          let valP ← whEval fuel env p
          match valP with
          | .pair (.boundVar j) _ => return .var j
          | .pair (.clos env' tm') _ => whEval fuel env' tm'
          | _ => return .fst valP
      | .snd p => do
          let valP ← whEval fuel env p
          match valP with
          | .pair _ (.boundVar j) => return .var j
          | .pair _ (.clos env' tm') => whEval fuel env' tm'
          | _ => return .snd valP

/-- **Soundness of `whEval`**:
Whenever `whEval R root fuel env t = some v`, `subst env.toSub t` reduces to `v.toTm`. -/
theorem whEval_sound :
    ∀ {fuel : Nat} {m n : Nat} {env : WhEnv Head m n} {t : Tm Head m} {v : WhVal Head n},
      whEval R root fuel env t = some v →
      Reduces R (subst env.toSub t) v.toTm
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, _, n, env, t, v, h => by
      cases t with
      | var i =>
          simp only [whEval] at h
          cases hLookup : env.lookup i with
          | boundVar j =>
              rw [hLookup] at h
              injection h with hEq; subst hEq
              have hTm : subst env.toSub (.var i) = .var j := by
                simp [subst, ← WhEnv.lookup_toTm, hLookup, WhEntry.toTm]
              rw [hTm]
              exact .refl
          | clos env' tm' =>
              rw [hLookup] at h
              have hTm : subst env.toSub (.var i) = subst env'.toSub tm' := by
                simp [subst, ← WhEnv.lookup_toTm, hLookup, WhEntry.toTm]
              rw [hTm]
              exact whEval_sound h
      | const name =>
          simp only [whEval] at h
          cases hRoot : root (Tm.const (Head := Head) (n := n) name) with
          | none =>
              rw [hRoot] at h
              injection h with hEq; subst hEq
              exact .refl
          | some next =>
              rw [hRoot] at h
              have hStep : StepCore R.computation R.headEq (.const name)
                  (subst (WhEnv.idEnv n).toSub next.val) := by
                simpa [WhEnv.toSub_idEnv, subst_ids] using StepCore.root next.property
              exact .head hStep (whEval_sound h)
      | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ =>
          simp only [whEval] at h
          injection h with hEq; subst hEq; exact .refl
      | app f a =>
          simp only [whEval, bind, Option.bind] at h
          cases hSubF : whEval R root fuel env f with
          | none => simp [hSubF] at h
          | some valF =>
              rw [hSubF] at h
              simp only at h
              have appRed : Reduces R (subst env.toSub (.app f a))
                  (.app valF.toTm (WhEntry.clos env a).toTm) :=
                reduces_app R (whEval_sound hSubF) .refl
              cases hValF : valF with
              | lam env' body' =>
                  rw [hValF] at h appRed
                  simp only at h
                  have hBetaStep : StepCore R.computation R.headEq
                      (.app (WhVal.lam env' body').toTm (WhEntry.clos env a).toTm)
                      (subst (env'.snoc (.clos env a)).toSub body') :=
                    WhVal.betaPi_toTm R env' body' (.clos env a)
                  exact appRed.trans (.head hBetaStep (whEval_sound h))
              | _ =>
                  have hMatch :
                      (match valF with
                      | .lam env' body' => whEval R root fuel (env'.snoc (.clos env a)) body'
                      | _ =>
                          match root (Tm.app valF.toTm (WhEntry.clos env a).toTm) with
                          | none => pure (.app valF (.clos env a))
                          | some next => whEval R root fuel (WhEnv.idEnv n) next.val) =
                      (match root (Tm.app valF.toTm (WhEntry.clos env a).toTm) with
                      | none => pure (.app valF (.clos env a))
                      | some next => whEval R root fuel (WhEnv.idEnv n) next.val) := by
                    rw [hValF]
                  rw [hMatch] at h
                  cases hRoot : root (Tm.app valF.toTm (WhEntry.clos env a).toTm) with
                  | none =>
                      rw [hRoot] at h
                      injection h with hEq; subst hEq
                      exact appRed
                  | some next =>
                      rw [hRoot] at h
                      have hRootStep : StepCore R.computation R.headEq
                          (Tm.app valF.toTm (WhEntry.clos env a).toTm)
                          (subst (WhEnv.idEnv n).toSub next.val) := by
                        simpa [WhEnv.toSub_idEnv, subst_ids] using StepCore.root next.property
                      exact appRed.trans (.head hRootStep (whEval_sound h))
      | fst p =>
          simp only [whEval, bind, Option.bind] at h
          cases hSubP : whEval R root fuel env p with
          | none => simp [hSubP] at h
          | some valP =>
              rw [hSubP] at h
              have fstRed : Reduces R (subst env.toSub (.fst p)) (.fst valP.toTm) :=
                reduces_fst R (whEval_sound hSubP)
              cases valP with
              | pair ca cb =>
                  cases ca with
                  | boundVar j =>
                      simp only [pure] at h
                      injection h with hEq; subst hEq
                      have hStep : StepCore R.computation R.headEq
                          (.fst (WhVal.pair (.boundVar j) cb).toTm) (WhVal.var j).toTm :=
                        StepCore.betaSigmaFst (WhEntry.boundVar j).toTm cb.toTm
                      exact fstRed.trans (.single hStep)
                  | clos env' tm' =>
                      simp only at h
                      have hStep : StepCore R.computation R.headEq
                          (.fst (WhVal.pair (.clos env' tm') cb).toTm) (subst env'.toSub tm') :=
                        StepCore.betaSigmaFst (WhEntry.clos env' tm').toTm cb.toTm
                      exact fstRed.trans (.head hStep (whEval_sound h))
              | _ =>
                  simp only [pure] at h
                  injection h with hEq; subst hEq
                  exact fstRed
      | snd p =>
          simp only [whEval, bind, Option.bind] at h
          cases hSubP : whEval R root fuel env p with
          | none => simp [hSubP] at h
          | some valP =>
              rw [hSubP] at h
              have sndRed : Reduces R (subst env.toSub (.snd p)) (.snd valP.toTm) :=
                reduces_snd R (whEval_sound hSubP)
              cases valP with
              | pair ca cb =>
                  cases cb with
                  | boundVar j =>
                      simp only [pure] at h
                      injection h with hEq; subst hEq
                      have hStep : StepCore R.computation R.headEq
                          (.snd (WhVal.pair ca (.boundVar j)).toTm) (WhVal.var j).toTm :=
                        StepCore.betaSigmaSnd ca.toTm (WhEntry.boundVar j).toTm
                      exact sndRed.trans (.single hStep)
                  | clos env' tm' =>
                      simp only at h
                      have hStep : StepCore R.computation R.headEq
                          (.snd (WhVal.pair ca (.clos env' tm')).toTm) (subst env'.toSub tm') :=
                        StepCore.betaSigmaSnd ca.toTm (WhEntry.clos env' tm').toTm
                      exact sndRed.trans (.head hStep (whEval_sound h))
              | _ =>
                  simp only [pure] at h
                  injection h with hEq; subst hEq
                  exact sndRed

/-- Weak-head NbE evaluation (`nbeWhnf`): evaluates `t : Tm Head n` in `WhEnv.idEnv n`
to a weak-head semantic value `v : WhVal Head n` and returns `v.toTm` together with
`Reduces R t v.toTm`. -/
def nbeWhnf (fuel : Nat) {n : Nat} (t : Tm Head n) :
    Option (ExecutableReduction.Result R t) :=
  match h : whEval R root fuel (WhEnv.idEnv n) t with
  | none => none
  | some v =>
      some ⟨v.toTm, by
        simpa [WhEnv.toSub_idEnv, subst_ids] using whEval_sound R root h⟩

/-- The weak-head NbE closure machine packaged as a verified `ExecutableReduction.Reducer R`
for use inside `ExecutableConversion` and `ExecutableChecking`. -/
def nbeWhnfReducer : ExecutableReduction.Reducer R :=
  fun fuel {_} t => nbeWhnf R root fuel t

/-- **Fuel Monotonicity of `whEval`**:
Once `whEval` succeeds at `fuel₁`, it returns the exact same value at every `fuel₂ ≥ fuel₁`. -/
theorem whEval_mono :
    ∀ {fuel₁ fuel₂ : Nat}, fuel₁ ≤ fuel₂ →
      ∀ {m n : Nat} {env : WhEnv Head m n} {t : Tm Head m} {v : WhVal Head n},
        whEval R root fuel₁ env t = some v →
        whEval R root fuel₂ env t = some v
  | 0, _, _, _, _, _, _, _, h => by cases h
  | fuel₁ + 1, 0, hle, _, _, _, _, _, _ => by omega
  | fuel₁ + 1, fuel₂ + 1, hle, _, n, env, t, v, h => by
      have hle' : fuel₁ ≤ fuel₂ := Nat.le_of_succ_le_succ hle
      revert h
      cases t with
      | var i =>
          simp only [whEval]
          cases env.lookup i with
          | boundVar j => exact id
          | clos env' tm' => exact whEval_mono hle'
      | const name =>
          simp only [whEval]
          cases root (Tm.const (Head := Head) (n := n) name) with
          | none => exact id
          | some next => exact whEval_mono hle'
      | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ =>
          simp only [whEval]
          exact id
      | app f a =>
          simp only [whEval, bind, Option.bind]
          cases hSubF : whEval R root fuel₁ env f with
          | none => intro h; cases h
          | some valF =>
              rw [whEval_mono hle' hSubF]
              cases valF <;> simp only
              case lam env' body' => exact whEval_mono hle'
              all_goals
                split
                · exact id
                · exact whEval_mono hle'
      | fst p =>
          simp only [whEval, bind, Option.bind]
          cases hSubP : whEval R root fuel₁ env p with
          | none => intro h; cases h
          | some valP =>
              rw [whEval_mono hle' hSubP]
              cases valP with
              | pair ca cb =>
                  cases ca with
                  | boundVar j => exact id
                  | clos env' tm' => exact whEval_mono hle'
              | _ => exact id
      | snd p =>
          simp only [whEval, bind, Option.bind]
          cases hSubP : whEval R root fuel₁ env p with
          | none => intro h; cases h
          | some valP =>
              rw [whEval_mono hle' hSubP]
              cases valP with
              | pair ca cb =>
                  cases cb with
                  | boundVar j => exact id
                  | clos env' tm' => exact whEval_mono hle'
              | _ => exact id

/-- **Fuel Monotonicity of `nbeWhnf`**: -/
theorem nbeWhnf_mono {fuel₁ fuel₂ : Nat} (hle : fuel₁ ≤ fuel₂)
    {n : Nat} {t : Tm Head n} {res : ExecutableReduction.Result R t}
    (h : nbeWhnf R root fuel₁ t = some res) :
    nbeWhnf R root fuel₂ t = some res := by
  unfold nbeWhnf at h ⊢
  split at h
  · cases h
  · rename_i v hEval₁
    have hEval₂ := whEval_mono R root hle hEval₁
    split
    · rename_i hNone
      rw [hEval₂] at hNone
      cases hNone
    · rename_i v₂ hEval₂'
      rw [hEval₂] at hEval₂'
      injection hEval₂' with hEq
      subst hEq
      exact h

/-- **Fuel Monotonicity of `nbeWhnfReducer`**: -/
theorem nbeWhnfReducer_mono {fuel₁ fuel₂ : Nat} (hle : fuel₁ ≤ fuel₂)
    {n : Nat} {t : Tm Head n} {res : ExecutableReduction.Result R t}
    (h : nbeWhnfReducer R root fuel₁ t = some res) :
    nbeWhnfReducer R root fuel₂ t = some res :=
  nbeWhnf_mono R root hle h

end WhMachine

/-! ## 6. Weak-Head Termination & Completeness of the Closure Machine (`whEval_complete_of_whRed`) -/

section WhCompleteness

variable {Head : Type}

/-- Syntactic size of a term `Tm Head n`, used as the secondary well-founded measure
when unfolding environment variables and traversing neutral spines. -/
def tmSize {n : Nat} : Tm Head n → Nat
  | .var _ | .const _ | .head _ => 1
  | .pi A B | .sigma A B | .app A B | .pair A B => 1 + tmSize A + tmSize B
  | .id A a b => 1 + tmSize A + tmSize a + tmSize b
  | .lam body | .fst body | .snd body | .refl body => 1 + tmSize body

mutual

/-- Potential depth of a `WhEntry Head n`. -/
def WhEntry.depth {n : Nat} : WhEntry Head n → Nat
  | .boundVar _ => 0
  | .clos env tm => WhEnv.maxDepth env + tmSize tm

/-- Maximum entry depth across all entries in `WhEnv Head m n`. -/
def WhEnv.maxDepth : {m n : Nat} → WhEnv Head m n → Nat
  | _, _, .nil => 0
  | _, _, .snoc env e => Nat.max (WhEnv.maxDepth env) (WhEntry.depth e)

end

theorem WhEnv.lookup_depth_le :
    ∀ {m n : Nat} (env : WhEnv Head m n) (i : Fin m),
      (env.lookup i).depth ≤ env.maxDepth
  | _, _, .nil, i => Fin.elim0 i
  | _, _, .snoc env e, i => by
      refine Fin.cases ?_ ?_ i
      · exact Nat.le_max_right _ _
      · intro j
        exact Nat.le_trans (WhEnv.lookup_depth_le env j) (Nat.le_max_left _ _)

/-- Step-indexed weak-head reduction `WhRedN R roles k t w`: `t` reduces to `w`
in `k` head `WhStep` steps. -/
inductive WhRedN (R : Rules Head) (roles : Roles Head) :
    Nat → {n : Nat} → Tm Head n → Tm Head n → Prop where
  | refl {n : Nat} {t : Tm Head n} : WhRedN R roles 0 t t
  | head {k n : Nat} {t u w : Tm Head n} :
      WhStep R roles t u → WhRedN R roles k u w → WhRedN R roles (k + 1) t w

theorem WhRed.to_whRedN {R : Rules Head} {roles : Roles Head}
    {n : Nat} {t w : Tm Head n} (red : WhRed R roles t w) :
    ∃ k, WhRedN R roles k t w := by
  induction red using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl⟩
  | head step _ ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, .head step hk⟩

theorem WhRedN.to_whRed {R : Rules Head} {roles : Roles Head}
    {k n : Nat} {t w : Tm Head n} (red : WhRedN R roles k t w) :
    WhRed R roles t w := by
  induction red with
  | refl => exact .refl
  | head step _ ih => exact .head step ih

theorem WhRedN.eq_of_whnf {R : Rules Head} {roles : Roles Head}
    {k n : Nat} {t w : Tm Head n} (red : WhRedN R roles k t w)
    (normal : Whnf R roles t) : k = 0 ∧ t = w := by
  cases red with
  | refl => exact ⟨rfl, rfl⟩
  | head step _ => exact absurd step (normal _)

theorem emptyRootShape {R : Rules Head} {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty) : RootShape R roles where
  spine step := by rw [hComp] at step; exact step.elim
  deterministic step := by rw [hComp] at step; exact step.elim

/-- Inversion of step-counted weak-head reduction on an application `.app f a`
when `R.computation = RootComputation.empty` and `roles = fun _ => .rigid`. -/
theorem whRedN_app_inv {R : Rules Head} {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty)
    (hRoles : roles = fun _ => .rigid) :
    ∀ {k n : Nat} {f a w : Tm Head n},
      WhRedN R roles k (.app f a) w →
      Whnf R roles w →
      (∃ k₁ f', k₁ ≤ k ∧ WhRedN R roles k₁ f f' ∧ Whnf R roles f' ∧
        w = .app f' a ∧ (∀ body, f' ≠ .lam body)) ∨
      (∃ k₁ k₂ body, k₁ + 1 + k₂ = k ∧
        WhRedN R roles k₁ f (.lam body) ∧ WhRedN R roles k₂ (inst0 a body) w)
  | 0, _, f, a, _, .refl, hWhnf => by
      left
      refine ⟨0, f, Nat.le_refl 0, .refl, ?_, rfl, ?_⟩
      · intro f' stepF
        exact hWhnf (.app f' a) (.appFun stepF)
      · intro body hLam
        subst hLam
        exact hWhnf (inst0 a body) (.beta body a)
  | k + 1, _, f, a, w, .head step rest, hWhnf => by
      generalize hTerm : Tm.app f a = t at step
      cases step with
      | beta body a' =>
          obtain ⟨rfl, rfl⟩ := Tm.app.inj hTerm
          right
          exact ⟨0, k, body, by omega, .refl, rest⟩
      | appFun stepF =>
          obtain ⟨rfl, rfl⟩ := Tm.app.inj hTerm
          rcases whRedN_app_inv hComp hRoles rest hWhnf with
            ⟨k₁, f', hk₁, redF, whnfF', hw, hNotLam⟩ |
            ⟨k₁, k₂, body, hk, redF, redBeta⟩
          · left
            exact ⟨k₁ + 1, f', Nat.succ_le_succ hk₁, .head stepF redF, whnfF', hw, hNotLam⟩
          · right
            exact ⟨k₁ + 1, k₂, body, by omega, .head stepF redF, redBeta⟩
      | root stepRoot =>
          rw [hComp] at stepRoot
          exact stepRoot.elim
      | scrutinee role _ _ _ =>
          rw [hRoles] at role
          cases role
      | fstPair _ _ | sndPair _ _ | fst _ | snd _ => cases hTerm

/-- Inversion of step-counted weak-head reduction on `.fst p`. -/
theorem whRedN_fst_inv {R : Rules Head} {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty)
    (hRoles : roles = fun _ => .rigid) :
    ∀ {k n : Nat} {p w : Tm Head n},
      WhRedN R roles k (.fst p) w →
      Whnf R roles w →
      (∃ k₁ p', k₁ ≤ k ∧ WhRedN R roles k₁ p p' ∧ Whnf R roles p' ∧
        w = .fst p' ∧ (∀ a b, p' ≠ .pair a b)) ∨
      (∃ k₁ k₂ a b, k₁ + 1 + k₂ = k ∧
        WhRedN R roles k₁ p (.pair a b) ∧ WhRedN R roles k₂ a w)
  | 0, _, p, _, .refl, hWhnf => by
      left
      refine ⟨0, p, Nat.le_refl 0, .refl, ?_, rfl, ?_⟩
      · intro p' stepP
        exact hWhnf (.fst p') (.fst stepP)
      · intro a b hPair
        subst hPair
        exact hWhnf a (.fstPair a b)
  | k + 1, _, p, w, .head step rest, hWhnf => by
      generalize hTerm : Tm.fst p = t at step
      cases step with
      | fstPair _ _ =>
          have hEq := Tm.fst.inj hTerm
          subst hEq
          right
          exact ⟨0, k, _, _, by omega, .refl, rest⟩
      | fst stepP =>
          have hEq := Tm.fst.inj hTerm
          subst hEq
          rcases whRedN_fst_inv hComp hRoles rest hWhnf with
            ⟨k₁, p', hk₁, redP, whnfP', hw, hNotPair⟩ |
            ⟨k₁, k₂, a, b, hk, redP, redA⟩
          · left
            exact ⟨k₁ + 1, p', Nat.succ_le_succ hk₁, .head stepP redP, whnfP', hw, hNotPair⟩
          · right
            exact ⟨k₁ + 1, k₂, a, b, by omega, .head stepP redP, redA⟩
      | root stepRoot =>
          rw [hComp] at stepRoot
          exact stepRoot.elim
      | scrutinee role _ _ _ =>
          rw [hRoles] at role
          cases role
      | beta _ _ | sndPair _ _ | appFun _ | snd _ => cases hTerm

/-- Inversion of step-counted weak-head reduction on `.snd p`. -/
theorem whRedN_snd_inv {R : Rules Head} {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty)
    (hRoles : roles = fun _ => .rigid) :
    ∀ {k n : Nat} {p w : Tm Head n},
      WhRedN R roles k (.snd p) w →
      Whnf R roles w →
      (∃ k₁ p', k₁ ≤ k ∧ WhRedN R roles k₁ p p' ∧ Whnf R roles p' ∧
        w = .snd p' ∧ (∀ a b, p' ≠ .pair a b)) ∨
      (∃ k₁ k₂ a b, k₁ + 1 + k₂ = k ∧
        WhRedN R roles k₁ p (.pair a b) ∧ WhRedN R roles k₂ b w)
  | 0, _, p, _, .refl, hWhnf => by
      left
      refine ⟨0, p, Nat.le_refl 0, .refl, ?_, rfl, ?_⟩
      · intro p' stepP
        exact hWhnf (.snd p') (.snd stepP)
      · intro a b hPair
        subst hPair
        exact hWhnf b (.sndPair a b)
  | k + 1, _, p, w, .head step rest, hWhnf => by
      generalize hTerm : Tm.snd p = t at step
      cases step with
      | sndPair _ _ =>
          have hEq := Tm.snd.inj hTerm
          subst hEq
          right
          exact ⟨0, k, _, _, by omega, .refl, rest⟩
      | snd stepP =>
          have hEq := Tm.snd.inj hTerm
          subst hEq
          rcases whRedN_snd_inv hComp hRoles rest hWhnf with
            ⟨k₁, p', hk₁, redP, whnfP', hw, hNotPair⟩ |
            ⟨k₁, k₂, a, b, hk, redP, redB⟩
          · left
            exact ⟨k₁ + 1, p', Nat.succ_le_succ hk₁, .head stepP redP, whnfP', hw, hNotPair⟩
          · right
            exact ⟨k₁ + 1, k₂, a, b, by omega, .head stepP redP, redB⟩
      | root stepRoot =>
          rw [hComp] at stepRoot
          exact stepRoot.elim
      | scrutinee role _ _ _ =>
          rw [hRoles] at role
          cases role
      | beta _ _ | fstPair _ _ | appFun _ | fst _ => cases hTerm

/-- **Weak-Head Completeness of the Closure Machine (`whEval_complete_of_whRedN`)**:
Whenever `subst env.toSub t` weak-head reduces in `k` steps to a weak-head normal
form `w`, `whEval R (fun _ => none) fuel env t` succeeds for some `fuel` and produces
a value `v` whose syntactic realization `v.toTm` is `w`. -/
theorem whEval_complete_of_whRedN {R : Rules Head} {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty)
    (hRoles : roles = fun _ => .rigid) {n : Nat} :
    ∀ (k : Nat) {m : Nat} (env : WhEnv Head m n) (t : Tm Head m) {w : Tm Head n},
      WhRedN R roles k (subst env.toSub t) w →
      Whnf R roles w →
      ∃ (fuel : Nat) (v : WhVal Head n),
        whEval R (fun _ => none) fuel env t = some v ∧ v.toTm = w := by
  have hShape : RootShape R roles := emptyRootShape hComp
  intro k
  induction k using Nat.strongRecOn with
  | ind k ihK =>
      intro m env t w hRed hWhnf
      generalize hd : env.maxDepth + tmSize t = d
      induction d using Nat.strongRecOn generalizing m env t w with
      | ind d ihD =>
          have runLe :
              ∀ {k₁ : Nat} {m₁ : Nat} (env₁ : WhEnv Head m₁ n) (t₁ : Tm Head m₁) {w₁ : Tm Head n},
                k₁ ≤ k →
                env₁.maxDepth + tmSize t₁ < d →
                WhRedN R roles k₁ (subst env₁.toSub t₁) w₁ →
                Whnf R roles w₁ →
                ∃ (fuel : Nat) (v : WhVal Head n),
                  whEval R (fun _ => none) fuel env₁ t₁ = some v ∧ v.toTm = w₁ := by
            intro k₁ m₁ env₁ t₁ w₁ hk₁ hd₁ hRed₁ hWhnf₁
            rcases Nat.lt_or_eq_of_le hk₁ with hlt | rfl
            · exact ihK k₁ hlt env₁ t₁ hRed₁ hWhnf₁
            · exact ihD (env₁.maxDepth + tmSize t₁) hd₁ env₁ t₁ hRed₁ hWhnf₁ rfl
          cases t with
          | var i =>
              cases hLookup : env.lookup i with
              | boundVar j =>
                  have hSub : subst env.toSub (.var i) = .var j := by
                    simp [subst, ← WhEnv.lookup_toTm, hLookup, WhEntry.toTm]
                  rw [hSub] at hRed
                  have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (var_whnf hShape j)
                  exact ⟨1, .var j, by simp [whEval, hLookup], hw⟩
              | clos env' tm' =>
                  have hSub : subst env.toSub (.var i) = subst env'.toSub tm' := by
                    simp [subst, ← WhEnv.lookup_toTm, hLookup, WhEntry.toTm]
                  have hRed' : WhRedN R roles k (subst env'.toSub tm') w := hSub ▸ hRed
                  have hDepth : env'.maxDepth + tmSize tm' < d := by
                    have hLe := WhEnv.lookup_depth_le env i
                    rw [hLookup] at hLe
                    simp only [WhEntry.depth] at hLe
                    simp only [tmSize] at hd
                    omega
                  obtain ⟨fuel, v, hEval, hToTm⟩ :=
                    ihD (env'.maxDepth + tmSize tm') hDepth env' tm' hRed' hWhnf rfl
                  exact ⟨fuel + 1, v, by simp [whEval, hLookup, hEval], hToTm⟩
          | const name =>
              have hWhnfConst : Whnf R roles (.const name : Tm Head n) :=
                constSpine_whnf hShape (args := []) (by
                  intro a s hRole
                  rw [congrFun hRoles name] at hRole
                  cases hRole)
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed hWhnfConst
              exact ⟨1, .const name, rfl, hw⟩
          | head h =>
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (head_whnf hShape h)
              exact ⟨1, .head h, rfl, hw⟩
          | pi A B =>
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (pi_whnf hShape _ _)
              exact ⟨1, .pi env A B, rfl, hw⟩
          | sigma A B =>
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (sigma_whnf hShape _ _)
              exact ⟨1, .sigma env A B, rfl, hw⟩
          | id A a b =>
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (id_whnf hShape _ _ _)
              exact ⟨1, .id env A a b, rfl, hw⟩
          | lam body =>
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (lam_whnf hShape _)
              exact ⟨1, .lam env body, rfl, hw⟩
          | pair a b =>
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (pair_whnf hShape _ _)
              exact ⟨1, .pair (.clos env a) (.clos env b), rfl, hw⟩
          | refl a =>
              have ⟨_, hw⟩ := WhRedN.eq_of_whnf hRed (refl_whnf hShape _)
              exact ⟨1, .refl (.clos env a), rfl, hw⟩
          | app f a =>
              have hSizeF : env.maxDepth + tmSize f < d := by
                simp only [tmSize] at hd
                omega
              rcases whRedN_app_inv hComp hRoles hRed hWhnf with
                ⟨k₁, f', hk₁, redF, whnfF', rfl, hNotLam⟩ |
                ⟨k₁, k₂, body₀, hk, redF, redBeta⟩
              · obtain ⟨fuelF, valF, hEvalF, hToTmF⟩ := runLe env f hk₁ hSizeF redF whnfF'
                have hValNotLam : ∀ {m'} (env' : WhEnv Head m' n) (body' : Tm Head (m' + 1)),
                    valF ≠ .lam env' body' := by
                  intro m' env' body' hEq
                  apply hNotLam (subst (liftSub env'.toSub) body')
                  rw [← hToTmF, hEq]
                  rfl
                refine ⟨fuelF + 1, .app valF (.clos env a), ?_, ?_⟩
                · simp only [whEval, hEvalF, bind, Option.bind]
                  cases valF with
                  | lam env' body' => exact False.elim (hValNotLam env' body' rfl)
                  | _ => rfl
                · simp [WhVal.toTm, WhEntry.toTm, hToTmF]
              · have hk₁ : k₁ < k := by omega
                have hk₂ : k₂ < k := by omega
                obtain ⟨fuel₁, valF, hEvalF, hToTmF⟩ :=
                  ihK k₁ hk₁ env f redF (lam_whnf hShape body₀)
                obtain ⟨m', env', body', hValF, hBodyEq⟩ := WhVal.toTm_eq_lam_iff.mp hToTmF
                have hSubBeta :
                    subst (env'.snoc (.clos env a)).toSub body' =
                      inst0 (subst env.toSub a) body₀ := by
                  rw [← hBodyEq, ← WhEnv.inst0_liftSub_toSub env' body' (.clos env a)]
                  rfl
                have redBeta' :
                    WhRedN R roles k₂ (subst (env'.snoc (.clos env a)).toSub body') w :=
                  hSubBeta.symm ▸ redBeta
                obtain ⟨fuel₂, valBeta, hEvalBeta, hToTmBeta⟩ :=
                  ihK k₂ hk₂ (env'.snoc (.clos env a)) body' redBeta' hWhnf
                have hEvalF' := whEval_mono R (fun _ => none) (Nat.le_max_left fuel₁ fuel₂) hEvalF
                have hEvalBeta' := whEval_mono R (fun _ => none) (Nat.le_max_right fuel₁ fuel₂) hEvalBeta
                refine ⟨Nat.max fuel₁ fuel₂ + 1, valBeta, ?_, hToTmBeta⟩
                simp [whEval, hEvalF', hValF, hEvalBeta', bind, Option.bind]
          | fst p =>
              have hSizeP : env.maxDepth + tmSize p < d := by
                simp only [tmSize] at hd
                omega
              rcases whRedN_fst_inv hComp hRoles hRed hWhnf with
                ⟨k₁, p', hk₁, redP, whnfP', rfl, hNotPair⟩ |
                ⟨k₁, k₂, a₀, b₀, hk, redP, redA⟩
              · obtain ⟨fuelP, valP, hEvalP, hToTmP⟩ := runLe env p hk₁ hSizeP redP whnfP'
                have hValNotPair : ∀ (ca cb : WhEntry Head n), valP ≠ .pair ca cb := by
                  intro ca cb hEq
                  apply hNotPair ca.toTm cb.toTm
                  rw [← hToTmP, hEq]
                  rfl
                refine ⟨fuelP + 1, .fst valP, ?_, ?_⟩
                · simp only [whEval, hEvalP, bind, Option.bind]
                  cases valP with
                  | pair ca cb => exact False.elim (hValNotPair ca cb rfl)
                  | _ => rfl
                · simp [WhVal.toTm, hToTmP]
              · have hk₁ : k₁ < k := by omega
                have hk₂ : k₂ < k := by omega
                obtain ⟨fuel₁, valP, hEvalP, hToTmP⟩ :=
                  ihK k₁ hk₁ env p redP (pair_whnf hShape a₀ b₀)
                obtain ⟨ca, cb, hValP, hCaTm, _⟩ := WhVal.toTm_eq_pair_iff.mp hToTmP
                cases hCa : ca with
                | boundVar j =>
                    have ha₀ : a₀ = .var j := by
                      rw [← hCaTm, hCa]
                      rfl
                    rw [ha₀] at redA
                    have ⟨_, hw⟩ := WhRedN.eq_of_whnf redA (var_whnf hShape j)
                    refine ⟨fuel₁ + 1, .var j, ?_, hw⟩
                    simp [whEval, hEvalP, hValP, hCa, bind, Option.bind, pure]
                | clos env' tm' =>
                    have ha₀ : subst env'.toSub tm' = a₀ := by
                      rw [← hCaTm, hCa]
                      rfl
                    have redA' : WhRedN R roles k₂ (subst env'.toSub tm') w := ha₀.symm ▸ redA
                    obtain ⟨fuel₂, valA, hEvalA, hToTmA⟩ :=
                      ihK k₂ hk₂ env' tm' redA' hWhnf
                    have hEvalP' := whEval_mono R (fun _ => none) (Nat.le_max_left fuel₁ fuel₂) hEvalP
                    have hEvalA' := whEval_mono R (fun _ => none) (Nat.le_max_right fuel₁ fuel₂) hEvalA
                    refine ⟨Nat.max fuel₁ fuel₂ + 1, valA, ?_, hToTmA⟩
                    simp [whEval, hEvalP', hValP, hCa, hEvalA', bind, Option.bind]
          | snd p =>
              have hSizeP : env.maxDepth + tmSize p < d := by
                simp only [tmSize] at hd
                omega
              rcases whRedN_snd_inv hComp hRoles hRed hWhnf with
                ⟨k₁, p', hk₁, redP, whnfP', rfl, hNotPair⟩ |
                ⟨k₁, k₂, a₀, b₀, hk, redP, redB⟩
              · obtain ⟨fuelP, valP, hEvalP, hToTmP⟩ := runLe env p hk₁ hSizeP redP whnfP'
                have hValNotPair : ∀ (ca cb : WhEntry Head n), valP ≠ .pair ca cb := by
                  intro ca cb hEq
                  apply hNotPair ca.toTm cb.toTm
                  rw [← hToTmP, hEq]
                  rfl
                refine ⟨fuelP + 1, .snd valP, ?_, ?_⟩
                · simp only [whEval, hEvalP, bind, Option.bind]
                  cases valP with
                  | pair ca cb => exact False.elim (hValNotPair ca cb rfl)
                  | _ => rfl
                · simp [WhVal.toTm, hToTmP]
              · have hk₁ : k₁ < k := by omega
                have hk₂ : k₂ < k := by omega
                obtain ⟨fuel₁, valP, hEvalP, hToTmP⟩ :=
                  ihK k₁ hk₁ env p redP (pair_whnf hShape a₀ b₀)
                obtain ⟨ca, cb, hValP, _, hCbTm⟩ := WhVal.toTm_eq_pair_iff.mp hToTmP
                cases hCb : cb with
                | boundVar j =>
                    have hb₀ : b₀ = .var j := by
                      rw [← hCbTm, hCb]
                      rfl
                    rw [hb₀] at redB
                    have ⟨_, hw⟩ := WhRedN.eq_of_whnf redB (var_whnf hShape j)
                    refine ⟨fuel₁ + 1, .var j, ?_, hw⟩
                    simp [whEval, hEvalP, hValP, hCb, bind, Option.bind, pure]
                | clos env' tm' =>
                    have hb₀ : subst env'.toSub tm' = b₀ := by
                      rw [← hCbTm, hCb]
                      rfl
                    have redB' : WhRedN R roles k₂ (subst env'.toSub tm') w := hb₀.symm ▸ redB
                    obtain ⟨fuel₂, valB, hEvalB, hToTmB⟩ :=
                      ihK k₂ hk₂ env' tm' redB' hWhnf
                    have hEvalP' := whEval_mono R (fun _ => none) (Nat.le_max_left fuel₁ fuel₂) hEvalP
                    have hEvalB' := whEval_mono R (fun _ => none) (Nat.le_max_right fuel₁ fuel₂) hEvalB
                    refine ⟨Nat.max fuel₁ fuel₂ + 1, valB, ?_, hToTmB⟩
                    simp [whEval, hEvalP', hValP, hCb, hEvalB', bind, Option.bind]

/-- **Weak-Head Completeness of `whEval` for `WhRed`**: -/
theorem whEval_complete_of_whRed {R : Rules Head} {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty)
    (hRoles : roles = fun _ => .rigid)
    {m n : Nat} (env : WhEnv Head m n) (t : Tm Head m) {w : Tm Head n}
    (hRed : WhRed R roles (subst env.toSub t) w)
    (hWhnf : Whnf R roles w) :
    ∃ (fuel : Nat) (v : WhVal Head n),
      whEval R (fun _ => none) fuel env t = some v ∧ v.toTm = w := by
  obtain ⟨k, hRedN⟩ := WhRed.to_whRedN hRed
  exact whEval_complete_of_whRedN hComp hRoles k env t hRedN hWhnf

/-- **Weak-Head Completeness of `nbeWhnf` (and `nbeWhnfReducer`)**:
Whenever `t` weak-head reduces to a weak-head normal form `w` (`WhRed R roles t w ∧ Whnf R roles w`),
there exists `fuel` such that `nbeWhnf R (fun _ => none) fuel t` returns `some res` with `res.val = w`. -/
theorem nbeWhnf_complete_of_whRed {R : Rules Head} {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty)
    (hRoles : roles = fun _ => .rigid)
    {n : Nat} {t w : Tm Head n}
    (hRed : WhRed R roles t w)
    (hWhnf : Whnf R roles w) :
    ∃ (fuel : Nat) (res : ExecutableReduction.Result R t),
      nbeWhnf R (fun _ => none) fuel t = some res ∧ res.val = w := by
  have hRedSub : WhRed R roles (subst (WhEnv.idEnv n).toSub t) w := by
    simpa [WhEnv.toSub_idEnv, subst_ids] using hRed
  obtain ⟨fuel, v, hEval, hToTm⟩ :=
    whEval_complete_of_whRed hComp hRoles (WhEnv.idEnv n) t hRedSub hWhnf
  refine ⟨fuel, ⟨v.toTm, by simpa [WhEnv.toSub_idEnv, subst_ids] using whEval_sound R (fun _ => none) hEval⟩,
    ?_, hToTm⟩
  unfold nbeWhnf
  split
  · rename_i hNone
    rw [hEval] at hNone
    cases hNone
  · rename_i v' hEval'
    rw [hEval] at hEval'
    injection hEval' with hEq
    subst hEq
    rfl

end WhCompleteness

/-! ## 7. Instrumented Closure-Machine Step Counter (`whEvalSteps`) -/

section InstrumentedCost

variable {Head : Type} (R : Rules Head) (root : ExecutableReduction.RootEvaluator R)

/-- Instrumented step counter `whEvalSteps` for `whEval`: counts the exact number of
recursive closure-machine evaluations performed at `fuel` on `(env, t)`. -/
def whEvalSteps : Nat → {m n : Nat} → (env : WhEnv Head m n) → (t : Tm Head m) →
    Option Nat
  | 0, _, _, _, _ => none
  | fuel + 1, _, n, env, t =>
      match t with
      | .var i =>
          match env.lookup i with
          | .boundVar _ => some 1
          | .clos env' tm' => do
              let s ← whEvalSteps fuel env' tm'
              return 1 + s
      | .const name =>
          match root (Tm.const (Head := Head) (n := n) name) with
          | none => some 1
          | some next => do
              let s ← whEvalSteps fuel (WhEnv.idEnv n) next.val
              return 1 + s
      | .head _ | .pi _ _ | .sigma _ _ | .id _ _ _ | .lam _ | .pair _ _ | .refl _ =>
          some 1
      | .app f a => do
          let valF ← whEval R root fuel env f
          let sF ← whEvalSteps fuel env f
          match valF with
          | .lam env' body' => do
              let sBeta ← whEvalSteps fuel (env'.snoc (.clos env a)) body'
              return 1 + sF + sBeta
          | _ =>
              match root (Tm.app valF.toTm (WhEntry.clos env a).toTm) with
              | none => return 1 + sF
              | some next => do
                  let sRoot ← whEvalSteps fuel (WhEnv.idEnv n) next.val
                  return 1 + sF + sRoot
      | .fst p => do
          let valP ← whEval R root fuel env p
          let sP ← whEvalSteps fuel env p
          match valP with
          | .pair (.boundVar _) _ => return 1 + sP
          | .pair (.clos env' tm') _ => do
              let sA ← whEvalSteps fuel env' tm'
              return 1 + sP + sA
          | _ => return 1 + sP
      | .snd p => do
          let valP ← whEval R root fuel env p
          let sP ← whEvalSteps fuel env p
          match valP with
          | .pair _ (.boundVar _) => return 1 + sP
          | .pair _ (.clos env' tm') => do
              let sB ← whEvalSteps fuel env' tm'
              return 1 + sP + sB
          | _ => return 1 + sP

/-- Top-level weak-head NbE step count (`nbeWhnfSteps`). -/
def nbeWhnfSteps (fuel : Nat) {n : Nat} (t : Tm Head n) : Option Nat :=
  whEvalSteps R root fuel (WhEnv.idEnv n) t

/-- Applying the identity lambda `.lam (.var 0)` to `arg` at `fuel + 2` consumes
1 step for the `.app` node, 1 step to evaluate `.lam (.var 0)` to a closure, and
1 step to look up `.var 0` in the extended environment before evaluating `arg` at `fuel`. -/
theorem whEvalSteps_app_id (fuel : Nat) {m n : Nat} (env : WhEnv Head m n) (arg : Tm Head m) :
    whEvalSteps R root (fuel + 2) env (.app (.lam (.var 0)) arg) =
      (whEvalSteps R root fuel env arg).map (fun s => 3 + s) := by
  have hLookup0 : (env.snoc (.clos env arg)).lookup (0 : Fin (m + 1)) = .clos env arg := by
    simp [WhEnv.lookup]
  simp only [whEvalSteps, whEval, hLookup0, bind, Option.bind, Option.map]
  cases whEvalSteps R root fuel env arg with
  | none => rfl
  | some s =>
      change some (1 + 1 + (1 + s)) = some (3 + s)
      congr 1
      omega

end InstrumentedCost

end Mettapedia.TypeTheory.NbE


