import Mettapedia.Logic.HOL.Semantics.StandardTransport
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.Metaphysics.DedekindCategoricity
import Mathlib.Tactic.DeriveCountable

/-!
# Virtue 4: a categorical theory of an infinite structure

Peano arithmetic as a theory of simple type theory: one base type `ι`, the
constants `0 : ι` and `s : ι ⇒ ι`, and three axioms, the last of which is
induction quantified over the predicates `ι ⇒ prop`.

* `peanoStructure`: a full-domain model of the axioms is a second-order Peano
  structure, so Dedekind's theorem applies.
* `categorical`: any two full-domain models are isomorphic by a bijection of
  their individuals that preserves `0` and `s`.
* `models_iff_of_models`: any two full-domain models satisfy the same
  sentences (with the isomorphism invariance of `StandardTransport`).
* `semanticallyComplete`: every sentence or its negation is true in all
  full-domain models of the axioms; `natModel` is one such model.
* `infinite_of_models`: the first two axioms already force an infinite base
  carrier, in every Henkin model.

Negative examples: without induction the axioms have the full model
`optionModel`, which refutes induction and is not isomorphic to the natural
numbers (`not_categorical_without_induction`). Full domains are needed too:
`GeneralModels.lean` gives a Henkin model of the same axioms with an element
that is no numeral.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues.Peano

open Mettapedia.Logic.Metaphysics

universe w w'

/-- The type of individuals. -/
abbrev ι : Ty Unit := .base ()

/-- Zero and successor. -/
inductive PeanoConst : Ty Unit → Type
  | zero : PeanoConst ι
  | succ : PeanoConst (ι ⇒ ι)
  deriving DecidableEq, Countable

section Axioms

variable {Const : Ty Unit → Type} (zero : Const ι) (succ : Const (ι ⇒ ι))

/-- `∀ x. ¬ (s x = 0)`. -/
def zeroNotSucc : ClosedFormula Const :=
  .all (.not (.eq (.app (.const succ) (.var (.vz : Var [ι] ι))) (.const zero)))

/-- `∀ x y. s x = s y → x = y`. -/
def succInjective : ClosedFormula Const :=
  .all (.all (.imp
    (.eq (.app (.const succ) (.var (.vs (.vz : Var [ι] ι) : Var [ι, ι] ι)))
      (.app (.const succ) (.var .vz)))
    (.eq (.var (.vs .vz)) (.var .vz))))

/-- `∀ p : ι ⇒ prop. p 0 ∧ (∀ x. p x → p (s x)) → ∀ x. p x`. -/
def induction : ClosedFormula Const :=
  .all (σ := ι ⇒ .prop) (.imp
    (.and (.app (.var .vz) (.const zero))
      (.all (.imp (.app (.var (.vs .vz)) (.var (.vz : Var [ι, ι ⇒ .prop] ι)))
        (.app (.var (.vs .vz)) (.app (.const succ) (.var .vz))))))
    (.all (.app (.var (.vs .vz)) (.var (.vz : Var [ι, ι ⇒ .prop] ι)))))

/-- Peano's axioms in simple type theory. -/
def axioms : ClosedTheorySet Const :=
  {zeroNotSucc zero succ, succInjective succ, induction zero succ}

/-- The numeral `sⁿ 0`. -/
def numeral : ℕ → ClosedTerm Const ι
  | 0 => .const zero
  | n + 1 => .app (.const succ) (numeral n)

variable (M : HenkinModel.{0, 0, w} Unit Const)

/-- Zero in a model, as an individual. -/
def zeroOf : M.Carrier () := M.constDen zero

/-- Successor in a model, as a function on individuals. -/
def succOf : M.Carrier () → M.Carrier () := M.constDen succ

theorem models_zeroNotSucc :
    M.models (zeroNotSucc zero succ) ↔ ∀ x : M.Carrier (), succOf succ M x ≠ zeroOf zero M := by
  constructor
  · intro h x
    exact h x (M.base_mem () x)
  · intro h x _
    exact h x

theorem models_succInjective :
    M.models (succInjective succ) ↔ Function.Injective (succOf succ M) := by
  constructor
  · intro h x y hxy
    exact h x (M.base_mem () x) y (M.base_mem () y) hxy
  · intro h x _ y _ hxy
    exact h hxy

theorem models_induction :
    M.models (induction zero succ) ↔
      ∀ p : M.Carrier () → ULift.{max 1 w} Prop, M.adm (ι ⇒ .prop) p →
        (p (zeroOf zero M)).down → (∀ x, (p x).down → (p (succOf succ M x)).down) →
          ∀ x, (p x).down := by
  constructor
  · intro h p hp hzero hstep x
    exact h p hp ⟨hzero, fun y _ hy => hstep y hy⟩ x (M.base_mem () x)
  · rintro h p hp ⟨hzero, hstep⟩ x _
    exact h p hp hzero (fun y hy => hstep y (M.base_mem () y) hy) x

theorem models_axioms_iff :
    (∀ ψ ∈ axioms zero succ, M.models ψ) ↔
      M.models (zeroNotSucc zero succ) ∧ M.models (succInjective succ) ∧
        M.models (induction zero succ) := by
  constructor
  · intro h
    exact ⟨h _ (by simp [axioms]), h _ (by simp [axioms]), h _ (by simp [axioms])⟩
  · rintro ⟨h₁, h₂, h₃⟩ ψ hψ
    simp only [axioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
    rcases hψ with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃

/-- The numeral `sⁿ 0` denotes the `n`-th iterate of the successor at zero. -/
theorem denote_numeral (n : ℕ) (ρ : M.Valuation []) :
    M.denote (numeral zero succ n) ρ = (succOf succ M)^[n] (zeroOf zero M) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change succOf succ M (M.denote (numeral zero succ n) ρ) = _
      rw [ih]

/-- **The first two axioms force infinitely many individuals**, in every Henkin
model: the numerals denote pairwise distinct values. -/
theorem infinite_of_models (h₁ : M.models (zeroNotSucc zero succ))
    (h₂ : M.models (succInjective succ)) : Infinite (M.Carrier ()) := by
  rw [models_zeroNotSucc] at h₁
  rw [models_succInjective] at h₂
  refine Infinite.of_injective (fun n : ℕ => (succOf succ M)^[n] (zeroOf zero M)) ?_
  intro m n hmn
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n =>
          dsimp only at hmn
          rw [Function.iterate_zero_apply, Function.iterate_succ_apply'] at hmn
          exact absurd hmn.symm (h₁ _)
  | succ m ih =>
      cases n with
      | zero =>
          dsimp only at hmn
          rw [Function.iterate_zero_apply, Function.iterate_succ_apply'] at hmn
          exact absurd hmn (h₁ _)
      | succ n =>
          dsimp only at hmn
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hmn
          exact congrArg Nat.succ (ih (h₂ hmn))

/-- A full-domain model of the axioms is a second-order Peano structure. -/
def peanoStructure (full : M.FullDomains) (h : ∀ ψ ∈ axioms zero succ, M.models ψ) :
    PeanoStructure.{max 1 w} where
  carrier := M.Carrier ()
  zero := zeroOf zero M
  succ := succOf succ M
  succ_inj := (models_succInjective succ M).mp ((models_axioms_iff zero succ M).mp h).2.1
  succ_ne_zero := (models_zeroNotSucc zero succ M).mp ((models_axioms_iff zero succ M).mp h).1
  induction := by
    intro S hzero hstep
    have hind := (models_induction zero succ M).mp ((models_axioms_iff zero succ M).mp h).2.2
    apply Set.eq_univ_of_forall
    intro x
    exact hind (fun y => ULift.up (y ∈ S)) (full _ _) hzero hstep x

end Axioms

/-! ## The Peano signature -/

variable (M : HenkinModel.{0, 0, w} Unit PeanoConst) (N : HenkinModel.{0, 0, w'} Unit PeanoConst)

/-- The interpretation of the two constants by a Peano structure. -/
def constDenOf (P : PeanoStructure.{max 1 w}) :
    {τ : Ty Unit} → PeanoConst τ → Ty.denote (fun _ => P.carrier) τ
  | _, .zero => P.zero
  | _, .succ => P.succ

/-- The standard model of a Peano structure. -/
def standardOf (P : PeanoStructure.{max 1 w}) : HenkinModel.{0, 0, w} Unit PeanoConst :=
  HenkinModel.standard (fun _ => P.carrier) (constDenOf P)

theorem standardOf_fullDomains (P : PeanoStructure.{max 1 w}) : (standardOf P).FullDomains :=
  HenkinModel.fullDomains_standard _ _

theorem standardOf_models (P : PeanoStructure.{max 1 w}) :
    ∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, (standardOf P).models ψ := by
  rw [models_axioms_iff]
  refine ⟨(models_zeroNotSucc _ _ _).mpr P.succ_ne_zero,
    (models_succInjective _ _).mpr P.succ_inj, (models_induction _ _ _).mpr ?_⟩
  intro p _ hzero hstep x
  have hS := P.induction {y | (p y).down} hzero hstep
  have hx : x ∈ {y | (p y).down} := hS ▸ Set.mem_univ x
  exact hx

/-- The natural numbers as a Peano structure, at any universe. -/
def natPeano : PeanoStructure.{max 1 w} where
  carrier := ULift.{max 1 w} ℕ
  zero := ⟨0⟩
  succ n := ⟨n.down + 1⟩
  succ_inj := by
    intro m n h
    exact ULift.ext _ _ (Nat.succ_injective (congrArg ULift.down h))
  succ_ne_zero := by
    intro n h
    exact Nat.succ_ne_zero n.down (congrArg ULift.down h)
  induction := by
    intro S hzero hstep
    apply Set.eq_univ_of_forall
    rintro ⟨n⟩
    induction n with
    | zero => exact hzero
    | succ n ih => exact hstep ⟨n⟩ ih

/-- The standard model of the natural numbers. -/
abbrev natModel : HenkinModel.{0, 0, w} Unit PeanoConst := standardOf natPeano.{w}

theorem natModel_models : ∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, natModel.{w}.models ψ :=
  standardOf_models _

/-- **Categoricity** (Dedekind 1888). Two full-domain models of Peano's axioms
are isomorphic by a bijection of individuals preserving zero and successor. -/
theorem categorical (fullM : M.FullDomains) (fullN : N.FullDomains)
    (hM : ∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, M.models ψ)
    (hN : ∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, N.models ψ) :
    ∃ e : M.Carrier () ≃ N.Carrier (),
      e (zeroOf PeanoConst.zero M) = zeroOf PeanoConst.zero N ∧
        ∀ x, e (succOf PeanoConst.succ M x) = succOf PeanoConst.succ N (e x) :=
  dedekind_categoricity (peanoStructure _ _ M fullM hM) (peanoStructure _ _ N fullN hN)

/-- Two full-domain models of Peano's axioms satisfy exactly the same
sentences. -/
theorem models_iff_of_models (fullM : M.FullDomains) (fullN : N.FullDomains)
    (hM : ∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, M.models ψ)
    (hN : ∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, N.models ψ)
    (φ : ClosedFormula PeanoConst) : M.models φ ↔ N.models φ := by
  obtain ⟨e, hzero, hsucc⟩ := categorical M N fullM fullN hM hN
  refine (StandardTransport.models_transport M N fullM fullN (fun _ => e) ?_ φ).symm
  intro τ c
  cases c with
  | zero => exact hzero
  | succ =>
      funext y
      change e (succOf PeanoConst.succ M (e.symm y)) = succOf PeanoConst.succ N y
      rw [hsucc]
      exact congrArg (succOf PeanoConst.succ N) (e.apply_symm_apply y)

/-- **Semantic completeness of the categorical theory.** For every sentence,
either it or its negation holds in all full-domain models of Peano's axioms. -/
theorem semanticallyComplete (φ : ClosedFormula PeanoConst) :
    (∀ M : HenkinModel.{0, 0, w} Unit PeanoConst, M.FullDomains →
        (∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, M.models ψ) → M.models φ) ∨
      (∀ M : HenkinModel.{0, 0, w} Unit PeanoConst, M.FullDomains →
        (∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, M.models ψ) → M.models (.not φ)) := by
  by_cases hφ : natModel.{w}.models φ
  · left
    intro M full hM
    exact (models_iff_of_models M natModel.{w} full (standardOf_fullDomains _) hM
      natModel_models φ).mpr hφ
  · right
    intro M full hM hMφ
    exact hφ ((models_iff_of_models M natModel.{w} full (standardOf_fullDomains _) hM
      natModel_models φ).mp hMφ)

/-! ## Negative example: induction is needed -/

/-- The successor on `Option ℕ` that fixes `none`. -/
def optionSucc (x : ULift.{1} (Option ℕ)) : ULift.{1} (Option ℕ) := ⟨x.down.map Nat.succ⟩

/-- The interpretation of zero and successor on `Option ℕ`. -/
def optionConstDen :
    {τ : Ty Unit} → PeanoConst τ → Ty.denote.{0, 0} (fun _ => ULift.{1} (Option ℕ)) τ
  | _, .zero => (⟨some 0⟩ : ULift.{1} (Option ℕ))
  | _, .succ => optionSucc

/-- The standard model on `Option ℕ`, with `none` a successor-fixed point. -/
def optionModel : HenkinModel.{0, 0, 0} Unit PeanoConst :=
  HenkinModel.standard (fun _ => ULift.{1} (Option ℕ)) optionConstDen

theorem optionModel_zeroNotSucc :
    optionModel.models (zeroNotSucc PeanoConst.zero PeanoConst.succ) := by
  rw [models_zeroNotSucc]
  rintro ⟨x⟩ h
  have h' : x.map Nat.succ = some 0 := congrArg ULift.down h
  cases x <;> simp at h'

theorem optionModel_succInjective : optionModel.models (succInjective PeanoConst.succ) := by
  rw [models_succInjective]
  rintro ⟨x⟩ ⟨y⟩ h
  have h' : x.map Nat.succ = y.map Nat.succ := congrArg ULift.down h
  exact ULift.ext _ _ (Option.map_injective Nat.succ_injective h')

theorem optionModel_not_induction :
    ¬ optionModel.models (induction PeanoConst.zero PeanoConst.succ) := by
  rw [models_induction]
  intro h
  have := h (fun x => ULift.up (x.down.isSome = true)) trivial (rfl : (some 0).isSome = true)
    (by
      rintro ⟨x⟩ hx
      cases x with
      | none => exact hx
      | some n => exact (rfl : (some (n + 1)).isSome = true))
    ⟨none⟩
  exact Bool.false_ne_true this

/-- Without induction, the remaining axioms are not categorical: `optionModel`
satisfies them, is full, and is not isomorphic to the natural numbers. -/
theorem not_categorical_without_induction :
    optionModel.FullDomains ∧
      optionModel.models (zeroNotSucc PeanoConst.zero PeanoConst.succ) ∧
      optionModel.models (succInjective PeanoConst.succ) ∧
      ¬ ∃ e : optionModel.Carrier () ≃ natModel.{0}.Carrier (),
        e (zeroOf PeanoConst.zero optionModel) = zeroOf PeanoConst.zero natModel.{0} ∧
          ∀ x, e (succOf PeanoConst.succ optionModel x) =
            succOf PeanoConst.succ natModel.{0} (e x) := by
  refine ⟨HenkinModel.fullDomains_standard _ _, optionModel_zeroNotSucc,
    optionModel_succInjective, ?_⟩
  rintro ⟨e, hzero, hsucc⟩
  apply optionModel_not_induction
  have hTransport := StandardTransport.models_transport optionModel natModel.{0}
    (HenkinModel.fullDomains_standard _ _) (standardOf_fullDomains _) (fun _ => e) (by
      intro τ c
      cases c with
      | zero => exact hzero
      | succ =>
          funext y
          change e (succOf PeanoConst.succ optionModel (e.symm y)) =
            succOf PeanoConst.succ natModel.{0} y
          rw [hsucc]
          exact congrArg (succOf PeanoConst.succ natModel.{0}) (e.apply_symm_apply y))
    (induction PeanoConst.zero PeanoConst.succ)
  exact hTransport.mp (natModel_models _ (by simp [axioms]))

#print axioms infinite_of_models
#print axioms categorical
#print axioms models_iff_of_models
#print axioms semanticallyComplete
#print axioms not_categorical_without_induction

end Mettapedia.Logic.HOL.SevenVirtues.Peano
