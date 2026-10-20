import Mettapedia.Logic.HOL.Embedding.FirstOrder
import Mettapedia.Logic.HOL.Semantics.StandardTransport

/-!
# Farmer's Theorem 2 for first-order logic, at the level of consequence

Farmer's Theorem 2 (The Seven Virtues of Simple Type Theory, 2008): every
theory of `n`-th order logic has a faithful interpretation in a theory of
simple type theory, i.e. `T ⊨ A` iff `T' ⊨ Φ(A)` for all sentences `A`.
This file proves the first-order case.

`Embedding.FirstOrder.embedSentence` translates a first-order sentence of a
language `L` into a closed HOL formula over one individual type, and
`Embedding.FirstOrder.denote_embedSentence_iff` preserves truth from a
structure to its induced standard model.  The translated theory adds one
sentence, `∃ x : ind. ⊤`, because first-order structures are nonempty while
standard HOL models may have empty base carriers.

* `faithful`: `T ⊨ A` over first-order structures in `Type (max 1 w)` iff the
  translation of `A` holds in every standard model of the translated theory
  with carriers in the same universe.
* `structureOf`: every standard model with a nonempty individual carrier
  determines a first-order structure on that carrier, and it satisfies the
  same sentences (`models_iff_evalb`), by isomorphism invariance of standard
  models (`StandardTransport.models_transport`).
* Negative control (`inhabitation_needed`): without `∃ x : ind. ⊤` the
  interpretation is not faithful; the standard model with an empty individual
  carrier refutes the translation of the valid sentence `∃ x. ⊤`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues.FirstOrderFaithfulness

open LO LO.FirstOrder
open Mettapedia.Logic.HOL.Embedding.FirstOrder

universe u w

variable {L : Language.{u}}

/-- The individual type is inhabited. -/
def indInhabited : ClosedFormula (Const L) := .ex (σ := indTy) .top

/-- The translated theory: the translated axioms and the inhabitation of the
individual type. -/
def translateTheory (T : Theory L) : Set (ClosedFormula (Const L)) :=
  insert indInhabited (embedSentence '' T)

/-- Consequence over standard HOL models with carriers in `Type (max 1 w)`. -/
def StandardConsequence (T : Set (ClosedFormula (Const L))) (ψ : ClosedFormula (Const L)) :
    Prop :=
  ∀ (C : BaseTy → Type (max 1 w)) (I : {τ : Ty BaseTy} → Const L τ → Ty.denote C τ),
    (∀ φ ∈ T, (HenkinModel.standard C I).models φ) → (HenkinModel.standard C I).models ψ

/-! ## Curried functions over a standard model -/

section Curry

variable {C : BaseTy → Type (max 1 w)}

/-- Apply a curried function on `k` individuals to a vector. -/
def uncurry {τ : Ty BaseTy} : {k : ℕ} →
    Ty.denote C (iterArrow k indTy τ) → (Fin k → C .ind) → Ty.denote C τ
  | 0, f, _ => f
  | k + 1, f, v => uncurry (k := k) (f (v 0)) (fun i => v i.succ)

/-- Curry a function of a vector of `k` individuals. -/
def curry {τ : Ty BaseTy} : {k : ℕ} →
    ((Fin k → C .ind) → Ty.denote C τ) → Ty.denote C (iterArrow k indTy τ)
  | 0, f => f ![]
  | k + 1, f => fun x => curry (k := k) (fun v => f (x :> v))

theorem curry_uncurry {τ : Ty BaseTy} :
    ∀ {k : ℕ} (f : Ty.denote C (iterArrow k indTy τ)), curry (k := k) (uncurry f) = f
  | 0, _ => rfl
  | k + 1, f => funext fun x => by
      show curry (k := k) (fun v => uncurry (f x) v) = f x
      exact curry_uncurry (f x)

end Curry

/-- The equivalence of individual carriers between the induced model of a
structure on `M` and a standard model whose individual carrier is `M`. -/
def baseEquiv (C : BaseTy → Type (max 1 w)) :
    ∀ b, BaseCarrier (C .ind) b ≃ C b
  | .ind => Equiv.ulift

theorem liftEquiv_curryVec (C : BaseTy → Type (max 1 w)) {τ : Ty BaseTy} :
    ∀ {k : ℕ} (F : (Fin k → IndCarrier (C .ind)) → Ty.denote (BaseCarrier (C .ind)) τ),
      StandardTransport.liftEquiv (baseEquiv C) (iterArrow k indTy τ) (Const.curryVec F) =
        curry (C := C) (k := k) fun v =>
          StandardTransport.liftEquiv (baseEquiv C) τ (F fun i => ULift.up (v i))
  | 0, F => by
      show StandardTransport.liftEquiv (baseEquiv C) τ (F ![]) = _
      congr 2
      funext i
      exact Fin.elim0 i
  | k + 1, F => by
      funext x
      show StandardTransport.liftEquiv (baseEquiv C) (iterArrow k indTy τ)
          (Const.curryVec (k := k) fun v => F (ULift.up x :> v)) = _
      rw [liftEquiv_curryVec C (k := k)]
      show curry (k := k) _ = curry (k := k) _
      congr 1
      funext v
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-! ## From standard models to first-order structures -/

/-- The first-order structure determined by a standard model on its individual
carrier. -/
@[reducible] def structureOf (C : BaseTy → Type (max 1 w))
    (I : {τ : Ty BaseTy} → Const L τ → Ty.denote C τ) : Structure L (C .ind) where
  func := fun _ f v => uncurry (C := C) (τ := indTy) (I (.func f)) v
  rel := fun _ r v => (uncurry (C := C) (τ := propTy) (I (.rel r)) v).down

theorem constants_correspond (C : BaseTy → Type (max 1 w))
    (I : {τ : Ty BaseTy} → Const L τ → Ty.denote C τ) :
    ∀ {τ : Ty BaseTy} (c : Const L τ),
      StandardTransport.liftEquiv (baseEquiv C) τ
          ((standardModel (structureOf C I)).constDen c) = I c
  | _, .func f => (liftEquiv_curryVec C _).trans (curry_uncurry (I (.func f)))
  | _, .rel r => (liftEquiv_curryVec C _).trans (curry_uncurry (I (.rel r)))

/-- Satisfaction reads the denotation at any valuation of the empty context. -/
theorem models_iff_denote {Base : Type*} {K : Ty Base → Type*} (M : HenkinModel Base K)
    (φ : ClosedFormula K) (ρ : HenkinModel.Valuation M []) :
    M.models φ ↔ (M.denote φ ρ).down := by
  show (PreModel.denote M.toPreModel φ (fun v => nomatch v)).down ↔ _
  have hρ : (fun {τ} (v : Var [] τ) => (nomatch v : Ty.denote M.Carrier τ)) =
      (fun {τ} (v : Var [] τ) => ρ v) := by
    funext τ v
    cases v
  rw [hρ]

/-- A standard model and the first-order structure it determines satisfy the
same sentences. -/
theorem models_iff_evalb (C : BaseTy → Type (max 1 w))
    (I : {τ : Ty BaseTy} → Const L τ → Ty.denote C τ) (φ : LO.FirstOrder.Sentence L) :
    (HenkinModel.standard C I).models (embedSentence φ) ↔
      Semiformula.Evalb (structureOf C I) ![] φ := by
  rw [StandardTransport.models_transport (standardModel (structureOf C I))
    (HenkinModel.standard C I) (HenkinModel.fullDomains_standard _ _)
    (HenkinModel.fullDomains_standard _ _) (baseEquiv C) (constants_correspond C I)]
  exact (models_iff_denote _ _ _).trans (denote_embedSentence_iff (structureOf C I) φ)

/-! ## Faithfulness -/

theorem models_indInhabited_iff (C : BaseTy → Type (max 1 w))
    (I : {τ : Ty BaseTy} → Const L τ → Ty.denote C τ) :
    (HenkinModel.standard C I).models (indInhabited (L := L)) ↔ Nonempty (C .ind) := by
  constructor
  · rintro ⟨d, _, _⟩
    exact ⟨d⟩
  · rintro ⟨d⟩
    exact ⟨d, trivial, trivial⟩

/-- **Farmer's Theorem 2, first-order case.**  First-order consequence is
consequence over standard models of the translated theory. -/
theorem faithful (T : Theory L) (A : LO.FirstOrder.Sentence L) :
    T ⊨[Struc.{max 1 w, u} L] A ↔
      StandardConsequence.{u, max 1 w} (translateTheory T) (embedSentence A) := by
  rw [consequence_iff]
  constructor
  · intro h C I hT
    have hne : Nonempty (C .ind) :=
      (models_indInhabited_iff C I).mp (hT _ (Set.mem_insert _ _))
    let _ : Structure L (C .ind) := structureOf C I
    have hT' : C .ind ⊧ₘ* T := modelsTheory_iff.mpr fun {ψ} hψ =>
      (models_iff_evalb C I ψ).mp (hT _ (Set.mem_insert_of_mem _ ⟨ψ, hψ, rfl⟩))
    exact (models_iff_evalb C I A).mpr (h (C .ind) hT')
  · intro h M hM s hT
    have hmodels := h (BaseCarrier M) (standardModel s).constDen fun φ hφ => by
      rcases hφ with rfl | ⟨ψ, hψ, rfl⟩
      · obtain ⟨m⟩ := hM
        exact ⟨ULift.up m, trivial, trivial⟩
      · exact (models_iff_denote _ _ _).mpr
          ((denote_embedSentence_iff s ψ).mpr (modelsTheory_iff.mp hT hψ))
    exact (denote_embedSentence_iff s A).mp ((models_iff_denote _ _ _).mp hmodels)

/-! ## Controls -/

/-- Positive control: an axiom is a consequence of its theory, on both sides. -/
theorem axiom_standardConsequence {T : Theory L} {A : LO.FirstOrder.Sentence L} (hA : A ∈ T) :
    StandardConsequence.{u, max 1 w} (translateTheory T) (embedSentence A) :=
  (faithful T A).mp ((consequence_iff).mpr fun _ _ _ hT => modelsTheory_iff.mp hT hA)

/-- The empty individual carrier. -/
def emptyCarrier : BaseTy → Type (max 1 w)
  | .ind => PEmpty

/-- Function symbols of positive arity on the empty carrier: the first
argument, which never exists. -/
def emptyFunc [IsEmpty (L.Func 0)] : {k : ℕ} → L.Func k →
    Ty.denote emptyCarrier.{w} (iterArrow k indTy indTy)
  | 0, f => (IsEmpty.false f).elim
  | _ + 1, _ => curry (C := emptyCarrier.{w}) (τ := indTy) fun v => v 0

/-- The standard model with an empty individual carrier, for a language
without constant symbols. -/
def emptyInterp [IsEmpty (L.Func 0)] :
    {τ : Ty BaseTy} → Const L τ → Ty.denote emptyCarrier.{w} τ
  | _, .func f => emptyFunc f
  | _, .rel _ => curry (C := emptyCarrier.{w}) (τ := propTy) fun _ => ULift.up False

/-- **Negative control: the inhabitation sentence is needed.**  For a language
without constant symbols, the sentence `∃ x. ⊤` holds in every first-order
structure, but its translation fails in the standard model with an empty
individual carrier, which models every translated axiom of the empty
theory. -/
theorem inhabitation_needed [IsEmpty (L.Func 0)] :
    (∅ : Theory L) ⊨[Struc.{max 1 w, u} L] (∃' ⊤ : LO.FirstOrder.Sentence L) ∧
      (∀ φ ∈ (embedSentence '' (∅ : Theory L)),
          (HenkinModel.standard emptyCarrier.{w} emptyInterp).models φ) ∧
        ¬ (HenkinModel.standard emptyCarrier.{w} emptyInterp).models
          (embedSentence (∃' ⊤ : LO.FirstOrder.Sentence L)) := by
  refine ⟨(consequence_iff).mpr fun M hM _ _ => ?_, ?_, ?_⟩
  · obtain ⟨m⟩ := hM
    have : Nonempty M := ⟨m⟩
    exact (models_iff).mpr ⟨m, trivial⟩
  · rintro φ ⟨ψ, hψ, _⟩
    exact absurd hψ (Set.notMem_empty ψ)
  · rintro ⟨d, _, _⟩
    exact d.elim

end Mettapedia.Logic.HOL.SevenVirtues.FirstOrderFaithfulness
