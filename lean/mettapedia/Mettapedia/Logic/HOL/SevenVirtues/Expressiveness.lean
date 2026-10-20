import Mettapedia.Logic.HOL.SevenVirtues.Peano
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Virtue 3: simple type theory is highly expressive

In standard (full-domain) models one sentence of simple type theory says that
a base type is infinite, and its negation says that it is finite:

* `models_dedekindInfinite_iff`: a full-domain model satisfies
  `dedekindInfinite b` exactly when the carrier of `b` is infinite;
* `models_finite_iff`: it satisfies `finite b` exactly when that carrier is
  finite.

First-order logic cannot do this (Mathlib's compactness theorem):

* `FirstOrder.no_theory_of_finite`: no first-order theory in the empty language
  has exactly the finite types as models;
* `FirstOrder.no_sentence_of_infinite`: no single first-order sentence in the
  empty language has exactly the infinite types as models (an infinite theory
  does, `Language.infiniteTheory`);
* `FirstOrder.not_categorical`: a first-order theory with an infinite model has a
  model of strictly larger cardinality, so it is not categorical (Farmer's
  Theorem 3). By contrast Peano's axioms in simple type theory are
  categorical (`Peano.categorical`).

The sentence `dedekindInfinite` is the primitive-connective form of HOL
Light's `ONE_ONE f /\ ~ONTO f` (`HOLLightBooleanDefinitions.infinityFormula`).
In every Henkin model it still implies an infinite carrier
(`infinite_of_models_dedekindInfinite`); the converse needs full domains.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

section HOL

variable (b : Base)

/-- `∀ x y. f x = f y → x = y`, for the bound function `f`. -/
def injectiveBody : Formula Const [.base b ⇒ .base b] :=
  .all (.all (.imp
    (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (.app (.var (.vs (.vs .vz))) (.var (.vz : Var [.base b, .base b, .base b ⇒ .base b] _))))
    (.eq (.var (.vs .vz)) (.var .vz))))

/-- `∀ y. ∃ x. f x = y`, for the bound function `f`. -/
def surjectiveBody : Formula Const [.base b ⇒ .base b] :=
  .all (.ex (.eq
    (.app (.var (.vs (.vs .vz))) (.var (.vz : Var [.base b, .base b, .base b ⇒ .base b] _)))
    (.var (.vs .vz))))

/-- Dedekind infinity of the base type `b`:
`∃ f : b ⇒ b. (∀ x y. f x = f y → x = y) ∧ ¬ ∀ y. ∃ x. f x = y`. -/
def dedekindInfinite : ClosedFormula Const :=
  .ex (.and (injectiveBody b) (.not (surjectiveBody b)))

/-- Finiteness of the base type `b`, as the negation of Dedekind infinity. -/
def finite : ClosedFormula Const := .not (dedekindInfinite b)

variable (M : HenkinModel.{u, v, w} Base Const)

/-- In every Henkin model, the sentence asks for an admissible injective,
non-surjective function on the carrier of `b`. -/
theorem models_dedekindInfinite_iff_general :
    M.models (dedekindInfinite b) ↔
      ∃ f : M.Carrier b → M.Carrier b, M.adm (.base b ⇒ .base b) f ∧
        Function.Injective f ∧ ¬ Function.Surjective f := by
  constructor
  · rintro ⟨f, hf, hinj, hsurj⟩
    refine ⟨f, hf, fun x y hxy => hinj x (M.base_mem b x) y (M.base_mem b y) hxy, ?_⟩
    intro hs
    apply hsurj
    intro y _
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, M.base_mem b x, hx⟩
  · rintro ⟨f, hf, hinj, hsurj⟩
    refine ⟨f, hf, fun x _ y _ hxy => hinj hxy, ?_⟩
    intro hs
    apply hsurj
    intro y
    obtain ⟨x, _, hx⟩ := hs y (M.base_mem b y)
    exact ⟨x, hx⟩

/-- An infinite type has an injective map to itself that is not surjective. -/
theorem exists_injective_not_surjective (α : Type w) [Infinite α] :
    ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f := by
  have hCard : Cardinal.mk (Option α) = Cardinal.mk α := by
    rw [Cardinal.mk_option]
    exact Cardinal.add_one_eq (Cardinal.infinite_iff.mp inferInstance)
  obtain ⟨e⟩ := Cardinal.eq.mp hCard
  refine ⟨fun x => e (some x), fun x y h => Option.some.inj (e.injective h), ?_⟩
  rintro hsurj
  obtain ⟨x, hx⟩ := hsurj (e none)
  exact Option.some_ne_none x (e.injective hx)

/-- In every Henkin model, Dedekind infinity of `b` makes its carrier
infinite. -/
theorem infinite_of_models_dedekindInfinite (h : M.models (dedekindInfinite b)) :
    Infinite (M.Carrier b) := by
  obtain ⟨f, _, hinj, hsurj⟩ := (models_dedekindInfinite_iff_general b M).mp h
  by_contra hFin
  rw [not_infinite_iff_finite] at hFin
  exact hsurj (Finite.surjective_of_injective hinj)

/-- **Infinity in one sentence.** A full-domain model satisfies
`dedekindInfinite b` exactly when the carrier of `b` is infinite. -/
theorem models_dedekindInfinite_iff (full : M.FullDomains) :
    M.models (dedekindInfinite b) ↔ Infinite (M.Carrier b) := by
  refine ⟨infinite_of_models_dedekindInfinite b M, fun hInf => ?_⟩
  obtain ⟨f, hinj, hsurj⟩ := exists_injective_not_surjective (M.Carrier b)
  exact (models_dedekindInfinite_iff_general b M).mpr ⟨f, full (.base b ⇒ .base b) f, hinj, hsurj⟩

/-- **Finiteness in one sentence.** A full-domain model satisfies `finite b`
exactly when the carrier of `b` is finite. -/
theorem models_finite_iff (full : M.FullDomains) :
    M.models (finite b) ↔ Finite (M.Carrier b) := by
  change ¬ M.models (dedekindInfinite b) ↔ _
  rw [models_dedekindInfinite_iff b M full, not_infinite_iff_finite]

end HOL

/-! ## Positive and negative instances -/

namespace Examples

/-- No constants, one base type. -/
abbrev Pure : Ty Unit → Type := fun _ => Empty

/-- The standard model on a given carrier. -/
def standardOn (α : Type) : HenkinModel.{0, 0, 0} Unit Pure :=
  HenkinModel.standard (fun _ => ULift.{1} α) (fun {_} c => nomatch c)

theorem natural_infinite : (standardOn ℕ).models (dedekindInfinite ()) :=
  (models_dedekindInfinite_iff () (standardOn ℕ) (HenkinModel.fullDomains_standard _ _)).mpr
    (inferInstanceAs (Infinite (ULift.{1} ℕ)))

theorem bool_not_infinite : ¬ (standardOn Bool).models (dedekindInfinite ()) := by
  rw [models_dedekindInfinite_iff () (standardOn Bool) (HenkinModel.fullDomains_standard _ _)]
  intro h
  exact not_infinite_iff_finite.mpr (inferInstanceAs (Finite (ULift.{1} Bool))) h

theorem bool_finite : (standardOn Bool).models (finite ()) :=
  (models_finite_iff () (standardOn Bool) (HenkinModel.fullDomains_standard _ _)).mpr
    (inferInstanceAs (Finite (ULift.{1} Bool)))

end Examples

/-! ## First-order contrast -/

namespace FirstOrder

open _root_.FirstOrder _root_.FirstOrder.Language Cardinal

attribute [local instance] Language.emptyStructure

/-- The sentence "at least `n` elements" holds in `Fin m` exactly when `n ≤ m`. -/
theorem fin_cardGe_iff (m n : ℕ) : Fin m ⊨ Sentence.cardGe Language.empty n ↔ n ≤ m := by
  rw [Sentence.realize_cardGe, Cardinal.mk_fin, Nat.cast_le]

/-- **Finiteness is not first-order axiomatizable.** No theory in the empty
language has exactly the finite types as its models. -/
theorem no_theory_of_finite :
    ¬ ∃ T : Language.empty.Theory, ∀ (M : Type) [Language.empty.Structure M],
      M ⊨ T ↔ Finite M := by
  classical
  rintro ⟨T, hT⟩
  have hSat : (T ∪ Language.empty.infiniteTheory).IsSatisfiable := by
    rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
    intro T0 hT0
    let idx : Language.empty.Sentence → ℕ := fun φ =>
      if h : ∃ n, Sentence.cardGe Language.empty n = φ then Classical.choose h else 0
    have hBound : ∀ φ ∈ T0, ∀ n, Sentence.cardGe Language.empty n = φ → n ≤ T0.sup idx := by
      intro φ hφ n hn
      have hex : ∃ m, Sentence.cardGe Language.empty m = φ := ⟨n, hn⟩
      have hk : Sentence.cardGe Language.empty (idx φ) = φ := by
        simp only [idx, dif_pos hex]
        exact Classical.choose_spec hex
      have hReal := (fin_cardGe_iff (idx φ) (idx φ)).mpr le_rfl
      rw [hk, ← hn, fin_cardGe_iff] at hReal
      exact le_trans hReal (Finset.le_sup (f := idx) (by rw [hn]; exact hφ))
    have hInf : Fin (T0.sup idx + 1) ⊨ (T0 : Language.empty.Theory) := by
      rw [Theory.model_iff]
      intro φ hφ
      rcases hT0 hφ with hφT | ⟨n, rfl⟩
      · exact (Theory.model_iff T).mp ((hT _).mpr inferInstance) φ hφT
      · exact (fin_cardGe_iff _ n).mpr (Nat.le_succ_of_le (hBound _ hφ n rfl))
    exact Theory.Model.isSatisfiable (Fin (T0.sup idx + 1))
  obtain ⟨M⟩ := hSat
  have hUnion := (Theory.model_union_iff.mp M.is_model)
  have hFin : Finite M := (hT M).mp hUnion.1
  exact not_finite_iff_infinite.mpr ((model_infiniteTheory_iff Language.empty).mp hUnion.2) hFin

/-- **Infinity is not definable by one first-order sentence** in the empty
language. -/
theorem no_sentence_of_infinite :
    ¬ ∃ φ : Language.empty.Sentence, ∀ (M : Type) [Language.empty.Structure M],
      M ⊨ φ ↔ Infinite M := by
  rintro ⟨φ, hφ⟩
  apply no_theory_of_finite
  refine ⟨{φ.not}, fun M _ => ?_⟩
  rw [Theory.model_singleton_iff, Sentence.realize_not, hφ M, not_infinite_iff_finite]

/-- **First-order theories with infinite models are not categorical**
(Löwenheim–Skolem upward; Farmer's Theorem 3). -/
theorem not_categorical {L : Language.{u, v}} (T : L.Theory) (M : Type w) [L.Structure M]
    [M ⊨ T] [Infinite M] :
    ∃ N : Theory.ModelType.{u, v, max u v w} T, IsEmpty (M ≃ N) := by
  obtain ⟨N, hN⟩ := Theory.exists_large_model_of_infinite_model T (Order.succ (#M)) M
  refine ⟨N, ⟨fun e => ?_⟩⟩
  have hEq : Cardinal.lift.{max u v w} (#M) = #N := by
    rw [← Cardinal.lift_id (#N)]
    exact Cardinal.lift_mk_eq.{w, max u v w, max u v w}.mpr ⟨e⟩
  rw [← hEq, Cardinal.lift_le] at hN
  exact absurd hN (not_le.mpr (Order.lt_succ (#M)))

end FirstOrder

#print axioms models_dedekindInfinite_iff
#print axioms models_finite_iff
#print axioms infinite_of_models_dedekindInfinite
#print axioms Examples.natural_infinite
#print axioms Examples.bool_finite
#print axioms FirstOrder.no_theory_of_finite
#print axioms FirstOrder.no_sentence_of_infinite
#print axioms FirstOrder.not_categorical

end Mettapedia.Logic.HOL.SevenVirtues
