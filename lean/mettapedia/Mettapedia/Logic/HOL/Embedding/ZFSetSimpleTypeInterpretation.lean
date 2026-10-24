import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation

/-!
# Structural HOL interpretation in material simple-type codes

Base sorts are supplied as actual sets. Arrows are total functional graphs,
lambda constructs a graph, application reads it, and quantification ranges
over actual members of the type code. The interpreter is independent of a
Henkin decoding. A separate induction proves agreement when the base carriers
and constants have the stated value comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.HOL.Embedding.ZFSetSimpleTypeInterpretation

open ZFSetHOLTypeInterpretation ZFSetDependentProducts

universe u v
variable {Base : Type} {Const : Ty Base → Type v}

abbrev Value (bases : Base → ZFSet.{u + 1}) (type : Ty Base) := Elements (simpleTypeCode bases type)
abbrev Valuation (bases : Base → ZFSet.{u + 1}) (Γ : Ctx Base) := ∀ {type}, Var Γ type → Value bases type

def extend (bases : Base → ZFSet.{u + 1}) {Γ : Ctx Base} {type : Ty Base}
    (valuation : Valuation bases Γ) (value : Value bases type) : Valuation bases (type :: Γ)
  | _, .vz => value
  | _, .vs index => valuation index

def lam (bases : Base → ZFSet.{u + 1}) {A B : Ty Base}
    (body : Value bases A → Value bases B) : Value bases (.arr A B) :=
  encodeFunction (a := simpleTypeCode bases A) (b := fun _ => simpleTypeCode bases B) body

def app (bases : Base → ZFSet.{u + 1}) {A B : Ty Base}
    (function : Value bases (.arr A B)) (argument : Value bases A) : Value bases B :=
  graphValue (a := simpleTypeCode bases A) (b := fun _ => simpleTypeCode bases B) function argument

/-- The original typed term syntax is traversed directly. -/
def interpret (bases : Base → ZFSet.{u + 1})
    (constants : {type : Ty Base} → Const type → Value bases type) :
    {Γ : Ctx Base} → {type : Ty Base} → Term Const Γ type → Valuation bases Γ → Value bases type
  | _, _, .var index, valuation => valuation index
  | _, _, .const symbol, _ => constants symbol
  | _, _, .app function argument, valuation => app bases
      (interpret bases constants function valuation) (interpret bases constants argument valuation)
  | _, _, .lam body, valuation => lam bases (fun value => interpret bases constants body (extend bases valuation value))
  | _, _, .top, _ => truth True
  | _, _, .bot, _ => truth False
  | _, _, .and left right, valuation => truth
      (holds (interpret bases constants left valuation) ∧ holds (interpret bases constants right valuation))
  | _, _, .or left right, valuation => truth
      (holds (interpret bases constants left valuation) ∨ holds (interpret bases constants right valuation))
  | _, _, .imp left right, valuation => truth
      (holds (interpret bases constants left valuation) → holds (interpret bases constants right valuation))
  | _, _, .not body, valuation => truth (¬ holds (interpret bases constants body valuation))
  | _, _, .eq left right, valuation => truth
      (interpret bases constants left valuation = interpret bases constants right valuation)
  | _, _, .all body, valuation => truth
      (∀ value, holds (interpret bases constants body (extend bases valuation value)))
  | _, _, .ex body, valuation => truth
      (∃ value, holds (interpret bases constants body (extend bases valuation value)))

variable (bases : Base → ZFSet.{u + 1}) {Carrier : Base → Type (u + 1)}
  (baseComparison : ∀ base, Elements (bases base) ≃ Carrier base)

abbrev Decode (type : Ty Base) := simpleTypeEquiv bases baseComparison type

def decodeValuation {Γ : Ctx Base} (valuation : Valuation bases Γ) :
    ∀ {type}, Var Γ type → Ty.denote.{0, u + 1} Carrier type :=
  fun {_} index => Decode bases baseComparison _ (valuation index)

def encodeValuation {Γ : Ctx Base}
    (valuation : ∀ {type}, Var Γ type → Ty.denote.{0, u + 1} Carrier type) : Valuation bases Γ :=
  fun {_} index => (Decode bases baseComparison _).symm (valuation index)

theorem decode_encode_valuation {Γ : Ctx Base}
    (valuation : ∀ {type}, Var Γ type → Ty.denote.{0, u + 1} Carrier type) :
    (decodeValuation bases baseComparison (encodeValuation bases baseComparison valuation) :
      ∀ {type}, Var Γ type → Ty.denote.{0, u + 1} Carrier type) =
      (valuation : ∀ {type}, Var Γ type → Ty.denote.{0, u + 1} Carrier type) := by
  funext type index
  exact (Decode bases baseComparison type).apply_symm_apply _

theorem encode_decode_valuation {Γ : Ctx Base} (valuation : Valuation bases Γ) :
    (encodeValuation bases baseComparison (decodeValuation bases baseComparison valuation) :
      Valuation bases Γ) = (valuation : Valuation bases Γ) := by
  funext type index
  exact (Decode bases baseComparison type).symm_apply_apply _

theorem decode_extend (denotation : {type : Ty Base} → Const type → Ty.denote.{0, u + 1} Carrier type)
    {Γ : Ctx Base} {type : Ty Base} (valuation : Valuation bases Γ) (value : Value bases type) :
    (decodeValuation bases baseComparison (extend bases valuation value) :
      (HenkinModel.standard Carrier denotation).Valuation (type :: Γ)) =
      ((HenkinModel.standard Carrier denotation).extend
        (decodeValuation bases baseComparison valuation) (Decode bases baseComparison type value) :
        (HenkinModel.standard Carrier denotation).Valuation (type :: Γ)) := by
  funext type index
  cases index <;> rfl

theorem decode_truth (proposition : Prop) :
    Decode bases baseComparison .prop (truth.{u + 1} proposition) = ULift.up proposition :=
  truthEquiv_truth proposition

private theorem standard_eqv_of_eq
    (denotation : {type : Ty Base} → Const type → Ty.denote.{0, u + 1} Carrier type)
    {type : Ty Base} {left right : Ty.denote.{0, u + 1} Carrier type} (same : left = right) :
    (HenkinModel.standard Carrier denotation).Eqv type left right := by
  subst right
  exact (HenkinModel.standard Carrier denotation).eqv_refl trivial

/-- Every constructor, including equality and higher-order quantifiers,
agrees with the independently specified full Henkin interpretation. -/
theorem decode_interpret
    (denotation : {type : Ty Base} → Const type → Ty.denote.{0, u + 1} Carrier type)
    (constants : {type : Ty Base} → Const type → Value bases type)
    (constantLaw : ∀ {type} (symbol : Const type), Decode bases baseComparison type (constants symbol) = denotation symbol)
    {Γ : Ctx Base} {type : Ty Base} (term : Term Const Γ type) (valuation : Valuation bases Γ) :
    Decode bases baseComparison type (interpret bases constants term valuation) =
      (HenkinModel.standard Carrier denotation).denote term (decodeValuation bases baseComparison valuation) := by
  induction term with
  | var => rfl
  | const symbol => exact constantLaw symbol
  | app function argument ihf iha =>
      rw [interpret, app, simpleTypeEquiv_app, ihf, iha]
      rfl
  | lam body ih =>
      rw [interpret, lam, simpleTypeEquiv_lam]
      funext value
      rw [ih, decode_extend, Equiv.apply_symm_apply]
      rfl
  | top => exact decode_truth bases baseComparison True
  | bot => exact decode_truth bases baseComparison False
  | and left right ihl ihr =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change ((Decode bases baseComparison .prop (interpret bases constants left valuation)).down ∧
        (Decode bases baseComparison .prop (interpret bases constants right valuation)).down) = _
      rw [ihl, ihr]
      rfl
  | or left right ihl ihr =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change ((Decode bases baseComparison .prop (interpret bases constants left valuation)).down ∨
        (Decode bases baseComparison .prop (interpret bases constants right valuation)).down) = _
      rw [ihl, ihr]
      rfl
  | imp left right ihl ihr =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change ((Decode bases baseComparison .prop (interpret bases constants left valuation)).down →
        (Decode bases baseComparison .prop (interpret bases constants right valuation)).down) = _
      rw [ihl, ihr]
      rfl
  | not body ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      change (¬ (Decode bases baseComparison .prop (interpret bases constants body valuation)).down) = _
      rw [ih]
      rfl
  | eq left right ihl ihr =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change interpret bases constants left valuation = interpret bases constants right valuation ↔
        (HenkinModel.standard Carrier denotation).Eqv _ _ _
      constructor
      · intro same
        have values := congrArg (Decode bases baseComparison _) same
        rw [ihl, ihr] at values
        exact standard_eqv_of_eq denotation values
      · intro same
        apply (Decode bases baseComparison _).injective
        rw [ihl, ihr]
        exact (HenkinModel.standard Carrier denotation).eq_of_eqv_of_fullDomains
          (HenkinModel.fullDomains_standard Carrier denotation) same
  | @all A Γ body ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change (∀ value, (Decode bases baseComparison .prop
        (interpret bases constants body (extend bases valuation value))).down) ↔ ∀ value, True → _
      simp only [ih, decode_extend bases baseComparison denotation]
      constructor
      · intro holds value _
        have witness := holds ((Decode bases baseComparison A).symm value)
        exact Eq.mp (congrArg (fun compared : Ty.denote.{0, u + 1} Carrier A =>
          ((HenkinModel.standard Carrier denotation).denote body
            ((HenkinModel.standard Carrier denotation).extend
              (decodeValuation bases baseComparison valuation) compared)).down)
          ((Decode bases baseComparison A).apply_symm_apply value)) witness
      · intro holds value
        exact holds (Decode bases baseComparison A value) trivial
  | @ex A Γ body ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change (∃ value, (Decode bases baseComparison .prop
        (interpret bases constants body (extend bases valuation value))).down) ↔ ∃ value, True ∧ _
      simp only [ih, decode_extend bases baseComparison denotation]
      constructor
      · rintro ⟨value, witness⟩
        exact ⟨Decode bases baseComparison A value, trivial, witness⟩
      · rintro ⟨value, _, witness⟩
        refine ⟨(Decode bases baseComparison A).symm value, ?_⟩
        exact Eq.mpr (congrArg (fun compared : Ty.denote.{0, u + 1} Carrier A =>
          ((HenkinModel.standard Carrier denotation).denote body
            ((HenkinModel.standard Carrier denotation).extend
              (decodeValuation bases baseComparison valuation) compared)).down)
          ((Decode bases baseComparison A).apply_symm_apply value)) witness


/-! ## Contextual coherence of the same material values -/

def substValuation (constants : {type : Ty Base} → Const type → Value bases type)
    {Γ Δ : Ctx Base} (substitution : Subst Const Γ Δ) (valuation : Valuation bases Δ) : Valuation bases Γ :=
  fun {_} index => interpret bases constants (substitution index) valuation

theorem decode_substValuation
    (denotation : {type : Ty Base} → Const type → Ty.denote.{0, u + 1} Carrier type)
    (constants : {type : Ty Base} → Const type → Value bases type)
    (constantLaw : ∀ {type} (symbol : Const type), Decode bases baseComparison type (constants symbol) = denotation symbol)
    {Γ Δ : Ctx Base} (substitution : Subst Const Γ Δ) (valuation : Valuation bases Δ) :
    (decodeValuation bases baseComparison (substValuation bases constants substitution valuation) :
      (HenkinModel.standard Carrier denotation).Valuation Γ) =
      (Soundness.substVal (HenkinModel.standard Carrier denotation) substitution
        (decodeValuation bases baseComparison valuation) :
        (HenkinModel.standard Carrier denotation).Valuation Γ) := by
  funext type index
  exact decode_interpret bases baseComparison denotation constants constantLaw (substitution index) valuation

theorem interpret_substitution
    (denotation : {type : Ty Base} → Const type → Ty.denote.{0, u + 1} Carrier type)
    (constants : {type : Ty Base} → Const type → Value bases type)
    (constantLaw : ∀ {type} (symbol : Const type), Decode bases baseComparison type (constants symbol) = denotation symbol)
    {Γ Δ : Ctx Base} {type : Ty Base} (term : Term Const Γ type)
    (substitution : Subst Const Γ Δ) (valuation : Valuation bases Δ) :
    interpret bases constants (HOL.subst substitution term) valuation =
      interpret bases constants term (substValuation bases constants substitution valuation) := by
  apply (Decode bases baseComparison type).injective
  exact (decode_interpret bases baseComparison denotation constants constantLaw (HOL.subst substitution term) valuation).trans
    ((Soundness.denote_subst (HenkinModel.standard Carrier denotation) substitution term
      (decodeValuation bases baseComparison valuation)).trans
      ((congrArg (fun environment : (HenkinModel.standard Carrier denotation).Valuation Γ =>
        (HenkinModel.standard Carrier denotation).denote term environment)
        (decode_substValuation bases baseComparison denotation constants constantLaw substitution valuation).symm).trans
        (decode_interpret bases baseComparison denotation constants constantLaw term
          (substValuation bases constants substitution valuation)).symm))

theorem interpret_rename
    (denotation : {type : Ty Base} → Const type → Ty.denote.{0, u + 1} Carrier type)
    (constants : {type : Ty Base} → Const type → Value bases type)
    (constantLaw : ∀ {type} (symbol : Const type), Decode bases baseComparison type (constants symbol) = denotation symbol)
    {Γ Δ : Ctx Base} {type : Ty Base} (term : Term Const Γ type)
    (rho : Rename Base Γ Δ) (valuation : Valuation bases Δ) :
    interpret bases constants (HOL.rename rho term) valuation =
      interpret bases constants term (fun {_} index => valuation (rho index)) := by
  apply (Decode bases baseComparison type).injective
  rw [decode_interpret bases baseComparison denotation constants constantLaw,
    decode_interpret bases baseComparison denotation constants constantLaw]
  exact Soundness.denote_rename (HenkinModel.standard Carrier denotation) rho term _

end Mettapedia.Logic.HOL.Embedding.ZFSetSimpleTypeInterpretation
