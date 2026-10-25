import Mettapedia.Logic.HOL.Embedding.ZFSetSimpleTypeInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation

/-!
# Original HOL terms interpreted by actual set operations

The interpreter traverses the original typed HOL syntax. Lambda creates a
functional graph, application reads its unique value, and quantifiers range
over the actual elements of the recursively constructed type codes. Set
constants use the lifted carrier's membership, union, powerset, separation,
replacement, and least closed-universe hull.

Structural induction proves agreement with the existing set/Henkin model.
The generic constant-commutation lemma is instantiated for both existing
signatures below; no second Henkin model or assumed adequacy instance is
introduced. The universe constant retains exactly its earlier lower-level
cofinal-inaccessible hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation

open ZFSetHOLTypeInterpretation ZFSetDependentProducts ZFSetUniverseLift
open ZFSetUniverseClosure ZFSetLiftedUniverseClosure ZFSetHenkinInterpretation
open ZFSetUniverseInterpretation

universe u v

abbrev Valuation (Γ : Ctx Unit) := ∀ {A}, Var Γ A → Value.{u} A
abbrev RawValuation (Γ : Ctx Unit) :=
  ∀ {A}, Var Γ A → Ty.denote.{0, u + 1} carrier.{u} A

noncomputable def decodeValuation {Γ : Ctx Unit} (ρ : Valuation.{u} Γ) :
    RawValuation.{u} Γ := fun {_} v => decode _ (ρ v)

noncomputable def encodeValuation {Γ : Ctx Unit} (ρ : RawValuation.{u} Γ) :
    Valuation.{u} Γ := fun {_} v => (decode _).symm (ρ v)

@[simp] theorem decode_encode_valuation {Γ : Ctx Unit} (ρ : RawValuation.{u} Γ) :
    (decodeValuation (encodeValuation ρ) : RawValuation Γ) = (ρ : RawValuation Γ) := by
  funext A v
  exact Equiv.apply_symm_apply (decode A) (ρ v)

@[simp] theorem encode_decode_valuation {Γ : Ctx Unit} (ρ : Valuation.{u} Γ) :
    (encodeValuation (decodeValuation ρ) : Valuation Γ) = (ρ : Valuation Γ) := by
  funext A v
  exact Equiv.symm_apply_apply (decode A) (ρ v)

theorem decodeValuation_injective {Γ : Ctx Unit} :
    Function.Injective (@decodeValuation.{u} Γ) := by
  intro ρ ν equal
  exact (encode_decode_valuation ρ).symm.trans
    ((congrArg (fun ξ : RawValuation Γ => (encodeValuation ξ : Valuation Γ)) equal).trans
      (encode_decode_valuation ν))

def extend {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation.{u} Γ)
    (x : Value A) : Valuation (A :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

theorem extend_simple {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation.{u} Γ) (x : Value A) :
    (ZFSetSimpleTypeInterpretation.extend (fun _ => carrierCode.{u}) ρ x : Valuation (A :: Γ)) =
      (extend ρ x : Valuation (A :: Γ)) := by
  funext B index
  cases index <;> rfl

theorem decode_extend {Const : Ty Unit → Type v}
    (denotation : {A : Ty Unit} → Const A → Ty.denote.{0, u + 1} carrier.{u} A)
    {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation.{u} Γ) (x : Value A) :
    (decodeValuation (extend ρ x) : RawValuation (A :: Γ)) =
      ((HenkinModel.standard carrier denotation).extend (decodeValuation ρ) (decode A x) :
        RawValuation (A :: Γ)) := by
  funext B v
  cases v <;> rfl

/-! ## Structural interpretation -/

noncomputable def interpret {Const : Ty Unit → Type v}
    (constants : {A : Ty Unit} → Const A → Value.{u} A) :
    {Γ : Ctx Unit} → {A : Ty Unit} → Term Const Γ A → Valuation Γ → Value A :=
  ZFSetSimpleTypeInterpretation.interpret (fun _ => carrierCode.{u}) constants

/-- The only parameterized law concerns constant denotations. Both concrete
set signatures discharge it using actual set-operation theorems below. -/
theorem decode_interpret {Const : Ty Unit → Type v}
    (denotation : {A : Ty Unit} → Const A → Ty.denote.{0, u + 1} carrier.{u} A)
    (constants : {A : Ty Unit} → Const A → Value.{u} A)
    (constant_law : ∀ {A} (c : Const A), decode A (constants c) = denotation c)
    {Γ : Ctx Unit} {A : Ty Unit} (term : Term Const Γ A) (ρ : Valuation Γ) :
    decode A (interpret constants term ρ) =
      (HenkinModel.standard carrier denotation).denote term (decodeValuation ρ) :=
  ZFSetSimpleTypeInterpretation.decode_interpret (fun _ => carrierCode.{u}) (fun _ => carrierEquiv)
    denotation constants constant_law term ρ

/-! ## Actual lifted set constants -/

noncomputable def separateValue (a : Value.{u} set) (p : Value predicate) : Value set :=
  carrierSeparation a (fun x => holds (app p (encode (lowerValue x))))

noncomputable def constants : {A : Ty Unit} → Symbol A → Value.{u} A
  | _, .member => lam (fun x => lam (fun a => truth (x.1 ∈ a.1)))
  | _, .empty => carrierEmpty
  | _, .union => lam carrierUnion
  | _, .power => lam carrierPower
  | _, .separate => lam (fun a => lam (separateValue a))
  | _, .replace => lam (fun a => lam (fun f => carrierReplacement a (app f)))

theorem decode_separateValue (a : Value.{u} set) (p : Value predicate) :
    decode set (separateValue a p) =
      ZFSet.sep (fun x => (decode predicate p x).down) (decode set a) := by
  change carrierEquiv (carrierSeparation a _) = _
  rw [decode_separation]
  congr 1
  funext x
  rw [lowerValue_lift]
  change (decode .prop (app p (encode x))).down = _
  rw [decode_app]
  change (decode predicate p (carrierEquiv (encode x))).down = _
  rw [decode_encode]

theorem decode_constants {A : Ty Unit} (c : Symbol A) :
    decode A (constants.{u} c) = denoteSymbol c := by
  cases c with
  | member =>
      rw [constants, decode_lam]
      funext x
      rw [decode_lam]
      funext a
      rw [decode_truth]
      apply ULift.ext
      apply propext
      exact (membership_decode ((decode set).symm x) ((decode set).symm a)).trans
        (iff_of_eq (congrArg₂ (fun x a : ZFSet.{u} => x ∈ a)
          (Equiv.apply_symm_apply carrierEquiv x)
          (Equiv.apply_symm_apply carrierEquiv a)))
  | empty => exact decode_empty
  | union =>
      rw [constants, decode_lam]
      funext a
      exact (decode_union ((decode set).symm a)).trans
        (congrArg ZFSet.sUnion (Equiv.apply_symm_apply (decode set) a))
  | power =>
      rw [constants, decode_lam]
      funext a
      exact (decode_power ((decode set).symm a)).trans
        (congrArg ZFSet.powerset (Equiv.apply_symm_apply (decode set) a))
  | separate =>
      rw [constants, decode_lam]
      funext a
      rw [decode_lam]
      funext p
      rw [decode_separateValue, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl
  | replace =>
      rw [constants, decode_lam]
      funext a
      rw [decode_lam]
      funext f
      change carrierEquiv (carrierReplacement _ _) = _
      rw [decode_replacement]
      change replacement (decode set ((decode set).symm a)) _ = _
      rw [Equiv.apply_symm_apply]
      congr 1
      funext x
      change decode set (app ((decode mapping).symm f) (encode x)) = _
      rw [decode_app, Equiv.apply_symm_apply]
      change f (carrierEquiv (encode x)) = _
      rw [decode_encode]

theorem core_term_agreement {Γ : Ctx Unit} {A : Ty Unit}
    (term : Expr Γ A) (ρ : Valuation.{u} Γ) :
    decode A (interpret constants term ρ) = model.denote term (decodeValuation ρ) :=
  decode_interpret denoteSymbol constants decode_constants term ρ

noncomputable def universeConstants (h : CofinalInaccessibles.{u}) :
    {A : Ty Unit} → UniverseSymbol A → Value.{u} A
  | _, .core c => constants c
  | _, .universe => lam (carrierUniverse h)

theorem decode_universeConstants (h : CofinalInaccessibles.{u})
    {A : Ty Unit} (c : UniverseSymbol A) :
    decode A (universeConstants h c) = constant h c := by
  cases c with
  | core c => exact decode_constants c
  | «universe» =>
      rw [universeConstants, decode_lam]
      funext a
      exact (decode_universe h ((decode set).symm a)).trans
        (congrArg (univOf h) (Equiv.apply_symm_apply (decode set) a))

theorem universe_term_agreement (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (term : UniverseExpr Γ A) (ρ : Valuation Γ) :
    decode A (interpret (universeConstants h) term ρ) =
      (universeModel h).denote term (decodeValuation ρ) :=
  decode_interpret (constant h) (universeConstants h) (decode_universeConstants h) term ρ

/-! ## Simultaneous substitutions on the same coded contexts -/

noncomputable def substValuation {Const : Ty Unit → Type v}
    (symbols : {A : Ty Unit} → Const A → Value.{u} A)
    {Γ Δ : Ctx Unit} (θ : Subst Const Γ Δ) (ρ : Valuation Δ) : Valuation Γ :=
  fun {_} boundVar => interpret symbols (θ boundVar) ρ

theorem decode_substValuation {Const : Ty Unit → Type v}
    (denotation : {A : Ty Unit} → Const A → Ty.denote.{0, u + 1} carrier.{u} A)
    (symbols : {A : Ty Unit} → Const A → Value.{u} A)
    (constant_law : ∀ {A} (c : Const A), decode A (symbols c) = denotation c)
    {Γ Δ : Ctx Unit} (θ : Subst Const Γ Δ) (ρ : Valuation Δ) :
    (decodeValuation (substValuation symbols θ ρ) : RawValuation Γ) =
      (Soundness.substVal (HenkinModel.standard carrier denotation) θ (decodeValuation ρ) :
        RawValuation Γ) := by
  funext A boundVar
  exact decode_interpret denotation symbols constant_law (θ boundVar) ρ

theorem interpret_substitution {Const : Ty Unit → Type v}
    (denotation : {A : Ty Unit} → Const A → Ty.denote.{0, u + 1} carrier.{u} A)
    (symbols : {A : Ty Unit} → Const A → Value.{u} A)
    (constant_law : ∀ {A} (c : Const A), decode A (symbols c) = denotation c)
    {Γ Δ : Ctx Unit} {A : Ty Unit} (term : Term Const Γ A)
    (θ : Subst Const Γ Δ) (ρ : Valuation Δ) :
    interpret symbols (HOL.subst θ term) ρ =
      interpret symbols term (substValuation symbols θ ρ) := by
  apply (decode A).injective
  exact (decode_interpret denotation symbols constant_law (HOL.subst θ term) ρ).trans
    ((Soundness.denote_subst (HenkinModel.standard carrier denotation) θ term
      (decodeValuation ρ)).trans
      ((congrArg (fun ν : RawValuation Γ =>
        (HenkinModel.standard carrier denotation).denote term ν)
        (decode_substValuation denotation symbols constant_law θ ρ).symm).trans
        (decode_interpret denotation symbols constant_law term
          (substValuation symbols θ ρ)).symm))

theorem core_substitution {Γ Δ : Ctx Unit} {A : Ty Unit}
    (term : Expr Γ A) (θ : Subst Symbol Γ Δ) (ρ : Valuation.{u} Δ) :
    interpret constants (HOL.subst θ term) ρ =
      interpret constants term (substValuation constants θ ρ) :=
  interpret_substitution denoteSymbol constants decode_constants term θ ρ

theorem universe_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit}
    (term : UniverseExpr Γ A) (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) :
    interpret (universeConstants h) (HOL.subst θ term) ρ =
      interpret (universeConstants h) term (substValuation (universeConstants h) θ ρ) :=
  interpret_substitution (constant h) (universeConstants h) (decode_universeConstants h) term θ ρ

theorem universe_substValuation_lift (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (θ : Subst UniverseSymbol Γ Δ)
    (ρ : Valuation Δ) (x : Value A) :
    (substValuation (universeConstants h) (Subst.lift θ) (extend ρ x) : Valuation (A :: Γ)) =
      (extend (substValuation (universeConstants h) θ ρ) x : Valuation (A :: Γ)) := by
  apply decodeValuation_injective
  have first := decode_substValuation (constant h) (universeConstants h)
    (decode_universeConstants h) (Subst.lift θ) (extend ρ x)
  have second := congrArg (fun ν : RawValuation (A :: Δ) =>
    (Soundness.substVal (universeModel h) (Subst.lift θ) ν : RawValuation (A :: Γ)))
    (decode_extend (constant h) ρ x)
  have third := Soundness.substVal_lift (universeModel h) θ (decodeValuation ρ) (decode A x)
  have fourth := congrArg (fun ν : RawValuation Γ =>
    ((universeModel h).extend ν (decode A x) : RawValuation (A :: Γ)))
    (decode_substValuation (constant h) (universeConstants h) (decode_universeConstants h) θ ρ).symm
  exact first.trans (second.trans (third.trans (fourth.trans
    (decode_extend (constant h) (substValuation (universeConstants h) θ ρ) x).symm)))

/-! ## Higher-order and changed-program controls -/

def emptyValuation : Valuation.{u} [] := fun {_} boundVar => nomatch boundVar

def applicationEta : ClosedFormula Symbol :=
  .all (.eq (.lam (.app (.var (.vs .vz)) (.var .vz)))
    (.var .vz : Expr [mapping] mapping))

theorem coded_function_eta : holds (interpret constants.{u} applicationEta emptyValuation) := by
  simp only [applicationEta, interpret, ZFSetSimpleTypeInterpretation.interpret,
    ZFSetSimpleTypeInterpretation.extend, holds_truth]
  exact lam_eta

def allFunctionsIdentity : ClosedFormula Symbol :=
  .all (.all (.eq (.app (.var (.vs .vz) : Expr [set, mapping] mapping) (.var .vz)) (.var .vz)))

theorem not_all_functions_identity :
    ¬ holds (interpret constants.{u} allFunctionsIdentity emptyValuation) := by
  intro claim
  simp only [allFunctionsIdentity, interpret, ZFSetSimpleTypeInterpretation.interpret,
    ZFSetSimpleTypeInterpretation.extend, holds_truth] at claim
  have equality := claim (lam (A := set) (B := set) (fun _ => carrierEmpty))
    (carrierPower carrierEmpty)
  change app (A := set) (B := set) (lam (A := set) (B := set) (fun _ => carrierEmpty)) (carrierPower carrierEmpty) = carrierPower carrierEmpty at equality
  rw [app_lam] at equality
  have decoded := congrArg carrierEquiv equality
  rw [decode_empty, decode_power, decode_empty] at decoded
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← decoded] at member
  exact ZFSet.mem_irrefl _ member

def applyParameter : Expr [mapping, set] set :=
  .app (.var .vz) (.var (.vs .vz))

def replaceFunction : Subst Symbol [mapping, set] [set]
  | _, .vz => .lam (.const .empty)
  | _, .vs .vz => .var .vz

theorem function_parameter_substitution (a : ZFSet.{u}) :
    interpret constants (HOL.subst replaceFunction applyParameter)
      (extend emptyValuation (encode a)) = carrierEmpty := by
  change app (A := set) (B := set) (lam (fun _ => carrierEmpty)) (encode a) = carrierEmpty
  exact app_lam (A := set) (B := set) _ _

theorem function_parameter_substitution_square (a : ZFSet.{u}) :
    interpret constants (HOL.subst replaceFunction applyParameter)
        (extend emptyValuation (encode a)) =
      interpret constants applyParameter
        (substValuation constants replaceFunction (extend (A := set) emptyValuation (encode a))) :=
  core_substitution applyParameter replaceFunction (extend (A := set) emptyValuation (encode a))

#print axioms decode_interpret
#print axioms decode_separateValue
#print axioms decode_constants
#print axioms core_term_agreement
#print axioms decode_universeConstants
#print axioms universe_term_agreement
#print axioms decode_substValuation
#print axioms interpret_substitution
#print axioms core_substitution
#print axioms universe_substitution
#print axioms universe_substValuation_lift
#print axioms coded_function_eta
#print axioms not_all_functions_identity
#print axioms function_parameter_substitution
#print axioms function_parameter_substitution_square

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation
