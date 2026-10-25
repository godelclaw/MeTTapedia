import Mettapedia.Languages.Megalodon.HenkinEqualityInterpretation
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# Full HOL term encoding using Megalodon's binary-relation equality

Primitive equality is expanded to the actual preamble definition
`forall Q, Q x y -> Q y x`. The other derived connectives use the maintained
impredicative expansion. Every HOL term constructor is translated, including
higher-order binders, HenkinEqualityInterpretation.equality, disjunction and existential quantification.

The encoding commutes with variable renaming and simultaneous substitution.
Actual values agree in full-domain Henkin models. Native inference additionally
checks the formed binder annotations at the selected type-variable depth.
This term translation does not supply the full forward proof compiler.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Megalodon.HOLTermEncoding
open Mettapedia.Logic.HOL
open HenkinEqualityInterpretation ImpredicativeConnectives
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : Ctx Base} {τ : Ty Base}

theorem equality_rename (ρ : Rename Base Γ Δ) (type : Ty Base) :
    rename (Const := Const) ρ (equality type) = equality type := by
  simp only [HenkinEqualityInterpretation.equality, rename, Rename.lift]

theorem equality_subst (θ : Subst Const Γ Δ) (type : Ty Base) :
    subst θ (equality type) = equality type := by
  simp only [HenkinEqualityInterpretation.equality, subst, Subst.lift, rename, Rename.weaken]

theorem equalityFormula_rename (ρ : Rename Base Γ Δ) (left right : Term Const Γ τ) :
    rename ρ (equalityFormula left right) = equalityFormula (rename ρ left) (rename ρ right) := by
  simp only [equalityFormula, rename, equality_rename]

theorem equalityFormula_subst (θ : Subst Const Γ Δ) (left right : Term Const Γ τ) :
    subst θ (equalityFormula left right) = equalityFormula (subst θ left) (subst θ right) := by
  simp only [equalityFormula, subst, equality_subst]

/-- The equality expansion uses the native binary definition, not the
unary-predicate Leibniz presentation of another calculus. -/
def expandEquality : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ
  | _, _, .var index => .var index
  | _, _, .const symbol => .const symbol
  | _, _, .app function argument => .app (expandEquality function) (expandEquality argument)
  | _, _, .lam body => .lam (expandEquality body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and left right => .and (expandEquality left) (expandEquality right)
  | _, _, .or left right => .or (expandEquality left) (expandEquality right)
  | _, _, .imp left right => .imp (expandEquality left) (expandEquality right)
  | _, _, .not body => .not (expandEquality body)
  | _, _, .eq left right => equalityFormula (expandEquality left) (expandEquality right)
  | _, _, .all body => .all (expandEquality body)
  | _, _, .ex body => .ex (expandEquality body)

theorem expandEquality_rename (ρ : Rename Base Γ Δ) (term : Term Const Γ τ) :
    expandEquality (rename ρ term) = rename ρ (expandEquality term) := by
  induction term generalizing Δ <;>
    simp_all only [rename, expandEquality, equalityFormula_rename]

private theorem expandEquality_lift (θ : Subst Const Γ Δ) (type : Ty Base) :
    (fun {τ} (index : Var (type :: Γ) τ) => expandEquality (Subst.lift θ index)) =
      (Subst.lift (fun index => expandEquality (θ index)) : Subst Const (type :: Γ) (type :: Δ)) := by
  funext τ index
  cases index with
  | vz => rfl
  | vs index => exact expandEquality_rename _ _

theorem expandEquality_subst (θ : Subst Const Γ Δ) (term : Term Const Γ τ) :
    expandEquality (subst θ term) = subst (fun index => expandEquality (θ index)) (expandEquality term) := by
  induction term generalizing Δ <;>
    simp_all only [subst, expandEquality, equalityFormula_subst, expandEquality_lift]

/-- Remove primitive equality and all derived connectives in that order. -/
def encode (term : Term Const Γ τ) : Term Const Γ τ := expandInline (expandEquality term)

theorem encode_rename (ρ : Rename Base Γ Δ) (term : Term Const Γ τ) :
    encode (rename ρ term) = rename ρ (encode term) := by
  rw [encode, expandEquality_rename, expandInline_rename]
  rfl

theorem encode_subst (θ : Subst Const Γ Δ) (term : Term Const Γ τ) :
    encode (subst θ term) = subst (fun index => encode (θ index)) (encode term) := by
  rw [encode, expandEquality_subst, expandInline_subst]
  rfl

/-- A syntactic condition on terms, independent of semantic equality. -/
def EqualityFree : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Prop
  | _, _, .var _ | _, _, .const _ | _, _, .top | _, _, .bot => True
  | _, _, .app left right | _, _, .and left right | _, _, .or left right
  | _, _, .imp left right => EqualityFree left ∧ EqualityFree right
  | _, _, .lam body | _, _, .not body | _, _, .all body | _, _, .ex body => EqualityFree body
  | _, _, .eq _ _ => False

theorem equalityFree_rename (ρ : Rename Base Γ Δ) (term : Term Const Γ τ) :
    EqualityFree (rename ρ term) ↔ EqualityFree term := by
  induction term generalizing Δ <;> simp_all only [rename, EqualityFree]

theorem expandEquality_equalityFree (term : Term Const Γ τ) : EqualityFree (expandEquality term) := by
  induction term <;> simp_all [expandEquality, equalityFormula, HenkinEqualityInterpretation.equality, EqualityFree]

theorem expandInline_equalityFree (term : Term Const Γ τ) (free : EqualityFree term) :
    EqualityFree (expandInline term) := by
  induction term <;>
    simp_all [expandInline, EqualityFree, truth, falsity, conjunctionFormula,
      disjunctionFormula, existentialInline, weaken, equalityFree_rename]

theorem encode_equalityFree (term : Term Const Γ τ) : EqualityFree (encode term) :=
  expandInline_equalityFree _ (expandEquality_equalityFree term)

theorem encode_core (term : Term Const Γ τ) : IsCore (encode term) := isCore_expandInline _

/-- With full domains the comparison preserves actual function values, not
only equality restricted to admitted arguments. -/
theorem denote_expandEquality (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (term : Term Const Γ τ) (valuation : model.Valuation Γ) :
    model.denote (expandEquality term) valuation = model.denote term valuation := by
  induction term with
  | eq left right ihl ihr =>
      dsimp only [expandEquality]
      apply ULift.ext
      apply propext
      rw [denote_equalityFormula]
      rw [ihl, ihr]
      exact relationEquality_iff_eqv model (model.functionsRespectEqv_of_fullDomains full)
        (full _ _) (full _ _)
  | var | const | top | bot => rfl
  | app function argument ihf iha => simp only [expandEquality, HenkinModel.denote, PreModel.denote, ihf, iha]
  | lam body ih => funext value; exact ih _
  | and left right ihl ihr | or left right ihl ihr | imp left right ihl ihr =>
      simp only [expandEquality, HenkinModel.denote, PreModel.denote, ihl, ihr]; rfl
  | not body ih => simp only [expandEquality, HenkinModel.denote, PreModel.denote, ih]; rfl
  | all body ih | ex body ih => simp only [expandEquality, HenkinModel.denote, PreModel.denote, ih]; rfl

theorem denote_encode (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (term : Term Const Γ τ) (valuation : model.Valuation Γ) :
    model.denote (encode term) valuation = model.denote term valuation :=
  (denote_expandInline model (expandEquality term) valuation).trans
    (denote_expandEquality model full term valuation)

section Native
open MathdataKernel HenkinTermInterpretation
variable {environment : Environment}

/-- The target grammar has an actual native erasure for every encoded term. -/
theorem erase_core_equalityFree {Γ : Ctx HenkinTermInterpretation.Base}
    {type : Ty HenkinTermInterpretation.Base} (term : Term (Constant environment) Γ type)
    (core : IsCore term) (free : EqualityFree term) : (erase term).isSome = true := by
  induction term with
  | var => rfl
  | const symbol => cases symbol <;> rfl
  | app first second ihf ihs | imp first second ihf ihs =>
      have firstSuccess := ihf core.1 free.1
      have secondSuccess := ihs core.2 free.2
      cases hf : erase first <;> cases hs : erase second <;> simp_all [erase]
  | lam body ih | all body ih =>
      have child := ih core free
      cases hb : erase body <;> simp_all [erase]
  | eq => cases free
  | top | bot | and | or | not | ex => cases core

/-- Total executable raw syntax translation; its proof field only shows the
encoding succeeded and selects no term by classical choice. -/
def native {Γ : Ctx HenkinTermInterpretation.Base} {type : Ty HenkinTermInterpretation.Base}
    (term : Term (Constant environment) Γ type) : Tm :=
  (erase (encode term)).get (erase_core_equalityFree _ (encode_core term) (encode_equalityFree term))

theorem native_erased {Γ : Ctx HenkinTermInterpretation.Base} {type : Ty HenkinTermInterpretation.Base}
    (term : Term (Constant environment) Γ type) : erase (encode term) = some (native term) :=
  (Option.some_get _).symm

/-- Native typing is inherited from the intrinsic source once its actual
binder annotations pass at the selected depth. -/
theorem native_infers {Γ : Ctx HenkinTermInterpretation.Base} {type : Ty HenkinTermInterpretation.Base}
    (term : Term (Constant environment) Γ type) (depth : Nat)
    (formed : plainAnnotations depth (native term) = true) :
    inferTerm environment depth (Γ.map reifyType) (native term) = some (reifyType type) :=
  infer_of_erase (encode term) (native_erased term) formed

namespace Controls
abbrev NoConstants := Constant ({} : Environment)

def formula : ClosedFormula NoConstants :=
  .all (σ := .prop) (.imp (.var .vz) (.ex (σ := .prop)
    (.and (.eq (.var .vz) (.var (.vs .vz))) (.or (.var .vz) (.not (.var .vz))))))

theorem original_erasure_refused : erase formula = none := rfl

theorem encoded_infers : inferTerm {} 0 [] (native formula) = some .prop :=
  native_infers formula 0 (by decide)

theorem insufficient_type_depth :
    plainAnnotations 0 (native
      (.lam (.var .vz) : ClosedTerm NoConstants (.base (.inl 0) ⇒ .base (.inl 0)))) = false := by decide

theorem one_type_variable_suffices :
    inferTerm {} 1 [] (native
      (.lam (.var .vz) : ClosedTerm NoConstants (.base (.inl 0) ⇒ .base (.inl 0)))) =
      some (.arr (.var 0) (.var 0)) := by decide

/-- Encoding forgets whether equality was primitive or written out using the
native definition. It does not recover the source presentation. -/
theorem distinct_presentations_same_encoding :
    (.eq .top .top : ClosedFormula NoConstants) ≠ equalityFormula .top .top ∧
      native (.eq .top .top : ClosedFormula NoConstants) = native (equalityFormula .top .top : ClosedFormula NoConstants) := by
  constructor
  · intro same
    cases same
  · rfl

end Controls

end Native
end Mettapedia.Languages.Megalodon.HOLTermEncoding
