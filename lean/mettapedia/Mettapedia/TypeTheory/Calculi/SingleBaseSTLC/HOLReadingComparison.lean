import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLConversionBubble
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingCompile

/-!
# The simple computational image inside a dependent HOL reading

Pure simple lambda terms are always read: they need no interpreted constants
or equality-proof algebra. The existing reader supplies their native code,
and its laws type that code in the selected dependent judgment. Beta
conversion of the simple terms becomes typed equality there.

The substitution square uses the reader's actual native environment, not a
second term encoding. These are inclusion and computational preservation
results. Reflection from arbitrary dependent inhabitants, a chosen classical
axiom package, and an implementation of either checker are separate claims.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLReadingComparison

open IntrinsicSTT HOLComparison
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation.TypedEquality.Impredicative

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (ρ : HOLReading Head Base Const) (ground : Base)
variable {Γ Δ : List Ty} {A : Ty}

/-- No constant interpretation is requested by a pure lambda term. -/
theorem reads (t : Term Γ A) : (ρ.term (term ground t)).isSome := by
  induction t with
  | var _ => rfl
  | lam body ih => simpa only [term, HOLReading.term, Option.isSome_map] using ih
  | app f a ihf iha =>
      obtain ⟨f', hf⟩ := Option.isSome_iff_exists.mp ihf
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.mp iha
      change (HOLReading.both Presentation.Tm.app
        (ρ.term (term ground f)) (ρ.term (term ground a))).isSome = true
      rw [hf, ha]
      rfl

/-- Reuse the selected reading's executable code constructor. -/
def code (t : Term Γ A) : Presentation.Tm Head (context ground Γ).length :=
  (ρ.term (term ground t)).get (reads ρ ground t)

theorem code_read (t : Term Γ A) : ρ.term (term ground t) = some (code ρ ground t) :=
  (Option.some_get (reads ρ ground t)).symm

theorem code_typed (laws : ρ.Laws) (t : Term Γ A) :
    Presentation.TypedEquality.Typed ρ.rules (ρ.objCtx (context ground Γ))
      (code ρ ground t) (ρ.carrierAt (context ground Γ).length (type ground A)) :=
  laws.term_typed (code_read ρ ground t)

/-- An independently supplied native substitution is suitable exactly at the
consulted variable images. The reader then commutes with substitution. -/
theorem code_substitution (σ : Substitution Γ Δ)
    (native : Presentation.Sub Head (context ground Γ).length (context ground Δ).length)
    (compatible : ∀ {τ} (index : HOL.Var (context ground Γ) τ),
      ρ.term (substitution ground σ index) = some (native (HOLReading.varIndex index)))
    (t : Term Γ A) :
    code ρ ground (t.substitute σ) = Presentation.subst native (code ρ ground t) := by
  have square := ρ.term_subst (substitution ground σ) native compatible (term ground t)
  rw [substitute_term, code_read, code_read] at square
  exact Option.some.inj square

/-- The maintained native-substitution constructor has no unread image on
this fragment. Its fallback is never used. -/
theorem nativeSub_compatible (σ : Substitution Γ Δ) {τ}
    (index : HOL.Var (context ground Γ) τ) :
    ρ.term (substitution ground σ index) =
      some (ρ.nativeSub (substitution ground σ) (HOLReading.varIndex index)) := by
  refine forall_variables ground (Γ := Γ)
    (fun index => ρ.term (substitution ground σ index) =
      some (ρ.nativeSub (substitution ground σ) (HOLReading.varIndex index))) ?_ index
  intro B index
  rw [substitution_variable]
  rw [ρ.nativeSub_varIndex (substitution ground σ) (toVar ground index)
    (by rw [substitution_variable]; exact code_read ρ ground (σ index))]
  exact code_read ρ ground (σ index)

/-- A concrete, total substitution square for the computed native code. -/
theorem code_substitute (σ : Substitution Γ Δ) (t : Term Γ A) :
    code ρ ground (t.substitute σ) =
      Presentation.subst (ρ.nativeSub (substitution ground σ)) (code ρ ground t) :=
  code_substitution ρ ground σ _ (nativeSub_compatible ρ ground σ) t

theorem betaStep_source {left right : Term Γ A} (step : BetaStep left right) :
    HOL.SourceStep ([] : List (HOL.DefiningEquation Const))
      (term ground left) (term ground right) := by
  induction step with
  | beta body argument => rw [← instantiate_term]; exact .beta _ _
  | lam _ ih => exact .lam ih
  | appLeft _ ih => exact .appFun _ ih
  | appRight _ ih => exact .appArg _ ih

/-- The local computational kernel remains sound inside every lawful reading,
without interpreting any additional HOL constant or adopting choice. -/
theorem beta_conversion_typed (laws : ρ.Laws) {left right : Term Γ A}
    (converted : BetaConv left right) :
    Presentation.TypedEquality.Equal ρ.rules (ρ.objCtx (context ground Γ))
      (code ρ ground left) (code ρ ground right)
      (ρ.carrierAt (context ground Γ).length (type ground A)) := by
  have path : ρ.RepConversion [] (term ground left) (term ground right) := by
    induction converted with
    | rel _ _ step => exact .rel _ _ ⟨reads ρ ground _, reads ρ ground _, betaStep_source ground step⟩
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ first second => exact .trans _ _ _ first second
  exact laws.conversion_equal (fun _ member => by cases member) path
    (code_read ρ ground left) (code_read ρ ground right)

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- The executable native observation is sound for the selected dependent
judgment through the actual reader and its typed-equality theorem. -/
theorem observed_typed (laws : ρ.Laws) {left right : Term Γ A}
    (observed : (gsltOSLF (HOLConversionBubble.theory (Const := Const) ground false Γ A)).satisfies
      (S := ()) left (HOLConversionBubble.nativeType ground false right).pred) :
    Presentation.TypedEquality.Equal ρ.rules (ρ.objCtx (context ground Γ))
      (code ρ ground left) (code ρ ground right)
      (ρ.carrierAt (context ground Γ).length (type ground A)) :=
  beta_conversion_typed ρ ground laws
    ((ConversionDecision.decideConversion_correct left right).1
      ((HOLConversionBubble.beta_satisfies_iff_decides ground left right).1 observed))

#print axioms code_typed
#print axioms code_substitution
#print axioms code_substitute
#print axioms beta_conversion_typed
#print axioms observed_typed

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLReadingComparison
