import Mettapedia.Languages.Megalodon.HOLTermConversion
import Mettapedia.Logic.HOL.BetaEtaNormalForms
import Mettapedia.Languages.Megalodon.ImpredicativeLogicalProofs

/-!
# Canonical native readings of encoded HOL terms

The existing monomorphic algorithm computes beta/eta normal forms of the full
HOL term encoding. Constants stay opaque in this phase. The context laws
below preserve actual typed terms and raw native codes, rather than only
their denotations. They supply the literal context and proposition shapes
needed by the native proof rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLNormalForms

open Mettapedia.Logic.HOL
open EtaConversion MathdataKernel HenkinTermInterpretation HOLTermEncoding

universe w
variable {environment : Environment} {gamma : Ctx Base} {type domain : Ty Base}

def normalForm (source : Term (Constant environment) gamma type) :
    Term (Constant environment) gamma type :=
  (NormalizationNormalForm.completedResult (encode source) (native_erased source)).normalForm

def normalFormCode (source : Term (Constant environment) gamma type) : Tm :=
  (NormalizationTermination.complete (encode source) (native_erased source)).val.2

theorem normalForm_erased (source : Term (Constant environment) gamma type) :
    erase (normalForm source) = some (normalFormCode source) :=
  NormalizationNormalForm.completed_erased (encode source) (native_erased source)

theorem normalForm_normal (source : Term (Constant environment) gamma type) :
    Mettapedia.Logic.Relation.IsNormal BetaEtaStep (normalForm source) :=
  (NormalizationNormalForm.completedResult (encode source) (native_erased source)).irreducible

theorem encoded_to_normalForm (source : Term (Constant environment) gamma type) :
    BetaEtaConv (encode source) (normalForm source) :=
  Relation.EqvGen.reflTransGen_le_eqvGen BetaEtaStep _ _
    (NormalizationNormalForm.completedResult (encode source) (native_erased source)).reduces

theorem normalForm_eq_of_normal (source : Term (Constant environment) gamma type)
    (target : Term (Constant environment) gamma type)
    (normal : Mettapedia.Logic.Relation.IsNormal BetaEtaStep target)
    (converted : BetaEtaConv (encode source) target) : normalForm source = target :=
  BetaEtaConfluence.normal_eq_of_convertible (normalForm_normal source) normal
    (.trans _ _ _ (.symm _ _ (encoded_to_normalForm source)) converted)

theorem normalForm_eq_of_conversion {left right : Term (Constant environment) gamma type}
    (converted : BetaEtaConv left right) : normalForm left = normalForm right :=
  normalForm_eq_of_normal left _ (normalForm_normal right)
    (.trans _ _ _ (HOLTermConversion.encode_conversion converted) (encoded_to_normalForm right))

theorem normalFormCode_of_normalizes (source : Term (Constant environment) gamma type)
    {fuel : Nat} {output : Tm} (accepted : Tm.normalize fuel (native source) = some output) :
    normalFormCode source = output :=
  NormalizationNormalForm.normalize_coherent (encode source) (encode source)
    (native_erased source) (native_erased source) (.refl _)
    (NormalizationTermination.complete (encode source) (native_erased source)).property accepted

theorem normalFormCode_eq_of_conversion {left right : Term (Constant environment) gamma type}
    (converted : BetaEtaConv left right) : normalFormCode left = normalFormCode right := by
  have same := congrArg erase (normalForm_eq_of_conversion converted)
  rw [normalForm_erased left, normalForm_erased right] at same
  exact Option.some.inj same

theorem normalForm_top :
    normalForm (.top : Formula (Constant environment) gamma) = ImpredicativeConnectives.truth :=
  normalForm_eq_of_normal .top _
    (BetaEtaNormalForms.all_normal (BetaEtaNormalForms.imp_normal
      (BetaEtaConfluence.variable_normal _) (BetaEtaConfluence.variable_normal _))) (.refl _)

theorem normalForm_bot :
    normalForm (.bot : Formula (Constant environment) gamma) = ImpredicativeConnectives.falsity :=
  normalForm_eq_of_normal .bot _
    (BetaEtaNormalForms.all_normal (BetaEtaConfluence.variable_normal _)) (.refl _)

theorem normalFormCode_top :
    normalFormCode (.top : Formula (Constant environment) gamma) = ImpredicativeLogicalProofs.truth := by
  apply Option.some.inj
  rw [← normalForm_erased (.top : Formula (Constant environment) gamma), normalForm_top]
  rfl

theorem normalFormCode_bot :
    normalFormCode (.bot : Formula (Constant environment) gamma) = ImpredicativeLogicalProofs.falsity := by
  apply Option.some.inj
  rw [← normalForm_erased (.bot : Formula (Constant environment) gamma), normalForm_bot]
  rfl

theorem normalForm_imp (left right : Formula (Constant environment) gamma) :
    normalForm (.imp left right) = .imp (normalForm left) (normalForm right) := by
  apply normalForm_eq_of_normal _ _
    (BetaEtaNormalForms.imp_normal (normalForm_normal left) (normalForm_normal right))
  exact BetaEtaSubstitution.imp_congr (encoded_to_normalForm left) (encoded_to_normalForm right)

theorem normalForm_not (source : Formula (Constant environment) gamma) :
    normalForm (.not source) = .imp (normalForm source) (normalForm (.bot : Formula (Constant environment) gamma)) := by
  apply normalForm_eq_of_normal _ _
    (BetaEtaNormalForms.imp_normal (normalForm_normal source) (normalForm_normal .bot))
  exact BetaEtaSubstitution.imp_congr (encoded_to_normalForm source) (encoded_to_normalForm .bot)

theorem normalForm_all (body : Formula (Constant environment) (domain :: gamma)) :
    normalForm (.all body) = .all (normalForm body) := by
  apply normalForm_eq_of_normal _ _ (BetaEtaNormalForms.all_normal (normalForm_normal body))
  exact BetaEtaSubstitution.all_congr (encoded_to_normalForm body)

theorem normalForm_weaken (source : Term (Constant environment) gamma type) :
    normalForm (weaken (σ := domain) source) = weaken (normalForm source) := by
  apply normalForm_eq_of_normal _ _ (BetaEtaNormalForms.weaken_normal (normalForm_normal source))
  simpa only [weaken, encode_rename] using
    BetaEtaSubstitution.rename (Rename.weaken (σ := domain)) (encoded_to_normalForm source)

theorem normalFormCode_imp (left right : Formula (Constant environment) gamma) :
    normalFormCode (.imp left right) = .imp (normalFormCode left) (normalFormCode right) := by
  apply Option.some.inj
  calc
    some (normalFormCode (.imp left right)) = erase (normalForm (.imp left right)) :=
      (normalForm_erased _).symm
    _ = erase (.imp (normalForm left) (normalForm right)) := congrArg erase (normalForm_imp left right)
    _ = some (.imp (normalFormCode left) (normalFormCode right)) := by
      simp [erase, normalForm_erased]

theorem normalFormCode_not (source : Formula (Constant environment) gamma) :
    normalFormCode (.not source) = .imp (normalFormCode source)
      (normalFormCode (.bot : Formula (Constant environment) gamma)) := by
  apply Option.some.inj
  calc
    some (normalFormCode (.not source)) = erase (normalForm (.not source)) := (normalForm_erased _).symm
    _ = erase (.imp (normalForm source) (normalForm (.bot : Formula (Constant environment) gamma))) :=
      congrArg erase (normalForm_not source)
    _ = some (.imp (normalFormCode source) (normalFormCode (.bot : Formula (Constant environment) gamma))) := by
      simp [erase, normalForm_erased]

theorem normalFormCode_all (body : Formula (Constant environment) (domain :: gamma)) :
    normalFormCode (.all body) = .all (reifyType domain) (normalFormCode body) := by
  apply Option.some.inj
  calc
    some (normalFormCode (.all body)) = erase (normalForm (.all body)) := (normalForm_erased _).symm
    _ = erase (.all (normalForm body)) := congrArg erase (normalForm_all body)
    _ = some (.all (reifyType domain) (normalFormCode body)) := by simp [erase, normalForm_erased]

theorem normalFormCode_weaken (source : Term (Constant environment) gamma type) :
    normalFormCode (weaken (σ := domain) source) = Tm.shift 0 1 (normalFormCode source) := by
  apply Option.some.inj
  calc
    some (normalFormCode (weaken (σ := domain) source)) =
        erase (normalForm (weaken (σ := domain) source)) := (normalForm_erased _).symm
    _ = erase (weaken (normalForm source)) := congrArg erase (normalForm_weaken source)
    _ = some (Tm.shift 0 1 (normalFormCode source)) := by
      rw [erase_weaken, normalForm_erased]
      rfl

/-- The canonical reading preserves actual values in every full-domain
interpretation, including the supplied set and hyperset models. -/
theorem denote_normalForm (model : HenkinModel.{0, 0, w} Base (Constant environment))
    (full : model.FullDomains) (source : Term (Constant environment) gamma type)
    (values : model.Valuation gamma) :
    model.denote (normalForm source) values = model.denote source values :=
  (denote_of_betaEtaConv model (encoded_to_normalForm source) values).symm.trans
    (denote_encode model full source values)

#print axioms normalForm
#print axioms normalForm_eq_of_conversion
#print axioms normalFormCode_of_normalizes
#print axioms normalFormCode_eq_of_conversion
#print axioms normalFormCode_top
#print axioms normalFormCode_bot
#print axioms normalFormCode_imp
#print axioms normalFormCode_not
#print axioms normalFormCode_all
#print axioms normalFormCode_weaken
#print axioms denote_normalForm

end Mettapedia.Languages.Megalodon.HOLNormalForms
