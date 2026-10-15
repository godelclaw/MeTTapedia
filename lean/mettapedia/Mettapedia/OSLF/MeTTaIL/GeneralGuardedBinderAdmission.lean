import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFlow
import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

/-!
# Whole-language admission of guarded binding and extrusion

The original authored grammar, equations and duplicate rules are compiled
without a consumer-specific state decoder. The admission theorem holds for
every finite provider list; occurrence generation covers all typed object
terms and all caller binder contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderAdmission

open Syntax GeneralExecutionAdmission GeneralTypedSites
open EquationFrontierBinderProfile
open Mettapedia.GSLT.LanguageDef.WellSorted

def providerSnapshot (allowed : List Token) : GeneralPremise.ProviderSnapshot where
  signatures := [{ relation := "allow", argumentTypes := [.proc], modes := [.input] }]
  rows := allowed.map fun token => { relation := "allow", values := [guard token] }

def snapshot (allowed : List Token) : Snapshot where
  language := language
  freeTypes := []
  provider := providerSnapshot allowed

def permissions : Permissions where
  sites := .all

theorem free_context (allowed : List Token) : (snapshot allowed).free = FreeTypeContext.empty := rfl

theorem provider_admitted (allowed : List Token) :
    GeneralPremise.checkProviderClosed language (snapshot allowed).free (providerSnapshot allowed) = true := by
  simp only [GeneralPremise.checkProviderClosed, providerSnapshot, List.all_cons, List.all_nil,
    Bool.and_true, List.map_cons, List.map_nil]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · decide
  · apply List.all_eq_true.mpr
    intro row member
    obtain ⟨token, _, same⟩ := List.mem_map.mp member
    subst row
    cases token <;> change GeneralPremise.checkRow language FreeTypeContext.empty []
      { relation := "allow", argumentTypes := [.proc], modes := [.input] }
      { relation := "allow", values := [guard _] } = true <;> decide +kernel

theorem binding_language_admitted : RuleBinding.bindingDeclarationsValid language = true :=
  EquationFrontierBinderProfile.bindings_valid

theorem selected_equations_balanced : GeneralEquationAdmission.checkLanguage language = true := by cbv

theorem admission_complete (allowed : List Token) :
    (compile (snapshot allowed) permissions).complete = true := by
  have provider := provider_admitted allowed
  unfold Plan.complete compile
  change ((if language.validate.isEmpty then [] else [Obligation.invalidLanguage]) ++
    (if checkFreeContext (snapshot allowed) then [] else [Obligation.invalidFreeContext]) ++
    (if GeneralPremise.checkProviderClosed language (snapshot allowed).free (providerSnapshot allowed)
      then [] else [Obligation.invalidProvider]) ++
    (if (Reflection.validate language permissions.reflection).isEmpty
      then [] else [Obligation.invalidReflection]) ++
    (missing permissions.ruleIndices language.rewrites.length).map Obligation.missingRule ++
    (missing permissions.equationIndices language.equations.length).map Obligation.missingEquation ++
    (selectedRules (snapshot allowed) permissions).flatMap
      (fun (rule, index) => ruleObligations (snapshot allowed) index rule) ++
    (selectedEquations (snapshot allowed) permissions).flatMap
      (fun (equation, index, direction) => equationObligations (snapshot allowed) index equation direction) ++
    (if GeneralPremise.checkStepStratification (executionLanguage (snapshot allowed) permissions)
      then [] else [Obligation.childStratification]) ++
    (if permissions.includeDerivedEquations &&
        (language.usesCollection .hashBag || language.usesCollection .hashSet || language.hasAlgebraDeclarations)
      then [Obligation.derivedEquationCoverage] else [])).isEmpty = true
  rw [provider]
  cbv

theorem all_typed_sites {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {site : GeneralTypedSites.SiteData} :
    site ∈ GeneralTypedSites.generate (snapshot allowed).language (snapshot allowed).free
      permissions.sites bound expected source ↔
    Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed language FreeTypeContext.empty
      OperationalPermissions.all bound expected source site :=
  GeneralTypedSites.generate_spec _ _ _ _ _ _ _

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderAdmission
