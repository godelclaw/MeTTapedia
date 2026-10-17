import Mettapedia.OSLF.Framework.GeneralCanonicalCongruenceAgreement
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.GSLT.Core.GSLTConstructions

/-!
# Native types are the same in the general and canonical semantics

For a language with the first-order profile, the general step and the canonical
step agree from every well-sorted source, in a relation environment that reads
the provider. The identity on patterns is then a
checked cover from the general GSLT onto the canonical GSLT restricted to steps
from well-sorted sources. Consequently every Hennessy--Milner native type over a
shared observation family has the same extension in both. This is predicate
transport; executable observations, completion and a decision procedure are
separate obligations.

The canonical side is restricted because the canonical engine is untyped: it also
takes steps from terms outside the sort, which the general semantics never
starts from.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.MeTTaIL MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

variable {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}

/-- The general GSLT of a language's root plan at a sort. -/
abbrev general (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (bound : List TypeExpr) (type : TypeExpr) : GSLT :=
  GeneralOccurrenceSemantics.gslt (rootPlan language provider) bound type

/-- The canonical GSLT of a language. -/
abbrev canonical (relEnv : Engine.RelationEnv) (language : LanguageDef) : GSLT :=
  TypeSynthesis.langGSLTUsing relEnv language

/-- The sources the general semantics starts from. -/
abbrev Sorted (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (bound : List TypeExpr) (type : TypeExpr) (term : Pattern) : Prop :=
  OpenPatternWellSorted (rootPlan language provider).snapshot.language (rootPlan language provider).snapshot.free
    bound type term

theorem FirstOrderProfile.canonical_equiv_iff (profile : FirstOrderProfile language provider)
    (relEnv : Engine.RelationEnv) (left right : Pattern) :
    (canonical relEnv language).Equiv left right ↔ left = right := by
  simpa [canonical, TypeSynthesis.langGSLTUsing] using
    (Mettapedia.GSLT.LanguageDef.EquationSemantics.gsltModuloEquations_equiv_iff_eq_of_no_generators
      (base := ContextualStep.engineBasePremises relEnv) profile.equationFree left right)

theorem FirstOrderProfile.general_equiv_iff (profile : FirstOrderProfile language provider)
    (bound : List TypeExpr) (type : TypeExpr) (left right : Pattern) :
    (general language provider bound type).Equiv left right ↔ left = right := by
  constructor
  · intro equivalent
    exact GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality
      (request := ⟨rootPlan language provider, bound, type, left⟩) profile.equations equivalent
  · rintro rfl
    exact Relation.EqvGen.refl left

/-- The general semantics starts only from well-sorted sources. -/
theorem FirstOrderProfile.general_source_sorted (profile : FirstOrderProfile language provider)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    (step : (general language provider bound type).Step source target) : Sorted language provider bound type source := by
  obtain ⟨representative, receipt, before, fired, _⟩ := step
  have same := (profile.general_equiv_iff bound type source representative).mp before
  subst same
  have site := rootOnly_site fired.1.2
  have firing := fired.2.1
  rw [site] at firing
  simp only [MeTTaIL.GeneralTypedSites.SiteData.here] at firing
  cases firing with
  | fire _ _ _ sorted _ _ _ _ _ =>
    exact (GeneralPlanEnvironment.typing_iff (rootPlan language provider) bound type source).mp sorted

/-- Canonical steps from well-sorted sources. -/
def sortedSteps (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (bound : List TypeExpr) (type : TypeExpr) : GSLT.StepFilter (canonical relEnv language) where
  keep source target := (canonical relEnv language).Step source target ∧ Sorted language provider bound type source
  keep_sound kept := kept.1
  resp_left equivalent kept := by
    have same := (profile.canonical_equiv_iff relEnv _ _).mp equivalent
    subst same
    exact ⟨_, kept, (profile.canonical_equiv_iff relEnv _ _).mpr rfl⟩
  resp_right kept equivalent := by
    have same := (profile.canonical_equiv_iff relEnv _ _).mp equivalent
    subst same
    exact kept

/-- The canonical GSLT restricted to steps from well-sorted sources. -/
def sortedCanonical (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (bound : List TypeExpr) (type : TypeExpr) : GSLT :=
  (canonical relEnv language).restrict (sortedSteps profile relEnv bound type)

/-- The one-label step system of a GSLT over an observation family that respects
its equivalence. -/
abbrev stepSystem (S : GSLT) {Atom : Type} (observes : Atom → S.Term → Prop)
    (resp : ∀ (atom : Atom) {left right : S.Term},
      S.Equiv left right → (observes atom left ↔ observes atom right)) : System S where
  Atom := Atom
  observes := observes
  observes_resp := resp
  Label := Unit
  act _ source target := S.Step source target
  act_resp_left equivalent step := S.rewrites_resp_left equivalent step
  act_resp_right step equivalent := S.rewrites_resp_right step equivalent

theorem general_resp (profile : FirstOrderProfile language provider) (bound : List TypeExpr) (type : TypeExpr)
    {Atom : Type} (observes : Atom → Pattern → Prop) (atom : Atom) {left right : Pattern}
    (equivalent : (general language provider bound type).Equiv left right) :
    observes atom left ↔ observes atom right := by
  have same := (profile.general_equiv_iff bound type left right).mp equivalent
  subst same
  exact Iff.rfl

theorem sortedCanonical_resp (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (bound : List TypeExpr) (type : TypeExpr) {Atom : Type} (observes : Atom → Pattern → Prop)
    (atom : Atom) {left right : Pattern}
    (equivalent : (sortedCanonical profile relEnv bound type).Equiv left right) :
    observes atom left ↔ observes atom right := by
  have same := (profile.canonical_equiv_iff relEnv left right).mp equivalent
  subst same
  exact Iff.rfl

/-- The general step system over an observation family. -/
abbrev generalSystem (profile : FirstOrderProfile language provider) (bound : List TypeExpr) (type : TypeExpr)
    {Atom : Type} (observes : Atom → Pattern → Prop) : System (general language provider bound type) :=
  stepSystem (general language provider bound type) observes (general_resp profile bound type observes)

/-- The sorted canonical step system over the same observation family. -/
abbrev canonicalSystem (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (bound : List TypeExpr) (type : TypeExpr) {Atom : Type} (observes : Atom → Pattern → Prop) :
    System (sortedCanonical profile relEnv bound type) :=
  stepSystem (sortedCanonical profile relEnv bound type) observes
    (sortedCanonical_resp profile relEnv bound type observes)

/-- **The identity is a checked cover.** -/
def nativeCover (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv provider) (bound : List TypeExpr) (type : TypeExpr) {Atom : Type} (observes : Atom → Pattern → Prop) :
    SystemCover (generalSystem profile bound type observes)
      (canonicalSystem profile relEnv bound type observes) where
  mapTerm term := term
  mapAtom atom := atom
  mapLabel label := label
  mapEquiv equivalent := by
    have same := (profile.general_equiv_iff bound type _ _).mp equivalent
    subst same
    exact (profile.canonical_equiv_iff relEnv _ _).mpr rfl
  observes_iff _ _ := Iff.rfl
  mapAct step := by
    have sorted := profile.general_source_sorted step
    exact ⟨(profile.general_step_iff_canonical relEnv reads bound type sorted).mp step, sorted⟩
  liftAct kept :=
    ⟨_, (profile.general_step_iff_canonical relEnv reads bound type kept.2).mpr kept.1,
      (profile.canonical_equiv_iff relEnv _ _).mpr rfl⟩

/-- **Native types agree.** Every Hennessy--Milner native type over the shared
observations has the same extension in the general semantics and in the sorted
canonical semantics. -/
theorem nativeType_iff (profile : FirstOrderProfile language provider) (relEnv : Engine.RelationEnv)
    (reads : ReadsProvider relEnv provider) (bound : List TypeExpr) (type : TypeExpr) {Atom : Type} (observes : Atom → Pattern → Prop)
    (formula : Formula Atom Unit) (term : Pattern) :
    (gsltOSLF (sortedCanonical profile relEnv bound type)).satisfies (S := ()) term
        (formulaNativeType (canonicalSystem profile relEnv bound type observes) formula).pred ↔
      (gsltOSLF (general language provider bound type)).satisfies (S := ()) term
        (formulaNativeType (generalSystem profile bound type observes) formula).pred := by
  have transported := systemCover_formulaNativeType_iff (generalSystem profile bound type observes)
    (nativeCover profile relEnv reads bound type observes) formula term
  have satisfied : (canonicalSystem profile relEnv bound type observes).sat (Formula.map id id formula) term ↔
      (generalSystem profile bound type observes).sat formula term := transported
  rw [Formula.map_id] at satisfied
  exact satisfied

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
