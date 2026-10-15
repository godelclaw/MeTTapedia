import Mettapedia.OSLF.NativeTypes.Generation.Schemas
import Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers
import Mettapedia.OSLF.NativeTypes.Modal.ProgramAdmission
import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

open Mettapedia.OSLF.Framework

/-!
# Full typed occurrence coverage for admitted classifying sources

Every independently licensed occurrence and every possible root typing is
covered for a source admitted by the declaration-derived classifying check.
Carrier membership in the finite candidate list is derived here, rather
than supplied by a caller. Binder contexts and grammar alternatives remain
the exact records constructed by the schematic derivative. Open collection
tails remain in the zipper. The classifying program family is distinguished
from arbitrary raw arrow and collection-expression root typings.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.CatalogueCoverage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences
open Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)

/-- Section 19.3's classifying admission earns all root carriers and all
licensed positions. No finite candidate-membership witness is requested. -/
theorem schemas_classified_complete {plan : Plan} (declaration : RulePlan) (ordinal : Nat)
    (declared : (declaration, ordinal) ∈ plan.rules.zipIdx)
    (classified : classifyingSource? plan.snapshot.language declaration.rule = true)
    (carrier : TypeExpr) (site : SiteData)
    (licensed : Licensed plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
      .all [] carrier declaration.rule.left site) :
    ∃ schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas plan,
      schema.declaration = declaration ∧ schema.ordinal = ordinal ∧ schema.bound = [] ∧
      schema.programCarrier = carrier ∧ schema.position = site.address ∧
      schema.focusBound = site.focusBound ∧ schema.focusCarrier = site.focusType :=
  Mettapedia.OSLF.NativeTypes.Generation.schemas_complete declaration ordinal declared carrier
    (classified_type_candidate classified licensed.source_typed) site licensed

/-- A successful computational source readout establishes the admission
used by the whole-family catalogue theorem. It is not a supplied predicate
claiming that a particular caller-written site list is complete. -/
theorem schemas_readout_complete {plan : Plan} (declaration : RulePlan) (ordinal : Nat)
    (declared : (declaration, ordinal) ∈ plan.rules.zipIdx) (carriers : List TypeExpr)
    (accepted : carrierStatus plan.snapshot.language declaration.rule = .classified carriers)
    (carrier : TypeExpr) (site : SiteData)
    (licensed : Licensed plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
      .all [] carrier declaration.rule.left site) :
    carrier ∈ carriers ∧
      ∃ schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas plan,
        schema.declaration = declaration ∧ schema.ordinal = ordinal ∧ schema.bound = [] ∧
        schema.programCarrier = carrier ∧ schema.position = site.address ∧
        schema.focusBound = site.focusBound ∧ schema.focusCarrier = site.focusType := by
  have classified := (carrier_status_sound accepted).1
  have computed := carrier_status_complete classified licensed.source_typed
    (carrier_status_representation accepted)
  have equal : typedCarriers plan.snapshot.language declaration.rule = carriers := by
    exact CarrierStatus.classified.inj (computed.1.symm.trans accepted)
  refine ⟨equal ▸ computed.2, ?_⟩
  exact schemas_classified_complete declaration ordinal declared classified carrier site licensed

/-- The same coverage holds before operational rule filtering, for every
authored declaration and every independently licensed typed occurrence. -/
theorem typed_generate_classified_complete {language : LanguageDef}
    (rule : RewriteRule) (ordinal : Nat) (declared : (rule, ordinal) ∈ language.rewrites.zipIdx)
    (classified : classifyingSource? language rule = true) (carrier : TypeExpr) (site : SiteData)
    (licensed : Licensed language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree rule) .all [] carrier rule.left site) :
    ({declaration := ordinal, rule := rule, sourceType := carrier, data := site} : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.TypedSite) ∈
      Mettapedia.OSLF.NativeTypes.Generation.Occurrences.typedGenerate language :=
  (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.typedGenerate_spec _ _).mpr
    ⟨declared, classified_type_candidate classified licensed.source_typed, licensed⟩

/-- For the source's classifying program-result family, every independently
typed schema occurrence is represented, including an authored REST tail.
The finite carrier admission is derived from the source typing and the
actual authored result declarations. -/
theorem schemas_program_complete {plan : Plan} (declaration : RulePlan) (ordinal : Nat)
    (declared : (declaration, ordinal) ∈ plan.rules.zipIdx)
    (classified : Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.classifyingProgramSource?
      plan.snapshot.language declaration.rule = true)
    (category : String) (site : SiteData)
    (licensed : Licensed plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
      .all [] (.base category) declaration.rule.left site) :
    ∃ schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas plan,
      schema.declaration = declaration ∧ schema.ordinal = ordinal ∧ schema.bound = [] ∧
      schema.programCarrier = .base category ∧ schema.position = site.address ∧
      schema.focusBound = site.focusBound ∧ schema.focusCarrier = site.focusType :=
  Mettapedia.OSLF.NativeTypes.Generation.schemas_complete declaration ordinal declared (.base category)
    (Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.classified_program_source_candidate
      classified licensed.source_typed) site licensed

theorem schemas_program_readout_complete {plan : Plan} (declaration : RulePlan) (ordinal : Nat)
    (declared : (declaration, ordinal) ∈ plan.rules.zipIdx) (carriers : List TypeExpr)
    (accepted : Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.programCarrierStatus plan.snapshot.language
      declaration.rule = .classified carriers) (category : String) (site : SiteData)
    (licensed : Licensed plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
      .all [] (.base category) declaration.rule.left site) :
    TypeExpr.base category ∈ carriers ∧
      ∃ schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas plan,
        schema.declaration = declaration ∧ schema.ordinal = ordinal ∧ schema.bound = [] ∧
        schema.programCarrier = .base category ∧ schema.position = site.address ∧
        schema.focusBound = site.focusBound ∧ schema.focusCarrier = site.focusType := by
  have admitted := Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.program_status_sound accepted
  have computed := Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.program_status_complete admitted.1
    admitted.2.1 licensed.source_typed
  have equal : Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.typedProgramCarriers
      plan.snapshot.language declaration.rule = carriers :=
    Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.ProgramCarrierStatus.classified.inj (computed.1.symm.trans accepted)
  exact ⟨equal ▸ computed.2,
    schemas_program_complete declaration ordinal declared admitted.1 category site licensed⟩

/-- Completeness against the pre-existing, algorithm-independent typed
one-hole relation. Structural permission is proved from the classified
source, rather than supplied as an occurrence-admission interface field. -/
theorem schemas_program_typedAt_complete {plan : Plan} (declaration : RulePlan) (ordinal : Nat)
    (declared : (declaration, ordinal) ∈ plan.rules.zipIdx)
    (classified : Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.classifyingProgramSource?
      plan.snapshot.language declaration.rule = true)
    (category : String) (focus : Pattern)
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    (focusBound : List TypeExpr) (focusCarrier : TypeExpr)
    (selected : TypedAt plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
      focus context [] (.base category) focusBound focusCarrier)
    (source : context.fill focus = declaration.rule.left)
    (supported : substitutionFree declaration.rule.left = true) :
    ∃ schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas plan,
      schema.declaration = declaration ∧ schema.ordinal = ordinal ∧ schema.bound = [] ∧
      schema.programCarrier = .base category ∧ schema.position = contextAddress context ∧
      schema.focusBound = focusBound ∧ schema.focusCarrier = focusCarrier := by
  have classifiedContext : substitutionFree (context.fill focus) = true := source ▸ supported
  obtain ⟨site, licensed, contextEq, focusEq, boundEq, typeEq⟩ :=
    typedAt_licensed selected classifiedContext (all_context_permitted focus context classifiedContext)
  have licensedSource : Licensed plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
      .all [] (.base category) declaration.rule.left site := source ▸ licensed
  obtain ⟨schema, member, declarationEq, ordinalEq, ambientEq, carrierEq, positionEq, focusBoundEq, focusTypeEq⟩ :=
    schemas_program_complete declaration ordinal declared classified category site licensedSource
  refine ⟨schema, member, declarationEq, ordinalEq, ambientEq, carrierEq, ?_,
    focusBoundEq.trans boundEq, focusTypeEq.trans typeEq⟩
  have address : site.address = contextAddress context := by
    simpa only [contextEq] using licensed.address_eq
  exact positionEq.trans address

theorem typed_generate_program_complete {language : LanguageDef}
    (rule : RewriteRule) (ordinal : Nat) (declared : (rule, ordinal) ∈ language.rewrites.zipIdx)
    (classified : Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.classifyingProgramSource? language rule = true)
    (category : String) (site : SiteData)
    (licensed : Licensed language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree rule) .all [] (.base category) rule.left site) :
    ({declaration := ordinal, rule := rule, sourceType := .base category, data := site} :
      Mettapedia.OSLF.NativeTypes.Generation.Occurrences.TypedSite) ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.typedGenerate language :=
  (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.typedGenerate_spec _ _).mpr
    ⟨declared, Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.classified_program_source_candidate
      classified licensed.source_typed, licensed⟩

end Mettapedia.OSLF.NativeTypes.Modal.CatalogueCoverage
