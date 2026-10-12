import Mettapedia.OSLF.NativeTypes.Generation.Core

open Mettapedia.OSLF.Framework

/-!
# Independent typing coverage of the generated modal catalogue

The source positions have a raw one-hole specification. The executable modal
catalogue additionally retains every grammar-licensed typing alternative.
These two domains are distinct: malformed authored sources can have raw
positions without a well-formed modal schema.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences (Licensed)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)

theorem schemas_sound {plan : Plan} {schema : Schema plan} (member : schema ∈ schemas plan) :
    schema.bound = [] ∧
      schema.programCarrier ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates plan.snapshot.language schema.declaration.rule ∧
      ∃ site, Licensed plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree schema.declaration.rule)
        .all [] schema.programCarrier schema.declaration.rule.left site ∧
        schema.position = site.address ∧ schema.focusBound = site.focusBound ∧
        schema.focusCarrier = site.focusType := by
  obtain ⟨entry, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨carrier, candidate, member⟩ := List.mem_flatMap.mp member
  obtain ⟨site, generated, same⟩ := List.mem_map.mp member
  subst schema
  exact ⟨rfl, candidate, site,
    (Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_spec _ _ _ _ _ _ _).mp generated, rfl, rfl, rfl⟩

theorem schemas_complete {plan : Plan} (declaration : RulePlan) (ordinal : Nat)
    (declared : (declaration, ordinal) ∈ plan.rules.zipIdx) (carrier : TypeExpr)
    (candidate : carrier ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates plan.snapshot.language declaration.rule)
    (site : SiteData)
    (licensed : Licensed plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
      .all [] carrier declaration.rule.left site) :
    ∃ schema ∈ schemas plan,
      schema.declaration = declaration ∧ schema.ordinal = ordinal ∧ schema.bound = [] ∧
      schema.programCarrier = carrier ∧ schema.position = site.address ∧
      schema.focusBound = site.focusBound ∧ schema.focusCarrier = site.focusType := by
  let entry : {entry // entry ∈ plan.rules.zipIdx} := ⟨(declaration, ordinal), declared⟩
  let schema : Schema plan :=
    {ordinal := ordinal, declaration := declaration, declared := declared,
      position := site.address, bound := [], programCarrier := carrier,
      focusBound := site.focusBound, focusCarrier := site.focusType}
  refine ⟨schema, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨entry, List.mem_attach _ _, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨carrier, candidate, ?_⟩
  exact List.mem_map.mpr ⟨site, Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_complete licensed, rfl⟩

theorem generated_modal_catalogue_disabled (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot language).language)
    (disabled : logic.core.modal = false) :
    (generate snapshot language logic vertex).modalCatalogue = [] := by
  simp [generate, disabled]

theorem generated_structural_catalogue_disabled (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot language).language)
    (disabled : logic.core.structural = false) :
    (generate snapshot language logic vertex).structuralCatalogue = [] := by
  simp [generate, disabled]

end Mettapedia.OSLF.NativeTypes.Generation
