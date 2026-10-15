import Mettapedia.OSLF.NativeTypes.Generation.Occurrences
import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

open Mettapedia.OSLF.Framework

/-!
# Declaration-derived carriers of generated rewrite modalities

The schematic syntax derivative is independent of sorting. The typed
derivative subsequently traverses every actual authored typing alternative;
its binder context, focus carrier and typing-frame origins are computed by
the schematic derivative, retaining collection tails. Missing rely declarations remain visible as
missing types, rather than disappearing from the slot vector.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Occurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences (Licensed)

def ruleFree (rule : RewriteRule) : FreeTypeContext :=
  fun name => (rule.typeContext.find? fun entry => entry.1 == name).map Prod.snd

/-- Finite source carrier candidates read from the authored signature and
rule context. The typed checker, rather than a label convention, determines
which candidates actually type the source. -/
def sourceCandidates (language : LanguageDef) (rule : RewriteRule) : List TypeExpr :=
  (language.types.map (fun type => TypeExpr.base type.name) ++
    rule.typeContext.map Prod.snd ++
    language.terms.flatMap (fun constructor => constructor.params.map TermParam.typeExpr)).eraseDups

structure TypedSite where
  declaration : Nat
  rule : RewriteRule
  sourceType : TypeExpr
  data : SiteData
  deriving Repr

def TypedSite.toSite (site : TypedSite) : Site :=
  { context := site.data.context
    focus := site.data.focus
    declaration := site.declaration
    rule := site.rule }

def TypedSite.carrier (site : TypedSite) : TypeExpr := site.data.focusType

inductive TypedLocalSlot where
  | rely (name : String) (type : Option TypeExpr)
  | output (type : TypeExpr)
  deriving DecidableEq, Repr

def TypedSite.localSlots (site : TypedSite) : List TypedLocalSlot :=
  site.toSite.relyNames.map (fun name => .rely name (ruleFree site.rule name)) ++
    [.output site.sourceType]

def typedGenerate (language : LanguageDef) : List TypedSite :=
  language.rewrites.zipIdx.flatMap fun (rule, index) =>
    (sourceCandidates language rule).flatMap fun sourceType =>
      (Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate
        language (ruleFree rule) .all [] sourceType rule.left).map fun data =>
          ⟨index, rule, sourceType, data⟩

theorem typedGenerate_spec (language : LanguageDef) (site : TypedSite) :
    site ∈ typedGenerate language ↔
      (site.rule, site.declaration) ∈ language.rewrites.zipIdx ∧
      site.sourceType ∈ sourceCandidates language site.rule ∧
      Licensed language (ruleFree site.rule) .all [] site.sourceType site.rule.left site.data := by
  constructor
  · intro member
    obtain ⟨⟨rule, index⟩, declared, member⟩ := List.mem_flatMap.mp member
    obtain ⟨sourceType, candidate, member⟩ := List.mem_flatMap.mp member
    obtain ⟨data, generated, equality⟩ := List.mem_map.mp member
    cases equality
    exact ⟨declared, candidate,
      (Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_spec _ _ _ _ _ _ _).mp generated⟩
  · rintro ⟨declared, candidate, licensed⟩
    refine List.mem_flatMap.mpr ⟨(site.rule, site.declaration), declared, ?_⟩
    refine List.mem_flatMap.mpr ⟨site.sourceType, candidate, ?_⟩
    exact List.mem_map.mpr ⟨site.data,
      Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_complete licensed, rfl⟩

theorem typed_generated_is_structural {language : LanguageDef} {site : TypedSite}
    (member : site ∈ typedGenerate language) : site.toSite ∈ generate language := by
  have licensed := (typedGenerate_spec _ _).mp member
  exact (generate_spec _ _).mpr ⟨licensed.1, licensed.2.2.selects⟩

theorem typed_generated_focus_carrier {language : LanguageDef} {site : TypedSite}
    (member : site ∈ typedGenerate language) :
    HasType language (ruleFree site.rule) site.data.focusBound site.data.focus site.carrier :=
  ((typedGenerate_spec _ _).mp member).2.2.focus_typed

theorem typed_generated_source_type {language : LanguageDef} {site : TypedSite}
    (member : site ∈ typedGenerate language) :
    HasType language (ruleFree site.rule) [] site.rule.left site.sourceType :=
  ((typedGenerate_spec _ _).mp member).2.2.source_typed

theorem typed_generated_address {language : LanguageDef} {site : TypedSite}
    (member : site ∈ typedGenerate language) : site.data.address = site.toSite.position :=
  ((typedGenerate_spec _ _).mp member).2.2.address_eq

theorem typed_generated_binder_depth {language : LanguageDef} {site : TypedSite}
    (member : site ∈ typedGenerate language) :
    site.data.focusBound.length =
      Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress.binderCount site.data.context := by
  simpa using ((typedGenerate_spec _ _).mp member).2.2.binder_depth

theorem typed_localSlots_length (site : TypedSite) :
    site.localSlots.length = site.toSite.relyNames.length + 1 := by
  simp [TypedSite.localSlots]

/-- The count is an earned projection of the complete slot vector. Its
output carrier is the actual source carrier, not the carrier of the hole. -/
theorem typed_output_slot (site : TypedSite) :
    TypedLocalSlot.output site.sourceType ∈ site.localSlots := by
  simp [TypedSite.localSlots]

end Mettapedia.OSLF.NativeTypes.Generation.Occurrences
