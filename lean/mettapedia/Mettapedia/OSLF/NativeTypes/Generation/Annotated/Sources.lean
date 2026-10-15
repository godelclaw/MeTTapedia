import Mettapedia.OSLF.NativeTypes.Modal.DescentAnnotations
import Mettapedia.OSLF.NativeTypes.Generation.Core
import Mettapedia.OSLF.NativeTypes.Generation.Occurrences.NameBridge

open Mettapedia.OSLF.Framework

/-!
# Annotated source instances of the one authored generator

The finite templates are the generator's actual raw authored sites. Typing
instances supply a finite annotation and a chosen source carrier, allowing
arbitrary arrow carriers and explicit substitution. The executable gate checks
the declaration origin, filled source and complete typing descent. It does
not turn an unresolved operational binding into a selected execution rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Annotations

deriving instance DecidableEq for RewriteRule

/-- Data choices only: no typing, soundness, or operational admission field. -/
structure SourceAnnotation where
  bound : List TypeExpr
  programCarrier : TypeExpr
  focusBound : List TypeExpr
  focusCarrier : TypeExpr
  descent : DescentAnnotation
  deriving DecidableEq, Repr

inductive AnnotationIssue where
  | missingTemplate (index : Nat)
  | malformedTemplate (index : Nat)
  | invalidTyping (index : Nat)
  | unresolvedOperationalDeclaration (declaration : Nat)
  deriving DecidableEq, Repr

/-- Original declaration identity and the actual filled template are checked
even if a caller constructs a `Generated` record directly. -/
def Generated.checkRawTemplate (generated : Generated) (site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site) : Bool :=
  decide (generated.snapshot.language.rewrites[site.declaration]? = some site.rule) &&
    selected generated.languageFragment.operational.ruleIndices site.declaration &&
    decide (site.context.fill site.focus = site.rule.left)

def Generated.checkSourceAnnotation (generated : Generated) (site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site)
    (annotation : SourceAnnotation) : Bool :=
  checkDescent generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree site.rule)
    site.focus site.context annotation.bound annotation.programCarrier
    annotation.focusBound annotation.focusCarrier annotation.descent

/-- This is the checked result of actual runtime tests. Its proof fields are
derived by the checker and disappear at execution; the annotation remains. -/
structure AnnotatedSource (generated : Generated) where
  index : Nat
  site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site
  present : generated.rawSites[index]? = some site
  annotation : SourceAnnotation
  templateChecked : generated.checkRawTemplate site = true
  typingChecked : generated.checkSourceAnnotation site annotation = true

/-- Instantiate one of the generated finite raw templates. A rejected
certificate reports its cause rather than an empty exhaustive catalogue. -/
def Generated.instantiateAnnotatedSource? (generated : Generated) (index : Nat)
    (annotation : SourceAnnotation) : Except AnnotationIssue (AnnotatedSource generated) :=
  match found : generated.rawSites[index]? with
  | none => .error (.missingTemplate index)
  | some site =>
      if templateChecked : generated.checkRawTemplate site = true then
        if typingChecked : generated.checkSourceAnnotation site annotation = true then
          .ok ⟨index, site, found, annotation, templateChecked, typingChecked⟩
        else .error (.invalidTyping index)
      else .error (.malformedTemplate index)

/-- The successful public result retains the supplied annotation and actual
raw-template index, rather than reconstructing only its final focus type. -/
theorem instantiated_source_input_retained {generated : Generated} {index : Nat}
    {annotation : SourceAnnotation} {checkedSource : AnnotatedSource generated}
    (produced : generated.instantiateAnnotatedSource? index annotation = .ok checkedSource) :
    checkedSource.index = index ∧ checkedSource.annotation = annotation := by
  unfold Generated.instantiateAnnotatedSource? at produced
  split at produced
  · cases produced
  · split at produced
    · split at produced
      · cases produced
        exact ⟨rfl, rfl⟩
      · cases produced
    · cases produced

namespace AnnotatedSource

variable {generated : Generated} (checkedSource : AnnotatedSource generated)

theorem authored :
    generated.snapshot.language.rewrites[checkedSource.site.declaration]? = some checkedSource.site.rule := by
  have checked := (Bool.and_eq_true _ _).mp checkedSource.templateChecked
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp checked.1).1

theorem selected_declaration :
    selected generated.languageFragment.operational.ruleIndices checkedSource.site.declaration = true := by
  exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp checkedSource.templateChecked).1).2

theorem source_eq : checkedSource.site.context.fill checkedSource.site.focus = checkedSource.site.rule.left := by
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp checkedSource.templateChecked).2

theorem selected : Selects checkedSource.site.focus checkedSource.site.context checkedSource.site.rule.left := by
  rw [← checkedSource.source_eq]
  exact Selects.of_fill _ _

theorem typedAt :
    TypedAt generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree checkedSource.site.rule)
      checkedSource.site.focus checkedSource.site.context checkedSource.annotation.bound checkedSource.annotation.programCarrier
      checkedSource.annotation.focusBound checkedSource.annotation.focusCarrier :=
  checkDescent_sound checkedSource.typingChecked

theorem source_typed :
    HasType generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree checkedSource.site.rule)
      checkedSource.annotation.bound checkedSource.site.rule.left checkedSource.annotation.programCarrier := by
  rw [← checkedSource.source_eq]
  exact checkedSource.typedAt.source_typed

theorem focus_typed :
    HasType generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree checkedSource.site.rule)
      checkedSource.annotation.focusBound checkedSource.site.focus checkedSource.annotation.focusCarrier :=
  checkedSource.typedAt.focus_typed

theorem binder_context_retained :
    ∃ binderPrefix, checkedSource.annotation.focusBound = binderPrefix ++ checkedSource.annotation.bound :=
  checkedSource.typedAt.ambient_suffix

theorem source_scope_checked :
    checkedSource.site.rule.left.isWellScopedAt checkedSource.annotation.bound.length = true :=
  checkedSource.source_typed.isWellScopedAt

theorem focus_scope_checked :
    checkedSource.site.focus.isWellScopedAt checkedSource.annotation.focusBound.length = true :=
  checkedSource.focus_typed.isWellScopedAt

theorem raw_origin_retained :
    checkedSource.site ∈ generated.rawSites := List.mem_of_getElem? checkedSource.present

end AnnotatedSource

/-- Completeness for any actual template whose authored source is typed.
This is an unrestricted annotated typing family, not a finite-carrier claim. -/
theorem instantiate_annotated_source_complete (generated : Generated)
    (index : Nat) (site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site)
    (present : generated.rawSites[index]? = some site)
    (templateChecked : generated.checkRawTemplate site = true)
    (bound focusBound : List TypeExpr) (programCarrier focusCarrier : TypeExpr)
    (typed : TypedAt generated.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree site.rule)
      site.focus site.context bound programCarrier focusBound focusCarrier) :
    ∃ annotation checkedSource,
      generated.instantiateAnnotatedSource? index annotation = .ok checkedSource ∧
      checkedSource.site = site ∧ checkedSource.annotation.bound = bound ∧
      checkedSource.annotation.programCarrier = programCarrier ∧
      checkedSource.annotation.focusBound = focusBound ∧ checkedSource.annotation.focusCarrier = focusCarrier := by
  obtain ⟨descent, accepted⟩ := checkDescent_complete typed
  let annotation : SourceAnnotation := ⟨bound, programCarrier, focusBound, focusCarrier, descent⟩
  have typedChecked : generated.checkSourceAnnotation site annotation = true := accepted
  let checkedSource : AnnotatedSource generated :=
    ⟨index, site, present, annotation, templateChecked, typedChecked⟩
  refine ⟨annotation, checkedSource, ?_, rfl, rfl, rfl, rfl, rfl⟩
  unfold Generated.instantiateAnnotatedSource?
  split
  · rename_i missing
    rw [present] at missing
    contradiction
  · rename_i actual actualAt
    have same : actual = site := Option.some.inj (actualAt.symm.trans present)
    subst actual
    simp only [templateChecked, typedChecked, ↓reduceDIte]
    rfl

/-- For the actual generated output, every raw template passes declaration
and one-hole validation before any typing annotation is selected. -/
theorem generated_raw_template_checked (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot language).language)
    {site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site}
    (member : site ∈ (generate snapshot language logic vertex).rawSites) :
    (generate snapshot language logic vertex).checkRawTemplate site = true := by
  change site ∈ selectedSites (selectedSnapshot snapshot language).language language.operational at member
  rcases (selected_sites_iff _ _ _).mp member with ⟨declared, selected, occurs⟩
  have lookup := List.mk_mem_zipIdx_iff_getElem?.mp declared
  have filled : site.context.fill site.focus = site.rule.left := selected.fill_eq
  change (decide ((selectedSnapshot snapshot language).language.rewrites[site.declaration]? = some site.rule) &&
      Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.selected language.operational.ruleIndices site.declaration &&
      decide (site.context.fill site.focus = site.rule.left)) = true
  simp only [lookup, filled, decide_true, occurs, Bool.and_self]

/-- All independently typed raw sites in an actual generated output have an
accepted annotated instance, including substitutions and arbitrary arrows. -/
theorem every_generated_typed_site_has_annotation (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot language).language)
    (index : Nat) (site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site)
    (present : (generate snapshot language logic vertex).rawSites[index]? = some site)
    (bound focusBound : List TypeExpr) (programCarrier focusCarrier : TypeExpr)
    (typed : TypedAt (selectedSnapshot snapshot language).language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree site.rule)
      site.focus site.context bound programCarrier focusBound focusCarrier) :
    ∃ annotation checkedSource,
      (generate snapshot language logic vertex).instantiateAnnotatedSource? index annotation = .ok checkedSource ∧
      checkedSource.site = site ∧ checkedSource.annotation.bound = bound ∧
      checkedSource.annotation.programCarrier = programCarrier ∧
      checkedSource.annotation.focusBound = focusBound ∧ checkedSource.annotation.focusCarrier = focusCarrier :=
  instantiate_annotated_source_complete _ index site present
    (generated_raw_template_checked snapshot language logic vertex (List.mem_of_getElem? present))
    bound focusBound programCarrier focusCarrier typed

end Mettapedia.OSLF.NativeTypes.Generation
