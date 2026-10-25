import Mettapedia.OSLF.MeTTaIL.CollectionSelectionCanonical
import Mettapedia.OSLF.MeTTaIL.CanonicalSites
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-!
# Licensed collection contexts modulo collection equality

An equivalent residual preserves the collection's pointwise element typing and
object status. Both direct collection sorts and authored collection constructors
therefore license the retained-copy context. The inner site may carry arbitrary
existing binder and constructor frames.

This is a collection-layer transport theorem. A recursive generator and its
admission certificate must still consume it before set descent is enabled.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection

open Syntax CanonicalBags DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef
open WellSorted GeneralTypedOccurrence

theorem presents_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elementType : TypeExpr} {kind : CollType}
    {left right : List Pattern} (same : Presents kind left right)
    (typed : ElementsHaveType language free bound left elementType) :
    ElementsHaveType language free bound right elementType :=
  elementsHaveType_iff.mpr fun element member =>
    elementsHaveType_iff.mp typed element ((same.mem element).mpr member)

theorem presents_objects {kind : CollType} {left right : List Pattern}
    (same : Presents kind left right) (objects : isObjectPatternList left = true) :
    isObjectPatternList right = true := by
  rw [isObjectPatternList_eq_all] at objects ⊢
  exact List.all_eq_true.mpr fun item member =>
    List.all_eq_true.mp objects item ((same.mem item).mpr member)

/-- Preserve the exact inner context and typing frames while changing only
the collection residual presentation. -/
def liftResidual (origin : TypingFrame) (kind : CollType) (rest : List Pattern)
    (inner : SiteData) : SiteData :=
  inner.wrapCollection origin kind (inner.context.fill inner.focus :: rest) 0

/-- The finite executable family of contexts for one selected collection
element. Set entries include both consume and retain choices; bag entries only
consume the selected physical occurrence. -/
def residualSites (origin : TypingFrame) (kind : CollType) (items : List Pattern)
    (selected : Nat) (inner : SiteData) : List SiteData :=
  (kindResiduals kind items selected).map fun residual =>
    liftResidual origin kind residual inner

theorem mem_residualSites {origin : TypingFrame} {kind : CollType}
    {items : List Pattern} {selected : Nat} {inner site : SiteData} :
    site ∈ residualSites origin kind items selected inner ↔
      ∃ residual ∈ kindResiduals kind items selected,
        site = liftResidual origin kind residual inner := by
  rw [residualSites, List.mem_map]
  constructor
  · rintro ⟨residual, member, rfl⟩
    exact ⟨residual, member, rfl⟩
  · rintro ⟨residual, member, rfl⟩
    exact ⟨residual, member, rfl⟩

theorem liftResidual_fill (origin : TypingFrame) (kind : CollType) (rest : List Pattern)
    (inner : SiteData) (replacement : Pattern) :
    (liftResidual origin kind rest inner).context.fill replacement =
      .collection kind (inner.context.fill replacement :: rest) none := by
  rfl

/-- No typing authority is obtained from equality alone: the supplied inner
site is already licensed, and the collection keeps its declared element type. -/
theorem licensed_direct_residual {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {elementType : TypeExpr} {kind : CollType} {items rest : List Pattern}
    {value : Pattern} {inner : SiteData}
    (permitted : kind ∈ permissions.collectionKinds)
    (typed : ElementsHaveType language free bound items elementType)
    (objects : isObjectPatternList items = true)
    (same : Presents kind items (value :: rest))
    (licensed : Licensed language free permissions bound elementType value inner) :
    Licensed language free permissions bound (.collection kind elementType)
      (.collection kind (value :: rest) none)
      (liftResidual (.directCollection kind) kind rest inner) := by
  have source := licensed.source_eq
  unfold liftResidual
  rw [source]
  exact .directCollection permitted (presents_typed same typed) (presents_objects same objects)
    rfl licensed

/-- Authored collection constructors retain the original declaration identity
and its declared result sort. -/
theorem licensed_authored_residual {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {elementType : TypeExpr} {kind : CollType} {items rest : List Pattern}
    {value : Pattern} {inner : SiteData} {rule : GrammarRule} {declaration : Nat}
    {parameterName : String}
    (declared : (rule, declaration) ∈ language.terms.zipIdx)
    (shape : rule.bareParams = [.simple parameterName (.collection kind elementType)])
    (permitted : kind ∈ permissions.collectionKinds)
    (typed : ElementsHaveType language free bound items elementType)
    (objects : isObjectPatternList items = true)
    (same : Presents kind items (value :: rest))
    (licensed : Licensed language free permissions bound elementType value inner) :
    Licensed language free permissions bound (.base rule.category)
      (.collection kind (value :: rest) none)
      (liftResidual (.authoredCollection declaration) kind rest inner) := by
  have source := licensed.source_eq
  unfold liftResidual
  rw [source]
  exact .authoredCollection declared shape permitted
    (presents_typed same typed) (presents_objects same objects) rfl licensed

/-- Every valid set or bag residual has a finite enumerated, licensed context
with the same source class and every same replacement class. -/
theorem direct_residual_coverage {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {elementType : TypeExpr} {kind : CollType} {items rest : List Pattern}
    {selected : Nat} {inner : SiteData}
    (unordered : kind ≠ .vec) (distinct : kind = .hashSet → items.Nodup)
    (within : selected < items.length)
    (permitted : kind ∈ permissions.collectionKinds)
    (typed : ElementsHaveType language free bound items elementType)
    (objects : isObjectPatternList items = true)
    (same : Presents kind items (items[selected] :: rest))
    (licensed : Licensed language free permissions bound elementType items[selected] inner) :
    ∃ actual ∈ kindResiduals kind items selected,
      Licensed language free permissions bound (.collection kind elementType)
        (.collection kind (items[selected] :: actual) none)
        (liftResidual (.directCollection kind) kind actual inner) ∧
      Same (.collection kind items none)
        ((liftResidual (.directCollection kind) kind actual inner).context.fill inner.focus) ∧
      ∀ replacement,
        Same ((liftResidual (.directCollection kind) kind actual inner).context.fill replacement)
          ((liftResidual (.directCollection kind) kind rest inner).context.fill replacement) := by
  obtain ⟨actual, member, equal⟩ :=
    (residuals_present_exact unordered distinct within).mpr same
  have reconstructs :=
    (residuals_present_exact unordered distinct within).mp
      ⟨actual, member, Presents.of_eq rfl⟩
  refine ⟨actual, member, licensed_direct_residual permitted typed objects reconstructs licensed, ?_, ?_⟩
  · rw [liftResidual_fill, licensed.source_eq]
    exact canon_collection_of_presents kind none (reconstructs.map canon)
  · intro replacement
    rw [liftResidual_fill, liftResidual_fill]
    exact canon_collection_of_presents kind none ((presents_cons equal _).map canon)

/-- The same finite residual enumeration preserves an authored collection
constructor's declaration identity and result sort. -/
theorem authored_residual_coverage {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {elementType : TypeExpr} {kind : CollType} {items rest : List Pattern}
    {selected : Nat} {inner : SiteData} {rule : GrammarRule} {declaration : Nat}
    {parameterName : String}
    (declared : (rule, declaration) ∈ language.terms.zipIdx)
    (shape : rule.bareParams = [.simple parameterName (.collection kind elementType)])
    (unordered : kind ≠ .vec) (distinct : kind = .hashSet → items.Nodup)
    (within : selected < items.length)
    (permitted : kind ∈ permissions.collectionKinds)
    (typed : ElementsHaveType language free bound items elementType)
    (objects : isObjectPatternList items = true)
    (same : Presents kind items (items[selected] :: rest))
    (licensed : Licensed language free permissions bound elementType items[selected] inner) :
    ∃ actual ∈ kindResiduals kind items selected,
      Licensed language free permissions bound (.base rule.category)
        (.collection kind (items[selected] :: actual) none)
        (liftResidual (.authoredCollection declaration) kind actual inner) ∧
      Same (.collection kind items none)
        ((liftResidual (.authoredCollection declaration) kind actual inner).context.fill inner.focus) ∧
      ∀ replacement,
        Same ((liftResidual (.authoredCollection declaration) kind actual inner).context.fill replacement)
          ((liftResidual (.authoredCollection declaration) kind rest inner).context.fill replacement) := by
  obtain ⟨actual, member, equal⟩ :=
    (residuals_present_exact unordered distinct within).mpr same
  have reconstructs :=
    (residuals_present_exact unordered distinct within).mp
      ⟨actual, member, Presents.of_eq rfl⟩
  refine ⟨actual, member,
    licensed_authored_residual declared shape permitted typed objects reconstructs licensed, ?_, ?_⟩
  · rw [liftResidual_fill, licensed.source_eq]
    exact canon_collection_of_presents kind none (reconstructs.map canon)
  · intro replacement
    rw [liftResidual_fill, liftResidual_fill]
    exact canon_collection_of_presents kind none ((presents_cons equal _).map canon)

/-- The executable direct-site family covers every semantic residual class. -/
theorem direct_site_coverage {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {elementType : TypeExpr} {kind : CollType} {items rest : List Pattern}
    {selected : Nat} {inner : SiteData}
    (unordered : kind ≠ .vec) (distinct : kind = .hashSet → items.Nodup)
    (within : selected < items.length)
    (permitted : kind ∈ permissions.collectionKinds)
    (typed : ElementsHaveType language free bound items elementType)
    (objects : isObjectPatternList items = true)
    (same : Presents kind items (items[selected] :: rest))
    (licensed : Licensed language free permissions bound elementType items[selected] inner) :
    ∃ site ∈ residualSites (.directCollection kind) kind items selected inner,
      Licensed language free permissions bound (.collection kind elementType)
        (site.context.fill inner.focus) site ∧
      Same (.collection kind items none) (site.context.fill inner.focus) ∧
      ∀ replacement,
        Same (site.context.fill replacement)
          ((liftResidual (.directCollection kind) kind rest inner).context.fill replacement) := by
  obtain ⟨actual, member, licensed', source, replacements⟩ :=
    direct_residual_coverage unordered distinct within permitted typed objects same licensed
  refine ⟨liftResidual (.directCollection kind) kind actual inner,
    (mem_residualSites).mpr ⟨actual, member, rfl⟩, ?_, source, replacements⟩
  simpa [liftResidual_fill, licensed.source_eq] using licensed'

/-- The executable authored-site family has the same coverage while retaining
the exact constructor declaration. -/
theorem authored_site_coverage {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {elementType : TypeExpr} {kind : CollType} {items rest : List Pattern}
    {selected : Nat} {inner : SiteData} {rule : GrammarRule} {declaration : Nat}
    {parameterName : String}
    (declared : (rule, declaration) ∈ language.terms.zipIdx)
    (shape : rule.bareParams = [.simple parameterName (.collection kind elementType)])
    (unordered : kind ≠ .vec) (distinct : kind = .hashSet → items.Nodup)
    (within : selected < items.length)
    (permitted : kind ∈ permissions.collectionKinds)
    (typed : ElementsHaveType language free bound items elementType)
    (objects : isObjectPatternList items = true)
    (same : Presents kind items (items[selected] :: rest))
    (licensed : Licensed language free permissions bound elementType items[selected] inner) :
    ∃ site ∈ residualSites (.authoredCollection declaration) kind items selected inner,
      Licensed language free permissions bound (.base rule.category)
        (site.context.fill inner.focus) site ∧
      Same (.collection kind items none) (site.context.fill inner.focus) ∧
      ∀ replacement,
        Same (site.context.fill replacement)
          ((liftResidual (.authoredCollection declaration) kind rest inner).context.fill replacement) := by
  obtain ⟨actual, member, licensed', source, replacements⟩ :=
    authored_residual_coverage declared shape unordered distinct within permitted typed objects same licensed
  refine ⟨liftResidual (.authoredCollection declaration) kind actual inner,
    (mem_residualSites).mpr ⟨actual, member, rfl⟩, ?_, source, replacements⟩
  simpa [liftResidual_fill, licensed.source_eq] using licensed'

end Mettapedia.OSLF.MeTTaIL.CollectionSelection
