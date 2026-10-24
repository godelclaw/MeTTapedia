import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
/-! # Constructor-preserving collection representations

Sharing a collection carrier does not identify two authored operations.
The actual declaration pass retains their labels. Named declarations are
excluded from bare lowering, so different labels remain different after
recursive collection unwrapping. This does not establish full algebraic
or binder-lowering adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.CoreReduction

theorem shared_collection_label_retained (language : LanguageDef) (first second : GrammarRule)
    (kind : CollType) (firstMember : first ∈ language.terms) (secondMember : second ∈ language.terms)
    (different : first.label ≠ second.label)
    (firstKind : collectionParameterKind first = some kind)
    (secondKind : collectionParameterKind second = some kind) :
    { first with collectionRepresentation := .wrapped } ∈
      (retainSharedCollectionLabels language).terms := by
  have shared : (language.terms.any fun other =>
      other.label != first.label && collectionParameterKind other == some kind) = true := by
    exact List.any_eq_true.mpr ⟨second, secondMember, by simp [Ne.symm different, secondKind]⟩
  apply List.mem_map.mpr
  refine ⟨first, firstMember, ?_⟩
  simp only [firstKind, shared, ite_true]

theorem retained_collection_labels (language : LanguageDef) :
    (retainSharedCollectionLabels language).terms.map (·.label) = language.terms.map (·.label) := by
  simp only [retainSharedCollectionLabels, List.map_map]
  apply List.map_congr_left
  intro rule _
  cases shape : collectionParameterKind rule <;> simp [shape]
  split <;> rfl

theorem wrapped_label_not_bare (language : LanguageDef) (label : String)
    (wrapped : ∀ rule ∈ language.terms, rule.label = label →
      rule.collectionRepresentation = .wrapped) :
    (bareLabels language).lookup label = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  obtain ⟨rule, ruleMember, produced⟩ := List.mem_filterMap.mp member
  split at produced
  · cases Option.some.inj produced
    simp only [bne_iff_ne]
    intro same
    have mode := wrapped rule ruleMember same.symm
    rename_i parameter kind element shape
    simp [mode] at shape
  · cases produced

theorem unwrap_keeps_named_application (bare : List (String × CollType))
    (label : String) (arguments : List Pattern) (named : bare.lookup label = none) :
    unwrap bare (.apply label arguments) = .apply label (arguments.map (unwrap bare)) := by
  rw [unwrap, named]

theorem unwrap_distinguishes_named_constructors (bare : List (String × CollType))
    (first second : String) (firstArguments secondArguments : List Pattern)
    (firstNamed : bare.lookup first = none) (secondNamed : bare.lookup second = none)
    (different : first ≠ second) :
    unwrap bare (.apply first firstArguments) ≠ unwrap bare (.apply second secondArguments) := by
  rw [unwrap_keeps_named_application bare first firstArguments firstNamed,
    unwrap_keeps_named_application bare second secondArguments secondNamed]
  intro equality
  exact different (Pattern.apply.inj equality).1
end Mettapedia.GSLT.LanguageDef.ModuleSource
