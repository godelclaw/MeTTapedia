import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Profiles: named law bundles that extend a language

A profile adds declared laws to a `LanguageDef`. Laws change behavior, so a profile is never
applied silently: a language either names it or does not have it.

`collectionLaws` is the standard bundle: a bag or set constructor whose elements are its own
category flattens, so `{P, {Q, R}}` and `{P, Q, R}` are the same term, and an empty nested
collection disappears. It declares nothing else, and it leaves every authored law it finds
in place.

Positive control: Ambient's parallel bag `PPar . ps:HashBag(Proc)` gains flattening.
Negative controls: a vector constructor, a bag of another category, and a constructor that
already declares its algebra are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.LanguageProfiles

open Syntax

/-- The flattening law for one constructor, when it is a self-nested bag or set. -/
def withCollectionLaw (rule : GrammarRule) : GrammarRule :=
  match rule.params, rule.algebra? with
  | [.simple _ (.collection kind (.base element))], none =>
      if kind != .vec && element == rule.category then { rule with algebra? := some ⟨true, none⟩ } else rule
  | _, _ => rule

/-- **The standard collection-laws profile.** -/
def collectionLaws (language : LanguageDef) : LanguageDef :=
  { language with terms := language.terms.map withCollectionLaw }

/-- The profile changes only collection algebra declarations. -/
theorem collectionLaws_same_rules (language : LanguageDef) :
    (collectionLaws language).rewrites = language.rewrites ∧
      (collectionLaws language).equations = language.equations ∧
      (collectionLaws language).types = language.types ∧
      (collectionLaws language).terms.map (·.label) = language.terms.map (·.label) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [collectionLaws, List.map_map]
  congr 1
  funext rule
  show (withCollectionLaw rule).label = rule.label
  unfold withCollectionLaw
  split <;> (try split) <;> rfl

private def bagRule : GrammarRule :=
  { label := "PPar", category := "Proc", params := [.simple "ps" (.collection .hashBag (.base "Proc"))],
    syntaxPattern := [] }

#guard (withCollectionLaw bagRule).algebra? == some ⟨true, none⟩
#guard (withCollectionLaw { bagRule with params := [.simple "ps" (.collection .vec (.base "Proc"))] }).algebra? == none
#guard (withCollectionLaw { bagRule with params := [.simple "ps" (.collection .hashBag (.base "Name"))] }).algebra? == none
#guard (withCollectionLaw { bagRule with algebra? := some ⟨true, some "PZero"⟩ }).algebra? == some ⟨true, some "PZero"⟩

end Mettapedia.OSLF.MeTTaIL.LanguageProfiles
