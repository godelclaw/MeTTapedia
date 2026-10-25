import Mettapedia.OSLF.MeTTaIL.LawNormalTyping
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Forward typing and bare readback have different domains

The supplied law list removes a unit inside a named collection argument and
keeps that argument's type and wrapper. Its forward typing interface is
available even though the language has no bare carrier. The stricter witness
needed to insert bare collections is unavailable. These are typing controls;
the compiler's declared-law extraction still excludes this wrapped row.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls

open Syntax CollectionLaws
open Mettapedia.GSLT.LanguageDef.WellSorted

def atom (label : String) : GrammarRule :=
  { label, category := "Token", params := [], syntaxPattern := [] }

def wrapper : GrammarRule :=
  { label := "Wrapped", category := "Token",
    params := [.simple "items" (.collection .hashBag (.base "Token"))],
    syntaxPattern := [], collectionRepresentation := .wrapped,
    algebra? := some { flatten := true, unit := some "Zero" } }

def language : LanguageDef :=
  LanguageDef.ofCore "WrappedLawTyping" ["Token"] [atom "Zero",atom "A",wrapper] [] []

def laws : List Laws := [⟨.hashBag,some "Zero"⟩]

theorem forward_admission : LawsTyped laws language FreeTypeContext.empty where
  homogeneous law kind found rule member name element parameters := by
    simp only [language, LanguageDef.ofCore, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp_all [atom, wrapper]
  parameters rule member parameter parameterMember type typed := by
    simp only [language, LanguageDef.ofCore, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [atom] at parameterMember
    · simp [atom] at parameterMember
    · have shape : parameter = .simple "items" (.collection .hashBag (.base "Token")) := by
        simpa [wrapper] using parameterMember
      subst parameter
      simp only [parameterType?, Option.some.injEq] at typed
      subst type
      exact ⟨trivial, fun _ _ _ same => by cases same⟩
  freeNames name type found := by simp [FreeTypeContext.empty] at found

def subject : Pattern :=
  .apply "Wrapped" [.collection .hashBag [.apply "Zero" [],.apply "A" []] none]

theorem subject_typed : HasType language FreeTypeContext.empty [] subject (.base "Token") :=
  checkHasType_sound (by decide)

theorem normalized_changes_content : normalize laws subject =
    .apply "Wrapped" [.collection .hashBag [.apply "A" []] none] := by
  simp [normalize, laws, subject, splice]

theorem normalized_stays_typed :
    HasType language FreeTypeContext.empty [] (normalize laws subject) (.base "Token") :=
  normalize_hasType forward_admission subject (by simp) trivial (by decide) subject_typed

theorem no_bare_carrier :
    ¬ ∃ rule ∈ language.terms, ∃ name,
      rule.bareParams = [.simple name (.collection .hashBag (.base rule.category))] := by
  rintro ⟨rule, member, name, shape⟩
  simp only [language, LanguageDef.ofCore, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [GrammarRule.bareParams, atom, wrapper] at shape

theorem no_strict_collection_license :
    ¬ LawTypeOk laws language (.collection .hashBag (.base "Token")) := by
  intro license
  obtain ⟨rule, member, name, shape, _⟩ := license.lawful
    (law := ⟨.hashBag,some "Zero"⟩) (by decide)
  exact no_bare_carrier ⟨rule,member,name,shape⟩

theorem forward_admission_does_not_supply_readback :
    ¬ LawsTypedStrict laws language FreeTypeContext.empty := by
  intro strict
  apply no_strict_collection_license
  exact strict.parameters wrapper (by simp [language, LanguageDef.ofCore])
    (.simple "items" (.collection .hashBag (.base "Token"))) (by simp [wrapper]) _ rfl

#guard (CollectionLaws.declared language).isEmpty

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls
