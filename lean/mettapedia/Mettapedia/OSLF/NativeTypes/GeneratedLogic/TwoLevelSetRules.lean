import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HereditarySets

/-!
# Set rules that look inside members

A flat set rule matches members by metavariables or closed terms (`FlatSetLanguage`). A **two-level** rule may also
match a member by a set pattern of flat elements, as in `{ {x, ...r}, ...s } ⇒ ...`. Under the set laws a member may
be presented with copies of its own members, so a rule can fire at presentations that the canonical form does not
show. Canonical regions still decide such languages: a step from any presentation is matched by one listed at a
presentation whose members are written up to `bound` times, each copy canonical or with copies of its own members
(`twoLevel_coherent`, `twoLevelForms`).

- **Matching is invariant under permuting the subject's list** (`matchBagRel_perm`, `matchBagRel_perm_none`): the
  element captures stay, and a rest captures the remaining members in another order, which presents the same
  collection.
- **A flat set pattern matched at any presentation is matched at a listed presentation with copies**
  (`copies_transfer`), the inner step of flat coherence, used as the partner of a member matched by a set pattern.
- **Captured names** (`patternNames`, `captured_names`, `bag_nodup`): a match captures only the pattern's names, and
  distinct names when the pattern's names are distinct. With distinct names, merging never compares captures
  (`mergeBindings_disjoint`).
- **The match moves to listed partners** (`twoLevel_transfer`): each element's match moves to a listed presentation
  of its member (`element_transfer`), and the rest to one canonical copy of each remaining member.
- **Grouping** (`twoLevelPresentations`, `perm_groups`): the partners and the copies, grouped by member, form a listed
  presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchBagRel)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon Same Unordered arrange_perm canon_collection)

/-- Entries alike: the same name, the same entry away from the rest's name, and values presenting the same term. -/
def EntryAlike (name : String) (a b : String × Pattern) : Prop :=
  a.1 = b.1 ∧ (a.1 ≠ name → a = b) ∧ Same a.2 b.2

theorem entryAlike_refl (name : String) (a : String × Pattern) : EntryAlike name a a := ⟨rfl, fun _ => rfl, rfl⟩

theorem names_alike {name : String} : ∀ {acc acc' : Bindings}, List.Forall₂ (EntryAlike name) acc acc' →
    acc.map Prod.fst = acc'.map Prod.fst
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons alike rest => by rw [List.map_cons, List.map_cons, alike.1, names_alike rest]

theorem find?_alike {name x : String} (differ : x ≠ name) : ∀ {acc acc' : Bindings},
    List.Forall₂ (EntryAlike name) acc acc' →
      acc.find? (fun item => item.1 == x) = acc'.find? (fun item => item.1 == x)
  | [], [], .nil => rfl
  | a :: acc, a' :: acc', .cons alike rest => by
    by_cases hit : a.1 = x
    · have equal : a = a' := alike.2.1 (hit ▸ differ)
      subst equal
      simp [hit]
    · have hit' : a'.1 ≠ x := alike.1 ▸ hit
      rw [List.find?_cons, List.find?_cons, beq_false_of_ne hit, beq_false_of_ne hit']
      exact find?_alike differ rest

theorem find?_none_alike {name x : String} {acc acc' : Bindings} (alike : List.Forall₂ (EntryAlike name) acc acc')
    (absent : acc.find? (fun item => item.1 == x) = none) : acc'.find? (fun item => item.1 == x) = none := by
  rw [List.find?_eq_none] at absent ⊢
  intro entry member hit
  have inNames : entry.1 ∈ acc.map Prod.fst := by
    rw [names_alike alike]
    exact List.mem_map_of_mem member
  obtain ⟨original, originalMember, sameName⟩ := List.mem_map.mp inNames
  exact absent original originalMember (by simpa [sameName] using hit)

/-- No two entries carry the name. -/
def OnceNamed (name : String) (bindings : Bindings) : Prop := bindings.Pairwise fun a b => ¬ (a.1 = name ∧ b.1 = name)

/-- **Merging alike bindings**: merging into alike accumulators gives alike results, when the rest's name enters at
most once and never meets an accumulated entry of its name. -/
theorem mergeBindings_alike {name : String} : ∀ (second second' acc acc' : Bindings) {result : Bindings},
    List.Forall₂ (EntryAlike name) acc acc' → List.Forall₂ (EntryAlike name) second second' →
    ((∃ entry ∈ acc, entry.1 = name) → ∀ entry ∈ second, entry.1 ≠ name) →
    OnceNamed name second → mergeBindings acc second = some result →
      ∃ result', mergeBindings acc' second' = some result' ∧ List.Forall₂ (EntryAlike name) result result'
  | [], [], acc, acc', result, accAlike, .nil, _, _, merged => by
    simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at merged ⊢
    subst merged
    exact ⟨acc', rfl, accAlike⟩
  | entry :: entries, entry' :: entries', acc, acc', result, accAlike, .cons alike tail, fresh, once, merged => by
    rw [mergeBindings_cons] at merged
    rw [mergeBindings_cons]
    obtain ⟨headOnce, tailOnce⟩ := List.pairwise_cons.mp once
    by_cases isName : entry.1 = name
    · have accNone : acc.find? (fun item => item.1 == entry.1) = none := by
        rw [List.find?_eq_none]
        intro other member hit
        exact fresh ⟨other, member, by simpa [isName] using hit⟩ entry List.mem_cons_self isName
      have accNone' : acc'.find? (fun item => item.1 == entry'.1) = none := by
        rw [← alike.1]
        exact find?_none_alike accAlike accNone
      rw [accNone] at merged
      rw [accNone']
      simp only [Option.bind_some] at merged ⊢
      exact mergeBindings_alike entries entries' (entry :: acc) (entry' :: acc') (.cons alike accAlike) tail
        (fun _ other member named => headOnce other member ⟨isName, named⟩) tailOnce merged
    · have equal : entry = entry' := alike.2.1 isName
      subst equal
      have freshTail : (∃ other ∈ entry :: acc, other.1 = name) → ∀ other ∈ entries, other.1 ≠ name := by
        rintro ⟨other, member, hit⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact absurd hit isName
        · exact fun third inside => fresh ⟨other, member, hit⟩ third (List.mem_cons_of_mem _ inside)
      rw [find?_alike isName accAlike] at merged
      cases found : acc'.find? (fun item => item.1 == entry.1) with
      | none =>
        rw [found] at merged
        simp only [Option.bind_some] at merged ⊢
        exact mergeBindings_alike entries entries' (entry :: acc) (entry :: acc') (.cons (entryAlike_refl name entry) accAlike)
          tail freshTail tailOnce merged
      | some hit =>
        rw [found] at merged
        obtain ⟨hitName, hitValue⟩ := hit
        by_cases agree : hitValue = entry.2
        · simp only [agree, beq_self_eq_true, if_true, Option.bind_some] at merged ⊢
          exact mergeBindings_alike entries entries' acc acc' accAlike tail
            (fun hasName other member => fresh hasName other (List.mem_cons_of_mem _ member)) tailOnce merged
        · simp [agree] at merged

theorem onceNamed_of_fresh {name : String} : ∀ {bindings : Bindings}, (∀ entry ∈ bindings, entry.1 ≠ name) →
    OnceNamed name bindings
  | [], _ => List.Pairwise.nil
  | entry :: _, fresh => List.pairwise_cons.mpr
    ⟨fun _ _ both => fresh entry List.mem_cons_self both.1,
      onceNamed_of_fresh fun other member => fresh other (List.mem_cons_of_mem _ member)⟩

/-- **Merging keeps the rest's name at most once**, when an accumulated entry of its name meets none in what is merged. -/
theorem mergeBindings_once {name : String} : ∀ (second acc : Bindings) {result : Bindings},
    OnceNamed name acc → OnceNamed name second →
    ((∃ entry ∈ acc, entry.1 = name) → ∀ entry ∈ second, entry.1 ≠ name) →
    mergeBindings acc second = some result → OnceNamed name result
  | [], acc, result, accOnce, _, _, merged => by
    simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at merged
    subst merged
    exact accOnce
  | entry :: entries, acc, result, accOnce, once, fresh, merged => by
    rw [mergeBindings_cons] at merged
    obtain ⟨headOnce, tailOnce⟩ := List.pairwise_cons.mp once
    cases found : acc.find? (fun item => item.1 == entry.1) with
    | none =>
      rw [found] at merged
      simp only [Option.bind_some] at merged
      refine mergeBindings_once entries (entry :: acc) (List.pairwise_cons.mpr ⟨fun other member both => ?_, accOnce⟩)
        tailOnce ?_ merged
      · exact fresh ⟨other, member, both.2⟩ entry List.mem_cons_self both.1
      · rintro ⟨other, member, named⟩ third inside thirdNamed
        rcases List.mem_cons.mp member with rfl | member
        · exact headOnce third inside ⟨named, thirdNamed⟩
        · exact fresh ⟨other, member, named⟩ third (List.mem_cons_of_mem _ inside) thirdNamed
    | some hit =>
      rw [found] at merged
      obtain ⟨hitName, hitValue⟩ := hit
      by_cases agree : hitValue = entry.2
      · simp only [agree, beq_self_eq_true, if_true, Option.bind_some] at merged
        exact mergeBindings_once entries acc accOnce tailOnce
          (fun hasName other member => fresh hasName other (List.mem_cons_of_mem _ member)) merged
      · simp [agree] at merged

/-- **A bag or set match transfers to every permutation of the subject's list**: the element captures stay, and the
rest captures the remaining members in another order. The rest's name is captured once. -/
theorem matchBagRel_perm {kind : CollType} (unordered : Unordered kind = true) {name : String} :
    ∀ {patterns : List Pattern} {terms : List Pattern} {bindings : Bindings},
      MatchBagRel patterns (some name) kind terms bindings →
      (∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, MatchRel pattern term captured →
        ∀ entry ∈ captured, entry.1 ≠ name) →
      OnceNamed name bindings ∧ ∀ {terms' : List Pattern}, terms.Perm terms' →
        ∃ bindings', MatchBagRel patterns (some name) kind terms' bindings' ∧
          List.Forall₂ (EntryAlike name) bindings bindings'
  | [], terms, _, .nilRest, _ => by
    refine ⟨List.pairwise_singleton _ _, fun {terms'} permutation => ⟨_, .nilRest, .cons ⟨rfl, fun differ => absurd rfl differ, ?_⟩ .nil⟩⟩
    change canon (.collection kind terms none) = canon (.collection kind terms' none)
    rw [canon_collection, canon_collection, arrange_perm unordered (permutation.map canon)]
  | pattern :: patterns, terms, bindings, .cons index bound head tail merged, fresh => by
    rename_i headBindings tailBindings
    obtain ⟨tailOnce, tailPerm⟩ := matchBagRel_perm unordered tail
      (fun other member => fresh other (List.mem_cons_of_mem _ member))
    have headFresh : ∀ entry ∈ headBindings, entry.1 ≠ name := fresh pattern List.mem_cons_self head
    have noHeadName : ¬ ∃ entry ∈ headBindings, entry.1 = name :=
      fun ⟨entry, member, named⟩ => headFresh entry member named
    refine ⟨mergeBindings_once tailBindings headBindings (onceNamed_of_fresh headFresh) tailOnce
      (fun has => absurd has noHeadName) merged, fun {terms'} permutation => ?_⟩
    have member : terms[index] ∈ terms' := permutation.subset (List.getElem_mem bound)
    obtain ⟨partner, partnerBound, partnerIs⟩ := List.getElem_of_mem member
    have remainder : (terms.eraseIdx index).Perm (terms'.eraseIdx partner) :=
      (List.perm_eraseIdx_of_getElem?_eq (by
        rw [List.getElem?_eq_getElem bound, List.getElem?_eq_getElem partnerBound, partnerIs])).mpr permutation
    obtain ⟨tailBindings', tail', tailAlike⟩ := tailPerm remainder
    obtain ⟨bindings', merged', alike⟩ := mergeBindings_alike tailBindings tailBindings' headBindings headBindings
      (List.forall₂_same.mpr fun entry _ => entryAlike_refl name entry) tailAlike (fun has => absurd has noHeadName)
      tailOnce merged
    exact ⟨bindings', .cons partner partnerBound (partnerIs ▸ head) tail' merged', alike⟩


/-! ## A flat set pattern matched at any presentation is matched at a listed presentation with copies -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (arrange arrange_mem canon_idempotent arrange_eq_of_presents)

/-- **A flat set pattern matched at any presentation of a hereditary set is matched, with like captures, at a
presentation with copies of its canonical form.** This is the inner step of coherence for flat set languages, and
the partner of a nested set pattern. -/
theorem copies_transfer {language : LanguageDef} {sort : String} {width : ℕ} {patterns : List Pattern}
    {rest : Option String} {terms : List Pattern} {bindings : Bindings}
    (flat : ∀ pattern ∈ patterns, FlatElement language sort rest pattern) (short : patterns.length ≤ width)
    (termsHold : ∀ term ∈ terms, Hereditary language sort term) (bag : MatchBagRel patterns rest .hashSet terms bindings) :
    ∃ shown ∈ copiesPresentations width (set (arrange .hashSet (terms.map BagForms.sortBags))), ∃ bindings',
      MatchRel (.collection .hashSet patterns rest) shown bindings' ∧ BagForms.BindingsSame bindings bindings' ∧
        CanonicalCaptures rest bindings' := by
  let values := arrange .hashSet (terms.map BagForms.sortBags)
  have distinct : values.Nodup := List.nodup_dedup _
  have valuesCanonical : ∀ value ∈ values, BagForms.sortBags value = value := fun value member => by
    obtain ⟨original, -, rfl⟩ := List.mem_map.mp ((arrange_mem value).mp member)
    rw [BagForms.sortBags_eq_canon, canon_idempotent]
  let extra := fun value => (if (terms.map BagForms.sortBags).count value ≤ patterns.length then
    (terms.map BagForms.sortBags).count value else patterns.length + 1) - 1
  let copies := values.flatMap fun value => List.replicate (extra value) value
  have othersCanonical : ∀ other ∈ values ++ copies, BagForms.sortBags other = other := by
    intro other member
    rcases List.mem_append.mp member with inValues | inCopies
    · exact valuesCanonical other inValues
    · obtain ⟨value, inValues, inReplicate⟩ := List.mem_flatMap.mp inCopies
      rw [List.eq_of_mem_replicate inReplicate]
      exact valuesCanonical value inValues
  have covers : Covers patterns.length terms (values ++ copies) := by
    intro value
    rw [List.count_append, count_copies extra values distinct value, distinct.count]
    have inValues : value ∈ values ↔ 0 < (terms.map BagForms.sortBags).count value := by
      rw [arrange_mem, List.count_pos_iff]
    by_cases member : value ∈ values
    · have positive := inValues.mp member
      simp only [member, if_true, extra]
      constructor
      · intro small
        simp only [small, if_true]
        omega
      · intro large
        simp only [show ¬ (terms.map BagForms.sortBags).count value ≤ patterns.length by omega, if_false]
        omega
    · have zero : (terms.map BagForms.sortBags).count value = 0 := by
        by_contra nonzero
        exact member (inValues.mpr (by omega))
      simp only [member, if_false, zero]
      exact ⟨fun _ => trivial, fun impossible => absurd impossible (Nat.not_lt_zero _)⟩
  obtain ⟨bindings', bag', sameBindings, captures⟩ := flat_transfer patterns rest terms (values ++ copies) bindings flat
    termsHold othersCanonical covers bag
  refine ⟨.collection .hashSet (values ++ copies) none, ?_, bindings', .collection (by decide) bag', sameBindings,
    captures⟩
  simp only [set, copiesPresentations, List.mem_map]
  exact ⟨copies, mem_copyChoices width extra (fun value => by simp only [extra]; split <;> omega) values, rfl⟩


/-! ## Merging bindings with disjoint names -/

theorem names_same : ∀ {left right : Bindings}, BagForms.BindingsSame left right →
    left.map Prod.fst = right.map Prod.fst
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons heads rest => by rw [List.map_cons, List.map_cons, heads.1, names_same rest]

/-- **Merging captures under disjoint names never compares them**: it succeeds, and like captures merge to like
results. -/
theorem mergeBindings_disjoint : ∀ (second second' acc acc' : Bindings), BagForms.BindingsSame acc acc' →
    BagForms.BindingsSame second second' → (∀ a ∈ acc, ∀ b ∈ second, a.1 ≠ b.1) → (second.map Prod.fst).Nodup →
      ∃ result result', mergeBindings acc second = some result ∧ mergeBindings acc' second' = some result' ∧
        BagForms.BindingsSame result result'
  | [], [], acc, acc', accSame, .nil, _, _ => ⟨acc, acc', rfl, rfl, accSame⟩
  | entry :: entries, entry' :: entries', acc, acc', accSame, .cons heads tail, disjoint, distinct => by
    rw [mergeBindings_cons, mergeBindings_cons]
    have absent : acc.find? (fun item => item.1 == entry.1) = none := by
      rw [List.find?_eq_none]
      intro other member hit
      exact disjoint other member entry List.mem_cons_self (by simpa using hit)
    have absent' : acc'.find? (fun item => item.1 == entry'.1) = none := by
      rw [List.find?_eq_none]
      intro other member hit
      obtain ⟨original, originalMember, sameName⟩ : ∃ original ∈ acc, original.1 = other.1 := by
        have inNames : other.1 ∈ acc'.map Prod.fst := List.mem_map_of_mem member
        rw [← names_same accSame] at inNames
        obtain ⟨original, originalMember, sameName⟩ := List.mem_map.mp inNames
        exact ⟨original, originalMember, sameName⟩
      exact disjoint original originalMember entry List.mem_cons_self (by
        rw [sameName, heads.1]
        simpa using hit)
    rw [absent, absent']
    simp only [Option.bind_some]
    obtain ⟨headFresh, tailDistinct⟩ := List.nodup_cons.mp distinct
    exact mergeBindings_disjoint entries entries' (entry :: acc) (entry' :: acc') (.cons heads accSame) tail
      (fun a aMember b bMember => by
        rcases List.mem_cons.mp aMember with rfl | aMember
        · exact fun same => headFresh (same ▸ List.mem_map_of_mem bMember)
        · exact disjoint a aMember b (List.mem_cons_of_mem _ bMember))
      tailDistinct


/-! ## The names a match captures -/

open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchArgsRel)

mutual
/-- The names a pattern can capture: its metavariables and the rests of its collections. -/
def patternNames : Pattern → List String
  | .fvar name => [name]
  | .bvar _ => []
  | .apply _ arguments => patternNamesList arguments
  | .lambda _ body => patternNames body
  | .multiLambda _ _ body => patternNames body
  | .subst body replacement => patternNames body ++ patternNames replacement
  | .collection _ elements rest => rest.toList ++ patternNamesList elements

/-- The names the patterns of a list can capture. -/
def patternNamesList : List Pattern → List String
  | [] => []
  | pattern :: patterns => patternNames pattern ++ patternNamesList patterns
end

theorem mem_of_mergeBindings : ∀ (second first : Bindings) {combined : Bindings},
    mergeBindings first second = some combined → ∀ entry ∈ combined, entry ∈ first ∨ entry ∈ second
  | [], first, combined, merged, entry, member => by
    simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at merged
    subst merged
    exact Or.inl member
  | head :: tail, first, combined, merged, entry, member => by
    rw [mergeBindings_cons] at merged
    cases found : first.find? (fun item => item.1 == head.1) with
    | none =>
      rw [found] at merged
      simp only [Option.bind_some] at merged
      rcases mem_of_mergeBindings tail (head :: first) merged entry member with inFirst | inTail
      · rcases List.mem_cons.mp inFirst with rfl | inFirst
        · exact Or.inr List.mem_cons_self
        · exact Or.inl inFirst
      · exact Or.inr (List.mem_cons_of_mem _ inTail)
    | some hit =>
      rw [found] at merged
      by_cases agree : hit.2 = head.2
      · simp only [agree, beq_self_eq_true, if_true, Option.bind_some] at merged
        rcases mem_of_mergeBindings tail first merged entry member with inFirst | inTail
        · exact Or.inl inFirst
        · exact Or.inr (List.mem_cons_of_mem _ inTail)
      · simp [agree] at merged

mutual
/-- **A match captures only the pattern's names.** -/
theorem captured_names : ∀ {pattern term : Pattern} {bindings : Bindings}, MatchRel pattern term bindings →
    ∀ entry ∈ bindings, entry.1 ∈ patternNames pattern
  | _, _, _, .fvar, entry, member => by
    rw [List.mem_singleton.mp member]
    exact List.mem_singleton_self _
  | _, _, _, .bvar, _, member => absurd member List.not_mem_nil
  | _, _, _, .apply arguments _, entry, member => captured_names_args arguments entry member
  | _, _, _, .lambda body, entry, member => captured_names body entry member
  | _, _, _, .multiLambda body, entry, member => captured_names body entry member
  | _, _, _, .collection _ bag, entry, member => captured_names_bag bag entry member
  | _, _, _, .vector arguments, entry, member => by
    simpa [patternNames] using captured_names_args arguments entry member
  | _, _, _, .vectorRest arguments merged, entry, member => by
    rcases mem_of_mergeBindings _ _ merged entry member with inPrefix | inRest
    · exact List.mem_append_right _ (captured_names_args arguments entry inPrefix)
    · rw [List.mem_singleton.mp inRest]
      exact List.mem_append_left _ (by simp)
  | _, _, _, .subst body replacement merged, entry, member => by
    rcases mem_of_mergeBindings _ _ merged entry member with inBody | inReplacement
    · exact List.mem_append_left _ (captured_names body entry inBody)
    · exact List.mem_append_right _ (captured_names replacement entry inReplacement)

theorem captured_names_args : ∀ {patterns terms : List Pattern} {bindings : Bindings},
    MatchArgsRel patterns terms bindings → ∀ entry ∈ bindings, entry.1 ∈ patternNamesList patterns
  | _, _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, _, .cons head tail merged, entry, member => by
    rcases mem_of_mergeBindings _ _ merged entry member with inHead | inTail
    · exact List.mem_append_left _ (captured_names head entry inHead)
    · exact List.mem_append_right _ (captured_names_args tail entry inTail)

theorem captured_names_bag : ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType}
    {terms : List Pattern} {bindings : Bindings}, MatchBagRel patterns rest kind terms bindings →
      ∀ entry ∈ bindings, entry.1 ∈ rest.toList ++ patternNamesList patterns
  | _, _, _, _, _, .nilNoRest, _, member => absurd member List.not_mem_nil
  | _, _, _, _, _, .nilRest, entry, member => by
    rw [List.mem_singleton.mp member]
    simp
  | _, _, _, _, _, .cons _ _ head tail merged, entry, member => by
    rcases mem_of_mergeBindings _ _ merged entry member with inHead | inTail
    · exact List.mem_append_right _ (List.mem_append_left _ (captured_names head entry inHead))
    · rcases List.mem_append.mp (captured_names_bag tail entry inTail) with inRest | inPatterns
      · exact List.mem_append_left _ inRest
      · exact List.mem_append_right _ (List.mem_append_right _ inPatterns)
end


/-! ## Distinct names -/

/-- **Merging captures under disjoint distinct names keeps them distinct.** -/
theorem mergeBindings_nodup : ∀ (second acc : Bindings) {combined : Bindings}, (acc.map Prod.fst).Nodup →
    (second.map Prod.fst).Nodup → (∀ a ∈ acc, ∀ b ∈ second, a.1 ≠ b.1) → mergeBindings acc second = some combined →
      (combined.map Prod.fst).Nodup
  | [], acc, combined, accDistinct, _, _, merged => by
    simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at merged
    subst merged
    exact accDistinct
  | entry :: entries, acc, combined, accDistinct, distinct, disjoint, merged => by
    rw [mergeBindings_cons] at merged
    have absent : acc.find? (fun item => item.1 == entry.1) = none := by
      rw [List.find?_eq_none]
      intro other member hit
      exact disjoint other member entry List.mem_cons_self (by simpa using hit)
    rw [absent] at merged
    simp only [Option.bind_some] at merged
    obtain ⟨headFresh, tailDistinct⟩ := List.nodup_cons.mp distinct
    refine mergeBindings_nodup entries (entry :: acc) ?_ tailDistinct ?_ merged
    · rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨fun inAcc => ?_, accDistinct⟩
      obtain ⟨other, member, same⟩ := List.mem_map.mp inAcc
      exact disjoint other member entry List.mem_cons_self same
    · intro a aMember b bMember
      rcases List.mem_cons.mp aMember with rfl | aMember
      · exact fun same => headFresh (same ▸ List.mem_map_of_mem bMember)
      · exact disjoint a aMember b (List.mem_cons_of_mem _ bMember)

/-- **A bag match of patterns that capture distinct names captures distinct names**, when the names of the
patterns and the rest are distinct. -/
theorem bag_nodup : ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType} {terms : List Pattern}
    {bindings : Bindings}, MatchBagRel patterns rest kind terms bindings →
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, MatchRel pattern term captured →
      (patternNames pattern).Nodup → (captured.map Prod.fst).Nodup) →
    (rest.toList ++ patternNamesList patterns).Nodup → (bindings.map Prod.fst).Nodup
  | _, _, _, _, _, .nilNoRest, _, _ => List.nodup_nil
  | _, _, _, _, _, .nilRest, _, _ => List.nodup_singleton _
  | pattern :: patterns, rest, _, _, _, .cons _index _bound head tail merged, each, distinct => by
    rename_i headBindings tailBindings
    have shape : (rest.toList ++ patternNamesList (pattern :: patterns)).Perm
        (patternNames pattern ++ (rest.toList ++ patternNamesList patterns)) := by
      simp only [patternNamesList]
      exact List.perm_append_comm_assoc _ _ _
    have distinct' := shape.nodup_iff.mp distinct
    obtain ⟨headNames, tailNames, apart⟩ := List.nodup_append.mp distinct'
    refine mergeBindings_nodup tailBindings headBindings (each pattern List.mem_cons_self head headNames)
      (bag_nodup tail (fun other member => each other (List.mem_cons_of_mem _ member)) tailNames) ?_ merged
    intro a aMember b bMember same
    exact apart _ (captured_names head a aMember) _ (captured_names_bag tail b bMember) same


/-! ## Two-level set rules -/

/-- Element patterns of a two-level set rule: metavariables, closed hereditary canonical terms, and set patterns of
at most `width` flat elements. -/
def TwoLevelElement (language : LanguageDef) (sort : String) (width : ℕ) (pattern : Pattern) : Prop :=
  (∃ name, pattern = .fvar name) ∨ (Hereditary language sort pattern ∧ BagForms.sortBags pattern = pattern) ∨
    ∃ elements inner, pattern = .collection .hashSet elements inner ∧ elements.length ≤ width ∧
      ∀ element ∈ elements, FlatElement language sort inner element

/-- The presentations of a member listed for a two-level rule: its canonical form and its presentations with copies. -/
def memberPresentations (width : ℕ) (value : Pattern) : List Pattern := value :: copiesPresentations width value

variable {language : LanguageDef} {sort : String} {width : ℕ}

theorem patternNamesList_nil : ∀ {values : List Pattern}, (∀ value ∈ values, patternNames value = []) →
    patternNamesList values = []
  | [], _ => rfl
  | head :: tail, each => by
    simp only [patternNamesList, List.append_eq_nil_iff]
    exact ⟨each head List.mem_cons_self, patternNamesList_nil fun other member => each other (List.mem_cons_of_mem _ member)⟩

theorem hereditary_names {pattern : Pattern} (holds : Hereditary language sort pattern) : patternNames pattern = [] := by
  induction holds with
  | atom _ => rfl
  | @members values _ ih =>
    show none.toList ++ patternNamesList values = []
    rw [Option.toList_none, List.nil_append]
    exact patternNamesList_nil ih

theorem flat_captures_distinct {rest : Option String} {pattern : Pattern} (flat : FlatElement language sort rest pattern)
    {term : Pattern} {captured : Bindings} (matched : MatchRel pattern term captured) :
    (captured.map Prod.fst).Nodup := by
  rcases flat with ⟨name, rfl, -⟩ | ⟨closed, -⟩
  · cases matched
    exact List.nodup_singleton _
  · have none : captured = [] := List.eq_nil_iff_forall_not_mem.mpr fun entry member => by
      have inNames := captured_names matched entry member
      rw [hereditary_names closed] at inNames
      exact absurd inNames List.not_mem_nil
    rw [none]
    exact List.nodup_nil

theorem twoLevel_captures_distinct {pattern : Pattern} (element : TwoLevelElement language sort width pattern)
    {term : Pattern} {captured : Bindings} (matched : MatchRel pattern term captured) (distinct : (patternNames pattern).Nodup) :
    (captured.map Prod.fst).Nodup := by
  rcases element with ⟨name, rfl⟩ | ⟨closed, canonical⟩ | ⟨elements, inner, rfl, -, flat⟩
  · cases matched
    exact List.nodup_singleton _
  · exact flat_captures_distinct (rest := none) (.inr ⟨closed, canonical⟩) matched
  · cases matched with
    | collection _ bag => exact bag_nodup bag (fun other member _ _ matched' _ =>
        flat_captures_distinct (flat other member) matched') distinct

/-- **An element's match moves to a listed presentation of the member**, with like captures. -/
theorem element_transfer {pattern term : Pattern} {bindings : Bindings} (element : TwoLevelElement language sort width pattern)
    (termHolds : Hereditary language sort term) (matched : MatchRel pattern term bindings) :
    ∃ partner ∈ memberPresentations width (BagForms.sortBags term), ∃ bindings',
      MatchRel pattern partner bindings' ∧ BagForms.BindingsSame bindings bindings' := by
  rcases element with ⟨name, rfl⟩ | ⟨closed, canonical⟩ | ⟨elements, inner, rfl, short, flat⟩
  · cases matched
    refine ⟨BagForms.sortBags term, List.mem_cons_self, [(name, BagForms.sortBags term)], .fvar, .cons ⟨rfl, ?_⟩ .nil⟩
    change canon term = canon (BagForms.sortBags term)
    rw [BagForms.sortBags_eq_canon, canon_idempotent]
  · obtain ⟨same, rfl⟩ := closed_match closed canonical termHolds matched
    refine ⟨BagForms.sortBags term, List.mem_cons_self, [], ?_, .nil⟩
    rw [same]
    exact match_self closed
  · rcases termHolds.cases with ⟨label, rfl, -⟩ | ⟨terms, rfl, termsHold⟩
    · cases matched
    · cases matched with
      | collection _ bag =>
        obtain ⟨shown, listed, bindings', matched', same, -⟩ := copies_transfer flat short termsHold bag
        refine ⟨shown, ?_, bindings', matched', same⟩
        rw [sortBags_set_values]
        exact List.mem_cons_of_mem _ listed


/-- **A set rule's match moves to listed partners of its elements, followed by any presentation of the remaining
members**, with like captures, when each element's match at a held member moves to a listed presentation of the member
and each element captures distinct names. The new captures have a property of entries (`good`) when the elements'
moved captures and the rest's capture of the remaining members' set have it. -/
theorem bag_transfer_with (presentationsOf : Pattern → List Pattern) (held : Pattern → Prop)
    (good : String × Pattern → Prop) :
    ∀ {patterns : List Pattern} {rest : Option String}
    {terms : List Pattern} {bindings : Bindings}, MatchBagRel patterns rest .hashSet terms bindings →
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, held term →
      MatchRel pattern term captured → ∃ partner ∈ presentationsOf (BagForms.sortBags term), ∃ captured',
        MatchRel pattern partner captured' ∧ BagForms.BindingsSame captured captured' ∧ ∀ entry ∈ captured', good entry) →
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, MatchRel pattern term captured →
      (patternNames pattern).Nodup → (captured.map Prod.fst).Nodup) →
    (∀ term ∈ terms, held term) → (rest.toList ++ patternNamesList patterns).Nodup →
    ∃ partners matched remaining : List Pattern, partners.length = patterns.length ∧
      List.Forall₂ (fun partner term => partner ∈ presentationsOf (BagForms.sortBags term)) partners matched ∧
      terms.Perm (matched ++ remaining) ∧ (rest = none → remaining = []) ∧
      ∀ extras : List Pattern, (rest = none → extras = []) →
        Same (.collection .hashSet remaining none) (.collection .hashSet extras none) →
        (∀ name, rest = some name → good (name, .collection .hashSet extras none)) →
        ∃ bindings', MatchBagRel patterns rest .hashSet (partners ++ extras) bindings' ∧
          BagForms.BindingsSame bindings bindings' ∧ ∀ entry ∈ bindings', good entry
  | _, _, _, _, .nilNoRest, _, _, _, _ =>
    ⟨[], [], [], rfl, .nil, List.Perm.refl _, fun _ => rfl,
      fun extras noExtras _ _ => by
        rw [noExtras rfl]
        exact ⟨[], .nilNoRest, .nil, fun _ member => absurd member List.not_mem_nil⟩⟩
  | _, _, terms, _, .nilRest, _, _, _, _ =>
    ⟨[], [], terms, rfl, .nil, List.Perm.refl _, (fun absurdity => nomatch absurdity),
      fun _ _ same goodRest => ⟨_, .nilRest, .cons ⟨rfl, same⟩ .nil, fun entry member => by
        rw [List.mem_singleton.mp member]
        exact goodRest _ rfl⟩⟩
  | pattern :: patterns, rest, terms, _, .cons _index bound head tail merged, transferOne, distinctOne, termsHold,
      distinct => by
    rename_i headBindings tailBindings
    have shape : (rest.toList ++ patternNamesList (pattern :: patterns)).Perm
        (patternNames pattern ++ (rest.toList ++ patternNamesList patterns)) := by
      simp only [patternNamesList]
      exact List.perm_append_comm_assoc _ _ _
    obtain ⟨headNames, tailNames, apart⟩ := List.nodup_append.mp (shape.nodup_iff.mp distinct)
    obtain ⟨partner, listed, headBindings', head', headSame, headGood⟩ :=
      transferOne pattern List.mem_cons_self (termsHold _ (List.getElem_mem bound)) head
    obtain ⟨partners, matched, remaining, length, partnersListed, split, noRemaining, transfer⟩ :=
      bag_transfer_with presentationsOf held good tail (fun other member => transferOne other (List.mem_cons_of_mem _ member))
        (fun other member => distinctOne other (List.mem_cons_of_mem _ member))
        (fun other member => termsHold other (List.mem_of_mem_eraseIdx member)) tailNames
    refine ⟨partner :: partners, terms[_index] :: matched, remaining,
      by rw [List.length_cons, length, List.length_cons], .cons listed partnersListed, ?_, noRemaining, ?_⟩
    · exact (List.getElem_cons_eraseIdx_perm bound).symm.trans (List.Perm.cons _ split)
    · intro extras noExtras same goodRest
      obtain ⟨tailBindings', tail', tailSame, tailGood⟩ := transfer extras noExtras same goodRest
      have tailDistinct := bag_nodup tail (fun other member _ _ matched distinctOther =>
        distinctOne other (List.mem_cons_of_mem _ member) matched distinctOther) tailNames
      obtain ⟨result, result', mergedAgain, merged', resultSame⟩ := mergeBindings_disjoint tailBindings tailBindings'
        headBindings headBindings' headSame tailSame
        (fun a aMember b bMember same' => apart _ (captured_names head a aMember) _ (captured_names_bag tail b bMember)
          same')
        tailDistinct
      rw [merged] at mergedAgain
      cases mergedAgain
      refine ⟨result', .cons 0 (Nat.succ_pos _) head' (by simpa using tail') merged', resultSame, fun entry member => ?_⟩
      rcases mem_of_mergeBindings _ _ merged' entry member with inHead | inTail
      · exact headGood entry inHead
      · exact tailGood entry inTail

/-- **A set rule's match moves to listed partners of its elements, followed by any presentation of the remaining
members**, with like captures, when each element's match moves to a listed presentation of its member and each
element captures distinct names. The new captures have a property of values (`good`) when the elements' moved captures
and the remaining members' set have it. -/
theorem bag_transfer (presentationsOf : Pattern → List Pattern) (good : Pattern → Prop) :
    ∀ {patterns : List Pattern} {rest : Option String}
    {terms : List Pattern} {bindings : Bindings}, MatchBagRel patterns rest .hashSet terms bindings →
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, Hereditary language sort term →
      MatchRel pattern term captured → ∃ partner ∈ presentationsOf (BagForms.sortBags term), ∃ captured',
        MatchRel pattern partner captured' ∧ BagForms.BindingsSame captured captured' ∧
          ∀ entry ∈ captured', good entry.2) →
    (∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, MatchRel pattern term captured →
      (patternNames pattern).Nodup → (captured.map Prod.fst).Nodup) →
    (∀ term ∈ terms, Hereditary language sort term) → (rest.toList ++ patternNamesList patterns).Nodup →
    ∃ partners matched remaining : List Pattern, partners.length = patterns.length ∧
      List.Forall₂ (fun partner term => partner ∈ presentationsOf (BagForms.sortBags term)) partners matched ∧
      terms.Perm (matched ++ remaining) ∧ (rest = none → remaining = []) ∧
      ∀ extras : List Pattern, (rest = none → extras = []) →
        Same (.collection .hashSet remaining none) (.collection .hashSet extras none) →
        good (.collection .hashSet extras none) →
        ∃ bindings', MatchBagRel patterns rest .hashSet (partners ++ extras) bindings' ∧
          BagForms.BindingsSame bindings bindings' ∧ ∀ entry ∈ bindings', good entry.2 := by
  intro patterns rest terms bindings bag transferOne distinctOne termsHold distinct
  obtain ⟨partners, matched, remaining, length, listed, split, noRemaining, transfer⟩ :=
    bag_transfer_with presentationsOf (Hereditary language sort) (fun entry => good entry.2) bag transferOne distinctOne
      termsHold distinct
  exact ⟨partners, matched, remaining, length, listed, split, noRemaining,
    fun extras noExtras same goodRest => transfer extras noExtras same fun _ _ => goodRest⟩

/-- **A two-level set rule's match moves to the listed partners of its elements, followed by any presentation of the
remaining members**, with like captures. -/
theorem twoLevel_transfer {patterns : List Pattern} {rest : Option String} {terms : List Pattern}
    {bindings : Bindings} (bag : MatchBagRel patterns rest .hashSet terms bindings)
    (elements : ∀ pattern ∈ patterns, TwoLevelElement language sort width pattern)
    (termsHold : ∀ term ∈ terms, Hereditary language sort term) (distinct : (rest.toList ++ patternNamesList patterns).Nodup) :
    ∃ partners matched remaining : List Pattern, partners.length = patterns.length ∧
      List.Forall₂ (fun partner term => partner ∈ memberPresentations width (BagForms.sortBags term)) partners matched ∧
      terms.Perm (matched ++ remaining) ∧ (rest = none → remaining = []) ∧
      ∀ extras : List Pattern, (rest = none → extras = []) →
        Same (.collection .hashSet remaining none) (.collection .hashSet extras none) →
        ∃ bindings', MatchBagRel patterns rest .hashSet (partners ++ extras) bindings' ∧
          BagForms.BindingsSame bindings bindings' :=
  (bag_transfer (memberPresentations width) (fun _ => True) bag
    (fun pattern member _ _ held matched => by
      obtain ⟨partner, listed, captured', matched', same⟩ := element_transfer (elements pattern member) held matched
      exact ⟨partner, listed, captured', matched', same, fun _ _ => trivial⟩)
    (fun pattern member _ _ matched names => twoLevel_captures_distinct (elements pattern member) matched names)
    termsHold distinct).imp fun _ ⟨matched, remaining, length, listed, split, noRemaining, transfer⟩ =>
      ⟨matched, remaining, length, listed, split, noRemaining, fun extras noExtras same => by
        obtain ⟨bindings', bag', sameBindings, -⟩ := transfer extras noExtras same trivial
        exact ⟨bindings', bag', sameBindings⟩⟩


/-- **A bag or set match with no rest transfers to every permutation of the subject's list**, with the same captures. -/
theorem matchBagRel_perm_none {kind : CollType} : ∀ {patterns terms : List Pattern} {bindings : Bindings},
    MatchBagRel patterns none kind terms bindings → ∀ {terms' : List Pattern}, terms.Perm terms' →
      MatchBagRel patterns none kind terms' bindings
  | _, _, _, .nilNoRest, _, permutation => by
    rw [List.perm_nil.mp permutation.symm]
    exact .nilNoRest
  | _, terms, _, .cons index bound head tail merged, terms', permutation => by
    have member : terms[index] ∈ terms' := permutation.subset (List.getElem_mem bound)
    obtain ⟨partner, partnerBound, partnerIs⟩ := List.getElem_of_mem member
    have remainder : (terms.eraseIdx index).Perm (terms'.eraseIdx partner) :=
      (List.perm_eraseIdx_of_getElem?_eq (by
        rw [List.getElem?_eq_getElem bound, List.getElem?_eq_getElem partnerBound, partnerIs])).mpr permutation
    exact .cons partner partnerBound (partnerIs ▸ head) (matchBagRel_perm_none tail remainder) merged


/-! ## The presentations listed for two-level set rules -/

theorem mem_of_mem_copyChoices {width : ℕ} : ∀ {values copies : List Pattern}, copies ∈ copyChoices width values →
    ∀ copy ∈ copies, copy ∈ values
  | [], copies, chosen, copy, member => by
    simp only [copyChoices, List.mem_singleton] at chosen
    subst chosen
    exact absurd member List.not_mem_nil
  | value :: values, copies, chosen, copy, member => by
    simp only [copyChoices, List.mem_flatMap, List.mem_map, List.mem_range] at chosen
    obtain ⟨rest, restChosen, count, -, rfl⟩ := chosen
    rcases List.mem_append.mp member with inReplicate | inRest
    · rw [List.eq_of_mem_replicate inReplicate]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_copyChoices restChosen copy inRest)

/-- **A listed presentation of a member presents it**: its canonical form is the member. -/
theorem memberPresentations_class {value shown : Pattern} (canonical : BagForms.sortBags value = value)
    (listed : shown ∈ memberPresentations width value) : BagForms.sortBags shown = value := by
  rcases List.mem_cons.mp listed with rfl | listed
  · exact canonical
  · cases value with
    | collection kind values rest =>
      cases kind <;> cases rest <;> simp only [copiesPresentations, List.mem_singleton, List.mem_map] at listed
      case hashSet.none =>
        obtain ⟨copies, chosen, rfl⟩ := listed
        have valuesArranged : arrange .hashSet (values.map BagForms.sortBags) = values := by
          have arranged := canonical
          rw [show Pattern.collection .hashSet values none = set values from rfl, sortBags_set_values] at arranged
          simpa [set] using arranged
        change BagForms.sortBags (set (values ++ copies)) = set values
        rw [sortBags_set_values]
        congr 1
        refine (arrange_eq_of_presents ?_).trans valuesArranged
        intro other
        simp only [List.map_append, List.mem_append]
        constructor
        · rintro (inValues | inCopies)
          · exact inValues
          · obtain ⟨copy, copyMember, rfl⟩ := List.mem_map.mp inCopies
            exact List.mem_map_of_mem (mem_of_mem_copyChoices chosen copy copyMember)
        · exact Or.inl
      all_goals (subst listed; exact canonical)
    | _ => simp only [copiesPresentations, List.mem_singleton] at listed; subst listed; exact canonical


/-- Lists of a length over the listed items. -/
def listsOf (items : List Pattern) : ℕ → List (List Pattern)
  | 0 => [[]]
  | n + 1 => items.flatMap fun item => (listsOf items n).map (item :: ·)

theorem mem_listsOf {items : List Pattern} : ∀ (members : List Pattern), (∀ member ∈ members, member ∈ items) →
    members ∈ listsOf items members.length
  | [], _ => List.mem_singleton_self _
  | head :: tail, inside => List.mem_flatMap.mpr ⟨head, inside head List.mem_cons_self,
      List.mem_map.mpr ⟨tail, mem_listsOf tail (fun other member => inside other (List.mem_cons_of_mem _ member)), rfl⟩⟩

/-- **Groups of listed presentations**: between one and `bound` of them. -/
def nestedGroups (bound : ℕ) (presentations : List Pattern) : List (List Pattern) :=
  (List.range bound).flatMap fun n => listsOf presentations (n + 1)

theorem mem_nestedGroups {presentations group : List Pattern} {bound : ℕ} (nonempty : group ≠ [])
    (short : group.length ≤ bound) (inside : ∀ member ∈ group, member ∈ presentations) :
    group ∈ nestedGroups bound presentations := by
  have positive := List.length_pos_iff.mpr nonempty
  refine List.mem_flatMap.mpr ⟨group.length - 1, List.mem_range.mpr (by omega), ?_⟩
  rw [show group.length - 1 + 1 = group.length by omega]
  exact mem_listsOf group inside

/-- The groups of a member: between one and `bound` of its listed presentations. -/
def groupChoices (width bound : ℕ) (value : Pattern) : List (List Pattern) :=
  nestedGroups bound (memberPresentations width value)

/-- Concatenations of one choice from each list of choices. -/
def chooseGroups : List (List (List Pattern)) → List (List Pattern)
  | [] => [[]]
  | groups :: rest => groups.flatMap fun group => (chooseGroups rest).map (group ++ ·)

theorem mem_chooseGroups : ∀ {choices : List (List (List Pattern))} {picked : List (List Pattern)},
    List.Forall₂ (· ∈ ·) picked choices → picked.flatten ∈ chooseGroups choices
  | [], [], .nil => List.mem_singleton_self _
  | _ :: _, group :: _, .cons member rest =>
    List.mem_flatMap.mpr ⟨group, member, List.mem_map.mpr ⟨_, mem_chooseGroups rest, rfl⟩⟩

/-- **The presentations listed for a two-level set language**: each member of a canonical set written between once
and `bound` times, each copy canonical or with copies of its own members. -/
def twoLevelPresentations (width bound : ℕ) : Pattern → List Pattern
  | .collection .hashSet values none =>
    (chooseGroups (values.map (groupChoices width bound))).map fun members => .collection .hashSet members none
  | other => [other]

/-- **Grouping a list by keys is a permutation of it**, when every element's key is listed once. -/
theorem perm_groups (key : Pattern → Pattern) : ∀ {keys : List Pattern} {list : List Pattern}, keys.Nodup →
    (∀ member ∈ list, key member ∈ keys) → list.Perm (keys.flatMap fun value => list.filter fun member => key member == value)
  | [], list, _, inside => by
    rw [List.eq_nil_iff_forall_not_mem.mpr fun member found => absurd (inside member found) List.not_mem_nil]
    rfl
  | value :: values, list, distinct, inside => by
    obtain ⟨fresh, valuesDistinct⟩ := List.nodup_cons.mp distinct
    rw [List.flatMap_cons]
    let others := list.filter fun member => !(key member == value)
    have split : list.Perm (list.filter (fun member => key member == value) ++ others) :=
      (List.filter_append_perm _ list).symm
    have othersInside : ∀ member ∈ others, key member ∈ values := by
      intro member found
      obtain ⟨original, differs⟩ := List.mem_filter.mp found
      rcases List.mem_cons.mp (inside member original) with same | inValues
      · simp [same] at differs
      · exact inValues
    refine split.trans (List.Perm.append_left _ ((perm_groups key valuesDistinct othersInside).trans ?_))
    refine List.Perm.of_eq (List.flatMap_congr fun other otherMember => ?_)
    rw [List.filter_filter]
    congr 1
    funext member
    by_cases hit : key member = other
    · have differs : key member ≠ value := fun same => fresh (same ▸ hit ▸ otherMember)
      simp [hit, show other ≠ value from hit ▸ differs]
    · simp [hit]


theorem mem_patternNamesList {name : String} : ∀ {patterns : List Pattern} {pattern : Pattern}, pattern ∈ patterns →
    name ∈ patternNames pattern → name ∈ patternNamesList patterns
  | _ :: _, _, .head _, inside => List.mem_append_left _ inside
  | _ :: _, _, .tail _ member, inside => List.mem_append_right _ (mem_patternNamesList member inside)

theorem bindingsSame_trans : ∀ {first second third : Bindings}, BagForms.BindingsSame first second →
    BagForms.BindingsSame second third → BagForms.BindingsSame first third
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons one oneRest, .cons two twoRest =>
    .cons ⟨one.1.trans two.1, one.2.trans two.2⟩ (bindingsSame_trans oneRest twoRest)

theorem bindingsSame_refl : ∀ (bindings : Bindings), BagForms.BindingsSame bindings bindings
  | [] => .nil
  | _ :: rest => .cons ⟨rfl, rfl⟩ (bindingsSame_refl rest)

theorem exists_left_of_forall₂ {α β : Type} {relation : α → β → Prop} : ∀ {left : List α} {right : List β},
    List.Forall₂ relation left right → ∀ b ∈ right, ∃ a ∈ left, relation a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | a :: _, _ :: _, .cons head rest, b, member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨a, List.mem_cons_self, head⟩
    · obtain ⟨other, inside, related⟩ := exists_left_of_forall₂ rest b member
      exact ⟨other, List.mem_cons_of_mem _ inside, related⟩

theorem exists_right_of_forall₂ {α β : Type} {relation : α → β → Prop} : ∀ {left : List α} {right : List β},
    List.Forall₂ relation left right → ∀ a ∈ left, ∃ b ∈ right, relation a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _ :: _, b :: _, .cons head rest, a, member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨b, List.mem_cons_self, head⟩
    · obtain ⟨other, inside, related⟩ := exists_right_of_forall₂ rest a member
      exact ⟨other, List.mem_cons_of_mem _ inside, related⟩


/-! ## Coherence for two-level set languages -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.MatchSpec (matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)

/-- **A two-level set language**: a hereditary set language whose rules rewrite a set at the root, with fewer than
`bound` element patterns, each a metavariable, a closed canonical term or a set pattern of at most `width` flat
elements, with distinct names and no premises. -/
structure TwoLevelSetLanguage (language : LanguageDef) (carrier : GrammarRule) (width bound : ℕ) : Prop where
  hereditary : HereditaryLanguage language carrier
  rules : ∀ rule ∈ language.rewrites, ∃ patterns rest, rule.left = .collection .hashSet patterns rest ∧
    patterns.length + 1 ≤ bound ∧ (∀ pattern ∈ patterns, TwoLevelElement language carrier.category width pattern) ∧
    (rest.toList ++ patternNamesList patterns).Nodup ∧ rule.premises = []

variable {relEnv : RelationEnv} {carrier : GrammarRule} {bound : ℕ}

/-- **A set rule's match regrouped by classes**: when each element's match moves to a listed presentation of its
member, a listed presentation of a canonical member presents it, and the member is listed for itself, the match moves
to a list of groups, one for each member of the canonical form, each of between one and `bound` listed presentations
of that member. -/
theorem regroup (presentationsOf : Pattern → List Pattern)
    (classOf : ∀ {value shown : Pattern}, BagForms.sortBags value = value → shown ∈ presentationsOf value →
      BagForms.sortBags shown = value)
    (selfListed : ∀ {value : Pattern}, BagForms.sortBags value = value → value ∈ presentationsOf value)
    {patterns : List Pattern} {rest : Option String} {terms : List Pattern} {bindings : Bindings}
    (bag : MatchBagRel patterns rest .hashSet terms bindings)
    (transferOne : ∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, Hereditary language sort term →
      MatchRel pattern term captured → ∃ partner ∈ presentationsOf (BagForms.sortBags term), ∃ captured',
        MatchRel pattern partner captured' ∧ BagForms.BindingsSame captured captured')
    (distinctOne : ∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, MatchRel pattern term captured →
      (patternNames pattern).Nodup → (captured.map Prod.fst).Nodup)
    (termsHold : ∀ term ∈ terms, Hereditary language sort term)
    (distinct : (rest.toList ++ patternNamesList patterns).Nodup) (short : patterns.length + rest.toList.length ≤ bound) :
    ∃ grouped ∈ chooseGroups ((arrange .hashSet (terms.map BagForms.sortBags)).map fun value =>
        nestedGroups bound (presentationsOf value)),
      ∃ bindings', MatchBagRel patterns rest .hashSet grouped bindings' ∧ BagForms.BindingsSame bindings bindings' := by
  let values := arrange .hashSet (terms.map BagForms.sortBags)
  have distinctValues : values.Nodup := List.nodup_dedup _
  have termClass : ∀ term ∈ terms, BagForms.sortBags term ∈ values :=
    fun term member => (arrange_mem _).mpr (List.mem_map_of_mem member)
  have sortIdem : ∀ term : Pattern, BagForms.sortBags (BagForms.sortBags term) = BagForms.sortBags term := by
    intro term
    rw [BagForms.sortBags_eq_canon, canon_idempotent]
  obtain ⟨partners, matchedTerms, remaining, length, partnersListed, split, noRemaining, transfer⟩ :=
    bag_transfer presentationsOf (fun _ => True) bag
      (fun pattern member _ _ held matched => by
        obtain ⟨partner, listed, captured', matched', same⟩ := transferOne pattern member held matched
        exact ⟨partner, listed, captured', matched', same, fun _ _ => trivial⟩)
      distinctOne termsHold distinct
  let extras := arrange .hashSet (remaining.map BagForms.sortBags)
  have extrasCanonical : ∀ extra ∈ extras, BagForms.sortBags extra = extra := by
    intro extra member
    obtain ⟨original, -, rfl⟩ := List.mem_map.mp ((arrange_mem _).mp member)
    exact sortIdem original
  have extrasSame : Same (.collection .hashSet remaining none) (.collection .hashSet extras none) := by
    change canon _ = canon _
    rw [canon_collection, canon_collection]
    congr 1
    apply arrange_eq_of_presents
    intro other
    rw [show extras.map canon = extras from by
      conv_rhs => rw [← List.map_id extras]
      exact List.map_congr_left fun extra member => by
        rw [← BagForms.sortBags_eq_canon]
        exact extrasCanonical extra member]
    rw [arrange_mem, ← BagForms.sortBags_eq_canon]
  have noExtras : rest = none → extras = [] := by
    intro none
    simp only [extras, noRemaining none, List.map_nil]
    rfl
  obtain ⟨bindings', matched', sameBindings, -⟩ := transfer extras noExtras extrasSame trivial
  have classInside : ∀ member ∈ partners ++ extras, BagForms.sortBags member ∈ values := by
    intro member inside
    rcases List.mem_append.mp inside with inPartners | inExtras
    · obtain ⟨term, termMember, listed⟩ := exists_right_of_forall₂ partnersListed member inPartners
      rw [classOf (sortIdem term) listed]
      exact termClass term (split.symm.subset (List.mem_append_left _ termMember))
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp ((arrange_mem _).mp inExtras)
      rw [sortIdem]
      exact termClass original (split.symm.subset (List.mem_append_right _ originalMember))
  let grouped := values.flatMap fun value => (partners ++ extras).filter fun member => BagForms.sortBags member == value
  have regrouped : (partners ++ extras).Perm grouped := perm_groups BagForms.sortBags distinctValues classInside
  obtain ⟨bindings'', matched'', sameBindings''⟩ : ∃ bindings'', MatchBagRel patterns rest .hashSet grouped bindings'' ∧
      BagForms.BindingsSame bindings' bindings'' := by
    cases rest with
    | none => exact ⟨bindings', matchBagRel_perm_none matched' regrouped, bindingsSame_refl _⟩
    | some name =>
      have fresh : ∀ pattern ∈ patterns, ∀ {term : Pattern} {captured : Bindings}, MatchRel pattern term captured →
          ∀ entry ∈ captured, entry.1 ≠ name := by
        intro pattern member term captured matchedPattern entry entryMember named
        exact (List.nodup_cons.mp distinct).1 (named ▸ mem_patternNamesList member
          (captured_names matchedPattern entry entryMember))
      obtain ⟨-, permuted⟩ := matchBagRel_perm (by decide) matched' fresh
      obtain ⟨bindings'', matched'', alike⟩ := permuted regrouped
      exact ⟨bindings'', matched'', alike.imp fun _ _ entryAlike => ⟨entryAlike.1, entryAlike.2.2⟩⟩
  refine ⟨grouped, ?_, bindings'', matched'', bindingsSame_trans sameBindings sameBindings''⟩
  rw [show grouped = (values.map fun value => (partners ++ extras).filter fun member =>
    BagForms.sortBags member == value).flatten from List.flatMap_def]
  refine mem_chooseGroups ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun value valueMember => mem_nestedGroups ?_ ?_ ?_
  · obtain ⟨term, termMember, termIs⟩ := List.mem_map.mp ((arrange_mem _).mp valueMember)
    rcases List.mem_append.mp (split.subset termMember) with inMatched | inRemaining
    · obtain ⟨partner, partnerMember, listed⟩ := exists_left_of_forall₂ partnersListed term inMatched
      refine List.ne_nil_of_mem (List.mem_filter.mpr ⟨List.mem_append_left _ partnerMember, ?_⟩)
      rw [classOf (sortIdem term) listed, termIs]
      exact beq_self_eq_true _
    · have inExtras : value ∈ extras := (arrange_mem _).mpr (termIs ▸ List.mem_map_of_mem inRemaining)
      refine List.ne_nil_of_mem (List.mem_filter.mpr ⟨List.mem_append_right _ inExtras, ?_⟩)
      rw [extrasCanonical value inExtras]
      exact beq_self_eq_true _
  · rw [List.filter_append, List.length_append]
    have partnersShort := List.length_filter_le (fun member => BagForms.sortBags member == value) partners
    have extrasShort : (extras.filter fun member => BagForms.sortBags member == value).length ≤ rest.toList.length := by
      cases rest with
      | none => rw [noExtras rfl]; exact Nat.zero_le _
      | some name =>
        have filtered : (extras.filter fun member => BagForms.sortBags member == value) =
            extras.filter fun member => member == value := by
          apply List.filter_congr
          intro member inside
          rw [extrasCanonical member inside]
        rw [filtered, ← List.count_eq_length_filter]
        exact List.nodup_iff_count_le_one.mp (List.nodup_dedup _) value
    rw [length] at partnersShort
    omega
  · intro member inside
    obtain ⟨inList, isValue⟩ := List.mem_filter.mp inside
    have sameClass : BagForms.sortBags member = value := by simpa using isValue
    rcases List.mem_append.mp inList with inPartners | inExtras
    · obtain ⟨term, -, listed⟩ := exists_right_of_forall₂ partnersListed member inPartners
      rw [← sameClass, classOf (sortIdem term) listed]
      exact listed
    · rw [← sameClass, extrasCanonical member inExtras]
      exact selfListed (extrasCanonical member inExtras)

/-- **Coherence for two-level set languages**: a step from any presentation of a canonical hereditary set is matched,
with the same labels and up to canonical form, by a step listed at a presentation whose members are written up to
`bound` times, each copy canonical or with copies of its own members. -/
theorem twoLevel_coherent (lang : TwoLevelSetLanguage language carrier width bound) (fuel : ℕ) :
    Coherent relEnv language fuel BagForms.sortBags (hereditary language carrier.category)
      (twoLevelPresentations width bound) := by
  intro state redex witness contractum _ admitted canonState complete before _ valid
  have canonical := hereditary_canonical (relEnv := relEnv) lang.hereditary
  have redexHolds : Hereditary language carrier.category redex :=
    (hereditary_iff _).mp (canonical.invariant admitted before)
  have redexCanon : BagForms.sortBags redex = state := ((canonical.same admitted before).symm).trans canonState
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    obtain ⟨patterns, rest, leftIs, short, elements, distinct, noPremises⟩ := lang.rules rule (List.mem_of_getElem? found)
    rw [noPremises] at premises
    cases premises
    rw [matchPatternForRule_eq_syntactic, leftIs] at matched
    have related := matchPattern_iff_matchRel.mp matched
    cases related with
    | collection _ bag =>
      rename_i terms restTerm _ _
      obtain ⟨presented, same, termsHold⟩ : ∃ presented, Pattern.collection .hashSet terms restTerm = set presented ∧
          ∀ term ∈ presented, Hereditary language carrier.category term := by
        rcases redexHolds.cases with ⟨label, same, -⟩ | ⟨presented, same, inside⟩
        · simp [token] at same
        · exact ⟨presented, same, inside⟩
      simp only [set, Pattern.collection.injEq, true_and] at same
      obtain ⟨rfl, rfl⟩ := same
      let values := arrange .hashSet (terms.map BagForms.sortBags)
      have stateIs : state = set values := by
        rw [← redexCanon]
        exact sortBags_set_values terms
      subst stateIs
      obtain ⟨grouped, groupedListed, bindings'', matched'', sameBindings⟩ :=
        regroup (memberPresentations width) memberPresentations_class (fun _ => List.mem_cons_self) bag
          (fun pattern member _ _ held matchedPattern => element_transfer (elements pattern member) held matchedPattern)
          (fun pattern member _ _ matchedPattern names =>
            twoLevel_captures_distinct (elements pattern member) matchedPattern names)
          termsHold distinct (Nat.le_trans (Nat.add_le_add_left (by cases rest <;> simp) _) short)
      have shown : Pattern.collection .hashSet grouped none ∈ twoLevelPresentations width bound (set values) := by
        simp only [set, twoLevelPresentations, List.mem_map]
        exact ⟨grouped, groupedListed, rfl⟩
      have matchedFinal : bindings'' ∈ matchPatternForRule language rule (.collection .hashSet grouped none) := by
        rw [matchPatternForRule_eq_syntactic, leftIs]
        exact matchPattern_iff_matchRel.mpr (.collection (by decide) matched'')
      have fired := StepValid.rule (relEnv := relEnv) found matchedFinal (by rw [noPremises]; exact .nil _)
      refine ⟨(.rule index bindings'' [], applyBindingsScoped (captureSites rule) bindings'' 0 rule.right),
        mem_listedAt.mpr ⟨_, shown, mem_stepsAt_of_enough (enoughAt_iff.mp complete _ shown) fired⟩,
        fun label => by cases label <;> rfl, ?_⟩
      rw [BagForms.sortBags_eq_canon]
      exact (BagForms.applyBindingsScoped_same (captureSites rule) sameBindings 0
        rule.right).symm

/-- **Canonical forms for a two-level set language**, for the front door. -/
def twoLevelForms (lang : TwoLevelSetLanguage language carrier width bound) (fuel : ℕ) :
    CanonicalForms relEnv language fuel :=
  .ofCoherent (hereditary_canonical lang.hereditary) (twoLevel_coherent lang fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
