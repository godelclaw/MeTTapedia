import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalParts

/-!
# The parts of bags

A language read modulo its bag laws splits a bag into any two sub-bags, in any order of their elements. With bags
sorted bottom up as canonical forms (`BagForms.canonical`), the splits of a canonical bag are listed by dealing its
elements into two (`deals`), and those of a vector by its cuts.

- **Dealing a list into two** (`deals`): every way of sending each element to the first or the second part. The two
  parts of a deal are a permutation of the list (`perm_of_mem_deals`), and any two lists whose concatenation is a
  permutation of it are, up to permutation, the parts of a deal (`exists_deal`).
- **Sub-collections stay admitted**: the well-sortedness checker reads a collection element by element
  (`checkOpen_sub`), so a collection of some of the elements of an admitted canonical collection is admitted
  (`domain_sub`).
- **The listing** (`BagForms.parts`): the canonical forms of the parts of each deal of a bag and of each cut of a
  vector, complete and sound for the language's splits, with emptiness read off the canonical form. A language with
  bag laws then decides splits at the front door (`partsDecider` with these canonical forms and this listing).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon canon_collection canon_idempotent setFree setFreeList setFreeList_iff
  setFree_collection arrange arrange_bag arrange_vec)
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (sortLex sortLex_perm sortLex_eq_of_perm)
open Mettapedia.GSLT.LanguageDef.WellSorted

/-! ## Dealing a list into two -/

/-- **The deals of a list**: every way of sending each element to the first or the second part. -/
def deals {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | head :: tail => (deals tail).flatMap fun pair => [(head :: pair.1, pair.2), (pair.1, head :: pair.2)]

/-- The two parts of a deal are a permutation of the list. -/
theorem perm_of_mem_deals {α : Type} : ∀ {list : List α} {pair : List α × List α}, pair ∈ deals list →
    (pair.1 ++ pair.2).Perm list
  | [], pair, member => by
    simp only [deals, List.mem_singleton] at member
    subst member
    exact List.Perm.refl _
  | head :: tail, pair, member => by
    simp only [deals, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at member
    obtain ⟨previous, inside, rfl | rfl⟩ := member
    · exact (perm_of_mem_deals inside).cons head
    · exact List.perm_middle.trans ((perm_of_mem_deals inside).cons head)

/-- **Two lists whose concatenation is a permutation of a list are, up to permutation, the parts of one of its
deals.** -/
theorem exists_deal {α : Type} [DecidableEq α] : ∀ {list left right : List α}, (left ++ right).Perm list →
    ∃ pair ∈ deals list, pair.1.Perm left ∧ pair.2.Perm right
  | [], left, right, perm => by
    have empty := List.Perm.eq_nil perm
    rw [List.append_eq_nil_iff] at empty
    obtain ⟨rfl, rfl⟩ := empty
    exact ⟨([], []), by simp [deals], List.Perm.refl _, List.Perm.refl _⟩
  | head :: tail, left, right, perm => by
    have inside : head ∈ left ++ right := perm.symm.subset List.mem_cons_self
    rcases List.mem_append.mp inside with inLeft | inRight
    · have rest : (left.erase head ++ right).Perm tail :=
        (((List.perm_cons_erase inLeft).append_right right).symm.trans perm).cons_inv
      obtain ⟨pair, member, permLeft, permRight⟩ := exists_deal rest
      refine ⟨(head :: pair.1, pair.2), ?_, (permLeft.cons head).trans (List.perm_cons_erase inLeft).symm, permRight⟩
      simp only [deals, List.mem_flatMap]
      exact ⟨pair, member, by simp⟩
    · have moved : (left ++ right).Perm (head :: (left ++ right.erase head)) :=
        ((List.perm_cons_erase inRight).append_left left).trans List.perm_middle
      have rest : (left ++ right.erase head).Perm tail := (moved.symm.trans perm).cons_inv
      obtain ⟨pair, member, permLeft, permRight⟩ := exists_deal rest
      refine ⟨(pair.1, head :: pair.2), ?_, permLeft, (permRight.cons head).trans (List.perm_cons_erase inRight).symm⟩
      simp only [deals, List.mem_flatMap]
      exact ⟨pair, member, by simp⟩

/-! ## Sub-collections stay admitted -/

theorem checkElementsHaveType_iff {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {elementType : TypeExpr} : ∀ {elements : List Pattern},
    checkElementsHaveType language free bound elements elementType = true ↔
      ∀ element ∈ elements, checkHasType language free bound element elementType = true
  | [] => by simp [checkElementsHaveType]
  | _ :: _ => by simp [checkElementsHaveType, checkElementsHaveType_iff]

theorem binderMetadataList_iff : ∀ {elements : List Pattern},
    Pattern.hasCanonicalBinderMetadataList elements = true ↔
      ∀ element ∈ elements, Pattern.hasCanonicalBinderMetadata element = true
  | [] => by simp [Pattern.hasCanonicalBinderMetadataList]
  | _ :: _ => by simp [Pattern.hasCanonicalBinderMetadataList, binderMetadataList_iff]

theorem wellScopedList_iff {depth : ℕ} : ∀ {elements : List Pattern},
    Pattern.isWellScopedListAt depth elements = true ↔ ∀ element ∈ elements, Pattern.isWellScopedAt depth element = true
  | [] => by simp [Pattern.isWellScopedListAt]
  | _ :: _ => by simp [Pattern.isWellScopedListAt, wellScopedList_iff]

/-- **The checker reads a collection element by element**: a collection of some of the elements of a collection it
accepts is accepted at the same type. -/
theorem checkOpen_sub {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {kind : CollType} {elements others : List Pattern}
    (checked : checkOpenPatternWellSorted language free bound expected (.collection kind elements none) = true)
    (sub : ∀ other ∈ others, other ∈ elements) :
    checkOpenPatternWellSorted language free bound expected (.collection kind others none) = true := by
  simp only [checkOpenPatternWellSorted, Bool.and_eq_true] at checked ⊢
  obtain ⟨⟨⟨typed, binders⟩, object⟩, scopeSafe⟩ := checked
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [checkHasType, Option.isNone_none, Bool.true_and, Bool.or_eq_true] at typed ⊢
    rcases typed with direct | authored
    · left
      cases expected with
      | collection actual elementType =>
        simp only [Bool.and_eq_true, checkElementsHaveType_iff] at direct ⊢
        exact ⟨direct.1, fun other member => direct.2 other (sub other member)⟩
      | base _ | arrow _ _ | multiBinder _ => simp at direct
    · right
      obtain ⟨rule, member, accepted⟩ := List.any_eq_true.mp authored
      refine List.any_eq_true.mpr ⟨rule, member, ?_⟩
      revert accepted
      cases bareCollectionElementType? rule kind expected with
      | none => simp
      | some elementType =>
        simp only [checkElementsHaveType_iff]
        exact fun accepted other inside => accepted other (sub other inside)
  · simp only [Pattern.hasCanonicalBinderMetadata, binderMetadataList_iff] at binders ⊢
    exact fun other member => binders other (sub other member)
  · simp only [isObjectPattern, Option.isNone_none, Bool.true_and, objectList_eq_all, List.all_eq_true] at object ⊢
    exact fun other member => object other (sub other member)
  · simp only [checkScopeSafeAt, Pattern.isWellScopedAt, wellScopedList_iff] at scopeSafe ⊢
    exact fun other member => scopeSafe other (sub other member)

variable {language : LanguageDef}

theorem sortedBag_sub {elements others : List Pattern}
    (sorted : sortedBag language (.collection .hashBag elements none) = true) (sub : ∀ other ∈ others, other ∈ elements) :
    sortedBag language (.collection .hashBag others none) = true := by
  obtain ⟨rule, member, checks⟩ := List.any_eq_true.mp sorted
  rw [Bool.and_eq_true] at checks
  exact List.any_eq_true.mpr ⟨rule, member, by rw [Bool.and_eq_true]; exact ⟨checks.1, checkOpen_sub checks.2 sub⟩⟩

/-- **A canonical collection of some of the elements of an admitted canonical collection is admitted.** -/
theorem domain_sub {kind : CollType} {elements others : List Pattern}
    (admitted : domain language (.collection kind elements none) = true)
    (canonElements : canon (.collection kind elements none) = .collection kind elements none)
    (canonOthers : canon (.collection kind others none) = .collection kind others none)
    (sub : ∀ other ∈ others, other ∈ elements) : domain language (.collection kind others none) = true := by
  simp only [domain, sortBags_eq_canon, canonElements, Bool.and_eq_true] at admitted
  simp only [domain, sortBags_eq_canon, canonOthers, Bool.and_eq_true]
  obtain ⟨⟨object, free⟩, sorted⟩ := admitted
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [isObjectPattern, Option.isNone_none, Bool.true_and, objectList_eq_all, List.all_eq_true] at object ⊢
    exact fun other member => object other (sub other member)
  · obtain ⟨notSet, elementsFree⟩ := setFree_collection free
    simp only [setFree, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, setFreeList_iff]
    exact ⟨notSet, fun other member => elementsFree other (sub other member)⟩
  · cases kind with
    | hashBag =>
      simp only [bagsSorted, Bool.and_eq_true, bagsSortedList_iff] at sorted ⊢
      exact ⟨sortedBag_sub sorted.1 sub, fun other member => sorted.2 other (sub other member)⟩
    | vec | hashSet =>
      simp only [bagsSorted, bagsSortedList_iff] at sorted ⊢
      exact fun other member => sorted other (sub other member)

/-! ## The listing -/

/-- **The splits of a canonical bag or vector**: the canonical forms of the parts of each deal of a bag's elements,
and of each cut of a vector's. -/
def bagSplits : Pattern → CollType → List (Pattern × Pattern)
  | .collection .hashBag elements none, .hashBag =>
    (deals elements).map fun pair =>
      (sortBags (.collection .hashBag pair.1 none), sortBags (.collection .hashBag pair.2 none))
  | .collection .vec elements none, .vec =>
    (cuts elements).map fun pair => (sortBags (.collection .vec pair.1 none), sortBags (.collection .vec pair.2 none))
  | _, _ => []

theorem mem_bagSplits {term : Pattern} {kind : CollType} {pair : Pattern × Pattern}
    (member : pair ∈ bagSplits term kind) :
    ∃ elements, term = .collection kind elements none ∧ ∃ left right,
      (left ++ right).Perm elements ∧ (kind = .vec → left ++ right = elements) ∧
        pair = (sortBags (.collection kind left none), sortBags (.collection kind right none)) := by
  unfold bagSplits at member
  split at member
  · rename_i elements
    obtain ⟨deal, dealt, rfl⟩ := List.mem_map.mp member
    exact ⟨elements, rfl, deal.1, deal.2, perm_of_mem_deals dealt, (fun differ => nomatch differ), rfl⟩
  · rename_i elements
    obtain ⟨cut, cutMember, rfl⟩ := List.mem_map.mp member
    have same := (mem_cuts elements cut.1 cut.2).mp cutMember
    exact ⟨elements, rfl, cut.1, cut.2, same ▸ List.Perm.refl _, fun _ => same, rfl⟩
  · cases member

theorem mem_arrange {kind : CollType} (noSet : kind ≠ .hashSet) {list : List Pattern} {element : Pattern} :
    element ∈ arrange kind list ↔ element ∈ list := by
  cases kind with
  | vec => exact Iff.rfl
  | hashBag => exact (sortLex_perm list).mem_iff
  | hashSet => exact absurd rfl noSet

/-- The elements of a canonical collection are canonical. -/
theorem canon_of_mem {kind : CollType} {elements : List Pattern} (noSet : kind ≠ .hashSet)
    (canonical : canon (.collection kind elements none) = .collection kind elements none) {element : Pattern}
    (member : element ∈ elements) : canon element ∈ elements := by
  rw [canon_collection, Pattern.collection.injEq] at canonical
  rw [← canonical.2.1]
  exact (mem_arrange noSet).mpr (List.mem_map_of_mem member)

theorem noSet_of_domain {kind : CollType} {elements : List Pattern}
    (admitted : domain language (.collection kind elements none) = true) : kind ≠ .hashSet := by
  simp only [domain, sortBags_eq_canon, canon_collection, Bool.and_eq_true] at admitted
  exact (setFree_collection admitted.1.2).1

theorem map_canon_canon (list : List Pattern) : (list.map canon).map canon = list.map canon := by
  rw [List.map_map]
  exact List.map_congr_left fun element _ => canon_idempotent element

theorem canon_map_canon (kind : CollType) (list : List Pattern) :
    canon (.collection kind (list.map canon) none) = canon (.collection kind list none) := by
  rw [canon_collection, canon_collection, map_canon_canon]

theorem canon_bag_of_perm {deal list : List Pattern} (perm : deal.Perm (list.map canon)) :
    canon (.collection .hashBag deal none) = canon (.collection .hashBag list none) := by
  rw [canon_collection, canon_collection, arrange_bag, arrange_bag,
    sortLex_eq_of_perm ((perm.map canon).trans (List.Perm.of_eq (map_canon_canon list)))]

variable {relEnv : RelationEnv}

/-- **A collection whose elements' canonical forms are elements of an admitted canonical collection is admitted.** -/
theorem domain_part {kind : CollType} {elements part : List Pattern} (noSet : kind ≠ .hashSet)
    (canonical : CanonicalDetermined relEnv language sortBags (domain language))
    (admitted : domain language (.collection kind elements none) = true)
    (canonElements : canon (.collection kind elements none) = .collection kind elements none)
    (inside : ∀ element ∈ part, canon element ∈ elements) : domain language (.collection kind part none) = true := by
  rw [← canonical.determined, sortBags_eq, canon_collection]
  refine domain_sub admitted canonElements (by rw [← canon_collection, canon_idempotent]) fun other member => ?_
  obtain ⟨element, member', rfl⟩ := List.mem_map.mp ((mem_arrange noSet).mp member)
  exact inside element member'

/-- **Bags and vectors list their splits**: the canonical forms of the parts of each deal of a canonical bag and
each cut of a canonical vector. -/
def parts (noEquations : language.equations = []) (noAlgebra : language.hasAlgebraDeclarations = false) :
    PartsListing relEnv language sortBags (domain language) where
  splits := bagSplits
  empty := isEmptyCollection
  complete := by
    intro state kind first second admitted canonState split
    have canonical := canonical (relEnv := relEnv) noEquations noAlgebra
    have determinedForms := canonicalDetermined (relEnv := relEnv) noEquations noAlgebra
    obtain ⟨-, left, right, equivalent, rfl, rfl⟩ := split
    have same := canonical.same admitted equivalent
    rw [canonState, sortBags_eq, canon_collection] at same
    subst same
    have noSet := noSet_of_domain admitted
    rw [sortBags_eq] at canonState
    have inside : ∀ element ∈ left ++ right, canon element ∈ arrange kind ((left ++ right).map canon) :=
      fun element member => (mem_arrange noSet).mpr (List.mem_map_of_mem member)
    refine ⟨domain_part noSet determinedForms admitted canonState fun element member =>
        inside element (List.mem_append_left _ member),
      domain_part noSet determinedForms admitted canonState fun element member =>
        inside element (List.mem_append_right _ member), ?_⟩
    cases kind with
    | vec =>
      simp only [bagSplits, arrange_vec, List.mem_map]
      refine ⟨(left.map canon, right.map canon), (mem_cuts _ _ _).mpr (List.map_append ..).symm, ?_⟩
      rw [sortBags_eq, sortBags_eq, sortBags_eq, sortBags_eq, canon_map_canon, canon_map_canon]
    | hashBag =>
      simp only [bagSplits, arrange_bag, List.mem_map]
      obtain ⟨deal, dealt, permLeft, permRight⟩ := exists_deal (list := sortLex ((left ++ right).map canon))
        (left := left.map canon) (right := right.map canon) (by rw [← List.map_append]; exact (sortLex_perm _).symm)
      exact ⟨deal, dealt, by rw [sortBags_eq, sortBags_eq, sortBags_eq, sortBags_eq, canon_bag_of_perm permLeft,
        canon_bag_of_perm permRight]⟩
    | hashSet => exact absurd rfl noSet
  sound := by
    intro state kind pair admitted canonState member
    have canonical := canonical (relEnv := relEnv) noEquations noAlgebra
    have determinedForms := canonicalDetermined (relEnv := relEnv) noEquations noAlgebra
    obtain ⟨elements, rfl, left, right, perm, ordered, rfl⟩ := mem_bagSplits member
    have noSet := noSet_of_domain admitted
    rw [sortBags_eq] at canonState
    have inside : ∀ element ∈ left ++ right, canon element ∈ elements :=
      fun element member => canon_of_mem noSet canonState (perm.subset member)
    have canonEq : sortBags (.collection kind (left ++ right) none) = sortBags (.collection kind elements none) := by
      rw [sortBags_eq, sortBags_eq]
      cases kind with
      | vec => rw [ordered rfl]
      | hashBag => rw [canon_collection, canon_collection, arrange_bag, arrange_bag, sortLex_eq_of_perm (perm.map canon)]
      | hashSet => exact absurd rfl noSet
    have admittedBoth : domain language (.collection kind (left ++ right) none) = true := by
      rw [← determinedForms.determined, canonEq, determinedForms.determined]
      exact admitted
    exact ⟨.collection kind left none, .collection kind right none,
      ⟨canonical.object admitted, left, right, (canonical.equivalent_iff admitted admittedBoth).mpr canonEq.symm, rfl,
        rfl⟩,
      domain_part noSet determinedForms admitted canonState fun element member =>
        inside element (List.mem_append_left _ member),
      domain_part noSet determinedForms admitted canonState fun element member =>
        inside element (List.mem_append_right _ member), rfl, rfl⟩
  empty_iff := by
    intro state kind admitted canonState
    have canonical := canonical (relEnv := relEnv) noEquations noAlgebra
    have determinedForms := canonicalDetermined (relEnv := relEnv) noEquations noAlgebra
    rw [isEmptyCollection_iff]
    constructor
    · rintro rfl
      exact ⟨canonical.object admitted, Relation.EqvGen.refl _⟩
    · rintro ⟨-, equivalent⟩
      have same := canonical.same admitted equivalent
      rw [canonState, sortBags_eq, canon_collection] at same
      rw [same]
      cases kind <;> simp [Mettapedia.OSLF.MeTTaIL.CanonicalBags.arrange, sortLex]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms
