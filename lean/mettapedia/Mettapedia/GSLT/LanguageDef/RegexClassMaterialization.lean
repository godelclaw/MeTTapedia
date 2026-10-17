import Mettapedia.GSLT.LanguageDef.RegexClassInterpretation

/-!
# Finite interval realization of the symbolic class algebra

Property ranges and finite simple-fold classes are input data. Intersection,
difference, scalar complement and fold closure are computed without expanding
the scalar universe. The result is proved to preserve and reflect the set
meaning of the actual input expression. A missing property is an unresolved
interpretation, never a fabricated empty class.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexClassMaterialization

open RegexClassInterpretation
open RegexSourceProjection (InRanges subtractRange complementRanges)
open RegexSelection (ScalarRange)
open Mettapedia.GSLT.Parsing.ParserProfileSemantics (isUnicodeScalar)

abbrev Ranges := List ScalarRange

def universeRanges : Ranges := [(0, 55295), (57344, 1114111)]

theorem universe_exact (scalar : Nat) :
    InRanges scalar universeRanges ↔ isUnicodeScalar scalar = true := by
  simp [InRanges, universeRanges, isUnicodeScalar]
  omega

def intersectOne (first second : ScalarRange) : Ranges :=
  if max first.1 second.1 ≤ min first.2 second.2
  then [(max first.1 second.1, min first.2 second.2)] else []

def intersect (first second : Ranges) : Ranges :=
  first.flatMap (fun one => second.flatMap (intersectOne one))

def difference (first second : Ranges) : Ranges :=
  second.foldl (fun remaining cut => remaining.flatMap (subtractRange · cut)) first

theorem intersectOne_exact (first second : ScalarRange) (scalar : Nat) :
    InRanges scalar (intersectOne first second) ↔
      first.1 ≤ scalar ∧ scalar ≤ first.2 ∧ second.1 ≤ scalar ∧ scalar ≤ second.2 := by
  unfold intersectOne
  split_ifs <;> simp [InRanges] <;> omega

theorem intersect_exact (first second : Ranges) (scalar : Nat) :
    InRanges scalar (intersect first second) ↔ InRanges scalar first ∧ InRanges scalar second := by
  simp only [intersect, InRanges, List.mem_flatMap]
  constructor
  · rintro ⟨range, ⟨one, inFirst, two, inSecond, inIntersection⟩, low, high⟩
    have both := (intersectOne_exact one two scalar).1 ⟨range, inIntersection, low, high⟩
    exact ⟨⟨one, inFirst, both.1, both.2.1⟩, ⟨two, inSecond, both.2.2⟩⟩
  · rintro ⟨⟨one, inFirst, lowFirst, highFirst⟩, ⟨two, inSecond, lowSecond, highSecond⟩⟩
    obtain ⟨range, inIntersection, low, high⟩ :=
      (intersectOne_exact one two scalar).2 ⟨lowFirst, highFirst, lowSecond, highSecond⟩
    exact ⟨range, ⟨one, inFirst, two, inSecond, inIntersection⟩, low, high⟩

theorem append_exact (first second : Ranges) (scalar : Nat) :
    InRanges scalar (first ++ second) ↔ InRanges scalar first ∨ InRanges scalar second := by
  simp [InRanges]
  aesop

theorem difference_exact (first second : Ranges) (scalar : Nat) :
    InRanges scalar (difference first second) ↔
      InRanges scalar first ∧ ¬ InRanges scalar second := by
  induction second generalizing first with
  | nil => simp [difference, InRanges]
  | cons cut rest ih =>
      simp only [difference, List.foldl_cons]
      rw [show rest.foldl (fun remaining cut => remaining.flatMap (subtractRange · cut))
          (first.flatMap (subtractRange · cut)) = difference (first.flatMap (subtractRange · cut)) rest from rfl]
      rw [ih, RegexSourceProjection.in_flatMap_subtract_iff]
      simp only [InRanges, List.mem_cons]
      aesop

structure Catalog where
  version : String
  properties : String → Option Ranges
  folds : List (List Nat)

def equivalents (catalog : Catalog) (scalar : Nat) : List Nat :=
  scalar :: catalog.folds.flatMap (fun members => if scalar ∈ members then members else [])

theorem equivalents_iff (catalog : Catalog) (first second : Nat) :
    second ∈ equivalents catalog first ↔ second = first ∨
      ∃ members ∈ catalog.folds, first ∈ members ∧ second ∈ members := by
  simp only [equivalents, List.mem_cons, List.mem_flatMap]
  constructor
  · rintro (same | ⟨members, admitted, belongs⟩)
    · exact Or.inl same
    · by_cases contains : first ∈ members
      · exact Or.inr ⟨members, admitted, contains, by simpa [contains] using belongs⟩
      · simp [contains] at belongs
  · rintro (same | ⟨members, admitted, contains, belongs⟩)
    · exact Or.inl same
    · exact Or.inr ⟨members, admitted, by simpa only [contains, ↓reduceIte] using belongs⟩

/-- A finite provider qualification: all entries are scalars and overlapping
classes agree. It checks table structure, not the Unicode standard's contents. -/
def checkFolds (catalog : Catalog) : Bool :=
  catalog.folds.all (fun members => members.all isUnicodeScalar &&
    members.all (fun point => catalog.folds.all (fun other =>
      if point ∈ other then other.all (fun member => decide (member ∈ members)) else true)))

theorem checked_fold_laws (catalog : Catalog) (checked : checkFolds catalog = true) :
    FoldLaws {
      version := catalog.version,
      property := fun _ _ => false,
      equivalents := equivalents catalog } := by
  have each := List.all_eq_true.mp checked
  have scalars : ∀ members ∈ catalog.folds, ∀ point ∈ members, isUnicodeScalar point = true := by
    intro members member point belongs
    exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp (each members member)).1 point belongs
  have overlapping : ∀ members ∈ catalog.folds, ∀ other ∈ catalog.folds,
      ∀ shared ∈ members, shared ∈ other → ∀ point ∈ other, point ∈ members := by
    intro members inCatalog other otherInCatalog shared sharedInFirst sharedInOther point pointInOther
    have allPoints := (Bool.and_eq_true_iff.mp (each members inCatalog)).2
    have allClasses := List.all_eq_true.mp allPoints shared sharedInFirst
    have condition := List.all_eq_true.mp allClasses other otherInCatalog
    simp only [sharedInOther, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at condition
    exact condition point pointInOther
  constructor
  · intro scalar _; exact List.mem_cons_self
  · intro first second related
    rcases (equivalents_iff catalog first second).1 related with same | ⟨members, admitted, firstIn, secondIn⟩
    · subst second; exact List.mem_cons_self
    · exact (equivalents_iff catalog second first).2 (Or.inr ⟨members, admitted, secondIn, firstIn⟩)
  · intro first second third firstRelated secondRelated
    rcases (equivalents_iff catalog first second).1 firstRelated with same | ⟨members, admitted, firstIn, secondIn⟩
    · subst second; exact secondRelated
    · rcases (equivalents_iff catalog second third).1 secondRelated with same | ⟨other, otherAdmitted, secondOther, thirdIn⟩
      · subst third; exact firstRelated
      · exact (equivalents_iff catalog first third).2 (Or.inr
          ⟨members, admitted, firstIn,
            overlapping members admitted other otherAdmitted second secondIn secondOther third thirdIn⟩)
  · intro first second valid related
    rcases (equivalents_iff catalog first second).1 related with same | ⟨members, admitted, _, secondIn⟩
    · subst second; exact valid
    · exact scalars members admitted second secondIn

def provider (catalog : Catalog) : Provider where
  version := catalog.version
  property := fun name scalar => testRanges ((catalog.properties name).getD []) scalar
  equivalents := equivalents catalog

theorem provider_fold_laws (catalog : Catalog) (checked : checkFolds catalog = true) :
    FoldLaws (provider catalog) := by
  have verified := checked_fold_laws catalog checked
  exact ⟨verified.reflexive, verified.symmetric, verified.transitive, verified.scalar⟩

def foldRanges (catalog : Catalog) (ranges : Ranges) : Ranges :=
  ranges ++ catalog.folds.flatMap (fun members =>
    if members.any (testRanges ranges) then members.map (fun scalar => (scalar, scalar)) else [])

theorem foldRanges_exact (catalog : Catalog) (ranges : Ranges) (scalar : Nat) :
    InRanges scalar (foldRanges catalog ranges) ↔
      ∃ representative ∈ equivalents catalog scalar, InRanges representative ranges := by
  rw [foldRanges, append_exact]
  constructor
  · rintro (original | expanded)
    · exact ⟨scalar, List.mem_cons_self, original⟩
    · obtain ⟨range, rangeMember, low, high⟩ := expanded
      obtain ⟨members, inCatalog, admitted⟩ := List.mem_flatMap.mp rangeMember
      by_cases witnesses : members.any (testRanges ranges) = true
      · simp only [witnesses, ↓reduceIte] at admitted
        obtain ⟨point, inMembers, same⟩ := List.mem_map.mp admitted
        subst range
        have pointSame : scalar = point := by omega
        obtain ⟨representative, belongs, recognized⟩ := List.any_eq_true.mp witnesses
        refine ⟨representative, List.mem_cons_of_mem _ ?_, (testRanges_iff ranges representative).1 recognized⟩
        apply List.mem_flatMap.mpr
        exact ⟨members, inCatalog, by simp only [pointSame, inMembers, ↓reduceIte]; exact belongs⟩
      · simp [witnesses] at admitted
  · rintro ⟨representative, member, accepted⟩
    rcases List.mem_cons.mp member with same | fromClass
    · subst representative; exact Or.inl accepted
    · obtain ⟨members, inCatalog, belongs⟩ := List.mem_flatMap.mp fromClass
      by_cases contains : scalar ∈ members
      · simp only [contains, ↓reduceIte] at belongs
        have intersects : members.any (testRanges ranges) = true :=
          List.any_eq_true.mpr ⟨representative, belongs, (testRanges_iff ranges representative).2 accepted⟩
        refine Or.inr ⟨(scalar, scalar), ?_, le_rfl, le_rfl⟩
        apply List.mem_flatMap.mpr
        refine ⟨members, inCatalog, ?_⟩
        simp only [intersects, ↓reduceIte]
        exact List.mem_map.mpr ⟨scalar, contains, rfl⟩
      · simp [contains] at belongs

def lower (catalog : Catalog) : Expr → Option Ranges
  | .empty => some []
  | .universe => some universeRanges
  | .range low high => some (intersect universeRanges [(low, high)])
  | .property name => (catalog.properties name).map (intersect universeRanges)
  | .union left right => do return (← lower catalog left) ++ (← lower catalog right)
  | .intersection left right => do return intersect (← lower catalog left) (← lower catalog right)
  | .difference left right => do return difference (← lower catalog left) (← lower catalog right)
  | .complement body => complementRanges <$> lower catalog body
  | .fold body => (intersect universeRanges ∘ foldRanges catalog) <$> lower catalog body

theorem lower_exact (catalog : Catalog) (expression : Expr) (ranges : Ranges)
    (compiled : lower catalog expression = some ranges) (scalar : Nat) :
    InRanges scalar ranges ↔ scalar ∈ meaning (provider catalog) expression := by
  induction expression generalizing ranges scalar with
  | empty => cases compiled; simp [InRanges, meaning]
  | «universe» => cases compiled; exact universe_exact scalar
  | range low high =>
      simp only [lower, Option.some.injEq] at compiled
      subst ranges
      rw [intersect_exact, universe_exact]
      simp [InRanges, meaning, Scalar]
  | property name =>
      cases propertyResult : catalog.properties name with
      | none => simp [lower, propertyResult] at compiled
      | some supplied =>
          simp only [lower, propertyResult, Option.map_some, Option.some.injEq] at compiled
          subst ranges
          simp only [intersect_exact, universe_exact, meaning, provider, propertyResult,
            Option.getD_some, testRanges_iff, Scalar, Set.mem_inter_iff, Set.mem_ofPred_eq]
  | union left right before after | intersection left right before after | difference left right before after =>
      cases leftResult : lower catalog left with
      | none => simp [lower, leftResult] at compiled
      | some leftRanges =>
          cases rightResult : lower catalog right with
          | none => simp [lower, leftResult, rightResult] at compiled
          | some rightRanges =>
              simp [lower, leftResult, rightResult] at compiled
              subst ranges
              first
              | rw [append_exact]; exact or_congr (before _ leftResult _) (after _ rightResult _)
              | rw [intersect_exact]; exact and_congr (before _ leftResult _) (after _ rightResult _)
              | rw [difference_exact]; exact and_congr (before _ leftResult _) (not_congr (after _ rightResult _))
  | complement body ih =>
      cases bodyResult : lower catalog body with
      | none => simp [lower, bodyResult] at compiled
      | some bodyRanges =>
          simp [lower, bodyResult] at compiled
          subst ranges
          rw [RegexSourceProjection.complementRanges_correct, ih bodyRanges bodyResult]
          rfl
  | fold body ih =>
      cases bodyResult : lower catalog body with
      | none => simp [lower, bodyResult] at compiled
      | some bodyRanges =>
          simp [lower, bodyResult] at compiled
          subst ranges
          simp only [intersect_exact, universe_exact, foldRanges_exact, meaning,
            Scalar, Set.mem_inter_iff, Set.mem_ofPred_eq, provider, ih bodyRanges bodyResult]

theorem lower_test (catalog : Catalog) (expression : Expr) (ranges : Ranges)
    (compiled : lower catalog expression = some ranges) (scalar : Nat) :
    testRanges ranges scalar = test (provider catalog) expression scalar :=
  materialization_exact (provider catalog) expression ranges (lower_exact catalog expression ranges compiled) scalar

namespace Controls

private def exampleCatalog : Catalog where
  version := "example"
  properties := fun name => if name = "Latin" then some [(65, 90), (97, 122)] else none
  folds := [[65, 97], [75, 107, 8490]]

theorem fold_and_complement_materialize :
    (lower exampleCatalog (.fold (.range 107 107))).map (fun ranges => testRanges ranges 8490) = some true ∧
    (lower exampleCatalog (.complement (.fold (.range 107 107)))).map
      (fun ranges => testRanges ranges 8490) = some false := by decide

theorem intersection_and_difference_materialize :
    (lower exampleCatalog (.intersection (.property "Latin") (.range 65 70))).map
      (fun ranges => testRanges ranges 68) = some true ∧
    (lower exampleCatalog (.difference (.property "Latin") (.range 65 90))).map
      (fun ranges => testRanges ranges 97) = some true := by decide

theorem missing_property_does_not_become_empty :
    lower exampleCatalog (.property "unavailable") = none ∧
    lower exampleCatalog (.complement (.property "unavailable")) = none := by decide

theorem finite_fold_table_qualification :
    checkFolds exampleCatalog = true ∧
    checkFolds { exampleCatalog with folds := [[65, 97], [75, 107, 8490]] } = true := by decide

theorem overlapping_partial_classes_and_surrogates_fail_qualification :
    checkFolds { exampleCatalog with folds := [[65, 97], [97, 98]] } = false ∧
    checkFolds { exampleCatalog with folds := [[65, 55296]] } = false := by decide

end Controls

#print axioms lower_exact
#print axioms lower_test
#print axioms provider_fold_laws

end Mettapedia.GSLT.LanguageDef.RegexClassMaterialization
