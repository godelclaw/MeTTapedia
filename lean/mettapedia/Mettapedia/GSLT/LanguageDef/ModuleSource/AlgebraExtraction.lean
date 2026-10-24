import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.Algebra.CollectionFold

/-!
# Boundaries of collection-algebra extraction

Algebra extraction and normalization share the same constructor-uniqueness
test. When a collection kind has several constructors, the original equations
remain available; none is replaced by an unavailable normalizer law.

Binary associativity is not an unrestricted variadic flattening axiom. The
finite countermodel below distinguishes the two. Monoid folds do justify
variadic flattening, by the existing list-product laws. The connection from
an authored binary replacement to that model is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CollectionLaws

theorem uniqueCollectionKind_iff {language : LanguageDef} {rule : GrammarRule}
    {kind : CollType} (shape : bareKind rule = some kind) :
    uniqueCollectionKind language rule = true ↔
      (language.terms.filter fun other => bareKind other == some kind).length = 1 := by
  simp [uniqueCollectionKind, shape]

/-- Retaining source equations is structural: it holds for every language
whose collection kinds fail the executable uniqueness test, independently of
the equations' contents. -/
theorem declareAlgebras_eq_self_of_unavailable (language : LanguageDef) (binaryLabels : List String)
    (unavailable : ∀ rule ∈ language.terms,
      rule.algebra?.isSome = true ∨ uniqueCollectionKind language rule = false) :
    declareAlgebras language binaryLabels = language := by
  unfold declareAlgebras
  suffices ∀ (rules : List GrammarRule),
      (∀ rule ∈ rules, rule.algebra?.isSome = true ∨ uniqueCollectionKind language rule = false) →
      rules.foldl (extractAlgebra language binaryLabels) language = language by
    exact this language.terms unavailable
  intro rules
  induction rules with
  | nil => simp
  | cons rule rules ih =>
    intro unavailable
    have head := unavailable rule List.mem_cons_self
    have guard : (rule.algebra?.isSome || !uniqueCollectionKind language rule ||
        !binaryLabels.contains rule.label) = true := by
      rcases head with known | absent
      · simp [known]
      · simp [absent]
    simp only [List.foldl_cons, extractAlgebra, guard, ↓reduceIte]
    exact ih (fun other member => unavailable other (List.mem_cons_of_mem _ member))

/-- A literal variadic declaration keeps all equations. The recognizer does
not promote its binary associativity instances into unrestricted flattening. -/
theorem declareAlgebras_without_binary_origins (language : LanguageDef) :
    declareAlgebras language [] = language := by
  unfold declareAlgebras
  have unchanged (current : LanguageDef) (rules : List GrammarRule) :
      rules.foldl (extractAlgebra language []) current = current := by
    induction rules generalizing current with
    | nil => rfl
    | cons rule rules ih =>
      simpa only [List.foldl_cons, extractAlgebra, List.contains_nil, Bool.not_false,
        Bool.or_true, Bool.true_eq, ↓reduceIte] using ih current
  exact unchanged language language.terms

/-- The actual argument mapper for a binary-to-collection replacement. The
old argument order is retained; the collection's equality policy is separate. -/
theorem argumentMap_binary_collection (old new : GrammarRule)
    (first second elements sort : String) (kind : CollType)
    (before : old.params = [.simple first (.base sort), .simple second (.base sort)])
    (after : new.params = [.simple elements (.collection kind (.base sort))]) :
    argumentMap old new = some (fun arguments => [Pattern.collection kind arguments none]) := by
  simp [argumentMap, namedArguments?, before, after, paramName]

namespace AlgebraExtractionControls

def bagConstructor (label sort : String) : GrammarRule :=
  { label, category := sort,
    params := [.simple "elements" (.collection .hashBag (.base sort))], syntaxPattern := [] }

def bagApplication (label : String) (elements : List Pattern) : Pattern :=
  .apply label [.collection .hashBag elements none]

def associativity (label : String) : Equation :=
  { name := label ++ ":associativity", typeContext := [], premises := [],
    left := bagApplication label
      [bagApplication label [.fvar "x", .fvar "y"], .fvar "z"],
    right := bagApplication label
      [.fvar "x", bagApplication label [.fvar "y", .fvar "z"]] }

def twoBagSorts : LanguageDef :=
  { name := "TwoBagSorts", types := [TypeDecl.plain "A", TypeDecl.plain "B"],
    terms := [bagConstructor "First" "A", bagConstructor "Second" "B"],
    equations := [associativity "First", associativity "Second"], rewrites := [] }

theorem ambiguous_algebras_retained :
    declareAlgebras twoBagSorts ["First", "Second"] = twoBagSorts := by
  apply declareAlgebras_eq_self_of_unavailable
  intro rule member
  simp only [twoBagSorts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .inr (by decide)

theorem ambiguous_equations_retained :
    (declareAlgebras twoBagSorts ["First", "Second"]).equations =
      [associativity "First", associativity "Second"] := by
  rw [ambiguous_algebras_retained]
  rfl

theorem ambiguous_normalizer_has_no_laws :
    declared (declareAlgebras twoBagSorts ["First", "Second"]) = [] := by
  rw [ambiguous_algebras_retained]
  decide

/-- A symmetric variadic operation whose binary operation is Boolean join.
Its ternary operation is independent of that binary operation. -/
def associativeBinaryOnly (elements : List Bool) : Bool :=
  if elements.length = 3 then true else elements.any id

theorem binary_associativity (x y z : Bool) :
    associativeBinaryOnly [associativeBinaryOnly [x, y], z] =
      associativeBinaryOnly [x, associativeBinaryOnly [y, z]] := by
  cases x <;> cases y <;> cases z <;> decide

theorem binary_commutativity (x y : Bool) :
    associativeBinaryOnly [x, y] = associativeBinaryOnly [y, x] := by
  cases x <;> cases y <;> decide

theorem variadic_flattening_not_entailed :
    associativeBinaryOnly [associativeBinaryOnly [false, false], false] ≠
      associativeBinaryOnly [false, false, false] := by decide

theorem recognized_binary_associativity :
    (statedAlgebra [associativity "First"] (bagConstructor "First" "A")).map
      (fun result => result.1) = some { flatten := true, unit := none } := by decide

/-- Genuine fold interpretations implement splicing at arbitrary arities. -/
theorem monoid_fold_splice {A : Type} [Monoid A]
    (before middle after : List A) :
    (before ++ middle.prod :: after).prod = (before ++ middle ++ after).prod := by
  simp [List.prod_append]

theorem monoid_fold_singleton {A : Type} [Monoid A] (value : A) :
    [value].prod = value := by simp

theorem monoid_fold_unit {A : Type} [Monoid A] (before after : List A) :
    (before ++ (1 : A) :: after).prod = (before ++ after).prod := by simp

end AlgebraExtractionControls
end Mettapedia.GSLT.LanguageDef.ModuleSource
