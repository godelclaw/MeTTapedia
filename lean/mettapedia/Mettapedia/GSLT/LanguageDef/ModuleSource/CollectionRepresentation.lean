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
    (secondKind : collectionParameterKind second = some kind)
    (binaryLabels : List String := []) :
    { first with collectionRepresentation := .wrapped } ∈
      (retainSharedCollectionLabels language binaryLabels).terms := by
  have shared : (language.terms.any fun other =>
      other.label != first.label && collectionParameterKind other == some kind) = true := by
    exact List.any_eq_true.mpr ⟨second, secondMember, by simp [Ne.symm different, secondKind]⟩
  apply List.mem_map.mpr
  refine ⟨first, firstMember, ?_⟩
  simp only [firstKind, shared, Bool.true_or, ite_true]

theorem existing_algebra_not_pending (rule : GrammarRule) (algebra : CollectionAlgebra)
    (binaryLabels : List String) (declared : rule.algebra? = some algebra) :
    collectionAlgebraCandidate rule binaryLabels = false := by
  simp [collectionAlgebraCandidate,declared]

theorem no_binary_origin_not_pending (rule : GrammarRule) :
    collectionAlgebraCandidate rule [] = false := rfl

/-- The data-role test observes every parameter, including parameters in
constructors with more than one field. Its authority is independent of typing. -/
theorem other_collection_parameter_of_member (language : LanguageDef) (rule other : GrammarRule)
    (kind : CollType) (parameter : TermParam) (otherMember : other ∈ language.terms)
    (different : other.label ≠ rule.label) (parameterMember : parameter ∈ other.params)
    (mentioned : parameter.typeExpr.mentionsCollection kind = true) :
    otherCollectionParameter language rule kind = true := by
  apply List.any_eq_true.mpr
  refine ⟨other, otherMember, ?_⟩
  change (other.label != rule.label &&
    other.params.any (fun field => field.typeExpr.mentionsCollection kind)) = true
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simpa, List.any_eq_true.mpr ⟨parameter, parameterMember, mentioned⟩⟩

/-- The finite absence certificate concerns this collection kind in the
other constructor slots. It makes no statement about root or free-variable roles. -/
theorem otherCollectionParameter_eq_false_iff (language : LanguageDef) (rule : GrammarRule)
    (kind : CollType) :
    otherCollectionParameter language rule kind = false ↔
      ∀ other ∈ language.terms, other.label ≠ rule.label →
        ∀ parameter ∈ other.params, parameter.typeExpr.mentionsCollection kind = false := by
  constructor
  · intro absent other member different parameter parameterMember
    cases mentioned : parameter.typeExpr.mentionsCollection kind with
    | false => rfl
    | true =>
      have present := other_collection_parameter_of_member language rule other kind parameter
        member different parameterMember mentioned
      rw [present] at absent
      cases absent
  · intro absent
    apply List.any_eq_false.mpr
    intro other member present
    change (other.label != rule.label &&
      other.params.any (fun field => field.typeExpr.mentionsCollection kind)) = true at present
    have fields := Bool.and_eq_true_iff.mp present
    have different : other.label ≠ rule.label := by simpa using fields.1
    obtain ⟨parameter, parameterMember, mentioned⟩ := List.any_eq_true.mp fields.2
    rw [absent other member different parameter parameterMember] at mentioned
    cases mentioned

/-- A protected declaration cannot become the stage that deletes an equation
in the actual algebra fold. Other declarations retain their own obligations. -/
theorem wrapped_collection_not_extracted (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule)
    (wrapped : rule.collectionRepresentation = .wrapped) :
    extractAlgebra language binaryLabels current rule = current := by
  simp [extractAlgebra, uniqueCollectionKind,
    Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind, GrammarRule.bareParams, wrapped]

/-- Pending binary-origin extraction retains a named operation when another
constructor exposes the same kind as data. Existing declared algebra profiles
remain outside this new protection boundary. -/
theorem data_exposed_algebra_label_retained (language : LanguageDef) (rule : GrammarRule)
    (kind : CollType) (binaryLabels : List String)
    (member : rule ∈ language.terms)
    (carrier : collectionParameterKind rule = some kind)
    (candidate : collectionAlgebraCandidate rule binaryLabels = true)
    (exposed : otherCollectionParameter language rule kind = true) :
    {rule with collectionRepresentation := .wrapped} ∈
      (retainSharedCollectionLabels language binaryLabels).terms := by
  exact List.mem_map.mpr ⟨rule, member, by simp [carrier, candidate, exposed]⟩

theorem retained_equations (language : LanguageDef) (binaryLabels : List String := []) :
    (retainSharedCollectionLabels language binaryLabels).equations = language.equations := rfl

theorem retained_types (language : LanguageDef) (binaryLabels : List String := []) :
    (retainSharedCollectionLabels language binaryLabels).types = language.types := rfl

theorem retained_rewrites (language : LanguageDef) (binaryLabels : List String := []) :
    (retainSharedCollectionLabels language binaryLabels).rewrites = language.rewrites := rfl

theorem retained_collection_labels (language : LanguageDef) (binaryLabels : List String := []) :
    (retainSharedCollectionLabels language binaryLabels).terms.map (·.label) = language.terms.map (·.label) := by
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
#print axioms shared_collection_label_retained
#print axioms existing_algebra_not_pending
#print axioms no_binary_origin_not_pending
#print axioms other_collection_parameter_of_member
#print axioms otherCollectionParameter_eq_false_iff
#print axioms wrapped_collection_not_extracted
#print axioms data_exposed_algebra_label_retained
#print axioms retained_equations
#print axioms retained_types
#print axioms retained_rewrites
#print axioms retained_collection_labels
#print axioms wrapped_label_not_bare
#print axioms unwrap_keeps_named_application
#print axioms unwrap_distinguishes_named_constructors
end Mettapedia.GSLT.LanguageDef.ModuleSource
