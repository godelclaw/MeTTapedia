import Mettapedia.Languages.MeTTa.HE.Spec.Type.RulePresentation

/-! # Reconstruction of HE typing-reference rule trees -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.RulePresentation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.TypeTheory.JudgmentDerivation

variable {space : Space} {lookup : TypeLookupRel} {matching : Matching}

private theorem node0 {goal : Judgment} (rule : Rule space lookup matching [] goal) :
    Nonempty (Tree space lookup matching goal) :=
  ⟨.node ⟨[], rule⟩ (fun position => Fin.elim0 position)⟩

private theorem node1 {first goal : Judgment} (rule : Rule space lookup matching [first] goal)
    (a : Nonempty (Tree space lookup matching first)) :
    Nonempty (Tree space lookup matching goal) := by
  obtain ⟨a⟩ := a
  exact ⟨.node ⟨[first], rule⟩ (Fin.cases a (fun position => Fin.elim0 position))⟩

private theorem node2 {first second goal : Judgment}
    (rule : Rule space lookup matching [first, second] goal)
    (a : Nonempty (Tree space lookup matching first))
    (b : Nonempty (Tree space lookup matching second)) :
    Nonempty (Tree space lookup matching goal) := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  exact ⟨.node ⟨[first, second], rule⟩ (Fin.cases a (Fin.cases b (fun position => Fin.elim0 position)))⟩

private theorem node3 {first second third goal : Judgment}
    (rule : Rule space lookup matching [first, second, third] goal)
    (a : Nonempty (Tree space lookup matching first))
    (b : Nonempty (Tree space lookup matching second))
    (c : Nonempty (Tree space lookup matching third)) :
    Nonempty (Tree space lookup matching goal) := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  obtain ⟨c⟩ := c
  exact ⟨.node ⟨[first, second, third], rule⟩
    (Fin.cases a (Fin.cases b (Fin.cases c (fun position => Fin.elim0 position))))⟩

theorem annotations_complete {subject : Atom} {rows types : List Atom}
    (source : AnnotationTypesRel subject rows types) :
    Nonempty (Tree space lookup matching (.annotations subject rows types)) := by
  induction source with
  | nil => exact node0 (.annotationsNil _)
  | hit _ ih => exact node1 (.annotationsHit _ _ _ _) ih
  | skip different _ ih => exact node1 (.annotationsSkip _ _ _ _ different) ih

theorem intrinsic_complete {value : GroundedValue} {type : Atom}
    (source : IntrinsicGroundedTypeRel value type) :
    Nonempty (Tree space lookup matching (.intrinsic value type)) := by
  cases source with
  | int => exact node0 (.intrinsicInt _)
  | bool => exact node0 (.intrinsicBool _)
  | string => exact node0 (.intrinsicString _)
  | custom => exact node0 (.intrinsicCustom _ _)

theorem occurrences_complete {subject : Atom} {types : Multiset Atom}
    (source : TypeOccurrencesRel (space.atoms : Multiset Atom) subject types) :
    Nonempty (Tree space lookup matching (.occurrences subject types)) := by
  cases source with
  | «variable» => exact node0 (.occurrencesVariable _)
  | grounded intrinsic => exact node1 (.occurrencesGrounded _ _) (intrinsic_complete intrinsic)
  | symbol => exact node0 (.occurrencesSymbol _)
  | unit => exact node0 .occurrencesUnit
  | expression => exact node0 (.occurrencesExpression _ _)

theorem storage_complete {subject : Atom} {types : List Atom}
    (source : StorageTypesRel space subject types) :
    Nonempty (Tree space lookup matching (.storage subject types)) := by
  cases source with
  | «variable» => exact node0 (.storageVariable _)
  | groundedKnown intrinsic known =>
      exact node1 (.storageGroundedKnown _ _ known) (intrinsic_complete intrinsic)
  | groundedUndefined intrinsic => exact node1 (.storageGroundedUndefined _) (intrinsic_complete intrinsic)
  | symbolKnown annotations nonempty =>
      exact node1 (.storageSymbolKnown _ _ nonempty) (annotations_complete annotations)
  | symbolUndefined annotations => exact node1 (.storageSymbolUndefined _) (annotations_complete annotations)
  | unit => exact node0 .storageUnit
  | expressionKnown annotations nonempty =>
      exact node1 (.storageExpressionKnown _ _ _ nonempty) (annotations_complete annotations)
  | expressionUndefined annotations =>
      exact node1 (.storageExpressionUndefined _ _) (annotations_complete annotations)

theorem lookup_complete {before : Bindings} {subject expected : Atom} {types : List Atom}
    (source : lookup before subject expected types) :
    Nonempty (Tree space lookup matching (.lookup before subject expected types)) :=
  node0 (.lookupQuery _ _ _ _ source)

theorem typeOf_complete {subject type : Atom} (source : TypeOfRel space subject type) :
    Nonempty (Tree space lookup matching (.typeOf subject type)) := by
  obtain ⟨types, stored, member⟩ := source
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  rw [← same]
  exact node1 (.typeOf _ _ position) (storage_complete stored)

theorem matchTypes_complete {expected actual : Atom} {before after : Bindings}
    (source : TypeMatchRel expected actual before after) :
    Nonempty (Tree space lookup matching (.matchTypes expected actual before after)) := by
  cases source with
  | undefinedLeft => exact node0 (.matchUndefinedLeft _ _)
  | atomLeft => exact node0 (.matchAtomLeft _ _)
  | undefinedRight => exact node0 (.matchUndefinedRight _ _)
  | atomRight => exact node0 (.matchAtomRight _ _)
  | structural h1 h2 h3 h4 hm hg =>
      exact node0 (.matchStructural _ _ _ _ _ h1 h2 h3 h4 hm hg)

theorem matching_complete {expected actual : Atom} {before after : Bindings}
    (source : matching expected actual before after) :
    Nonempty (Tree space lookup matching (.matching expected actual before after)) :=
  node0 (.matchingPolicy _ _ _ _ source)

theorem typeAt_complete {before : Bindings} {subject expected actual : Atom}
    (source : TypeAtRel lookup before subject expected actual) :
    Nonempty (Tree space lookup matching (.typeAt before subject expected actual)) := by
  obtain ⟨types, query, member⟩ := source
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  rw [← same]
  exact node1 (.typeAt _ _ _ _ position) (lookup_complete query)

theorem cast_complete {subject expected : Atom} {before : Bindings} {result : ResultPair}
    (source : TypeCastRel space subject expected before result lookup) :
    Nonempty (Tree space lookup matching (.cast subject expected before result)) := by
  cases source with
  | success query split skipped matched =>
      cases split
      exact node2 (.castSuccess _ _ _ _ _ _ _ skipped)
        (lookup_complete query) (matchTypes_complete matched)
  | failure query member failed =>
      obtain ⟨position, same⟩ := List.mem_iff_get.mp member
      rw [← same]
      exact node1 (.castFailure _ _ _ _ position failed) (lookup_complete query)

theorem castBatch_complete {subject expected : Atom} {before : Bindings} {results : ResultSet}
    (source : TypeCastBatchRel space subject expected before results lookup matching) :
    Nonempty (Tree space lookup matching (.castBatch subject expected before results)) := by
  cases source with
  | success query split skipped matched =>
      cases split
      exact node2 (.castBatchSuccess _ _ _ _ _ _ _ skipped)
        (lookup_complete query) (matching_complete matched)
  | failure query failed => exact node1 (.castBatchFailure _ _ _ _ failed) (lookup_complete query)

theorem functionType_complete {type result : Atom} {arguments : List Atom}
    (source : FunctionTypeRel type arguments result) :
    Nonempty (Tree space lookup matching (.functionType type arguments result)) := by
  cases source
  exact node0 (.functionType _ _)

theorem arguments_complete {arguments expected : List Atom} {before after : Bindings}
    (source : ArgumentsApplicableRel space arguments expected before after lookup) :
    Nonempty (Tree space lookup matching (.arguments arguments expected before after)) := by
  induction source with
  | nil => exact node0 (.argumentsNil _)
  | cons selected matched _ ih =>
      exact node3 (.argumentsCons _ _ _ _ _ _ _ _) (typeAt_complete selected) (matchTypes_complete matched) ih

theorem application_complete {expression type expected : Atom} {before after : Bindings}
    (source : ApplicationSuccessRel space expression type expected before after lookup) :
    Nonempty (Tree space lookup matching (.application expression type expected before after)) := by
  cases source with
  | mk shape arrow arguments matched =>
      cases shape
      exact node3 (.application _ _ _ _ _ _ _ _ _)
        (functionType_complete arrow) (arguments_complete arguments) (matchTypes_complete matched)

theorem applicability_complete {expression type expected : Atom} {before : Bindings}
    {outcome : ApplicabilityOutcome}
    (source : ApplicabilityRel space expression type expected before outcome lookup) :
    Nonempty (Tree space lookup matching (.applicability expression type expected before outcome)) := by
  cases source with
  | success applied => exact node1 (.applicable _ _ _ _ _) (application_complete applied)
  | wrongArity shape arrow different =>
      cases shape
      exact node1 (.wrongArity _ _ _ _ _ _ _ different) (functionType_complete arrow)
  | badArgument shape arrow lengths arguments selected badMatch noSuccess =>
      cases shape
      exact node3 (.badArgument _ _ _ _ _ _ _ _ _ _ _ _ _ lengths badMatch noSuccess)
        (functionType_complete arrow) (arguments_complete arguments) (typeAt_complete selected)
  | badReturn shape arrow arguments badMatch noSuccess =>
      cases shape
      exact node2 (.badReturn _ _ _ _ _ _ _ _ badMatch noSuccess)
        (functionType_complete arrow) (arguments_complete arguments)

/-- Every published source judgment has a generated tree. The external lookup
and matching relations are the same on both sides, including failure guards. -/
theorem complete {goal : Judgment} (source : Source space lookup matching goal) :
    Nonempty (Tree space lookup matching goal) := by
  cases goal with
  | annotations => exact annotations_complete source
  | intrinsic => exact intrinsic_complete source
  | occurrences => exact occurrences_complete source
  | storage => exact storage_complete source
  | lookup => exact lookup_complete source
  | typeOf => exact typeOf_complete source
  | matchTypes => exact matchTypes_complete source
  | matching => exact matching_complete source
  | typeAt => exact typeAt_complete source
  | cast => exact cast_complete source
  | castBatch => exact castBatch_complete source
  | functionType => exact functionType_complete source
  | arguments => exact arguments_complete source
  | application => exact application_complete source
  | applicability => exact applicability_complete source

theorem source_iff_tree (goal : Judgment) :
    Source space lookup matching goal ↔ Nonempty (Tree space lookup matching goal) :=
  ⟨complete, fun ⟨tree⟩ => sound tree⟩

#print axioms complete
#print axioms source_iff_tree

end Mettapedia.Languages.MeTTa.HE.Spec.Type.RulePresentation
