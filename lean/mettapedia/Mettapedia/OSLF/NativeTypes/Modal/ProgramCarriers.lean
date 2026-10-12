import Mettapedia.OSLF.NativeTypes.Modal.SourceCarriers

open Mettapedia.OSLF.Framework

/-!
# Declared program carriers of schematic rewrite sources

Section 19.3 works with classifying presentations: a program result has an
authored base sort. A bare collection constructor has the same result sort
as its declared collection grammar rule, including when its schema retains
a REST variable. This finite program family does not enumerate arbitrary
arrow or collection-expression typings of raw syntax.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences

/-- The program result carriers are read from the language's actual type
declarations, rather than a manually supplied site or admissibility list. -/
def programCandidates (language : LanguageDef) : List TypeExpr :=
  (language.types.map fun type => TypeExpr.base type.name).eraseDups

def collectionDeclarations (language : LanguageDef) (kind : CollType) : List GrammarRule :=
  language.terms.filter fun constructor =>
    match constructor.params with
    | [.simple _ (.collection actual _)] => actual == kind
    | _ => false

/-- The finite classifying result of a constructor, declared variable or
bare collection comes from the authored signature. This test classifies
base results only; raw arrows and raw collection type expressions remain
outside this program family. -/
def classifyingProgramSource? (language : LanguageDef) (rule : RewriteRule) : Bool :=
  match rule.left with
  | .apply label _ =>
      (language.terms.filter fun constructor => constructor.label == label).all fun constructor =>
        language.types.any fun type => type.name == constructor.category
  | .fvar name =>
      match ruleFree rule name with
      | some (.base category) => language.types.any fun type => type.name == category
      | _ => false
  | .collection kind _ _ =>
      (collectionDeclarations language kind).all fun constructor =>
        language.types.any fun type => type.name == constructor.category
  | _ => false

theorem declared_program_candidate {language : LanguageDef} {type : TypeDecl}
    (declared : List.Mem type language.types) : TypeExpr.base type.name ∈ programCandidates language := by
  exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨type, declared, rfl⟩)

theorem program_candidate_in_source {language : LanguageDef} {rule : RewriteRule}
    {carrier : TypeExpr} (candidate : carrier ∈ programCandidates language) :
    carrier ∈ sourceCandidates language rule := by
  simp only [programCandidates, List.mem_eraseDups] at candidate
  simp only [sourceCandidates, List.mem_eraseDups, List.mem_append]
  exact Or.inl (Or.inl candidate)

private theorem result_declared {language : LanguageDef} {category : String}
    (accepted : language.types.any (fun type => type.name == category) = true) :
    TypeExpr.base category ∈ programCandidates language := by
  obtain ⟨type, membership, same⟩ := List.any_eq_true.mp accepted
  have equality : type.name = category := beq_iff_eq.mp same
  simpa only [equality] using declared_program_candidate membership

/-- Every independently typed base-result source admitted by the executable
classifying test has its carrier in the language-derived finite family.
For collections this refers to the classifying constructor result, rather
than all raw collection-expression types of the same representation. -/
theorem classified_program_type_candidate {language : LanguageDef} {rule : RewriteRule}
    {category : String} (classified : classifyingProgramSource? language rule = true)
    (typed : HasType language (ruleFree rule) [] rule.left (.base category)) :
    TypeExpr.base category ∈ programCandidates language := by
  cases left : rule.left with
  | fvar name =>
      rw [left] at typed
      cases typed with
      | fvar lookup =>
          exact result_declared (by simpa only [classifyingProgramSource?, left, lookup] using classified)
  | apply label arguments =>
      rw [left] at typed
      cases typed with
      | constructor declared ordinary argumentsTyped =>
          rename_i constructor
          have selected : constructor ∈ language.terms.filter
              (fun declaration => declaration.label == constructor.label) := by simp [declared]
          have accepted := List.all_eq_true.mp
            (by simpa only [classifyingProgramSource?, left] using classified) constructor selected
          exact result_declared accepted
  | collection kind elements rest =>
      rw [left] at typed
      cases typed with
      | collectionConstructor declared shape elementsTyped =>
          rename_i constructor parameterName elementType
          have selected : constructor ∈ collectionDeclarations language kind := by
            simp [collectionDeclarations, declared, shape]
          have accepted := List.all_eq_true.mp
            (by simpa only [classifyingProgramSource?, left] using classified) constructor selected
          exact result_declared accepted
  | bvar index => simp [classifyingProgramSource?, left] at classified
  | lambda binder body => simp [classifyingProgramSource?, left] at classified
  | multiLambda arity binders body => simp [classifyingProgramSource?, left] at classified
  | subst body replacement => simp [classifyingProgramSource?, left] at classified

theorem classified_program_source_candidate {language : LanguageDef} {rule : RewriteRule}
    {category : String} (classified : classifyingProgramSource? language rule = true)
    (typed : HasType language (ruleFree rule) [] rule.left (.base category)) :
    TypeExpr.base category ∈ sourceCandidates language rule :=
  program_candidate_in_source (classified_program_type_candidate classified typed)

end Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers
