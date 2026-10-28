import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQuery

/-! Replacing the isolated lookup operation by a finite query preserves and
reflects every resulting binding assignment. Both sides match the original
output pattern and merge with the same initial bindings, so already bound
relation/literal slots and repeated clause variables remain constraints. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Query

open Mettapedia.OSLF.MeTTaIL Syntax Match Engine

def environment (known : List Pattern) : Engine.RelationEnv where
  tuples := fun requested _ => if requested = factRelation then known.map (fun fact => [fact]) else []

private theorem matched_argument (initial matched : Bindings) (head : String)
    (arguments : List Pattern) (fact : Pattern) :
    matched ∈ matchRelationArgs initial [.apply head arguments] [fact] ↔
      matched ∈ matchPattern (.apply head arguments) fact ∧
        (mergeBindings initial matched).isSome := by
  simp only [matchRelationArgs,matchRelationArgument,List.mem_flatMap]
  constructor
  · rintro ⟨raw,found,emitted⟩
    cases accepted : mergeBindings initial raw with
    | none => simp [accepted] at emitted
    | some extended =>
      rw [accepted] at emitted
      have same : matched = raw := by simpa [mergeBindings] using emitted
      subst matched
      exact ⟨found,by simp [accepted]⟩
  · rintro ⟨found,accepted⟩
    obtain ⟨extended,same⟩ := Option.isSome_iff_exists.mp accepted
    refine ⟨matched,found,?_⟩
    rw [same]
    simp [mergeBindings]

theorem query_answers_exact (known : List Pattern) (language : LanguageDef)
    (initial final : Bindings) (head : String) (arguments : List Pattern) :
    final ∈ premiseStepWithEnv (environment known) language initial
      (.relationQuery factRelation [.apply head arguments]) ↔
      ∃ fact ∈ known, ∃ matched ∈ matchPattern (.apply head arguments) fact,
        mergeBindings initial matched = some final := by
  have builtin : builtinRelationTuples language factRelation
      ([.apply head arguments].map (applyBindings initial)) = [] := rfl
  simp only [premiseStepWithEnv,relationQueryStep,builtin,List.nil_append,environment]
  constructor
  · intro emitted
    obtain ⟨tuple,present,output⟩ := List.mem_flatMap.mp emitted
    obtain ⟨fact,available,rfl⟩ := List.mem_map.mp present
    obtain ⟨extension,member,merged⟩ := List.mem_filterMap.mp output
    exact ⟨fact,available,extension,((matched_argument _ _ _ _ _).mp member).1,merged⟩
  · rintro ⟨fact,available,matched,found,merged⟩
    apply List.mem_flatMap.mpr
    refine ⟨[fact],List.mem_map.mpr ⟨fact,available,rfl⟩,?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨matched,(matched_argument _ _ _ _ _).mpr ⟨found,by simp [merged]⟩,merged⟩

theorem lookup_query_exact (known : List Pattern) (language : LanguageDef)
    (sourceEnvironment : Engine.RelationEnv) (initial final : Bindings)
    (head : String) (arguments : List Pattern) :
    final ∈ premiseStepWithEnv (environment known) language initial
      (.relationQuery factRelation [.apply head arguments]) ↔
      ∃ fact matched, ReferenceStep.Step sourceEnvironment Lookup.language (Lookup.call known) fact ∧
        matched ∈ matchPattern (.apply head arguments) fact ∧ mergeBindings initial matched = some final := by
  rw [query_answers_exact]
  constructor
  · rintro ⟨fact,available,matched,found,merged⟩
    exact ⟨fact,matched,(Lookup.reference_exact sourceEnvironment _ _).mpr available,found,merged⟩
  · rintro ⟨fact,matched,stepped,found,merged⟩
    exact ⟨fact,(Lookup.reference_exact sourceEnvironment _ _).mp stepped,matched,found,merged⟩

#print axioms query_answers_exact
#print axioms lookup_query_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Query
