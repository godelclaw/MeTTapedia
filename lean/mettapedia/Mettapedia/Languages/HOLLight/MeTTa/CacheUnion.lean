import Mettapedia.Data.List.KeyedUnion
import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorization

/-!
# Exact source union of authorized theorem records

The source merges metadata by its encoded representation. The retained
representative and order are preserved. Registered identity reflection
proves that erasing those lists gives the shared calculus's hypothesis and
axiom unions, including dependencies with different retained labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.CacheUnion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization

def hypotheses (constants : Const → Atom) (left right : Record) : List CanonicalTerm :=
  List.KeyedUnion.merge (TheoremMetadata.hypothesisAtom constants) left.hypotheses right.hypotheses

def dependencies (constants : Const → Atom) (left right : Record) : List Dependency :=
  List.KeyedUnion.merge (Dependency.atom constants) left.dependencies right.dependencies

def record (constants : Const → Atom) (left right : Record)
    (conclusion : CanonicalTerm) (origin : Atom) : Record :=
  ⟨hypotheses constants left right, conclusion, dependencies constants left right, origin⟩

theorem hypotheses_encoded (constants : Const → Atom) (left right : Record) :
    (hypotheses constants left right).map (TheoremMetadata.hypothesisAtom constants) =
      Transitivity.union (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants)) := by
  unfold hypotheses
  rw [List.KeyedUnion.map_keys]
  unfold Transitivity.union
  congr 1
  funext items item
  by_cases present : item ∈ items <;> simp [present]

theorem dependencies_encoded (constants : Const → Atom) (left right : Record) :
    (dependencies constants left right).map (Dependency.atom constants) =
      Transitivity.union (left.dependencies.map (Dependency.atom constants))
        (right.dependencies.map (Dependency.atom constants)) := by
  unfold dependencies
  rw [List.KeyedUnion.map_keys]
  unfold Transitivity.union
  congr 1
  funext items item
  by_cases present : item ∈ items <;> simp [present]

theorem dependency_formed (world : TheoryContext) (record : Record)
    (formed : TheoremFormed world.signature record.fact) (dependency : Dependency)
    (member : dependency ∈ record.dependencies) :
    AnnotationsFormed world.signature dependency.statement.term := by
  apply (formed.2 dependency.sequent ?_).1
  simp only [Record.fact, List.mem_toFinset, List.mem_map]
  exact ⟨dependency, member, rfl⟩

theorem hypotheses_formed (world : TheoryContext) (constants : Const → Atom) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) (term : CanonicalTerm)
    (member : term ∈ hypotheses constants left right) : AnnotationsFormed world.signature term.term := by
  have admitted := List.KeyedUnion.mem_subset (TheoremMetadata.hypothesisAtom constants)
    left.hypotheses right.hypotheses member
  rcases List.mem_append.mp admitted with first | second
  · exact leftFormed.1.2 term (List.mem_toFinset.mpr first)
  · exact rightFormed.1.2 term (List.mem_toFinset.mpr second)

theorem hypotheses_support (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) :
    (hypotheses constants left right).toFinset = left.fact.sequent.hyp ∪ right.fact.sequent.hyp := by
  have formed : ∀ term ∈ left.hypotheses ++ right.hypotheses,
      AnnotationsFormed world.signature term.term := by
    intro term member
    rcases List.mem_append.mp member with first | second
    · exact leftFormed.1.2 term (List.mem_toFinset.mpr first)
    · exact rightFormed.1.2 term (List.mem_toFinset.mpr second)
  have support := List.KeyedUnion.readout_support (TheoremMetadata.hypothesisAtom constants) id
    left.hypotheses right.hypotheses (by
      intro first firstMember second secondMember same
      exact CanonicalTerm.ext_term (TermReflection.registered_termAtom_injective world constants identified []
        first.term second.term (formed first firstMember) (formed second secondMember) same))
  simpa only [hypotheses, List.map_id, Record.fact] using support

theorem dependencies_support (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) :
    ((dependencies constants left right).map Dependency.sequent).toFinset =
      left.fact.axioms ∪ right.fact.axioms := by
  have formed : ∀ dependency ∈ left.dependencies ++ right.dependencies,
      AnnotationsFormed world.signature dependency.statement.term := by
    intro dependency member
    rcases List.mem_append.mp member with first | second
    · exact dependency_formed world left leftFormed dependency first
    · exact dependency_formed world right rightFormed dependency second
  apply List.KeyedUnion.readout_support
  intro first firstMember second secondMember same
  have parts : first.label = second.label ∧
      TheoremMetadata.hypothesisAtom constants first.statement =
        TheoremMetadata.hypothesisAtom constants second.statement := by
    simpa only [Dependency.atom, Atom.expression.injEq, List.cons.injEq, true_and, and_true] using same
  have termsSame := TermReflection.registered_termAtom_injective world constants identified []
    first.statement.term second.statement.term (formed first firstMember) (formed second secondMember) parts.2
  have sameStatement := CanonicalTerm.ext_term termsSame
  simp only [Dependency.sequent, sameStatement]

theorem record_parts (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) (conclusion : CanonicalTerm) (origin : Atom) :
    HasParts (record constants left right conclusion origin).fact
      (left.fact.axioms ∪ right.fact.axioms) (left.fact.sequent.hyp ∪ right.fact.sequent.hyp) conclusion :=
  ⟨dependencies_support world constants identified left right leftFormed rightFormed,
    hypotheses_support world constants identified left right leftFormed rightFormed, rfl⟩

theorem record_formed (world : TheoryContext) (constants : Const → Atom) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) (conclusion : CanonicalTerm)
    (conclusionFormed : AnnotationsFormed world.signature conclusion.term) (origin : Atom) :
    TheoremFormed world.signature (record constants left right conclusion origin).fact := by
  refine ⟨⟨conclusionFormed, ?_⟩, ?_⟩
  · intro term member
    exact hypotheses_formed world constants left right leftFormed rightFormed term (List.mem_toFinset.mp member)
  · intro sequent member
    obtain ⟨dependency, present, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have admitted := List.KeyedUnion.mem_subset (Dependency.atom constants)
      left.dependencies right.dependencies present
    have annotations : AnnotationsFormed world.signature dependency.statement.term := by
      rcases List.mem_append.mp admitted with first | second
      · exact dependency_formed world left leftFormed dependency first
      · exact dependency_formed world right rightFormed dependency second
    exact ⟨annotations, by simp [Dependency.sequent]⟩

theorem record_encoded (constants : Const → Atom) (left right : Record)
    (conclusion : CanonicalTerm) (origin : Atom) :
    (record constants left right conclusion origin).atom constants =
      Representation.theoremAtom constants [] conclusion.term
        (Transitivity.union (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
          (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants)))
        (Transitivity.union (left.dependencies.map (Dependency.atom constants))
          (right.dependencies.map (Dependency.atom constants))) origin := by
  simp only [Record.atom, record, hypotheses_encoded, dependencies_encoded]

end Mettapedia.Languages.HOLLight.MeTTa.CacheUnion
