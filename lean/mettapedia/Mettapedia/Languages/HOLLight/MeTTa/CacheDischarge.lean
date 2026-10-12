import Mettapedia.Languages.HOLLight.MeTTa.CacheUnion
import Mettapedia.Languages.HOLLight.MeTTa.DeductionAntisymmetry

/-!
# Ordered hypothesis discharge in an authorized cache

The actual rule removes the opposite conclusion from each hypothesis list
and then merges the resulting lists. Registered identity reflection connects
that operation to the shared calculus's two finite-set erasures. Dependencies
retain their labels and their existing ordered union.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.CacheDischarge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization

def hypotheses (constants : Const → Atom) (left right : Record) : List CanonicalTerm :=
  List.KeyedUnion.merge (TheoremMetadata.hypothesisAtom constants)
    (left.hypotheses.filter (fun term => term != right.conclusion))
    (right.hypotheses.filter (fun term => term != left.conclusion))

def record (constants : Const → Atom) (left right : Record)
    (conclusion : CanonicalTerm) (origin : Atom) : Record :=
  ⟨hypotheses constants left right, conclusion, CacheUnion.dependencies constants left right, origin⟩

private theorem union_encoding (left right : List CanonicalTerm) (constants : Const → Atom) :
    (List.KeyedUnion.merge (TheoremMetadata.hypothesisAtom constants) left right).map
        (TheoremMetadata.hypothesisAtom constants) =
      Transitivity.union (left.map (TheoremMetadata.hypothesisAtom constants))
        (right.map (TheoremMetadata.hypothesisAtom constants)) := by
  rw [List.KeyedUnion.map_keys]
  unfold Transitivity.union
  congr 1
  funext items item
  by_cases present : item ∈ items <;> simp [present]

theorem hypotheses_encoded (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) :
    (hypotheses constants left right).map (TheoremMetadata.hypothesisAtom constants) =
      DeductionAntisymmetry.hypotheses
        (TheoremMetadata.hypothesisAtom constants left.conclusion)
        (TheoremMetadata.hypothesisAtom constants right.conclusion)
        (left.hypotheses.map (TheoremMetadata.hypothesisAtom constants))
        (right.hypotheses.map (TheoremMetadata.hypothesisAtom constants)) := by
  unfold hypotheses
  rw [union_encoding]
  unfold DeductionAntisymmetry.hypotheses
  rw [TheoremMetadata.remove_encoded_hypothesis world constants identified right.conclusion
    rightFormed.1.1 left.hypotheses (fun term member => leftFormed.1.2 term (List.mem_toFinset.mpr member))]
  rw [TheoremMetadata.remove_encoded_hypothesis world constants identified left.conclusion
    leftFormed.1.1 right.hypotheses (fun term member => rightFormed.1.2 term (List.mem_toFinset.mpr member))]

private theorem filtered_support (items : List CanonicalTerm) (removed : CanonicalTerm) :
    (items.filter (fun term => term != removed)).toFinset = items.toFinset.erase removed := by
  ext term
  simp [and_comm]

theorem hypotheses_formed (world : TheoryContext) (constants : Const → Atom) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) (term : CanonicalTerm)
    (member : term ∈ hypotheses constants left right) : AnnotationsFormed world.signature term.term := by
  have admitted := List.KeyedUnion.mem_subset (TheoremMetadata.hypothesisAtom constants)
    (left.hypotheses.filter (fun term => term != right.conclusion))
    (right.hypotheses.filter (fun term => term != left.conclusion)) member
  rcases List.mem_append.mp admitted with first | second
  · exact leftFormed.1.2 term (List.mem_toFinset.mpr (List.mem_filter.mp first).1)
  · exact rightFormed.1.2 term (List.mem_toFinset.mpr (List.mem_filter.mp second).1)

theorem hypotheses_support (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) :
    (hypotheses constants left right).toFinset =
      (left.fact.sequent.hyp.erase right.conclusion) ∪ (right.fact.sequent.hyp.erase left.conclusion) := by
  have formed : ∀ term ∈
      (left.hypotheses.filter (fun term => term != right.conclusion)) ++
      (right.hypotheses.filter (fun term => term != left.conclusion)),
      AnnotationsFormed world.signature term.term := by
    intro term member
    rcases List.mem_append.mp member with first | second
    · exact leftFormed.1.2 term (List.mem_toFinset.mpr (List.mem_filter.mp first).1)
    · exact rightFormed.1.2 term (List.mem_toFinset.mpr (List.mem_filter.mp second).1)
  have support := List.KeyedUnion.readout_support (TheoremMetadata.hypothesisAtom constants) id
    (left.hypotheses.filter (fun term => term != right.conclusion))
    (right.hypotheses.filter (fun term => term != left.conclusion)) (by
      intro first firstMember second secondMember same
      exact CanonicalTerm.ext_term (TermReflection.registered_termAtom_injective world constants identified []
        first.term second.term (formed first firstMember) (formed second secondMember) same))
  simpa only [hypotheses, List.map_id, filtered_support, Record.fact] using support

theorem record_parts (world : TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants) (left right : Record)
    (leftFormed : TheoremFormed world.signature left.fact)
    (rightFormed : TheoremFormed world.signature right.fact) (conclusion : CanonicalTerm) (origin : Atom) :
    HasParts (record constants left right conclusion origin).fact
      (left.fact.axioms ∪ right.fact.axioms)
      ((left.fact.sequent.hyp.erase right.conclusion) ∪ (right.fact.sequent.hyp.erase left.conclusion)) conclusion :=
  ⟨CacheUnion.dependencies_support world constants identified left right leftFormed rightFormed,
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
    have admitted := List.KeyedUnion.mem_subset (Dependency.atom constants) left.dependencies right.dependencies present
    have annotations : AnnotationsFormed world.signature dependency.statement.term := by
      rcases List.mem_append.mp admitted with first | second
      · exact CacheUnion.dependency_formed world left leftFormed dependency first
      · exact CacheUnion.dependency_formed world right rightFormed dependency second
    exact ⟨annotations, by simp [Dependency.sequent]⟩

end Mettapedia.Languages.HOLLight.MeTTa.CacheDischarge
