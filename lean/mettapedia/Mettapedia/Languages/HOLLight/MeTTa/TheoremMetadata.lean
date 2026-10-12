import Mettapedia.Languages.HOLLight.MeTTa.Transitivity

/-!
# Logical support of retained theorem metadata

The authored checker keeps ordered lists and proof origins. Shared HOL rules
use finite sets of canonical hypotheses and axiom sequents. These laws give
the precise support interpretation without discarding the original lists.
Faithful readback is qualified by the actual registered identities, not by
constant spellings or the presence of theorem-shaped data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TheoremMetadata

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open Representation (registeredOperatorAtom termAtom theoremAtom)

/-- The shared term carrier supplies the hypothesis representation. -/
def hypothesisAtom (constants : Const → Atom) (hypothesis : CanonicalTerm) : Atom :=
  termAtom registeredOperatorAtom constants [] hypothesis.term

/-- Encoding the actual ordered union gives exactly the image of logical
support. No order or occurrence list is reconstructed from that support. -/
theorem union_encoded_support {Value : Type} [DecidableEq Value]
    (encode : Value → Atom) (left right : List Value) :
    (Transitivity.union (left.map encode) (right.map encode)).toFinset =
      (left.toFinset ∪ right.toFinset).image encode := by
  have support : (Transitivity.union (left.map encode) (right.map encode)).toFinset =
      (left.map encode).toFinset ∪ (right.map encode).toFinset := by
    apply Finset.ext
    intro item
    simp only [List.mem_toFinset, Finset.mem_union, Transitivity.union_support]
  rw [support]
  simp only [List.toFinset_map, Finset.image_union]

/-- Registered canonical hypothesis identities are recoverable from a
source metadata list, independently of its order and repetition. -/
theorem hypothesis_support_faithful (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (left right : List CanonicalTerm)
    (leftFormed : ∀ hypothesis ∈ left, SignatureFormation.AnnotationsFormed world.signature hypothesis.term)
    (rightFormed : ∀ hypothesis ∈ right, SignatureFormation.AnnotationsFormed world.signature hypothesis.term) :
    (left.map (hypothesisAtom constants)).toFinset = (right.map (hypothesisAtom constants)).toFinset ↔
      left.toFinset = right.toFinset := by
  constructor
  · intro equal
    apply Finset.ext
    intro hypothesis
    simp only [List.mem_toFinset]
    constructor
    · intro member
      have encoded : hypothesisAtom constants hypothesis ∈ (right.map (hypothesisAtom constants)).toFinset := by
        rw [← equal]
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨hypothesis, member, rfl⟩
      obtain ⟨other, otherMember, same⟩ := List.mem_map.mp (List.mem_toFinset.mp encoded)
      have termsSame := TermReflection.registered_termAtom_injective world constants identified [] other.term
        hypothesis.term (rightFormed other otherMember) (leftFormed hypothesis member) same
      have sameTerm : other = hypothesis := CanonicalTerm.ext_term termsSame
      simpa only [sameTerm] using otherMember
    · intro member
      have encoded : hypothesisAtom constants hypothesis ∈ (left.map (hypothesisAtom constants)).toFinset := by
        rw [equal]
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨hypothesis, member, rfl⟩
      obtain ⟨other, otherMember, same⟩ := List.mem_map.mp (List.mem_toFinset.mp encoded)
      have termsSame := TermReflection.registered_termAtom_injective world constants identified [] other.term
        hypothesis.term (leftFormed other otherMember) (rightFormed hypothesis member) same
      have sameTerm : other = hypothesis := CanonicalTerm.ext_term termsSame
      simpa only [sameTerm] using otherMember
  · intro equal
    simpa only [List.toFinset_map] using congrArg (fun support : Finset CanonicalTerm => support.image (hypothesisAtom constants)) equal

/-- Discharge compares actual registered canonical identities. Every matching
occurrence is removed, while the other occurrences retain their source order.
No global injectivity assumption is imposed on uninterpreted vocabulary. -/
theorem remove_encoded_hypothesis (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (removed : CanonicalTerm)
    (removedFormed : SignatureFormation.AnnotationsFormed world.signature removed.term)
    (items : List CanonicalTerm)
    (formed : ∀ hypothesis ∈ items, SignatureFormation.AnnotationsFormed world.signature hypothesis.term) :
    (items.map (hypothesisAtom constants)).filter (fun entry => entry != hypothesisAtom constants removed) =
      (items.filter (fun hypothesis => hypothesis != removed)).map (hypothesisAtom constants) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      have comparison : (hypothesisAtom constants first != hypothesisAtom constants removed) = (first != removed) := by
        by_cases same : first = removed
        · simp [bne, same]
        · have encodedDifferent : hypothesisAtom constants first ≠ hypothesisAtom constants removed := by
            intro equal
            apply same
            exact CanonicalTerm.ext_term (TermReflection.registered_termAtom_injective world constants identified []
              first.term removed.term (formed first (by simp)) removedFormed equal)
          simp [bne, beq_eq_decide, encodedDifferent, same]
      simp only [List.map_cons, List.filter_cons, comparison]
      have tail := ih (fun hypothesis member => formed hypothesis (List.mem_cons_of_mem first member))
      split <;> simp only [List.map_cons, tail]

/-- The exact source discharge list has the shared rule's erased logical
support, without reconstructing an occurrence list from a finite set. -/
theorem remove_encoded_support (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (removed : CanonicalTerm)
    (removedFormed : SignatureFormation.AnnotationsFormed world.signature removed.term)
    (items : List CanonicalTerm)
    (formed : ∀ hypothesis ∈ items, SignatureFormation.AnnotationsFormed world.signature hypothesis.term) :
    ((items.map (hypothesisAtom constants)).filter (fun entry => entry != hypothesisAtom constants removed)).toFinset =
      (items.toFinset.erase removed).image (hypothesisAtom constants) := by
  rw [remove_encoded_hypothesis world constants identified removed removedFormed items formed]
  simp only [List.toFinset_map]
  have remaining : (items.filter (fun hypothesis => hypothesis != removed)).toFinset = items.toFinset.erase removed := by
    ext hypothesis
    simp [and_comm]
  rw [remaining]

/-- Dependency labels recover their axiom sequents only through a faithful
selected label interpretation. Equal printed labels are no substitute. -/
theorem axiom_support_faithful (encode : Sequent → Atom) (faithful : Function.Injective encode)
    (left right : List Sequent) :
    (left.map encode).toFinset = (right.map encode).toFinset ↔ left.toFinset = right.toFinset := by
  simp only [List.toFinset_map]
  exact Finset.image_injective faithful |>.eq_iff

/-- Logical support omits proof origins, but the retained record distinguishes
those origins even when every logical field agrees. -/
theorem different_origins_distinguish_records (constants : Const → Atom) (positions : List Ty)
    (conclusion : DBTerm) (hypotheses dependencies : List Atom) (first second : Atom)
    (different : first ≠ second) :
    theoremAtom constants positions conclusion hypotheses dependencies first ≠
      theoremAtom constants positions conclusion hypotheses dependencies second := by
  simpa using different

end Mettapedia.Languages.HOLLight.MeTTa.TheoremMetadata
