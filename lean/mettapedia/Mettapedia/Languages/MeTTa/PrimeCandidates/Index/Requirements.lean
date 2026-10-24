import Mettapedia.Enactive.Razor

/-!
# Evidence for requirements in Prime specification studies

This module is bookkeeping for an explicitly supplied type of systems and
predicates on those systems. Applications choose their actual calculus, model
or assembly before stating a requirement. There is no implicit class of all
Prime candidates here, and no evaluation or type-theory choice is imposed.

Evidence for an assembly keeps the same assembly index throughout. Universal
consequences use ordinary quantification over the supplied class, with a
separate existence witness when nonvacuity matters. Comparing a preference
does not prove that the preferred construction is logically forced.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Requirements

open Mettapedia.Enactive.Razor

universe u v

/-- One actual counterexample refutes a universal consequence, even when the
class also has an explicit existence witness. -/
theorem counterexample_refutes_consequence {Candidate : Type u}
    {admissible property : Candidate → Prop} {candidate : Candidate}
    (accepted : admissible candidate) (fails : ¬ property candidate) :
    ¬ ((∃ candidate, admissible candidate) ∧
      ∀ candidate, admissible candidate → property candidate) := by
  rintro ⟨_, entails⟩
  exact fails (entails candidate accepted)

/-- An empty class supplies no witness, regardless of its vacuous universal
consequences. -/
theorem empty_class_excludes_consequence {Candidate : Type u}
    {admissible property : Candidate → Prop}
    (impossible : ¬ ∃ candidate, admissible candidate) :
    ¬ ((∃ candidate, admissible candidate) ∧
      ∀ candidate, admissible candidate → property candidate) := by
  rintro ⟨witness, _⟩
  exact impossible witness

/-- A named family of semantic requirements and the subset currently demanded.
`holds` must state the actual property, including any observer or assumptions;
names and evidence provenance belong to its application-specific ledger. -/
structure Specification (Candidate : Type u) (Requirement : Type v) where
  holds : Requirement → Candidate → Prop
  required : List Requirement

namespace Specification

variable {Candidate : Type u} {Requirement : Type v}

def Satisfies (spec : Specification Candidate Requirement) (candidate : Candidate) : Prop :=
  ∀ requirement ∈ spec.required, spec.holds requirement candidate

/-- The same candidate index is shared by every supported requirement. -/
structure Evidence (spec : Specification Candidate Requirement) (candidate : Candidate) where
  supported : List Requirement
  verifies : ∀ requirement ∈ supported, spec.holds requirement candidate

def Evidence.remaining [DecidableEq Requirement]
    {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) : List Requirement :=
  spec.required.filter (fun requirement => requirement ∉ evidence.supported)

/-- Completing the evidence list establishes the conjunction for this actual
candidate, not for a collection of independently chosen witnesses. -/
theorem Evidence.complete [DecidableEq Requirement]
    {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) (complete : evidence.remaining = []) :
    spec.Satisfies candidate := by
  intro requirement required
  apply evidence.verifies requirement
  by_contra unsupported
  have member : requirement ∈ evidence.remaining := by
    simp only [Evidence.remaining, List.mem_filter, decide_eq_true_eq]
    exact ⟨required, unsupported⟩
  rw [complete] at member
  exact List.not_mem_nil member

/-- Requiring more properties narrows the candidate class, not the meaning
of the properties that were already present. -/
def extend (spec : Specification Candidate Requirement) (additional : List Requirement) :
    Specification Candidate Requirement :=
  { spec with required := spec.required ++ additional }

theorem satisfies_extend_iff (spec : Specification Candidate Requirement)
    (additional : List Requirement) (candidate : Candidate) :
    (spec.extend additional).Satisfies candidate ↔
      spec.Satisfies candidate ∧
        ∀ requirement ∈ additional, spec.holds requirement candidate := by
  constructor
  · intro satisfies
    exact ⟨fun requirement member => satisfies requirement (List.mem_append.mpr (.inl member)),
      fun requirement member => satisfies requirement (List.mem_append.mpr (.inr member))⟩
  · rintro ⟨original, added⟩ requirement member
    rcases List.mem_append.mp member with before | after
    · exact original requirement before
    · exact added requirement after

/-- A preference relation is restricted to independently stated requirements.
The preference alone does not supply a satisfaction proof or a selection. -/
def compare (spec : Specification Candidate Requirement) (preference : Criterion Candidate) :
    Criterion Candidate :=
  { preference with admissible := fun candidate =>
      spec.Satisfies candidate ∧ preference.admissible candidate }

theorem optimal_satisfies (spec : Specification Candidate Requirement)
    (preference : Criterion Candidate) {candidate : Candidate}
    (optimal : (spec.compare preference).IsOptimal candidate) : spec.Satisfies candidate :=
  optimal.1.1

/-- Necessity survives adding consistent requirements. The inhabitance premise
cannot be dropped: inconsistent extensions do not determine a design. -/
theorem consequence_of_extension (spec : Specification Candidate Requirement)
    (additional : List Requirement) {property : Candidate → Prop}
    (consequence : (∃ candidate, spec.Satisfies candidate) ∧
      ∀ candidate, spec.Satisfies candidate → property candidate)
    (consistent : ∃ candidate, (spec.extend additional).Satisfies candidate) :
    ((∃ candidate, (spec.extend additional).Satisfies candidate) ∧
      ∀ candidate, (spec.extend additional).Satisfies candidate → property candidate) := by
  refine ⟨consistent, ?_⟩
  intro candidate satisfies
  exact consequence.2 candidate
    ((spec.satisfies_extend_iff additional candidate).mp satisfies).1

end Specification

/-! ## Specifications on parts of one assembly

Projection brings a component's requirements to the actual assembly which
contains it. Conjunction then keeps that same assembly index throughout.
These operations do not assert that arbitrary components are compatible:
interface agreement is a further requirement on the assembly, and must be
proved before it can appear in completed evidence.
-/

namespace Specification

universe u' v'

variable {Candidate : Type u} {Requirement : Type v}
  {Whole : Type u'} {OtherRequirement : Type v'}

/-- Read component requirements on the component actually selected by an
assembly. No independent existential witness is substituted for this part. -/
def pullback (spec : Specification Candidate Requirement)
    (project : Whole → Candidate) : Specification Whole Requirement where
  holds requirement whole := spec.holds requirement (project whole)
  required := spec.required

@[simp] theorem satisfies_pullback_iff
    (spec : Specification Candidate Requirement) (project : Whole → Candidate)
    (whole : Whole) :
    (spec.pullback project).Satisfies whole ↔ spec.Satisfies (project whole) := Iff.rfl

/-- Component evidence can be used only at its actual projected index. -/
def Evidence.pullback {spec : Specification Candidate Requirement}
    (project : Whole → Candidate) (whole : Whole)
    (evidence : spec.Evidence (project whole)) :
    (spec.pullback project).Evidence whole where
  supported := evidence.supported
  verifies := evidence.verifies

/-- Combine two requirement namespaces without merging their identities. -/
def conjoin (left : Specification Candidate Requirement)
    (right : Specification Candidate OtherRequirement) :
    Specification Candidate (Requirement ⊕ OtherRequirement) where
  holds
    | .inl requirement => left.holds requirement
    | .inr requirement => right.holds requirement
  required := left.required.map Sum.inl ++ right.required.map Sum.inr

theorem satisfies_conjoin_iff (left : Specification Candidate Requirement)
    (right : Specification Candidate OtherRequirement) (candidate : Candidate) :
    (left.conjoin right).Satisfies candidate ↔
      left.Satisfies candidate ∧ right.Satisfies candidate := by
  constructor
  · intro satisfies
    constructor
    · intro requirement required
      exact satisfies (.inl requirement) (by simp [conjoin, required])
    · intro requirement required
      exact satisfies (.inr requirement) (by simp [conjoin, required])
  · rintro ⟨leftHolds, rightHolds⟩ requirement required
    cases requirement with
    | inl requirement =>
        exact leftHolds requirement (by simpa [conjoin] using required)
    | inr requirement =>
        exact rightHolds requirement (by simpa [conjoin] using required)

/-- Both proofs concern the same candidate. This constructor cannot assemble
evidence for different candidates merely because both exist. -/
def Evidence.conjoin {left : Specification Candidate Requirement}
    {right : Specification Candidate OtherRequirement} {candidate : Candidate}
    (leftEvidence : left.Evidence candidate)
    (rightEvidence : right.Evidence candidate) :
    (left.conjoin right).Evidence candidate where
  supported := leftEvidence.supported.map Sum.inl ++ rightEvidence.supported.map Sum.inr
  verifies := by
    intro requirement supported
    cases requirement with
    | inl requirement =>
        exact leftEvidence.verifies requirement (by simpa using supported)
    | inr requirement =>
        exact rightEvidence.verifies requirement (by simpa using supported)

/-- Evidence growth does not change old predicates or the candidate. The
new requirement is added only with a proof at that very index. -/
def Evidence.add {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) (requirement : Requirement)
    (proof : spec.holds requirement candidate) : spec.Evidence candidate where
  supported := requirement :: evidence.supported
  verifies := by
    intro claimed membership
    rcases List.mem_cons.mp membership with rfl | previous
    · exact proof
    · exact evidence.verifies claimed previous

theorem Evidence.remaining_add_subset [DecidableEq Requirement]
    {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) (requirement : Requirement)
    (proof : spec.holds requirement candidate) :
    (evidence.add requirement proof).remaining ⊆ evidence.remaining := by
  intro claimed remaining
  simp only [Evidence.remaining, Evidence.add, List.mem_filter,
    decide_eq_true_eq, List.mem_cons, not_or] at remaining ⊢
  exact ⟨remaining.1, remaining.2.2⟩

end Specification

#print axioms Specification.Evidence.complete
#print axioms Specification.satisfies_conjoin_iff
#print axioms Specification.Evidence.remaining_add_subset

end Mettapedia.Languages.MeTTa.PrimeCandidates.Requirements
