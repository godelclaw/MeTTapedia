import Mettapedia.Logic.TheoryModel.Basic

/-!
# Consistency: a theory with a model

A set of sentences is consistent for a satisfaction relation when its model
class is nonempty (`Consistent`).  For two sentences this is a common model
(`consistent_pair_iff`): the theory–model reading of consistency.

Read with concretization as satisfaction, this is the consistency of gradual
types in Abstracting Gradual Typing (Garcia, Clark and Tanter, POPL 2016): a
static type satisfies the gradual types it concretizes, and two gradual types
are consistent when their concretizations share a static type.  Read with
completion as satisfaction, it is the consistency of partial programs.

Joint consistency implies pairwise consistency (`Consistent.pairwise`); the
converse fails when sentences share unknowns.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

universe uStr uSent

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-- **Consistency**: the theory has a model. -/
def Consistent (T : Set Sent) : Prop :=
  (models Sat T).Nonempty

/-- Two sentences are consistent exactly when some structure satisfies
both. -/
theorem consistent_pair_iff {φ ψ : Sent} :
    Consistent Sat {φ, ψ} ↔ ∃ m, Sat m φ ∧ Sat m ψ := by
  constructor
  · rintro ⟨m, model⟩
    exact ⟨m, model (Or.inl rfl), model (Or.inr rfl)⟩
  · rintro ⟨m, satisfiesφ, satisfiesψ⟩
    refine ⟨m, fun χ member => ?_⟩
    rcases member with rfl | rfl
    · exact satisfiesφ
    · exact satisfiesψ

/-- Consistency of two sentences does not depend on their order. -/
theorem consistent_pair_comm {φ ψ : Sent} :
    Consistent Sat {φ, ψ} ↔ Consistent Sat {ψ, φ} := by
  rw [consistent_pair_iff, consistent_pair_iff]
  exact ⟨fun ⟨m, first, second⟩ => ⟨m, second, first⟩,
    fun ⟨m, first, second⟩ => ⟨m, second, first⟩⟩

variable {Sat}

/-- Fewer sentences stay consistent. -/
theorem Consistent.mono {T T' : Set Sent} (included : T ⊆ T') (consistent : Consistent Sat T') :
    Consistent Sat T := by
  obtain ⟨m, model⟩ := consistent
  exact ⟨m, fun _ member => model (included member)⟩

variable (Sat)

/-- Pairwise consistency. -/
def PairwiseConsistent (T : Set Sent) : Prop :=
  ∀ φ ∈ T, ∀ ψ ∈ T, Consistent Sat {φ, ψ}

variable {Sat}

/-- Joint consistency implies pairwise consistency. -/
theorem Consistent.pairwise {T : Set Sent} (consistent : Consistent Sat T) :
    PairwiseConsistent Sat T := by
  intro φ memberφ ψ memberψ
  apply consistent.mono
  intro χ member
  rcases member with rfl | rfl
  · exact memberφ
  · exact memberψ

/-! ## Controls -/

namespace ConsistencyControl

/-- Booleans satisfy the predicates that hold of them. -/
def sat : Bool → (Bool → Prop) → Prop := fun value predicate => predicate value

/-- Positive: `· = true` and the trivial predicate share the model `true`. -/
theorem consistent_example : Consistent sat {(· = true), fun _ => True} :=
  (consistent_pair_iff sat).mpr ⟨true, rfl, trivial⟩

/-- Negative: `· = true` and `· = false` have no common model. -/
theorem inconsistent_example : ¬Consistent sat {(· = true), (· = false)} := by
  rw [consistent_pair_iff]
  rintro ⟨value, isTrue, isFalse⟩
  simp only [sat] at isTrue isFalse
  rw [isTrue] at isFalse
  cases isFalse

end ConsistencyControl

end Mettapedia.Logic.TheoryModel
