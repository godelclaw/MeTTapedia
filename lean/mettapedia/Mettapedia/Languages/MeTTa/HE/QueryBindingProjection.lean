import Mettapedia.Languages.MeTTa.HE.NativeBindingsData

/-!
# Constructed logical presentation of executable query bindings

The projection retains every value assignment and explicit equality edge.
For image-valued records, its model theory is proved equal to the executable
record's model theory. A reachable runtime invariant then constructs the
paired query invariant; the caller need not supply logical correspondence.
Successful query hits construct both an independent derivation and the next
projected binding state. Logical endpoints are related by their complete
solution theories, while the data codec retains concrete relation order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaSpecConformance
open Spec.Eval.Steps

def project (bindings : Metta.Bindings) : Bindings :=
  ⟨bindings.filterMap (fun relation => match relation with
      | .val name value => some (name, fromLeaTTaAtom value)
      | .eq _ _ => none), leaEqualityEdges bindings⟩

theorem assignment_mem_iff (bindings : Metta.Bindings) (name : String) (value : Atom) :
    (name, value) ∈ (project bindings).assignments ↔
      ∃ original, Metta.BindingRel.val name original ∈ bindings ∧ fromLeaTTaAtom original = value := by
  constructor
  · intro member
    obtain ⟨relation, relationMember, converted⟩ := List.mem_filterMap.mp member
    cases relation with
    | val key original =>
        simp only [Option.some.injEq, Prod.mk.injEq] at converted
        obtain ⟨rfl, rfl⟩ := converted
        exact ⟨original, relationMember, rfl⟩
    | eq left right => simp at converted
  · rintro ⟨original, member, rfl⟩
    exact List.mem_filterMap.mpr ⟨.val name original, member, rfl⟩

theorem equality_mem_iff (bindings : Metta.Bindings) (left right : String) :
    (left, right) ∈ (project bindings).equalities ↔ .eq left right ∈ bindings :=
  mem_leaEqualityEdges_iff

/-- Complete solution-theory correspondence is derived from concrete fields. -/
theorem solutionTheory (bindings : Metta.Bindings) (image : LeaBindingsHEImage bindings) :
    LeaBindingSolutionTheoryEquiv (project bindings) bindings := by
  intro valuation
  constructor
  · intro satisfied
    constructor
    · intro key original member
      have assignment := satisfied.1 key (fromLeaTTaAtom original)
        ((assignment_mem_iff bindings key _).mpr ⟨original, member, rfl⟩)
      rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage (image key original member)] at assignment
      exact assignment
    · intro left right member
      exact satisfied.2 left right ((equality_mem_iff bindings left right).mpr member)
  · intro satisfied
    constructor
    · intro key value member
      obtain ⟨original, originalMember, rfl⟩ := (assignment_mem_iff bindings key value).mp member
      rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage (image key original originalMember)]
      exact satisfied.1 key original originalMember
    · intro left right member
      exact satisfied.2 left right ((equality_mem_iff bindings left right).mp member)

theorem assignmentsNonVariable (bindings : Metta.Bindings)
    (image : LeaBindingsHEImage bindings) (normalized : LeaAssignmentsNonVariable bindings) :
    HEAssignmentsNonVariable (project bindings) := by
  intro key target member
  obtain ⟨original, originalMember, decoded⟩ := (assignment_mem_iff bindings key _).mp member
  have translated := congrArg toLeaTTaAtom decoded
  rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage (image key original originalMember)] at translated
  exact normalized key target (by simpa only [toLeaTTaAtom, translated] using originalMember)

theorem paired (bindings : Metta.Bindings) (image : LeaBindingsHEImage bindings)
    (runtime : LeaRuntimeBindingInvariant bindings) :
    ScopedEquationQuery.BindingInvariant (project bindings) bindings :=
  ⟨⟨solutionTheory bindings image,
      assignmentsNonVariable bindings image runtime.assignmentsNonVariable, runtime⟩, image⟩

theorem paired_empty : ScopedEquationQuery.BindingInvariant (project []) [] :=
  paired [] leaBindingsHEImage_empty leaRuntimeBindingInvariant_empty

theorem value_name_mem {bindings : Metta.Bindings} {key name : String} {value : Metta.Atom}
    (member : .val key value ∈ bindings) (occurrence : name = key ∨ name ∈ value.vars) :
    name ∈ bindings.vars := by
  simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨.val key value, member, by simpa only [List.mem_cons] using occurrence⟩

theorem equality_name_mem {bindings : Metta.Bindings} {left right name : String}
    (member : .eq left right ∈ bindings) (occurrence : name = left ∨ name = right) :
    name ∈ bindings.vars := by
  simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨.eq left right, member, by simpa using occurrence⟩

/-- The projected presentation adds no variable outside the concrete record. -/
theorem binding_name_mem {bindings : Metta.Bindings} {name : String}
    (image : LeaBindingsHEImage bindings)
    (member : name ∈ EquationScope.bindingNames (project bindings)) : name ∈ bindings.vars := by
  simp only [EquationScope.bindingNames, List.mem_append, List.mem_flatMap] at member
  rcases member with assignment | equality
  · obtain ⟨⟨key, value⟩, stored, occurrence⟩ := assignment
    obtain ⟨original, originalMember, rfl⟩ := (assignment_mem_iff bindings key value).mp stored
    simp only [List.mem_cons] at occurrence
    rw [toLeaTTaAtom_fromLeaTTaAtom_of_heImage (image key original originalMember)] at occurrence
    exact value_name_mem originalMember occurrence
  · obtain ⟨⟨left, right⟩, stored, occurrence⟩ := equality
    apply equality_name_mem ((equality_mem_iff bindings left right).mp stored)
    simpa using occurrence

/-- Each query output provides a logical derivation and a constructed next
projected state with the same complete solution theory as that derivation. -/
theorem ruleResults_sound {space : Space} {live : List Atom} {query lhs rhs : Atom}
    {incoming : Metta.Bindings} {counter : Nat} {hit : ScopedEquationQuery.Hit}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : hit ∈ ScopedEquationQuery.ruleResults live query (project incoming) incoming counter lhs rhs) :
    ∃ output,
      EquationQueryCandidateRel space live query (project incoming) hit.value output ∧
        ScopedEquationQuery.BindingInvariant (project hit.bindings) hit.bindings ∧
        ∀ valuation,
          HEBindingSatisfied valuation output ↔ HEBindingSatisfied valuation (project hit.bindings) := by
  obtain ⟨output, derivation, next⟩ :=
    ScopedEquationQuery.ruleResults_sound stored (paired incoming image runtime) member
  have projectedNext := paired hit.bindings next.image next.semantic.runtime
  refine ⟨output, derivation, projectedNext, ?_⟩
  intro valuation
  exact (next.semantic.solutionTheory valuation).trans
    (projectedNext.semantic.solutionTheory valuation).symm

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
