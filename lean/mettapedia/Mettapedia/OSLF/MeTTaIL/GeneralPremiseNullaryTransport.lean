import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics
import Mettapedia.OSLF.MeTTaIL.CanonicalTyping

/-!
# Capture transport for nullary provider guards

A nullary query reads no captured value and produces no binding. Its selected
provider occurrence and complete event history therefore survive replacement
of the captures by any other typed assignment in the same rule context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax ScopedRuleMatching

theorem Interpreted.TracedArgumentsHold.nil_readout {context : Context} {index : Nat}
    {initial final : Assignment} {values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial [] values modes final origins) :
    values = [] ∧ modes = [] ∧ final = initial ∧ origins = [] := by
  cases held
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem DynamicInputs.nil_readout {context : Context} {index : Nat}
    {initial : Assignment} {modes : List RelationArgMode} {values : List Pattern}
    (held : DynamicInputs context index initial [] modes values) : modes = [] ∧ values = [] := by
  cases held
  exact ⟨rfl, rfl⟩

theorem Interpreted.TracedQuery.nullary_transport {environment : Environment} {context : Context}
    {relation : String} {initial final : Assignment} {row : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedQuery environment context relation [] initial row final origins) :
    final = initial ∧ origins = [] ∧
      ∀ other, TypedAssignment environment context other →
        GeneralPremise.TracedQuery environment context relation [] other row other [] := by
  cases held with
  | row selected declared typed arguments finalTyped =>
    obtain ⟨values, modes, same, origins⟩ := arguments.nil_readout
    refine ⟨same, origins, fun other otherTyped => .row selected declared typed ?_ otherTyped⟩
    rw [values, modes]
    exact .nil
  | dynamicRow registered declared resolved source selected typed arguments finalTyped =>
    obtain ⟨modes, inputs⟩ := resolved.nil_readout
    obtain ⟨values, _, same, origins⟩ := arguments.nil_readout
    refine ⟨same, origins, fun other otherTyped =>
      .dynamicRow registered declared ?_ source selected typed ?_ otherTyped⟩
    · rw [modes, inputs]
      exact .nil
    · rw [values, modes]
      exact .nil

theorem Interpreted.PremiseHolds.nullary_transport {environment : Environment} {context : Context}
    {relation : String} {initial final : Assignment} {event : Event}
    (held : GeneralPremise.PremiseHolds environment context (.relationQuery relation []) initial final event) :
    final = initial ∧
      ∀ other, TypedAssignment environment context other →
        GeneralPremise.PremiseHolds environment context (.relationQuery relation []) other other event := by
  cases held with
  | query query =>
    obtain ⟨same, origins, transport⟩ := query.nullary_transport
    refine ⟨same, fun other typed => ?_⟩
    rw [origins]
    exact .query (transport other typed)

def NullaryGuards (premises : List Premise) : Prop :=
  ∀ premise ∈ premises, ∃ relation, premise = .relationQuery relation []

def checkNullaryGuards (premises : List Premise) : Bool :=
  premises.all fun premise => match premise with
    | .relationQuery _ [] => true
    | _ => false

theorem checkNullaryGuards_iff (premises : List Premise) :
    checkNullaryGuards premises = true ↔ NullaryGuards premises := by
  constructor
  · intro checked premise member
    have accepted := List.all_eq_true.mp checked premise member
    cases premise with
    | relationQuery relation arguments =>
      cases arguments with
      | nil => exact ⟨relation, rfl⟩
      | cons _ _ => cases accepted
    | _ => cases accepted
  · intro guards
    apply List.all_eq_true.mpr
    intro premise member
    obtain ⟨relation, rfl⟩ := guards premise member
    rfl

theorem Interpreted.PremisesHold.nullary_transport {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {history : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (guards : NullaryGuards premises) :
    final = initial ∧
      ∀ other, TypedAssignment environment context other →
        GeneralPremise.PremisesHold environment context premises other other history := by
  cases held with
  | nil => exact ⟨rfl, fun _ _ => .nil⟩
  | @cons context premise premises initial middle final event history first rest =>
    obtain ⟨relation, same⟩ := guards premise List.mem_cons_self
    subst premise
    obtain ⟨middleEq, head⟩ := first.nullary_transport
    obtain ⟨finalEq, tail⟩ := rest.nullary_transport (fun p member => guards p (List.mem_cons_of_mem _ member))
    refine ⟨finalEq.trans middleEq, fun other typed => ?_⟩
    exact .cons (head other typed) (tail other typed)
termination_by premises.length
decreasing_by all_goals simp_all [List.length_cons]

/-- Canonicalizing captured collection presentations changes no guard event
and manufactures no new provider occurrence. -/
theorem Interpreted.PremisesHold.nullary_canon {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {history : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final history)
    (guards : NullaryGuards premises) (typed : TypedAssignment environment context initial) :
    GeneralPremise.PremisesHold environment context premises (CanonicalBags.canonAssignment initial)
      (CanonicalBags.canonAssignment final) history := by
  obtain ⟨same, transported⟩ := held.nullary_transport guards
  rw [same]
  exact transported _ (CanonicalBags.typedAssignment_canon typed)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
