import Mettapedia.Languages.C11.ReadExpressionHead

/-!
# Exhaustive executable contextual expression reductions

The executable operation returns all immediate head, fault-propagation and
nested-context reductions, in a retained occurrence order. The independent
relation states head rules and contextual closure without calling that
operation. Both directions hold for arbitrary finite expression nesting.
Events retain the complete focus context, distinguishing repeated operands.

Every reduction strictly decreases a constructed expression weight. This
excludes stuttering inside this call-free expression profile; it does not
assert termination of C loops, recursion or external interactions. The
relation preserves the declared pure memory and scope environment. The full
C11 side-effect and control machine remains an additional obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ReadExpression

open ObjectAccessMemory

inductive Reduction (layout : Layout) (policy : SignedConversionPolicy)
    (memory : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment) :
    Expression layout → Event layout → Expression layout → Prop where
  | head (before after : Expression layout) (observation : Observation)
      (reduced : HeadReduction layout policy memory environment before observation after) :
      Reduction layout policy memory environment before (event layout observation) after
  | fault (frame : Frame layout) (reason : Fault) :
      Reduction layout policy memory environment (frame.plug (.fault reason)) (event layout (.fault reason)) (.fault reason)
  | under (frame : Frame layout) (before after : Expression layout) (observed : Event layout)
      (reduced : Reduction layout policy memory environment before observed after) :
      Reduction layout policy memory environment (frame.plug before) (observed.under frame) (frame.plug after)

def faults (layout : Layout) (expression : Expression layout) : List (Event layout × Expression layout) :=
  (parts expression).filterMap fun part =>
    match part.2 with
    | .fault reason => some (event layout (.fault reason), .fault reason)
    | _ => none

theorem faults_sound (layout : Layout) (expression : Expression layout)
    (observed : Event layout) (after : Expression layout) (selected : (observed, after) ∈ faults layout expression) :
    ∃ (frame : Frame layout) (reason : Fault), frame.plug (.fault reason) = expression ∧ observed = event layout (.fault reason) ∧
      after = .fault reason := by
  obtain ⟨part, present, selected⟩ := List.mem_filterMap.mp selected
  obtain ⟨frame, child⟩ := part
  cases child <;> simp only [reduceCtorEq] at selected
  case fault reason =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj selected)
    exact ⟨frame, reason, parts_sound expression (frame, .fault reason) present, rfl, rfl⟩

theorem faults_complete (layout : Layout) (frame : Frame layout) (reason : Fault) :
    (event layout (.fault reason), Expression.fault reason) ∈ faults layout (frame.plug (.fault reason)) := by
  exact List.mem_filterMap.mpr ⟨(frame, .fault reason), parts_complete frame (.fault reason), rfl⟩

def steps (layout : Layout) (policy : SignedConversionPolicy) (memory : State layout.representation.characters)
    (environment : ScopedLvalues.Environment) (expression : Expression layout) : List (Event layout × Expression layout) :=
  ((head layout policy memory environment expression).toList.map
    (fun pair => (event layout pair.1, pair.2)) ++ faults layout expression) ++
    (parts expression).attach.flatMap (fun part =>
      (steps layout policy memory environment part.val.2).map
        (fun pair => (pair.1.under part.val.1, part.val.1.plug pair.2)))
termination_by weight expression
decreasing_by exact parts_weight expression part.val part.property

theorem steps_value (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (scalar : IntegerScalar.Value layout.parameters) :
    steps layout policy memory environment (.value scalar) = [] := by rw [steps]; rfl

theorem steps_fault (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment) (reason : Fault) :
    steps layout policy memory environment (.fault reason) = [] := by rw [steps]; rfl

theorem steps_sound (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Event layout)
    (selected : (observed, after) ∈ steps layout policy memory environment before) :
    Reduction layout policy (represent memory) environment before observed after := by
  rw [steps] at selected
  rcases List.mem_append.mp selected with immediate | nested
  · rcases List.mem_append.mp immediate with normal | fault
    · obtain ⟨pair, present, same⟩ := List.mem_map.mp normal
      obtain ⟨observation, result⟩ := pair
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact .head _ _ _ (head_sound _ _ _ _ _ _ _ (Option.mem_toList.mp present))
    · obtain ⟨frame, reason, same, rfl, rfl⟩ := faults_sound layout before observed after fault
      rw [← same]
      exact .fault frame reason
  · obtain ⟨part, _, inMap⟩ := List.mem_flatMap.mp nested
    obtain ⟨⟨frame, child⟩, inParts⟩ := part
    obtain ⟨pair, inChild, same⟩ := List.mem_map.mp inMap
    obtain ⟨observation, result⟩ := pair
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    have reduced := steps_sound layout policy memory environment child result observation inChild
    have source := parts_sound before (frame, child) inParts
    simpa only [source] using Reduction.under frame _ _ _ reduced
termination_by weight before
decreasing_by exact parts_weight before (frame, child) inParts

theorem steps_complete (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Event layout)
    (reduced : Reduction layout policy (represent memory) environment before observed after) :
    (observed, after) ∈ steps layout policy memory environment before := by
  induction reduced with
  | head before after observation reduced =>
      rw [steps]
      apply List.mem_append.mpr
      left
      apply List.mem_append.mpr
      left
      exact List.mem_map.mpr ⟨(observation, after),
        Option.mem_toList.mpr (head_complete _ _ _ _ _ _ _ reduced), rfl⟩
  | fault frame reason =>
      rw [steps]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (faults_complete layout frame reason))))
  | under frame before after observation reduced ih =>
      rw [steps]
      apply List.mem_append.mpr
      right
      let part : {part // part ∈ parts (frame.plug before)} := ⟨(frame, before), parts_complete frame before⟩
      apply List.mem_flatMap.mpr
      refine ⟨part, List.mem_attach _ _, ?_⟩
      exact List.mem_map.mpr ⟨(observation, after), ih, rfl⟩

theorem steps_iff (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Event layout) :
    (observed, after) ∈ steps layout policy memory environment before ↔
      Reduction layout policy (represent memory) environment before observed after :=
  ⟨steps_sound layout policy memory environment before after observed,
    steps_complete layout policy memory environment before after observed⟩

theorem reduction_weight (layout : Layout) (policy : SignedConversionPolicy)
    (memory : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Event layout)
    (reduced : Reduction layout policy memory environment before observed after) : weight after < weight before := by
  induction reduced with
  | head before after observation reduced => exact head_weight _ _ _ _ _ _ _ reduced
  | fault frame reason => exact frame_weight_positive frame (.fault reason)
  | under frame before after observation reduced ih => exact frame_weight_monotone frame before after ih

theorem steps_weight (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Event layout)
    (selected : (observed, after) ∈ steps layout policy memory environment before) : weight after < weight before :=
  reduction_weight _ _ _ _ _ _ _ (steps_sound _ _ _ _ _ _ _ selected)

theorem reduction_context (layout : Layout) (policy : SignedConversionPolicy)
    (memory : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment)
    (context : Context layout) (before after : Expression layout) (observed : Event layout)
    (reduced : Reduction layout policy memory environment before observed after) :
    Reduction layout policy memory environment (plug context before)
      ⟨context ++ observed.context, observed.observation⟩ (plug context after) := by
  induction context with
  | nil => exact reduced
  | cons frame rest ih => exact .under frame _ _ _ ih

inductive History (layout : Layout) (policy : SignedConversionPolicy)
    (memory : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment) :
    Expression layout → List (Event layout) → Expression layout → Prop where
  | empty (expression : Expression layout) : History layout policy memory environment expression [] expression
  | next (before intermediate after : Expression layout) (observed : Event layout) (rest : List (Event layout))
      (reduced : Reduction layout policy memory environment before observed intermediate)
      (history : History layout policy memory environment intermediate rest after) :
      History layout policy memory environment before (observed :: rest) after

theorem history_weight_bound (layout : Layout) (policy : SignedConversionPolicy)
    (memory : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (events : List (Event layout))
    (history : History layout policy memory environment before events after) : events.length + weight after ≤ weight before := by
  induction history with
  | empty expression => simp
  | next before intermediate after observed rest reduced history ih =>
      have decrease := reduction_weight _ _ _ _ _ _ _ reduced
      simp only [List.length_cons]
      omega

end Mettapedia.Languages.C11.ReadExpression
