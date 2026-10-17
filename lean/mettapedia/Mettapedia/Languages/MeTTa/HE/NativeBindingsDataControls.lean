import Mettapedia.Languages.MeTTa.HE.NativeBindingsData
import Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
import Mettapedia.Languages.MeTTa.HE.LeaTTaScopedQuery

/-!
# Binding-data retention and rejection controls

The general guard, decoding and injectivity laws live in `NativeBindingsData`.
These controls retain duplicate relations and alias endpoints, check recursively
stored values, and reject payload constructors outside the declared HE image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeBindingsDataControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge NativeBindingsData

def retained : Metta.Bindings :=
  [.val "x#0" (.sym "a"), .eq "x#0" "other", .eq "x#0" "other",
    .val "stored" (.expr [.sym "pair", .var "x#0", .var "other"])]

def payload : Atom := .expression [.symbol "he-query-bindings-v1", .expression
  [.expression [.symbol "he-query-value-v1", .var "x#0", .symbol "a"],
   .expression [.symbol "he-query-equality-v1", .var "x#0", .var "other"],
   .expression [.symbol "he-query-equality-v1", .var "x#0", .var "other"],
   .expression [.symbol "he-query-value-v1", .var "stored",
     .expression [.symbol "pair", .var "x#0", .var "other"]]]]

theorem ordered_encoding_retains_aliases_duplicates_and_values : bindingsData retained = some payload := by
  simp [bindingsData, bindingsInImage, retained, relationData, payload, atomInImage,
    atomsInImage, LeaTTaTypeConformance.fromLeaTTaAtom, LeaTTaTypeConformance.fromLeaTTaAtoms]

theorem ordered_decoding_retains_aliases_duplicates_and_values : readBindings payload = some retained := by
  simp [readBindings, readRelation, payload, retained, toLeaTTaAtom, toLeaTTaAtoms]

theorem exact_roundtrip : (bindingsData retained).bind readBindings = some retained := by
  rw [ordered_encoding_retains_aliases_duplicates_and_values]
  exact ordered_decoding_retains_aliases_duplicates_and_values

theorem logical_projection_retains_duplicate_edges :
    (QueryBindingProjection.project retained).equalities =
      [("x#0", "other"), ("x#0", "other")] := by
  simp [QueryBindingProjection.project, retained, leaEqualityEdges]

theorem logical_projection_retains_nested_assignments :
    (QueryBindingProjection.project retained).assignments =
      [("x#0", .symbol "a"),
        ("stored", .expression [.symbol "pair", .var "x#0", .var "other"])] := by
  simp [QueryBindingProjection.project, retained,
    LeaTTaTypeConformance.fromLeaTTaAtom, LeaTTaTypeConformance.fromLeaTTaAtoms]

theorem image_guard_accepts_inconsistent_values :
    (bindingsData [.val "x" (.sym "a"), .val "x" (.sym "b")]).isSome = true := by
  simp [bindingsData, bindingsInImage, atomInImage]

theorem inconsistent_values_have_no_logical_model (valuation : String → Metta.Atom) :
    ¬HEBindingSatisfied valuation
      (QueryBindingProjection.project [.val "x" (.sym "a"), .val "x" (.sym "b")]) := by
  intro satisfied
  have first := satisfied.1 "x" (.symbol "a") (by
    simp [QueryBindingProjection.project, LeaTTaTypeConformance.fromLeaTTaAtom])
  have second := satisfied.1 "x" (.symbol "b") (by
    simp [QueryBindingProjection.project, LeaTTaTypeConformance.fromLeaTTaAtom])
  have incompatible := first.symm.trans second
  simp [toLeaTTaAtom, applyClassSolution] at incompatible

def previous : Metta.Minimal.Stack :=
  [{ atom := .expr [.sym "saved", .var "pending"], vars := ["explicit"] }]

theorem actual_stack_scope_contains_pending_atom_names :
    "pending" ∈ Metta.Minimal.queryOpAvoid previous (.sym "query") [] := by
  simp [Metta.Minimal.queryOpAvoid, Metta.Minimal.liveStackVars, previous,
    Metta.Bindings.vars, Metta.Atom.vars]

theorem actual_stack_scope_contains_explicit_frame_names :
    "explicit" ∈ Metta.Minimal.queryOpAvoid previous (.sym "query") [] := by
  simp [Metta.Minimal.queryOpAvoid, Metta.Minimal.liveStackVars, previous,
    Metta.Bindings.vars, Metta.Atom.vars]

theorem empty_stack_omits_the_pending_name :
    "pending" ∉ Metta.Minimal.queryOpAvoid [] (.sym "query") [] := by
  simp [Metta.Minimal.queryOpAvoid, Metta.Minimal.liveStackVars,
    Metta.Bindings.vars, Metta.Atom.vars]

theorem actual_work_item_constructs_an_independent_derivation
    {space : Space} {query lhs rhs : Atom} {counter : Nat} {item : Metta.Minimal.Item}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (member : item ∈ Metta.Minimal.queryOpItemsOfRule previous (toLeaTTaAtom query)
      [] counter (toLeaTTaAtom lhs, toLeaTTaAtom rhs)) :
    ∃ emitted output merged,
      Spec.Eval.Steps.EquationQueryCandidateRel space (LeaTTaScopedQuery.liveScope previous) query
          (QueryBindingProjection.project []) emitted output ∧
        item = Metta.Minimal.evalResult previous (toLeaTTaAtom emitted) merged ∧
        ScopedEquationQuery.BindingInvariant (QueryBindingProjection.project merged) merged ∧
        ∀ valuation,
          HEBindingSatisfied valuation output ↔
            HEBindingSatisfied valuation (QueryBindingProjection.project merged) := by
  obtain ⟨emitted, output, merged, candidate, itemEq, paired, theory, _⟩ :=
    LeaTTaScopedQuery.queryOpItemsOfRule_sound stored leaBindingsHEImage_empty
      LeaTTaSpecConformance.leaRuntimeBindingInvariant_empty member
  exact ⟨emitted, output, merged, candidate, itemEq, paired, theory⟩

theorem malformed_outer_shape_rejected : readBindings (.symbol "bindings") = none := rfl

theorem malformed_relation_rejected :
    readBindings (.expression [.symbol "he-query-bindings-v1", .expression
      [.expression [.symbol "he-query-equality-v1", .var "x", .symbol "y"]]]) = none := by
  simp [readBindings, readRelation]

theorem host_float_rejected (value : Float) : bindingsData [.val "float" (.gnd (.float value))] = none := by
  simp [bindingsData, bindingsInImage, atomInImage, groundInImage]

theorem host_unit_rejected : bindingsData [.val "unit" (.gnd .unit)] = none := by
  simp [bindingsData, bindingsInImage, atomInImage, groundInImage]

theorem host_error_rejected (message : String) :
    bindingsData [.val "error" (.gnd (.error message))] = none := by
  simp [bindingsData, bindingsInImage, atomInImage, groundInImage]

theorem opaque_binding_payload_rejected (relations : List Metta.StoredBinding) :
    bindingsData [.val "opaque" (.gnd (.bindings relations))] = none := by
  simp [bindingsData, bindingsInImage, atomInImage, groundInImage]

theorem every_query_hit_has_lossless_binding_data
    {live : List Atom} {query lhs rhs : Atom} {specIncoming : Bindings}
    {incoming : Metta.Bindings} {counter : Nat} {hit : ScopedEquationQuery.Hit}
    (incomingImage : LeaBindingsHEImage incoming)
    (member : hit ∈ ScopedEquationQuery.ruleResults live query specIncoming incoming counter lhs rhs) :
    (bindingsData hit.bindings).bind readBindings = some hit.bindings :=
  readBindings_bindingsData hit.bindings
    (ScopedEquationQuery.ruleResults_bindingsImage incomingImage member)

end Mettapedia.Languages.MeTTa.HE.NativeBindingsDataControls
