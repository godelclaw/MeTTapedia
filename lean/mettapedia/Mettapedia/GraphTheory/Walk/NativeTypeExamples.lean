import Mettapedia.GSLT.Core.RewritePathInversion
import Mettapedia.GraphTheory.Walk.Examples
import Mettapedia.GraphTheory.Walk.ProofTheory

/-!
# Positive and negative examples for graph-walk native types

The three-vertex path example now exercises all three layers together:
Mathlib reachability proofs, generated native certificates, and exact GSLT
executions.  The negative examples distinguish endpoint indexing from the
dynamic adjacency guard.
-/

namespace Mettapedia.GraphTheory.Walk.NativeTypeExamples

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Walk.Examples
open Mettapedia.GraphTheory.Walk.LanguageDef
open Mettapedia.GraphTheory.Walk.NativeTypeTheory
open Mettapedia.GraphTheory.Walk.Operational
open Mettapedia.GraphTheory.Walk.ProofTheory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.PathTypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax
open SimpleGraph

set_option autoImplicit false

def native01 : NativeProof pathGraph vertex0 vertex1 :=
  NativeProof.ofWalk pathGraph walk01

def native12 : NativeProof pathGraph vertex1 vertex2 :=
  NativeProof.ofWalk pathGraph walk12

def native02 : NativeProof pathGraph vertex0 vertex2 :=
  native01.comp native12

theorem native02_witness : native02.walk = walk02 := rfl

theorem native02_is_generated :
    NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 native02.term :=
  native02.native

theorem native_composition_executes :
    gradedPathDiamond (theory pathGraph pathGraph Hom.id) 5
      (saturatePredicate
        (gradedPathGSLT (theory pathGraph pathGraph Hom.id) 5)
        (fun candidate => candidate = donePattern walk02))
      (appendRequestPattern walk01 walk12) := by
  simpa [walk01, walk12, walk02] using
    (append_inhabits_exact_work_type pathGraph pathGraph Hom.id walk01 walk12)

theorem native_inverse_executes :
    gradedPathDiamond (theory pathGraph pathGraph Hom.id) 4
      (saturatePredicate
        (gradedPathGSLT (theory pathGraph pathGraph Hom.id) 4)
        (fun candidate => candidate = donePattern walk02.reverse))
      (reverseRequestPattern walk02) := by
  simpa [walk02] using
    (reverse_inhabits_exact_work_type pathGraph pathGraph Hom.id walk02)

/-- A valid closed walk occupies the diagonal native fiber. -/
def closedAtOne : NativeClosedWalk pathGraph pathGraph Hom.id vertex1 :=
  closedWalkInhabitant pathGraph pathGraph Hom.id vertex1
    (walk12.append walk12.reverse)

/-- Endpoint indexing is load-bearing independently of execution: the empty
walk at vertex 0 cannot inhabit the `0 → 1` native fiber. -/
theorem wrong_endpoint_not_native :
    ¬ NativeWalk pathGraph pathGraph Hom.id vertex0 vertex1
      (walkPattern (Walk.nil : pathGraph.Walk vertex0 vertex0)) := by
  intro native
  have indexed :=
    (nativeWalk_iff pathGraph pathGraph Hom.id vertex0 vertex1 _).1 native |>.2.1
  rcases indexed with ⟨node, equality⟩
  have endpoints : finPattern vertex0 = finPattern vertex1 := by
    simp only [walkPattern, walkNodePattern, Pattern.apply.injEq,
      List.cons.injEq] at equality
    aesop
  exact (finPattern_ne (by decide)) endpoints

/-- A syntactically formed recursive node that claims the absent edge
`0--2`.  It is intentionally not constructed through `SimpleGraph.Walk`. -/
def forgedWalk02 : Pattern :=
  .apply "WalkValue"
    [finPattern vertex0, finPattern vertex2,
      .apply "WalkCons"
        [finPattern vertex0, finPattern vertex2, finPattern vertex2,
          walkPattern (Walk.nil : pathGraph.Walk vertex2 vertex2)]]

/-- The generated static grammar accepts the forged term: all constructor
sorts are correct.  Its later rejection is therefore genuinely due to the
dynamic adjacency premise. -/
theorem forgedWalk02_has_static_type : grammarWalk forgedWalk02 := by
  unfold grammarWalk
  apply Mettapedia.GSLT.LanguageDef.CarrierWellSorted.checkHasType_complete_of_object
  · exact walkValue_typed (vertexPattern_typed vertex0.val)
      (vertexPattern_typed vertex2.val)
      (walkCons_typed (vertexPattern_typed vertex0.val)
        (vertexPattern_typed vertex2.val) (vertexPattern_typed vertex2.val)
        (walkPattern_and_node_typed (Walk.nil : pathGraph.Walk vertex2 vertex2)).1)
  · simp [forgedWalk02, walkPattern, walkNodePattern, finPattern,
      Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern,
      Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList,
      vertexPattern_object]

theorem forgedWalk02_reverse_start :
    rewriteOnce pathGraph pathGraph Hom.id
      (.apply "ReverseRequest" [forgedWalk02]) =
      [uncheckedReverseScanPattern
        (Walk.nil : pathGraph.Walk vertex2 vertex2)
        (Walk.nil : pathGraph.Walk vertex0 vertex0)] := by
  simpa [forgedWalk02, uncheckedReverseScanPattern, walkPattern,
    walkNodePattern] using
    (reverse_raw_start_exact pathGraph pathGraph Hom.id vertex0 vertex2
      (.apply "WalkCons"
        [finPattern vertex0, finPattern vertex2, finPattern vertex2,
          walkPattern (Walk.nil : pathGraph.Walk vertex2 vertex2)]))

/-- Sort-correct syntax still requires a real first edge. -/
theorem forged_nonedge_not_native :
    ¬ NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 forgedWalk02 := by
  intro native
  obtain ⟨next, encoded, edge, _⟩ :=
    (nativeWalk_cons_iff pathGraph pathGraph Hom.id vertex0 vertex2 _ _).1 native
  have same : vertex2 = next := finPattern_injective encoded
  subst next
  exact nonedge02 edge

/-- Every repeated endpoint is consistent, but the interior vertex is outside
`Fin 3`.  Unary vertex syntax alone does not enforce the finite bound. -/
def outOfRangeWalk : Pattern :=
  .apply "WalkValue" [finPattern vertex0, finPattern vertex1,
    .apply "WalkCons" [finPattern vertex0, vertexPattern 3, finPattern vertex1,
      .apply "WalkValue" [vertexPattern 3, finPattern vertex1,
        .apply "WalkCons" [vertexPattern 3, finPattern vertex1, finPattern vertex1,
          walkPattern (Walk.nil : pathGraph.Walk vertex1 vertex1)]]]]

theorem outOfRangeWalk_has_static_type : grammarWalk outOfRangeWalk := by
  simp only [outOfRangeWalk, walkPattern, walkNodePattern]
  unfold grammarWalk
  decide +kernel

theorem outOfRangeWalk_not_native :
    ¬ NativeWalk pathGraph pathGraph Hom.id vertex0 vertex1 outOfRangeWalk := by
  intro native
  obtain ⟨next, encoded, _, _⟩ :=
    (nativeWalk_cons_iff pathGraph pathGraph Hom.id vertex0 vertex1 _ _).1 native
  have decoded := congrArg (decodeFin? 3) encoded
  simp only [decodeFin?_finPattern] at decoded
  simp [decodeFin?] at decoded

/-- The first edge exists, but its tail starts at zero instead of one. -/
def inconsistentTailWalk : Pattern :=
  .apply "WalkValue" [finPattern vertex0, finPattern vertex0,
    .apply "WalkCons" [finPattern vertex0, finPattern vertex1, finPattern vertex0,
      walkPattern (Walk.nil : pathGraph.Walk vertex0 vertex0)]]

theorem inconsistentTailWalk_has_static_type : grammarWalk inconsistentTailWalk := by
  simp only [inconsistentTailWalk, walkPattern, walkNodePattern]
  unfold grammarWalk
  decide +kernel

theorem inconsistentTailWalk_not_native :
    ¬ NativeWalk pathGraph pathGraph Hom.id vertex0 vertex0 inconsistentTailWalk := by
  intro native
  obtain ⟨next, encoded, _, tail⟩ :=
    (nativeWalk_cons_iff pathGraph pathGraph Hom.id vertex0 vertex0 _ _).1 native
  have same : vertex1 = next := finPattern_injective encoded
  subst next
  obtain ⟨_, ⟨node, shape⟩, _⟩ :=
    (nativeWalk_iff pathGraph pathGraph Hom.id vertex1 vertex0 _).1 tail
  simp [walkPattern, walkNodePattern, finPattern, vertex0, vertex1, vertexPattern] at shape

/-- An empty `WalkNil` application violates its authored unary arity. -/
theorem malformed_nil_not_native :
    ¬ NativeWalk pathGraph pathGraph Hom.id vertex0 vertex0
      (.apply "WalkValue" [finPattern vertex0, finPattern vertex0, .apply "WalkNil" []]) := by
  intro native
  have checked := (nativeWalk_iff pathGraph pathGraph Hom.id vertex0 vertex0 _).1 native |>.1
  have rejected : ¬ grammarWalk
      (.apply "WalkValue" [finPattern vertex0, finPattern vertex0, .apply "WalkNil" []]) := by
    unfold grammarWalk
    decide +kernel
  exact rejected checked

/-- Decoding preserves the repeated-edge closed walk as a proof object. -/
theorem closed_walk_roundtrip :
    (NativeProof.ofAccepted pathGraph closedAtOne).walk = walk12.append walk12.reverse := by
  have roundtrip := (NativeProof.acceptedEquiv pathGraph vertex1 vertex1).symm_apply_apply
    (NativeProof.ofWalk pathGraph (walk12.append walk12.reverse))
  exact congrArg NativeProof.walk roundtrip

section AxiomAudit

#print axioms native02_is_generated
#print axioms native_composition_executes
#print axioms native_inverse_executes
#print axioms wrong_endpoint_not_native
#print axioms forgedWalk02_has_static_type
#print axioms forged_nonedge_not_native
#print axioms outOfRangeWalk_has_static_type
#print axioms outOfRangeWalk_not_native
#print axioms inconsistentTailWalk_has_static_type
#print axioms inconsistentTailWalk_not_native
#print axioms malformed_nil_not_native
#print axioms closed_walk_roundtrip

end AxiomAudit

end Mettapedia.GraphTheory.Walk.NativeTypeExamples
