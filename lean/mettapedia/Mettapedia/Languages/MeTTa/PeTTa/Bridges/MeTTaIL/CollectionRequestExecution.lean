import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRequestPrimitives

/-!
# Complete-plan decoding for collection search

The rule reader and its ordered traversal are shared primitives. This module
reads the enclosing plan and current source, and compares the resulting native
search with the admitted Lean request construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRequestExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval BridgeKit WireKit
open CollectionLoggedSearchExecution

theorem select_complete_plan (environment permissions bound expected rules equations admitted source body : Atom) :
    let plan := apply "CompletePlan" [environment, permissions, bound, expected, rules, equations, admitted]
    let caller := [("source", source), ("plan", plan)]
    SpaceSemantics.selectCase caller plan
      [(apply "CompletePlan" [.var "environment", .var "permissions", .var "bound",
          .var "expected", .var "rules", .var "equations", .var "admitted"], body)] =
      some ([("admitted", admitted), ("equations", equations), ("rules", rules),
        ("expected", expected), ("bound", bound), ("permissions", permissions),
        ("environment", environment)] ++ caller, body) := by
  simp [apply, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Subst.lookup]

theorem select_noncollection_source (caller : Subst) (head : String)
    (values : List Atom) (yes no : Atom) (different : "PCollection" ≠ head)
    (fresh : caller.lookup "not-source" = none) :
    SpaceSemantics.selectCase caller (apply head values)
      [(apply "PCollection" [.var "kind", .var "targets", .symbol "RNone"], yes),
        (.var "not-source", no)] =
      some (("not-source", apply head values) :: caller, no) := by
  rw [PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.select_skip_constructor
    caller "PCollection" head [.var "kind", .var "targets", .symbol "RNone"]
    values yes [(.var "not-source", no)] (by decide) different]
  simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh]

theorem select_closed_collection_source (caller : Subst) (kind targets yes no : Atom)
    (kindFresh : caller.lookup "kind" = none)
    (targetsFresh : caller.lookup "targets" = none) :
    SpaceSemantics.selectCase caller (apply "PCollection" [kind, targets, .symbol "RNone"])
      [(apply "PCollection" [.var "kind", .var "targets", .symbol "RNone"], yes),
        (.var "not-source", no)] =
      some ([("targets", targets), ("kind", kind)] ++ caller, yes) := by
  dsimp [Subst.lookup] at kindFresh targetsFresh
  simp [apply, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    kindFresh, targetsFresh, Subst.lookup]

theorem select_open_collection_source (caller : Subst) (kind targets rest yes no : Atom)
    (fallbackFresh : caller.lookup "not-source" = none) :
    let source := apply "PCollection" [kind, targets, apply "RSome" [rest]]
    SpaceSemantics.selectCase caller source
      [(apply "PCollection" [.var "kind", .var "targets", .symbol "RNone"], yes),
        (.var "not-source", no)] =
      some (("not-source", source) :: caller, no) := by
  dsimp [Subst.lookup] at fallbackFresh
  simp [apply, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fallbackFresh, Subst.lookup]

def sourceSelection (caller : Subst) (source : Pattern) (yes no : Atom) : Subst × Atom :=
  match source with
  | .collection kind targets none =>
      ([("targets", encoded (InferenceCettaWire.encodePatterns targets)),
        ("kind", encoded (InferenceCettaWire.encodeCollectionType kind))] ++ caller, yes)
  | _ => (("not-source", encoded (InferenceCettaWire.encodePattern source)) :: caller, no)

theorem select_source_pattern (caller : Subst) (source : Pattern) (yes no : Atom)
    (kindFresh : caller.lookup "kind" = none)
    (targetsFresh : caller.lookup "targets" = none)
    (fallbackFresh : caller.lookup "not-source" = none) :
    SpaceSemantics.selectCase caller (encoded (InferenceCettaWire.encodePattern source))
      [(apply "PCollection" [.var "kind", .var "targets", .symbol "RNone"], yes),
        (.var "not-source", no)] = some (sourceSelection caller source yes no) := by
  cases source with
  | bvar index =>
      simpa only [sourceSelection, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeRest, encoded, number,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        select_noncollection_source caller "Var" [number index] yes no (by decide) fallbackFresh
  | fvar name =>
      simpa only [sourceSelection, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeRest, encoded, number,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        select_noncollection_source caller "FVar" [encoded (.string name)] yes no
        (by decide) fallbackFresh
  | apply head arguments =>
      simpa only [sourceSelection, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeRest, encoded, number,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        select_noncollection_source caller "PApp"
        [encoded (.string head), encoded (InferenceCettaWire.encodePatterns arguments)]
        yes no (by decide) fallbackFresh
  | lambda binder body =>
      simpa only [sourceSelection, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeRest, encoded, number,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        select_noncollection_source caller "PLam"
        [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.encodePattern body)]
        yes no (by decide) fallbackFresh
  | multiLambda arity binders body =>
      simpa only [sourceSelection, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeRest, encoded, number,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        select_noncollection_source caller "PMultiLam"
        [number arity, encoded (InferenceCettaWire.encodeList InferenceCettaWire.CettaTerm.string binders),
          encoded (InferenceCettaWire.encodePattern body)]
        yes no (by decide) fallbackFresh
  | subst body replacement =>
      simpa only [sourceSelection, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeRest, encoded, number,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        select_noncollection_source caller "PSubst"
        [encoded (InferenceCettaWire.encodePattern body), encoded (InferenceCettaWire.encodePattern replacement)]
        yes no (by decide) fallbackFresh
  | collection kind targets rest =>
      cases rest with
      | none =>
          simpa only [sourceSelection, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeRest, encoded, CettaWireAtom.encode,
            CettaWireAtom.encodeMany] using
            select_closed_collection_source caller
            (encoded (InferenceCettaWire.encodeCollectionType kind))
            (encoded (InferenceCettaWire.encodePatterns targets)) yes no kindFresh targetsFresh
      | some name =>
          simpa only [sourceSelection, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeRest, encoded, CettaWireAtom.encode,
            CettaWireAtom.encodeMany] using
            select_open_collection_source caller
            (encoded (InferenceCettaWire.encodeCollectionType kind))
            (encoded (InferenceCettaWire.encodePatterns targets)) (encoded (.string name))
            yes no fallbackFresh

@[metta_head "gslt:collection-search:requests-for-source"]
theorem requests_for_source_returns (state : Effects.State)
    (plan : GeneralExecutionAdmission.Plan) (table : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:requests-for-source"
        [encoded (CompletePlanWire.planTerm plan table bound expected),
          encoded (InferenceCettaWire.encodePattern source)])
      state (encoded (encodeList CollectionPlanExecution.requestEntryTerm
        (profileRequests plan source))) := by
  metta_call checked
  simp only [Library.bind, List.zip, List.zipWith, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  simp only [CompletePlanWire.planTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  apply pure_case_returns _ _ _ _ _ _ _ _ rfl
  · exact bound_returns _ _ _ (by rfl)
  · rw [select_complete_plan]
    rfl
  · intro selected body selection
    rw [select_complete_plan] at selection
    simp only [Option.some.injEq, Prod.mk.injEq] at selection
    obtain ⟨rfl, rfl⟩ := selection
    apply pure_case_returns _ _ _ _ _ _ _ _ rfl
    · exact bound_returns _ _ _ (by rfl)
    · rw [select_source_pattern _ _ _ _ (by rfl) (by rfl) (by rfl)]
      rfl
    · intro selected body selection
      rw [select_source_pattern _ _ _ _ (by rfl) (by rfl) (by rfl)] at selection
      cases source with
      | collection kind targets rest =>
          cases rest with
          | none =>
              simp only [sourceSelection, Option.some.injEq, Prod.mk.injEq] at selection
              obtain ⟨rfl, rfl⟩ := selection
              have requested := requests_from_rules_returns state kind targets plan.rules 0
              metta_capture_any requested
                unfolding [profileRequests, InferenceCettaWire.encodePatterns_eq_encodeList,
                  Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
          | some name =>
              simp only [sourceSelection, Option.some.injEq, Prod.mk.injEq] at selection
              obtain ⟨rfl, rfl⟩ := selection
              metta_eval with checked unfolding [profileRequests]
      | bvar | fvar | apply | lambda | multiLambda | subst =>
          simp only [sourceSelection, Option.some.injEq, Prod.mk.injEq] at selection
          obtain ⟨rfl, rfl⟩ := selection
          metta_eval with checked unfolding [profileRequests]

theorem requests_for_source_admitted_returns (state : Effects.State)
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (arranged : ArrangedRoot source) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:requests-for-source"
        [encoded (CompletePlanWire.planTerm plan table bound expected),
          encoded (InferenceCettaWire.encodePattern source)])
      state (encoded (encodeList CollectionPlanExecution.requestEntryTerm
        (CollectionExecutionAdmission.requestsForSource plan certificate source))) := by
  rw [← profileRequests_eq_admitted plan certificate source arranged]
  exact requests_for_source_returns state plan table bound expected source

@[metta_head "gslt:collection-search:run-plan"]
theorem run_plan_returns (state : Effects.State)
    (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (arranged : ArrangedRoot source) (work : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:run-plan"
        [encoded (CompletePlanWire.planTerm plan table bound expected),
          encoded (InferenceCettaWire.encodePattern source), number work])
      state (encoded (loggedRunTerm (CollectionLoggedSearch.run plan certificate source work))) := by
  have requests := requests_for_source_admitted_returns state plan certificate
    table bound expected source arranged
  have executed := CollectionLoggedSearchExecution.run_returns state
    (CollectionExecutionAdmission.requestsForSource plan certificate source)
    (fun _ member => CollectionExecutionAdmission.requestForSource?_fixed
      (CollectionExecutionAdmission.requestsForSource_selected member)) source work
  request_eval [requests, executed]
    unfolding [CollectionLoggedSearch.run, CollectionLoggedSearch.requests]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRequestExecution
