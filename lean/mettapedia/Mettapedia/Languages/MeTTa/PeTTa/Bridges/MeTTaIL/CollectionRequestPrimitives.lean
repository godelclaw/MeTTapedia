import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionLoggedSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire

/-!
# Native collection request primitives

The existing complete-plan wire retains authored rules and their binding
elaboration.  The native request builder reads those fields without traversing
captured payloads.  Its source correspondence is qualified on arranged root
collections, as supplied by canonical search commits.
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

/-- The source-level request construction read by the native profile. -/
def requestFromRule (actualKind : CollType) (targets : List Pattern)
    (declaration : GeneralExecutionAdmission.RulePlan) :
    Option ScopedCollectionMachine.Request :=
  match declaration.rule.left with
  | .collection .vec _ _ => none
  | .collection kind schemas rest =>
      if kind = actualKind then
        some ⟨declaration.rule, declaration.binding.spec, 0, .left, [], 0, 0,
          [], schemas, rest, kind, targets⟩
      else none
  | _ => none

def requestsFromRules (ordinal : Nat) (actualKind : CollType)
    (targets : List Pattern) :
    List GeneralExecutionAdmission.RulePlan →
      List (Nat × ScopedCollectionMachine.Request)
  | [] => []
  | declaration :: rest =>
      match requestFromRule actualKind targets declaration with
      | some request => (ordinal, request) ::
          requestsFromRules (ordinal + 1) actualKind targets rest
      | none => requestsFromRules (ordinal + 1) actualKind targets rest

def profileRequests (plan : GeneralExecutionAdmission.Plan) : Pattern →
    List (Nat × ScopedCollectionMachine.Request)
  | .collection kind targets none => requestsFromRules 0 kind targets plan.rules
  | _ => []

def elaboratedTypeContext (types : List (String × TypeExpr)) :
    GeneralRuleBindingInference.Origin → List (String × TypeExpr)
  | .inferredGrammar implicitTypes => types ++ implicitTypes
  | .authored | .inferredRootInputs => types

theorem elaboratedTypeContext_eq (types : List (String × TypeExpr))
    (spec : RuleBindingSpec) (origin : GeneralRuleBindingInference.Origin) :
    elaboratedTypeContext types origin =
      types ++ (GeneralRuleBindingInference.BindingPlan.mk spec origin).implicitTypes := by
  cases origin <;> simp [elaboratedTypeContext,
    GeneralRuleBindingInference.BindingPlan.implicitTypes]

theorem requestsFromRules_eq_range (actualKind : CollType) (targets : List Pattern)
    (rules : List GeneralExecutionAdmission.RulePlan) (start : Nat) :
    requestsFromRules start actualKind targets rules =
      (List.range rules.length).filterMap (fun index =>
        rules[index]?.bind fun declaration =>
          (requestFromRule actualKind targets declaration).map fun request => (start + index, request)) := by
  induction rules generalizing start with
  | nil => simp [requestsFromRules]
  | cons declaration rest ih =>
      rw [requestsFromRules, List.length_cons, List.range_succ_eq_map,
        List.filterMap_cons, List.filterMap_map]
      simp only [List.getElem?_cons_zero,
        Option.bind_some, Nat.add_zero]
      rw [ih]
      cases requestFromRule actualKind targets declaration <;>
        simp [Nat.add_comm, Nat.add_left_comm]

theorem requestFromRule_eq_admitted (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (index : Nat) (declaration : GeneralExecutionAdmission.RulePlan)
    (selected : plan.rules[index]? = some declaration)
    (actualKind : CollType) (targets : List Pattern)
    (fixed : CanonicalBags.arrange actualKind targets = targets) :
    requestFromRule actualKind targets declaration =
      CollectionExecutionAdmission.requestForSource? plan certificate index
        (.collection actualKind targets none) := by
  cases left : declaration.rule.left <;>
    try simp [requestFromRule, CollectionExecutionAdmission.requestForSource?,
      CollectionExecutionAdmission.request?, selected, left]
  rename_i kind schemas rest
  cases kind <;> cases actualKind <;>
    simp_all


def ArrangedRoot : Pattern → Prop
  | .collection kind targets none => CanonicalBags.arrange kind targets = targets
  | _ => True

theorem arrangedRoot_canon (source : Pattern) : ArrangedRoot (CanonicalBags.canon source) := by
  cases source <;> simp only [CanonicalBags.canon, ArrangedRoot]
  rename_i kind elements rest
  cases rest with
  | none => exact CollectionExecutionAdmission.arrange_fixed _ _
  | some name => trivial

theorem profileRequests_eq_admitted (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Pattern) (arranged : ArrangedRoot source) :
    profileRequests plan source =
      CollectionExecutionAdmission.requestsForSource plan certificate source := by
  cases source with
  | collection kind targets rest =>
      cases rest with
      | some name =>
          simp [profileRequests, CollectionExecutionAdmission.requestsForSource,
            CollectionExecutionAdmission.requestForSource?]
      | none =>
          rw [profileRequests, requestsFromRules_eq_range]
          simp only [CollectionExecutionAdmission.requestsForSource, Nat.zero_add]
          apply List.filterMap_congr
          intro index member
          cases selected : plan.rules[index]? with
          | none =>
              simp [CollectionExecutionAdmission.requestForSource?,
                CollectionExecutionAdmission.request?, selected]
          | some declaration =>
              simp only [Option.bind_some]
              rw [requestFromRule_eq_admitted plan certificate index declaration selected
                kind targets arranged]
  | bvar | fvar | apply | lambda | multiLambda | subst =>
      simp [profileRequests, CollectionExecutionAdmission.requestsForSource,
        CollectionExecutionAdmission.requestForSource?]

theorem constructor_selection (caller : Subst) (head : String)
    (names : List String) (values : List Atom) (body : Atom)
    (rest : SpaceSemantics.Cases) (ordinary : head ≠ "cons")
    (distinct : names.Nodup) (length : values.length = names.length)
    (fresh : ∀ name ∈ names, Subst.lookup caller name = none) :
    SpaceSemantics.selectCase caller (.expression (.symbol head :: values))
      ((.expression (.symbol head :: names.map Atom.var), body) :: rest) =
      some ((names.zip values).reverse ++ caller, body) := by
  have matched : SpaceSemantics.matchValue caller
      (.expression (.symbol head :: names.map Atom.var))
      (.expression (.symbol head :: values)) =
      some ((names.zip values).reverse ++ caller) := by
    rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
      intro first rest same
      exact ordinary (Atom.symbol.inj (List.cons.inj same).1))]
    simp only [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, beq_self_eq_true,
      Option.bind_eq_bind]
    exact PureData.match_variable_values names values caller distinct length fresh
  rw [SpaceSemantics.selectCase, matched]

theorem select_rule_plan (actualKind targets ordinal rule spec origin body : Atom) :
    let entry := apply "RuleJobDeclaration"
      [ordinal, rule, apply "RuleBindingPlan" [spec, origin]]
    let caller := [("entry", entry), ("targets", targets), ("actual-kind", actualKind)]
    SpaceSemantics.selectCase caller entry
      [(apply "RuleJobDeclaration" [.var "declared-ordinal", .var "rule",
          apply "RuleBindingPlan" [.var "spec", .var "origin"]], body)] =
      some ([("origin", origin), ("spec", spec), ("rule", rule),
        ("declared-ordinal", ordinal)] ++ caller, body) := by
  simp [apply, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Subst.lookup]



/-- Rule fields are selected without inspecting their encoded payloads. -/
theorem select_rule_fields (caller : Subst) (label types premises left right binding body invalid : Atom)
    (fresh : ∀ name ∈ ["label", "types", "premises", "left", "right", "binding"],
      caller.lookup name = none) :
    SpaceSemantics.selectCase caller
      (apply "ScopedRewriteRuleV1" [label, types, premises, left, right, binding])
      [(apply "ScopedRewriteRuleV1" [.var "label", .var "types", .var "premises",
          .var "left", .var "right", .var "binding"], body), (.var "not-rule", invalid)] =
      some ([("binding", binding), ("right", right), ("left", left),
        ("premises", premises), ("types", types), ("label", label)] ++ caller, body) := by
  simpa using constructor_selection caller "ScopedRewriteRuleV1"
    ["label", "types", "premises", "left", "right", "binding"]
    [label, types, premises, left, right, binding] body [(.var "not-rule", invalid)]
    (by decide) (by decide) rfl fresh

theorem select_collection_fields (caller : Subst) (kind schemas rest body invalid : Atom)
    (fresh : ∀ name ∈ ["kind", "schemas", "rest"], caller.lookup name = none) :
    SpaceSemantics.selectCase caller
      (apply "PCollection" [kind, schemas, rest])
      [(apply "PCollection" [.var "kind", .var "schemas", .var "rest"], body),
        (.var "not-collection", invalid)] =
      some ([("rest", rest), ("schemas", schemas), ("kind", kind)] ++ caller, body) := by
  simpa using constructor_selection caller "PCollection" ["kind", "schemas", "rest"]
    [kind, schemas, rest] body [(.var "not-collection", invalid)]
    (by decide) (by decide) rfl fresh

syntax "request_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| request_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic|
      (metta_call checked
       try simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
         Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil.applySubstList_nil,
         Library.bind, List.zip, List.zipWith, List.reverse_cons, List.reverse_nil,
         List.nil_append, List.cons_append]
       metta_eval [$facts,*] with checked
         unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
           select_rule_plan, select_rule_fields, select_collection_fields,
           PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.select_skip_constructor,
           PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized.symbol_constructor_mismatch,
           encodeList, encodeOption, $extra,*]))

@[metta_head "gslt:collection-search:elaborated-types"]
theorem elaborated_types_returns (state : Effects.State)
    (types : List (String × TypeExpr))
    (origin : GeneralRuleBindingInference.Origin) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:elaborated-types"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm types),
          encoded (ScopedRuleJobReadoutExecution.originTerm origin)])
      state (encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm
        (elaboratedTypeContext types origin))) := by
  cases origin with
  | authored =>
      request_eval unfolding [ScopedRuleJobReadoutExecution.originTerm, elaboratedTypeContext]
  | inferredRootInputs =>
      request_eval unfolding [ScopedRuleJobReadoutExecution.originTerm, elaboratedTypeContext]
  | inferredGrammar implicitTypes =>
      have appendedAtBase := ScopedCollectionExecution.append_returns
        InferenceCettaWire.AuthoredRule.typeBindingTerm state types implicitTypes
      have appended := by
        metta_lift checked ["left", "right"] appendedAtBase
      request_eval [appended]
        unfolding [ScopedRuleJobReadoutExecution.originTerm, elaboratedTypeContext]


@[metta_head "gslt:collection-search:request-from-rule"]
theorem request_from_rule_returns (state : Effects.State)
    (actualKind : CollType) (targets : List Pattern)
    (declaration : GeneralExecutionAdmission.RulePlan) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:request-from-rule"
        [encoded (InferenceCettaWire.encodeCollectionType actualKind),
          encoded (encodeList InferenceCettaWire.encodePattern targets),
          encoded (ScopedRuleJobReadoutExecution.rulePlanTerm declaration)])
      state (encoded (encodeOption ScopedCollectionExecution.requestTerm
        (requestFromRule actualKind targets declaration))) := by
  obtain ⟨declarationIndex, authored, binding⟩ := declaration
  obtain ⟨spec, origin⟩ := binding
  obtain ⟨label, types, premises, left, right, bindings⟩ := authored
  have elaborated := elaborated_types_returns state types origin
  simp only [ScopedRuleJobReadoutExecution.rulePlanTerm,
    ScopedRuleJobReadoutExecution.bindingPlanTerm] at ⊢
  cases left <;> request_eval [elaborated]
    unfolding [requestFromRule, GeneralExecutionAdmission.RulePlan.rule,
      GeneralRuleBindingInference.BindingPlan.elaborate,
      ScopedCollectionExecution.requestTerm,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      InferenceCettaWire.AuthoredRule.rewriteTerm,
      InferenceCettaWire.AuthoredRule.bindingSpecTerm,
      InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
      InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest]
  rename_i kind schemas rest
  cases kind <;> cases actualKind <;>
    metta_eval [elaborated] with checked
      unfolding [requestFromRule, GeneralExecutionAdmission.RulePlan.rule,
        GeneralRuleBindingInference.BindingPlan.elaborate,
        encodeOption, elaboratedTypeContext_eq, ScopedCollectionExecution.requestTerm,
        ScopedCollectionMachine.Request.machine,
        InferenceCettaWire.AuthoredRule.optionalBindingTerm,
        RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
        InferenceCettaWire.AuthoredRule.rewriteTerm,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm,
        InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest]

  all_goals
    apply data_returns
    · decide +kernel
    · simp only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
      cases origin <;> simp [elaboratedTypeContext,
        GeneralRuleBindingInference.BindingPlan.implicitTypes,
        encoded, CettaWireAtom.encode, InferenceCettaWire.AuthoredRule.siteTerm,
        RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
        MatchAutomataBindingExecution.payloadBindingsTerm,
        InferenceCettaWire.encodePatterns_eq_encodeList,
        encodeList, InferenceCettaWire.encodeList]

@[metta_head "gslt:collection-search:requests-from-rules"]
theorem requests_from_rules_returns (state : Effects.State)
    (actualKind : CollType) (targets : List Pattern) :
    ∀ (rules : List GeneralExecutionAdmission.RulePlan) (ordinal : Nat),
    PureReturns library.runtime [] state
      (apply "gslt:collection-search:requests-from-rules"
        [number ordinal, encoded (InferenceCettaWire.encodeCollectionType actualKind),
          encoded (encodeList InferenceCettaWire.encodePattern targets),
          encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm rules)])
      state (encoded (encodeList CollectionPlanExecution.requestEntryTerm
        (requestsFromRules ordinal actualKind targets rules)))
  | [], ordinal => by
      request_eval unfolding [requestsFromRules]
  | declaration :: rest, ordinal => by
      have made := request_from_rule_returns state actualKind targets declaration
      have later := requests_from_rules_returns state actualKind targets rest (ordinal + 1)
      cases selected : requestFromRule actualKind targets declaration with
      | none =>
          rw [selected] at made
          request_eval [made, later]
            unfolding [requestsFromRules, selected, encodeOption]
      | some request =>
          rw [selected] at made
          request_eval [made, later]
            unfolding [requestsFromRules, selected, encodeOption,
              CollectionPlanExecution.requestEntryTerm]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRequestExecution
