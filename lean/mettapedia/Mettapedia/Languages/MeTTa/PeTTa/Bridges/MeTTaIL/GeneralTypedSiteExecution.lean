import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution.Program

/-!
# Typed occurrence and selected rule enumeration through PeTTa execution

The authored enumerator reads the original declaration, pattern and permission
wire. Its outputs use the existing typed site and rule-job codecs, retaining
physical addresses, exact binder sorts and authored typing alternatives.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution

open Mettapedia.GSLT.LanguageDef CettaWire WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts GeneralTypedSites GeneralRuleJobs
open GeneralExecutionAdmission
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program Equation)
open Effects (State)
open Eval
open ScopedRuleJobReadoutExecution (siteTerm typingFrameTerm jobTerm rulePlanTerm)
open scoped ProgramQuotation

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev sitesValue (sites : List SiteData) : Atom := encoded (encodeList siteTerm sites)
private abbrev jobsValue (jobs : List Job) : Atom := encoded (encodeList jobTerm jobs)
private abbrev rulesValue (rules : List RulePlan) : Atom := encoded (encodeList rulePlanTerm rules)

private def sitePattern : Atom := a "RuleJobSite"
  [v "address", v "context", v "focus", v "bound", v "type", v "frames"]

private def siteFields (site : SiteData) (rest : List SiteData) (caller : Subst) : Subst :=
  [("rest", sitesValue rest), ("frames", encoded (encodeList typingFrameTerm site.typingFrames)),
   ("type", encoded (InferenceCettaWire.AuthoredRule.typeTerm site.focusType)),
   ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm site.focusBound)),
   ("focus", encoded (InferenceCettaWire.encodePattern site.focus)),
   ("context", encoded (InferenceCettaWire.ContextObservation.contextTerm site.context)),
   ("address", encoded (encodeList Term.natural site.address))] ++ caller

local macro "site_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private def crossSitesPairs : List (Atom × Atom) :=
  [(v "tail", a "gslt:sites:cross-sites" [v "ordinal", v "declaration", v "rest"]),
   (v "job", a "RuleJob" [v "ordinal", v "declaration", v "site"])]

private def crossSitesBody : Atom := a "let*"
  [.expression (crossSitesPairs.map fun pair => .expression [pair.1, pair.2]),
   a "LCons" [v "job", v "tail"]]

private def crossSitesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "site", v "rest"], crossSitesBody)]

private theorem cross_sites_shape : (equation .crossSites).body =
    a "case" [v "sites", .expression (crossSitesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem cross_sites_returns (state : State) (ordinal : Nat) (declaration : RulePlan)
    (sites : List SiteData) :
    PureReturns program [] state
      (a "gslt:sites:cross-sites" [number ordinal, encoded (rulePlanTerm declaration), sitesValue sites]) state
      (jobsValue (sites.map fun site => ⟨ordinal, declaration, site⟩)) := by
  induction sites with
  | nil =>
      let caller := environment .crossSites [number ordinal, encoded (rulePlanTerm declaration), sitesValue []]
      apply helper_call .crossSites [] state _
        [number ordinal, encoded (rulePlanTerm declaration), sitesValue []] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [cross_sites_shape]
      apply case_returns program caller caller state state state (v "sites") (.symbol "LNil")
        (.symbol "LNil") _ _ crossSitesCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, sitesValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "sites"
      · simp [crossSitesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons site sites ih =>
      let caller := environment .crossSites
        [number ordinal, encoded (rulePlanTerm declaration), sitesValue (site :: sites)]
      let selected := ("rest", sitesValue sites) :: ("site", encoded (siteTerm site)) :: caller
      let tail := jobsValue (sites.map fun site => ⟨ordinal, declaration, site⟩)
      let bound := ("tail", tail) :: selected
      let job := encoded (jobTerm ⟨ordinal, declaration, site⟩)
      let final := ("job", job) :: bound
      apply helper_call .crossSites [] state _
        [number ordinal, encoded (rulePlanTerm declaration), sitesValue (site :: sites)] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [cross_sites_shape]
      apply case_returns program caller selected state state state (v "sites") (sitesValue (site :: sites))
        crossSitesBody _ _ crossSitesCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "sites"
      · simp [crossSitesCases, sitesValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · unfold crossSitesBody
        apply PureData.let_bindings_return (final := final) (middle := state) (pairs := crossSitesPairs)
        · apply PureData.BindingsReturn.cons (bound := bound) (value := tail)
          · apply helper_capture .crossSites selected state _
              [number ordinal, encoded (rulePlanTerm declaration), sitesValue sites] _ rfl _ ih
            simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              bound, selected, caller, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := final) (value := job)
            · have templated : PureData.Template program (a "RuleJob" [v "ordinal", v "declaration", v "site"]) := by
                site_template
              simpa [job, jobTerm, bound, selected, caller, environment, Helper.names,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
                Subst.lookup] using PureData.template_return program bound state _ templated
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                final, bound, selected, caller, environment, Helper.names, Subst.lookup]
            · exact .nil _ _
        · have templated : PureData.Template program (a "LCons" [v "job", v "tail"]) := by site_template
          simpa [final, job, tail, bound, selected, caller, environment, Helper.names,
            jobsValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program final state _ templated

theorem cross_sites_captured_returns (caller : Subst) (state : State) (ordinal : Nat)
    (declaration : RulePlan) (sites : List SiteData) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [number ordinal, encoded (rulePlanTerm declaration), sitesValue sites]) :
    PureReturns program caller state (a "gslt:sites:cross-sites" arguments) state
      (jobsValue (sites.map fun site => ⟨ordinal, declaration, site⟩)) :=
  helper_capture .crossSites caller state arguments _ _ rfl captured
    (cross_sites_returns state ordinal declaration sites)

theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns program caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

theorem append_values_returns (caller : Subst) (state : State)
    (left right : List Term) (first second : String)
    (captured : [v first, v second].map (applySubst caller) =
      [MatchAutomataSourceExecution.listValue left, MatchAutomataSourceExecution.listValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v first, v second]) state
      (MatchAutomataSourceExecution.listValue (left ++ right)) := by
  apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  exact MatchAutomataSourceExecution.append_captured_returns caller state left right
    (v first) (v second) captured

private def crossRulesPairs : List (Atom × Atom) :=
  [(v "here", a "gslt:sites:cross-sites" [v "ordinal", v "declaration", v "sites"]),
   (v "next", a "+" [v "ordinal", number 1]),
   (v "tail", a "gslt:sites:cross-rules" [v "rest", v "sites", v "next"])]

private def crossRulesBody : Atom := a "let*"
  [.expression (crossRulesPairs.map fun pair => .expression [pair.1, pair.2]),
   a "gslt:automata:append" [v "here", v "tail"]]

private def crossRulesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "declaration", v "rest"], crossRulesBody)]

private theorem cross_rules_shape : (equation .crossRules).body =
    a "case" [v "rules", .expression (crossRulesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem cross_rules_returns (state : State) (rules : List RulePlan) (sites : List SiteData) (ordinal : Nat) :
    PureReturns program [] state
      (a "gslt:sites:cross-rules" [rulesValue rules, sitesValue sites, number ordinal]) state
      (jobsValue (rules.zipIdx ordinal |>.flatMap fun (declaration, index) =>
        sites.map fun site => ⟨index, declaration, site⟩)) := by
  induction rules generalizing ordinal with
  | nil =>
      let caller := environment .crossRules [rulesValue [], sitesValue sites, number ordinal]
      apply helper_call .crossRules [] state _ [rulesValue [], sitesValue sites, number ordinal] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [cross_rules_shape]
      apply case_returns program caller caller state state state (v "rules") (.symbol "LNil")
        (.symbol "LNil") _ _ crossRulesCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, rulesValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "rules"
      · simp [crossRulesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons declaration rules ih =>
      let caller := environment .crossRules [rulesValue (declaration :: rules), sitesValue sites, number ordinal]
      let selected := ("rest", rulesValue rules) :: ("declaration", encoded (rulePlanTerm declaration)) :: caller
      let here := sites.map fun site => (⟨ordinal, declaration, site⟩ : Job)
      let rest := (rules.zipIdx (ordinal + 1)).flatMap fun (declaration, index) =>
        sites.map fun site => (⟨index, declaration, site⟩ : Job)
      let withHere := ("here", jobsValue here) :: selected
      let withNext := ("next", number (ordinal + 1)) :: withHere
      let final := ("tail", jobsValue rest) :: withNext
      apply helper_call .crossRules [] state _ [rulesValue (declaration :: rules), sitesValue sites, number ordinal] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [cross_rules_shape]
      apply case_returns program caller selected state state state (v "rules") (rulesValue (declaration :: rules))
        crossRulesBody _ _ crossRulesCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "rules"
      · simp [crossRulesCases, rulesValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · unfold crossRulesBody
        apply PureData.let_bindings_return (final := final) (middle := state) (pairs := crossRulesPairs)
        · apply PureData.BindingsReturn.cons (bound := withHere) (value := jobsValue here)
          · apply cross_sites_captured_returns selected state ordinal declaration sites
            simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
              withHere, selected, caller, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := withNext) (value := number (ordinal + 1))
            · apply add_one_returns withHere state ordinal "ordinal"
              simp [withHere, selected, caller, environment, Helper.names, applySubst, Subst.lookup]
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                withNext, withHere, selected, caller, environment, Helper.names, Subst.lookup]
            · apply PureData.BindingsReturn.cons (bound := final) (value := jobsValue rest)
              · apply helper_capture .crossRules withNext state _
                  [rulesValue rules, sitesValue sites, number (ordinal + 1)] _ rfl _ (ih (ordinal + 1))
                simp [withNext, withHere, selected, caller, environment, Helper.names, applySubst, Subst.lookup]
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                  final, withNext, withHere, selected, caller, environment, Helper.names, Subst.lookup]
              · exact .nil _ _
        · have returned := append_values_returns final state (here.map jobTerm) (rest.map jobTerm) "here" "tail"
            (by simp [final, withNext, withHere, selected, caller, environment, Helper.names,
              applySubst, Subst.lookup, jobsValue, MatchAutomataSourceExecution.listValue, encodeList_map])
          simpa only [List.zipIdx_cons, List.flatMap_cons, here, rest, jobsValue,
            MatchAutomataSourceExecution.listValue, ← List.map_append, encodeList_map, Function.comp_def, id_eq]
            using returned

theorem cross_rules_captured_returns (caller : Subst) (state : State) (rules : List RulePlan)
    (sites : List SiteData) (ordinal : Nat) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [rulesValue rules, sitesValue sites, number ordinal]) :
    PureReturns program caller state (a "gslt:sites:cross-rules" arguments) state
      (jobsValue (rules.zipIdx ordinal |>.flatMap fun (declaration, index) =>
        sites.map fun site => ⟨index, declaration, site⟩)) :=
  helper_capture .crossRules caller state arguments _ _ rfl captured
    (cross_rules_returns state rules sites ordinal)


private def wrap_lambda_template : Atom := a "RuleJobSite" [a "LCons" [number 0, v "address"], a "ContextLam" [v "binder", v "context"], v "focus", v "bound", v "type", a "LCons" [a "TypingLambda" [v "domain"], v "frames"]]

private def wrap_lambda_body : Atom :=
  a "let" [v "tail", a Helper.wrapLambda.head [v "binder", v "domain", v "rest"],
    a "LCons" [wrap_lambda_template, v "tail"]]

private def wrap_lambda_cases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [sitePattern, v "rest"], wrap_lambda_body)]

private theorem wrap_lambda_shape : (equation .wrapLambda).body =
    a "case" [v "sites", .expression (wrap_lambda_cases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem wrap_lambda_returns (state : State) (binder : Option String) (domain : TypeExpr) (sites : List SiteData) :
    PureReturns program [] state
      (a Helper.wrapLambda.head [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue sites]) state
      (sitesValue (sites.map (SiteData.wrapLambda binder domain))) := by
  induction sites with
  | nil =>
      let caller := environment .wrapLambda [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue []]
      apply helper_call .wrapLambda [] state _ [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue []] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_lambda_shape]
      apply case_returns program caller caller state state state (v "sites") (.symbol "LNil")
        (.symbol "LNil") _ _ wrap_lambda_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, sitesValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "sites"
      · simp [wrap_lambda_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons site sites ih =>
      let caller := environment .wrapLambda [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue (site :: sites)]
      let selected := siteFields site sites caller
      let tail := sitesValue (sites.map (SiteData.wrapLambda binder domain))
      let final := ("tail", tail) :: selected
      apply helper_call .wrapLambda [] state _ [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue (site :: sites)] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_lambda_shape]
      apply case_returns program caller selected state state state (v "sites") (sitesValue (site :: sites))
        wrap_lambda_body _ _ wrap_lambda_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "sites"
      · simp [wrap_lambda_cases, sitePattern, siteFields, siteTerm, sitesValue, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · unfold wrap_lambda_body
        apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.named_let_returns
          program selected state "tail" _ tail
        · simp [selected, siteFields, caller, environment, Helper.names, Subst.lookup]
        · apply helper_capture .wrapLambda selected state _
            [encoded (InferenceCettaWire.encodeBinder binder), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue sites] _ rfl _ ih
          simp [selected, siteFields, caller, environment, Helper.names, applySubst, Subst.lookup]
        · have templated : PureData.Template program
              (a "LCons" [wrap_lambda_template, v "tail"]) := by
            unfold wrap_lambda_template
            site_template
          simpa [final, tail, selected, siteFields, caller, environment, Helper.names,
            wrap_lambda_template, sitesValue, siteTerm, typingFrameTerm, SiteData.wrapLambda,
            InferenceCettaWire.ContextObservation.contextTerm, InferenceCettaWire.encodeList,
            InferenceCettaWire.encodeRest, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program final state _ templated

private def wrap_multi_template : Atom := a "RuleJobSite" [a "LCons" [number 0, v "address"], a "ContextMultiLam" [v "arity", v "binders", v "context"], v "focus", v "bound", v "type", a "LCons" [a "TypingMultiLambda" [v "arity", v "domain"], v "frames"]]

private def wrap_multi_body : Atom :=
  a "let" [v "tail", a Helper.wrapMulti.head [v "arity", v "binders", v "domain", v "rest"],
    a "LCons" [wrap_multi_template, v "tail"]]

private def wrap_multi_cases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [sitePattern, v "rest"], wrap_multi_body)]

private theorem wrap_multi_shape : (equation .wrapMulti).body =
    a "case" [v "sites", .expression (wrap_multi_cases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem wrap_multi_returns (state : State) (arity : Nat) (binders : List String) (domain : TypeExpr) (sites : List SiteData) :
    PureReturns program [] state
      (a Helper.wrapMulti.head [number arity, encoded (encodeList Term.string binders), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue sites]) state
      (sitesValue (sites.map (SiteData.wrapMultiLambda arity binders domain))) := by
  induction sites with
  | nil =>
      let caller := environment .wrapMulti [number arity, encoded (encodeList Term.string binders), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue []]
      apply helper_call .wrapMulti [] state _ [number arity, encoded (encodeList Term.string binders), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue []] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_multi_shape]
      apply case_returns program caller caller state state state (v "sites") (.symbol "LNil")
        (.symbol "LNil") _ _ wrap_multi_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, sitesValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "sites"
      · simp [wrap_multi_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons site sites ih =>
      let caller := environment .wrapMulti [number arity, encoded (encodeList Term.string binders), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue (site :: sites)]
      let selected := siteFields site sites caller
      let tail := sitesValue (sites.map (SiteData.wrapMultiLambda arity binders domain))
      let final := ("tail", tail) :: selected
      apply helper_call .wrapMulti [] state _ [number arity, encoded (encodeList Term.string binders), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue (site :: sites)] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_multi_shape]
      apply case_returns program caller selected state state state (v "sites") (sitesValue (site :: sites))
        wrap_multi_body _ _ wrap_multi_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "sites"
      · simp [wrap_multi_cases, sitePattern, siteFields, siteTerm, sitesValue, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · unfold wrap_multi_body
        apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.named_let_returns
          program selected state "tail" _ tail
        · simp [selected, siteFields, caller, environment, Helper.names, Subst.lookup]
        · apply helper_capture .wrapMulti selected state _
            [number arity, encoded (encodeList Term.string binders), encoded (InferenceCettaWire.AuthoredRule.typeTerm domain), sitesValue sites] _ rfl _ ih
          simp [selected, siteFields, caller, environment, Helper.names, applySubst, Subst.lookup]
        · have templated : PureData.Template program
              (a "LCons" [wrap_multi_template, v "tail"]) := by
            unfold wrap_multi_template
            site_template
          simpa [final, tail, selected, siteFields, caller, environment, Helper.names,
            wrap_multi_template, sitesValue, siteTerm, typingFrameTerm, SiteData.wrapMultiLambda,
            InferenceCettaWire.ContextObservation.contextTerm, InferenceCettaWire.encodeList,
            InferenceCettaWire.encodeRest, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program final state _ templated

private def wrap_application_template : Atom := a "RuleJobSite" [a "LCons" [v "index", v "address"], a "ContextApp" [v "constructor", v "before", v "context", v "after"], v "focus", v "bound", v "type", a "LCons" [a "TypingApplication" [v "declaration", v "index"], v "frames"]]

private def wrap_application_body : Atom :=
  a "let" [v "tail", a Helper.wrapApplication.head [v "declaration", v "constructor", v "before", v "index", v "after", v "rest"],
    a "LCons" [wrap_application_template, v "tail"]]

private def wrap_application_cases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [sitePattern, v "rest"], wrap_application_body)]

private theorem wrap_application_shape : (equation .wrapApplication).body =
    a "case" [v "sites", .expression (wrap_application_cases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem wrap_application_returns (state : State) (declaration : Nat) (constructor : String) (arguments : List Pattern) (index : Nat) (sites : List SiteData) :
    PureReturns program [] state
      (a Helper.wrapApplication.head [number declaration, encoded (.string constructor), encoded (InferenceCettaWire.encodePatterns (arguments.take index)), number index, encoded (InferenceCettaWire.encodePatterns (arguments.drop (index + 1))), sitesValue sites]) state
      (sitesValue (sites.map (SiteData.wrapApplication declaration constructor arguments index))) := by
  induction sites with
  | nil =>
      let caller := environment .wrapApplication [number declaration, encoded (.string constructor), encoded (InferenceCettaWire.encodePatterns (arguments.take index)), number index, encoded (InferenceCettaWire.encodePatterns (arguments.drop (index + 1))), sitesValue []]
      apply helper_call .wrapApplication [] state _ [number declaration, encoded (.string constructor), encoded (InferenceCettaWire.encodePatterns (arguments.take index)), number index, encoded (InferenceCettaWire.encodePatterns (arguments.drop (index + 1))), sitesValue []] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_application_shape]
      apply case_returns program caller caller state state state (v "sites") (.symbol "LNil")
        (.symbol "LNil") _ _ wrap_application_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, sitesValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "sites"
      · simp [wrap_application_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons site sites ih =>
      let caller := environment .wrapApplication [number declaration, encoded (.string constructor), encoded (InferenceCettaWire.encodePatterns (arguments.take index)), number index, encoded (InferenceCettaWire.encodePatterns (arguments.drop (index + 1))), sitesValue (site :: sites)]
      let selected := siteFields site sites caller
      let tail := sitesValue (sites.map (SiteData.wrapApplication declaration constructor arguments index))
      let final := ("tail", tail) :: selected
      apply helper_call .wrapApplication [] state _ [number declaration, encoded (.string constructor), encoded (InferenceCettaWire.encodePatterns (arguments.take index)), number index, encoded (InferenceCettaWire.encodePatterns (arguments.drop (index + 1))), sitesValue (site :: sites)] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_application_shape]
      apply case_returns program caller selected state state state (v "sites") (sitesValue (site :: sites))
        wrap_application_body _ _ wrap_application_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "sites"
      · simp [wrap_application_cases, sitePattern, siteFields, siteTerm, sitesValue, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · unfold wrap_application_body
        apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.named_let_returns
          program selected state "tail" _ tail
        · simp [selected, siteFields, caller, environment, Helper.names, Subst.lookup]
        · apply helper_capture .wrapApplication selected state _
            [number declaration, encoded (.string constructor), encoded (InferenceCettaWire.encodePatterns (arguments.take index)), number index, encoded (InferenceCettaWire.encodePatterns (arguments.drop (index + 1))), sitesValue sites] _ rfl _ ih
          simp [selected, siteFields, caller, environment, Helper.names, applySubst, Subst.lookup]
        · have templated : PureData.Template program
              (a "LCons" [wrap_application_template, v "tail"]) := by
            unfold wrap_application_template
            site_template
          simpa [final, tail, selected, siteFields, caller, environment, Helper.names,
            wrap_application_template, sitesValue, siteTerm, typingFrameTerm, SiteData.wrapApplication,
            InferenceCettaWire.ContextObservation.contextTerm, InferenceCettaWire.encodeList,
            InferenceCettaWire.encodeRest, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program final state _ templated

private def wrap_collection_template : Atom := a "RuleJobSite" [a "LCons" [v "index", v "address"], a "ContextCollection" [v "kind", v "before", v "context", v "after", .symbol "RNone"], v "focus", v "bound", v "type", a "LCons" [v "frame", v "frames"]]

private def wrap_collection_body : Atom :=
  a "let" [v "tail", a Helper.wrapCollection.head [v "frame", v "kind", v "before", v "index", v "after", v "rest"],
    a "LCons" [wrap_collection_template, v "tail"]]

private def wrap_collection_cases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [sitePattern, v "rest"], wrap_collection_body)]

private theorem wrap_collection_shape : (equation .wrapCollection).body =
    a "case" [v "sites", .expression (wrap_collection_cases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem wrap_collection_returns (state : State) (origin : TypingFrame) (kind : CollType) (elements : List Pattern) (index : Nat) (sites : List SiteData) :
    PureReturns program [] state
      (a Helper.wrapCollection.head [encoded (typingFrameTerm origin), encoded (InferenceCettaWire.encodeCollectionType kind), encoded (InferenceCettaWire.encodePatterns (elements.take index)), number index, encoded (InferenceCettaWire.encodePatterns (elements.drop (index + 1))), sitesValue sites]) state
      (sitesValue (sites.map (SiteData.wrapCollection origin kind elements index))) := by
  induction sites with
  | nil =>
      let caller := environment .wrapCollection [encoded (typingFrameTerm origin), encoded (InferenceCettaWire.encodeCollectionType kind), encoded (InferenceCettaWire.encodePatterns (elements.take index)), number index, encoded (InferenceCettaWire.encodePatterns (elements.drop (index + 1))), sitesValue []]
      apply helper_call .wrapCollection [] state _ [encoded (typingFrameTerm origin), encoded (InferenceCettaWire.encodeCollectionType kind), encoded (InferenceCettaWire.encodePatterns (elements.take index)), number index, encoded (InferenceCettaWire.encodePatterns (elements.drop (index + 1))), sitesValue []] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_collection_shape]
      apply case_returns program caller caller state state state (v "sites") (.symbol "LNil")
        (.symbol "LNil") _ _ wrap_collection_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, sitesValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "sites"
      · simp [wrap_collection_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons site sites ih =>
      let caller := environment .wrapCollection [encoded (typingFrameTerm origin), encoded (InferenceCettaWire.encodeCollectionType kind), encoded (InferenceCettaWire.encodePatterns (elements.take index)), number index, encoded (InferenceCettaWire.encodePatterns (elements.drop (index + 1))), sitesValue (site :: sites)]
      let selected := siteFields site sites caller
      let tail := sitesValue (sites.map (SiteData.wrapCollection origin kind elements index))
      let final := ("tail", tail) :: selected
      apply helper_call .wrapCollection [] state _ [encoded (typingFrameTerm origin), encoded (InferenceCettaWire.encodeCollectionType kind), encoded (InferenceCettaWire.encodePatterns (elements.take index)), number index, encoded (InferenceCettaWire.encodePatterns (elements.drop (index + 1))), sitesValue (site :: sites)] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [wrap_collection_shape]
      apply case_returns program caller selected state state state (v "sites") (sitesValue (site :: sites))
        wrap_collection_body _ _ wrap_collection_cases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "sites"
      · simp [wrap_collection_cases, sitePattern, siteFields, siteTerm, sitesValue, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
      · unfold wrap_collection_body
        apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.named_let_returns
          program selected state "tail" _ tail
        · simp [selected, siteFields, caller, environment, Helper.names, Subst.lookup]
        · apply helper_capture .wrapCollection selected state _
            [encoded (typingFrameTerm origin), encoded (InferenceCettaWire.encodeCollectionType kind), encoded (InferenceCettaWire.encodePatterns (elements.take index)), number index, encoded (InferenceCettaWire.encodePatterns (elements.drop (index + 1))), sitesValue sites] _ rfl _ ih
          simp [selected, siteFields, caller, environment, Helper.names, applySubst, Subst.lookup]
        · have templated : PureData.Template program
              (a "LCons" [wrap_collection_template, v "tail"]) := by
            unfold wrap_collection_template
            site_template
          simpa [final, tail, selected, siteFields, caller, environment, Helper.names,
            wrap_collection_template, sitesValue, siteTerm, typingFrameTerm, SiteData.wrapCollection,
            InferenceCettaWire.ContextObservation.contextTerm, InferenceCettaWire.encodeList,
            InferenceCettaWire.encodeRest, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program final state _ templated


private abbrev listValue (values : List Term) : Atom := encoded (encodeList id values)

private theorem equal_zero_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "==" [v name, number 0]) state
      (Effects.boolean (decide (value = 0))) := by
  simpa only [Term.natural.injEq] using CettaWireAtom.equality_evaluated_returns program caller state
    (.natural value) (.natural 0) (v name) (number 0) (by decide +kernel) (by decide +kernel)
    (by simpa only [captured] using variable_returns program caller state name)
    (grounded_returns program caller state (.int 0))

private theorem subtract_one_returns (caller : Subst) (state : State) (value : Nat)
    (name : String) (positive : 0 < value) (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "-" [v name, number 1]) state (number (value - 1)) := by
  apply native_binary_call_returns program caller state state state state "-"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · have casts : ((value - 1 : Nat) : Int) = (value : Int) - 1 := by omega
    simpa only [number, encoded, CettaWireAtom.encode, casts, Int.natCast_one] using
      StdLib.integer_subtraction state (value : Int) 1

private def takePairs : List (Atom × Atom) :=
  [(v "previous", a "-" [v "count", number 1]),
   (v "tail", a Helper.take.head [v "previous", v "rest"])]

private def takeBody : Atom := a "let*"
  [.expression (takePairs.map fun pair => .expression [pair.1, pair.2]),
   a "LCons" [v "item", v "tail"]]

private def takeCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "item", v "rest"], takeBody)]

private theorem take_shape : (equation .take).body =
    a "if" [a "==" [v "count", number 0], .symbol "LNil",
      a "case" [v "items", .expression (takeCases.map fun row => .expression [row.1, row.2])]] := by
  decide +kernel

theorem take_returns (state : State) (count : Nat) (items : List Term) :
    PureReturns program [] state (a Helper.take.head [number count, listValue items]) state
      (listValue (items.take count)) := by
  induction count generalizing items with
  | zero =>
      let caller := environment .take [number 0, listValue items]
      apply helper_call .take [] state _ [number 0, listValue items] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [take_shape]
      apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
        program caller state _ (decide (0 = 0))
      · apply equal_zero_returns caller state 0 "count"
        simp [caller, environment, Helper.names, applySubst, Subst.lookup]
      · exact symbol_returns program caller state "LNil"
  | succ count ih =>
      let caller := environment .take [number (count + 1), listValue items]
      apply helper_call .take [] state _ [number (count + 1), listValue items] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [take_shape]
      apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
        program caller state _ (decide (count + 1 = 0))
      · apply equal_zero_returns caller state (count + 1) "count"
        simp [caller, environment, Helper.names, applySubst, Subst.lookup]
      · simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        cases items with
        | nil =>
            apply case_returns program caller caller state state state (v "items") (.symbol "LNil")
              (.symbol "LNil") _ _ takeCases (read_cases_encoded _)
            · simpa [caller, environment, Helper.names, listValue, encodeList, CettaWireAtom.encode,
                applySubst, Subst.lookup] using variable_returns program caller state "items"
            · simp [takeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · exact symbol_returns program caller state "LNil"
        | cons item items =>
            let selected := ("rest", listValue items) :: ("item", encoded item) :: caller
            let previous := ("previous", number count) :: selected
            let final := ("tail", listValue (items.take count)) :: previous
            apply case_returns program caller selected state state state (v "items") (listValue (item :: items))
              takeBody _ _ takeCases (read_cases_encoded _)
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
                variable_returns program caller state "items"
            · simp [takeCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
            · unfold takeBody
              apply PureData.let_bindings_return (final := final) (middle := state) (pairs := takePairs)
              · apply PureData.BindingsReturn.cons (bound := previous) (value := number count)
                · simpa only [Nat.add_sub_cancel] using
                    subtract_one_returns selected state (count + 1) "count" (by omega)
                      (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                    previous, selected, caller, environment, Helper.names, Subst.lookup]
                · apply PureData.BindingsReturn.cons (bound := final) (value := listValue (items.take count))
                  · apply helper_capture .take previous state _ [number count, listValue items] _ rfl _ (ih items)
                    simp [previous, selected, caller, environment, Helper.names, applySubst, Subst.lookup]
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                      final, previous, selected, caller, environment, Helper.names, Subst.lookup]
                  · exact .nil _ _
              · have templated : PureData.Template program (a "LCons" [v "item", v "tail"]) := by site_template
                simpa [final, previous, selected, caller, environment, Helper.names,
                  listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  applySubst, applySubst.applySubstList, Subst.lookup] using
                  PureData.template_return program final state _ templated

private def dropBody : Atom := a "let" [v "previous", a "-" [v "count", number 1],
  a Helper.drop.head [v "previous", v "rest"]]

private def dropCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "item", v "rest"], dropBody)]

private theorem drop_shape : (equation .drop).body =
    a "if" [a "==" [v "count", number 0], v "items",
      a "case" [v "items", .expression (dropCases.map fun row => .expression [row.1, row.2])]] := by
  decide +kernel

theorem drop_returns (state : State) (count : Nat) (items : List Term) :
    PureReturns program [] state (a Helper.drop.head [number count, listValue items]) state
      (listValue (items.drop count)) := by
  induction count generalizing items with
  | zero =>
      let caller := environment .drop [number 0, listValue items]
      apply helper_call .drop [] state _ [number 0, listValue items] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [drop_shape]
      apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
        program caller state _ (decide (0 = 0))
      · apply equal_zero_returns caller state 0 "count"
        simp [caller, environment, Helper.names, applySubst, Subst.lookup]
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "items"
  | succ count ih =>
      let caller := environment .drop [number (count + 1), listValue items]
      apply helper_call .drop [] state _ [number (count + 1), listValue items] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
      rw [drop_shape]
      apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.bool_if_returns
        program caller state _ (decide (count + 1 = 0))
      · apply equal_zero_returns caller state (count + 1) "count"
        simp [caller, environment, Helper.names, applySubst, Subst.lookup]
      · simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        cases items with
        | nil =>
            apply case_returns program caller caller state state state (v "items") (.symbol "LNil")
              (.symbol "LNil") _ _ dropCases (read_cases_encoded _)
            · simpa [caller, environment, Helper.names, listValue, encodeList, CettaWireAtom.encode,
                applySubst, Subst.lookup] using variable_returns program caller state "items"
            · simp [dropCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · exact symbol_returns program caller state "LNil"
        | cons item items =>
            let selected := ("rest", listValue items) :: ("item", encoded item) :: caller
            let previous := ("previous", number count) :: selected
            apply case_returns program caller selected state state state (v "items") (listValue (item :: items))
              dropBody _ _ dropCases (read_cases_encoded _)
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
                variable_returns program caller state "items"
            · simp [dropCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
            · unfold dropBody
              apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.named_let_returns
                program selected state "previous" _ (number count)
              · simp [selected, caller, environment, Helper.names, Subst.lookup]
              · simpa only [Nat.add_sub_cancel] using
                  subtract_one_returns selected state (count + 1) "count" (by omega)
                    (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              · apply helper_capture .drop previous state _ [number count, listValue items] _ rfl _ (ih items)
                simp [previous, selected, caller, environment, Helper.names, applySubst, Subst.lookup]


theorem member_values_returns (caller : Subst) (state : State)
    (value : Term) (values : List Term) (first second : String)
    (captured : [v first, v second].map (applySubst caller) = [encoded value, listValue values]) :
    PureReturns program caller state (a "gslt:automata:member" [v first, v second]) state
      (Effects.boolean (decide (value ∈ values))) := by
  apply retained_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, retainedHead])
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  apply PureData.raw_capture_returns MatchAutomataProgram.program [] caller state state
    "gslt:automata:member" [encoded value, listValue values] [v first, v second] _
    (by decide +kernel) _ (by decide) _ (MatchAutomataSourceExecution.member_returns state value values)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]
      using captured.symm

private abbrev permissionsValue (permissions : OperationalPermissions) : Atom :=
  encoded (InferenceCettaWire.ContextObservation.permissionsTerm permissions)

private def permissionsPattern : Atom := a "OperationalPermissions"
  [v "enabled", v "all", v "slots", v "lambda", v "multi", v "kinds"]

private def permissionsFields (permissions : OperationalPermissions) (caller : Subst) : Subst :=
  [("kinds", encoded (encodeList InferenceCettaWire.encodeCollectionType permissions.collectionKinds)),
   ("multi", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underMultiLambda)),
   ("lambda", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.underLambda)),
   ("slots", encoded (encodeList InferenceCettaWire.ContextObservation.slotTerm permissions.constructorArguments)),
   ("all", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.allConstructorArguments)),
   ("enabled", encoded (InferenceCettaWire.ContextObservation.booleanTerm permissions.enabled))] ++ caller

private def argumentPermittedBody : Atom := a "let"
  [v "slot", a "TermSlot" [v "constructor", v "index"],
   a "gslt:automata:member" [v "slot", v "slots"]]

private def argumentFlagCases : SpaceSemantics.Cases :=
  [(.symbol "PermissionYes", Effects.boolean true), (.symbol "PermissionNo", argumentPermittedBody)]

private def argumentPermissionCases : SpaceSemantics.Cases :=
  [(permissionsPattern, a "case"
    [v "all", .expression (argumentFlagCases.map fun row => .expression [row.1, row.2])])]

private theorem argument_permitted_shape : (equation .argumentPermitted).body =
    a "case" [v "permissions", .expression (argumentPermissionCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem argument_permitted_returns (state : State) (permissions : OperationalPermissions)
    (constructor : String) (index : Nat) :
    PureReturns program [] state
      (a Helper.argumentPermitted.head [permissionsValue permissions, encoded (.string constructor), number index]) state
      (Effects.boolean (permissions.permitsArgument constructor index)) := by
  let caller := environment .argumentPermitted
    [permissionsValue permissions, encoded (.string constructor), number index]
  let selected := permissionsFields permissions caller
  apply helper_call .argumentPermitted [] state _
    [permissionsValue permissions, encoded (.string constructor), number index] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [argument_permitted_shape]
  apply case_returns program caller selected state state state (v "permissions") (permissionsValue permissions)
    (a "case" [v "all", .expression (argumentFlagCases.map fun row => .expression [row.1, row.2])])
    _ _ argumentPermissionCases (read_cases_encoded _)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "permissions"
  · simp [argumentPermissionCases, permissionsPattern, permissionsValue, permissionsFields,
      InferenceCettaWire.ContextObservation.permissionsTerm, InferenceCettaWire.encodeList,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
  · cases flag : permissions.allConstructorArguments with
    | true =>
        apply case_returns program selected selected state state state (v "all") (.symbol "PermissionYes")
          (Effects.boolean true) _ _ argumentFlagCases (read_cases_encoded _)
        · simpa [selected, permissionsFields, flag, InferenceCettaWire.ContextObservation.booleanTerm,
            CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program selected state "all"
        · simp [argumentFlagCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [OperationalPermissions.permitsArgument, flag, Effects.boolean] using grounded_returns program selected state (.bool true)
    | false =>
        apply case_returns program selected selected state state state (v "all") (.symbol "PermissionNo")
          argumentPermittedBody _ _ argumentFlagCases (read_cases_encoded _)
        · simpa [selected, permissionsFields, flag, InferenceCettaWire.ContextObservation.booleanTerm,
            CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program selected state "all"
        · simp [argumentFlagCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · let slot := InferenceCettaWire.ContextObservation.slotTerm (constructor, index)
          let final := ("slot", encoded slot) :: selected
          unfold argumentPermittedBody
          apply PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.named_let_returns
            program selected state "slot" _ (encoded slot)
          · simp [selected, permissionsFields, caller, environment, Helper.names, Subst.lookup]
          · have templated : PureData.Template program (a "TermSlot" [v "constructor", v "index"]) := by site_template
            simpa [slot, InferenceCettaWire.ContextObservation.slotTerm,
              selected, permissionsFields, caller, environment, Helper.names,
              CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return program selected state _ templated
          · have returned := member_values_returns final state slot
              (permissions.constructorArguments.map InferenceCettaWire.ContextObservation.slotTerm)
              "slot" "slots" (by simp [final, selected, permissionsFields, applySubst, Subst.lookup,
                listValue, encodeList_map])
            have same : slot ∈ permissions.constructorArguments.map InferenceCettaWire.ContextObservation.slotTerm ↔
                (constructor, index) ∈ permissions.constructorArguments := by
              simp only [List.mem_map, slot]
              constructor
              · rintro ⟨⟨name, position⟩, member, equal⟩
                simp only [InferenceCettaWire.ContextObservation.slotTerm, Term.application.injEq,
                  List.cons.injEq, Term.string.injEq, Term.natural.injEq, and_true, true_and] at equal
                rcases equal with ⟨rfl, rfl⟩
                exact member
              · intro member
                exact ⟨(constructor, index), member, rfl⟩
            simpa only [same, OperationalPermissions.permitsArgument, flag, Bool.false_or] using returned

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution
