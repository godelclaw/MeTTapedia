import Mettapedia.Languages.HOLLight.InferenceHosting
import Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
import Mettapedia.Logic.HOL.Embedding.InferenceRuleInstances
import Mettapedia.Languages.HOLLight.GraphExpansion
import Mettapedia.Languages.HOLLight.QuantifierExpansion
import Mettapedia.Languages.HOLLight.ImplicationExpansion
import Mettapedia.Languages.HOLLight.ProofDataEncoding

/-!
# Concrete HOL Light expansion of admitted inference rules

Each rule row contributes its original universally closed axiom. An instance
supplies its arguments to universal elimination, then uses its theorem premises
in authored order. The graph retains the full theorem objects and axiom tags.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.InferenceRuleExpansion

open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Logic.HOL.Embedding.InferenceRules
open GraphExpansion
open ProofExecution (Origin)
open Mettapedia.Logic.DerivationGraph

/-- The actual finite axiom associated to one stored source schema. -/
def ruleSequent (rule : RuleSchema) : Sequent :=
  ⟨∅, render (ruleFormula (inferenceRule rule))⟩

theorem ruleSequent_isBool (rule : RuleSchema) : (ruleSequent rule).IsBool :=
  ⟨render_isBool _, by simp [ruleSequent]⟩

def ruleTheorem (rule : RuleSchema) : Theorem :=
  Theorem.axiomResult (ruleSequent rule) (ruleSequent_isBool rule)

theorem ruleSequent_admitted {definition : CalculusLanguageDef} {rule : RuleSchema}
    (member : rule ∈ definition.rules) : policy (inferenceRules definition) (ruleSequent rule) := by
  refine ⟨rfl, List.mem_map.mpr ⟨ruleFormula (inferenceRule rule), ?_, rfl⟩⟩
  exact List.mem_map.mpr ⟨inferenceRule rule, List.mem_map.mpr ⟨rule, member, rfl⟩, rfl⟩

theorem ruleTheorem_checked {definition : CalculusLanguageDef} {rule : RuleSchema}
    (member : rule ∈ definition.rules) :
    (RuleRequest.axiom (ruleSequent rule)).check (policy (inferenceRules definition)) =
      some (ruleTheorem rule) := by
  apply (RuleRequest.check_eq_some_iff _ _ _).mpr
  exact ⟨rfl, ruleSequent_admitted member, ruleSequent_isBool rule, rfl, rfl, rfl⟩

theorem ruleTheorem_parts (rule : RuleSchema) :
    (ruleTheorem rule).axioms = {ruleSequent rule} ∧
    (ruleTheorem rule).sequent = ruleSequent rule := ⟨rfl, rfl⟩

/-- The original source instantiator exposes exactly the admitted rule row,
ordered argument substitution and premise vector. -/
theorem instantiated_rule {definition : ValidatedCalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition.1) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (checked : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    ∃ rule, definition.1.lookupRule? ruleInstance.ruleId = some rule ∧
      rule ∈ definition.1.rules ∧
      ruleInstance.arguments.length = (inferenceRule rule).vars.length ∧
      premises = (inferenceRule rule).instPremises ruleInstance.arguments ∧
      conclusion = (inferenceRule rule).instConclusion ruleInstance.arguments := by
  have application := instantiateRule?_eq_some_iff_application.mp checked
  cases application with
  | intro rule found valid conditions instantiated concluded =>
      have member : rule ∈ definition.1.rules := List.mem_of_find?_eq_some found
      have id : rule.id = ruleInstance.ruleId := of_decide_eq_true
        (List.find?_some (p := fun candidate : RuleSchema => decide (candidate.id = ruleInstance.ruleId)) found)
      obtain ⟨instanceId, arguments⟩ := ruleInstance
      simp only at id
      subst instanceId
      have full : RuleApplication definition ⟨rule.id, arguments⟩ premises conclusion :=
        .intro rule found valid conditions instantiated concluded
      have details := (ruleApplication_iff definition firstOrder member arguments premises conclusion).mp full
      exact ⟨rule, found, member, details.1, details.2.2.1, details.2.2.2⟩

/-- Reversal of an open typed formula keeps its variables as bound indices. -/
def renderOpen {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy}
    (formula : HOL.Formula HOL.Embedding.InferenceRules.Symbol context) : DBTerm :=
  ReverseTranslation.reverseTermOpen (term formula)

private def closeSpine : List Ty → DBTerm → DBTerm
  | [], body => body
  | domain :: domains, body =>
      closeSpine domains (DerivedRules.forallAppDB domain (.abs domain body))

theorem renderOpen_all {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy}
    {domain : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (body : HOL.Formula HOL.Embedding.InferenceRules.Symbol (domain :: context)) :
    renderOpen (.all body) = DerivedRules.forallAppDB (ReverseTranslation.reverseTy (type domain))
      (.abs (ReverseTranslation.reverseTy (type domain)) (renderOpen body)) := by
  simp only [renderOpen, term, HOL.mapTypes, ReverseTranslation.reverseTermOpen_all]
  rfl

/-- The oldest formal is the outermost universal; no variable order is changed. -/
theorem render_closeAll_spine (context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy)
    (formula : HOL.Formula HOL.Embedding.InferenceRules.Symbol context) :
    (render (HOL.closeAll context formula)).term =
      closeSpine (context.map fun domain => ReverseTranslation.reverseTy (type domain))
        (renderOpen formula) := by
  have closed (formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) :
      (render formula).term = renderOpen formula :=
    ReverseTranslation.reverseTerm_eq_reverseTermOpen _
  induction context with
  | nil => exact closed formula
  | cons domain context ih =>
      simp only [HOL.closeAll, List.map_cons, closeSpine]
      rw [ih (.all formula), renderOpen_all]

/-- Concrete universal arguments in elimination order, outermost first. -/
def closingArguments : (context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy) →
    HOL.Subst HOL.Embedding.InferenceRules.Symbol context [] → List CanonicalTerm
  | [], _ => []
  | _ :: context, substitution =>
      closingArguments context (fun {_} index => substitution (.vs index)) ++
        [ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term (substitution .vz))]

theorem closingArguments_length (context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy)
    (substitution : HOL.Subst HOL.Embedding.InferenceRules.Symbol context []) :
    (closingArguments context substitution).length = context.length := by
  induction context with
  | nil => rfl
  | cons domain context ih => simp [closingArguments, ih]

theorem closingArguments_values (count : Nat)
    (values : Fin count → HOL.ClosedTerm HOL.Embedding.InferenceRules.Symbol dataTy) :
    closingArguments (HOL.Embedding.FirstOrder.CtxOfArity count) (substOfValues values) =
      (List.ofFn fun index => ReverseTranslation.reverseCanonical
        ReverseTranslation.Naming.empty (term (values index))).reverse := by
  induction count with
  | zero => simp [closingArguments]
  | succ count ih =>
      simp only [List.replicate_succ,
        closingArguments, substOfValues, List.ofFn_succ, List.reverse_cons]
      rw [ih (fun index => values index.succ)]

theorem closingArguments_argumentSubstitution (names : List String) (arguments : List Pattern)
    (arity : arguments.length = names.length) :
    closingArguments (HOL.Embedding.FirstOrder.CtxOfArity names.length)
      (argumentSubstitution names arguments arity) =
        (arguments.map fun argument => ReverseTranslation.reverseCanonical
          ReverseTranslation.Naming.empty (term (encode argument))).reverse := by
  unfold argumentSubstitution
  rw [closingArguments_values]
  congr 1
  apply List.ext_getElem
  · simp [arity]
  · intro index leftBound rightBound
    simp only [List.getElem_ofFn, List.getElem_map]


theorem render_all_shape {domain : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (body : HOL.Formula HOL.Embedding.InferenceRules.Symbol [domain]) :
    (render (.all body)).term =
      DerivedRules.forallAppDB (ReverseTranslation.reverseTy (type domain))
        (.abs (ReverseTranslation.reverseTy (type domain)) (renderOpen body)) := by
  rw [show (render (.all body)).term = renderOpen (.all body) from
    ReverseTranslation.reverseTerm_eq_reverseTermOpen _]
  exact renderOpen_all body

theorem renderOpen_body_type {domain : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (body : HOL.Formula HOL.Embedding.InferenceRules.Symbol [domain]) :
    (renderOpen body).inferType [ReverseTranslation.reverseTy (type domain)] = some Ty.bool := by
  apply ReverseTranslation.inferType_reverseTermWith
  intro variableType index
  cases index with
  | vz => simp [ReverseTranslation.VarEnv.loose, deBruijnIndex, DBTerm.inferType]
  | vs index => nomatch index

theorem render_instantiate {domain : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (argument : HOL.ClosedTerm HOL.Embedding.InferenceRules.Symbol domain)
    (body : HOL.Formula HOL.Embedding.InferenceRules.Symbol [domain]) :
    (render (HOL.instantiate argument body)).term =
      DBTerm.instantiateAt
        (ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term argument)).term 0
        (renderOpen body) := by
  unfold render
  change ReverseTranslation.reverseTerm ReverseTranslation.Naming.empty
    (term (HOL.instantiate argument body)) = _
  rw [term, HOL.mapTypes_instantiate, ReverseTranslation.reverseTerm_instantiate]
  congr 1
  apply ReverseTranslation.reverseTermWith_congr
  intro variableType index
  cases index with
  | vz => rfl
  | vs index => nomatch index


theorem instantiate?_render_all (input : Theorem)
    {domain : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (argument : HOL.ClosedTerm HOL.Embedding.InferenceRules.Symbol domain)
    (body : HOL.Formula HOL.Embedding.InferenceRules.Symbol [domain])
    (inputShape : input.sequent.concl = render (.all body)) :
    QuantifierExpansion.instantiate? input
      (ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term argument)) =
        some (Theorem.preserveAxiomsResult input input.sequent.hyp
          (render (HOL.instantiate argument body))) := by
  have shape : input.sequent.concl.term = DerivedRules.forallAppDB
      (ReverseTranslation.reverseTy (type domain))
      (.abs (ReverseTranslation.reverseTy (type domain)) (renderOpen body)) := by
    rw [inputShape]
    exact render_all_shape body
  have accepted := QuantifierExpansion.instantiate?_eq_some input _ _
    (renderOpen_body_type body)
    (ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term argument)) rfl shape
  have result : QuantifierExpansion.specResult input _ _ (renderOpen_body_type body)
      (ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term argument)) rfl =
        Theorem.preserveAxiomsResult input input.sequent.hyp
          (render (HOL.instantiate argument body)) := by
    apply Theorem.ext
    · rfl
    · apply Sequent.ext
      · rfl
      · apply CanonicalTerm.ext_term
        exact (render_instantiate argument body).symm
  rw [result] at accepted
  exact accepted


theorem instantiateMany?_render_closeAll
    (context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy)
    (formula : HOL.Formula HOL.Embedding.InferenceRules.Symbol context)
    (substitution : HOL.Subst HOL.Embedding.InferenceRules.Symbol context [])
    (input : Theorem)
    (shape : input.sequent.concl = render (HOL.closeAll context formula)) :
    QuantifierExpansion.instantiateMany? input (closingArguments context substitution) =
      some (Theorem.preserveAxiomsResult input input.sequent.hyp
        (render (HOL.subst substitution formula))) := by
  induction context with
  | nil =>
      have closed : HOL.subst substitution formula = formula := by
        have same := HOL.subst_weakenCtx substitution formula
        simpa only [HOL.weakenCtx_nil] using same
      rw [closed]
      change some input = _
      congr 1
      apply Theorem.ext
      · rfl
      · apply Sequent.ext
        · rfl
        · exact shape
  | cons domain context ih =>
      let tail : HOL.Subst HOL.Embedding.InferenceRules.Symbol context [] :=
        fun {_} index => substitution (.vs index)
      let body := HOL.subst (HOL.Subst.lift tail) formula
      let intermediate := Theorem.preserveAxiomsResult input input.sequent.hyp
        (render (.all body))
      have first : QuantifierExpansion.instantiateMany? input (closingArguments context tail) =
          some intermediate := ih (.all formula) tail shape
      have next := instantiate?_render_all intermediate (substitution .vz) body rfl
      have exactBody : HOL.instantiate (substitution .vz) body = HOL.subst substitution formula := by
        dsimp only [body]
        rw [HOL.instantiate, HOL.subst_comp]
        apply HOL.subst_ext
        intro indexType index
        cases index with
        | vz => rfl
        | vs index => exact HOL.instantiate_weaken _ _
      simp only [closingArguments]
      rw [QuantifierExpansion.instantiateMany?_append, first]
      simp only [Option.bind_some, QuantifierExpansion.instantiateMany?]
      rw [next]
      rw [exactBody]
      rfl

/-- Every original source argument, including opaque closed binder-bearing
values, is instantiated by the actual universal-elimination operation. -/
theorem instantiateMany?_rule {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) {rule : RuleSchema}
    (member : rule ∈ definition.rules) (arguments : List Pattern)
    (arity : arguments.length = (inferenceRule rule).vars.length) :
    QuantifierExpansion.instantiateMany? (ruleTheorem rule)
      (arguments.map fun argument => ReverseTranslation.reverseCanonical
        ReverseTranslation.Naming.empty (term (encode argument))).reverse =
      some (Theorem.preserveAxiomsResult (ruleTheorem rule) ∅
        (render (HOL.hypChain ((inferenceRule rule).instPremises arguments |>.map judgment)
          (judgment ((inferenceRule rule).instConclusion arguments))))) := by
  have accepted := instantiateMany?_render_closeAll
    (HOL.Embedding.FirstOrder.CtxOfArity (inferenceRule rule).vars.length)
    (openRule (inferenceRule rule))
    (argumentSubstitution (inferenceRule rule).vars arguments arity) (ruleTheorem rule) rfl
  rw [closingArguments_argumentSubstitution] at accepted
  rw [subst_openRule (inferenceRules_schemaPackage firstOrder)
    (List.mem_map.mpr ⟨rule, member, rfl⟩) arguments arity] at accepted
  exact accepted


/-- Implication remains the ordinary defined HOL Light connective. -/
theorem render_imp_shape
    (left right : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) :
    (render (.imp left right)).term =
      ExcludedMiddle.impAppDB (render left).term (render right).term := rfl

/-- The external ordered theorem vector contributes its exact dependency set.
Repeated uses remain separate graph parents even though axiom tags are sets. -/
def premiseAxioms : List Theorem → Finset Sequent
  | [] => ∅
  | input :: inputs => input.axioms ∪ premiseAxioms inputs



/-- Arguments are emitted in actual universal-elimination order. -/
def instantiationArguments (arguments : List Pattern) : List CanonicalTerm :=
  (arguments.map fun argument => ReverseTranslation.reverseCanonical
    ReverseTranslation.Naming.empty (term (encode argument))).reverse

private theorem selected_kept {before after : Array Theorem}
    (kept : ∀ (index : Nat) (fact : Theorem),
      before[index]? = some fact → after[index]? = some fact)
    {roots : List Nat} {inputs : List Theorem}
    (selected : lookupPremises before roots = some inputs) :
    lookupPremises after roots = some inputs := by
  induction roots generalizing inputs with
  | nil => cases Option.some.inj selected; rfl
  | cons root roots ih =>
      cases head : before[root]? with
      | none => simp [lookupPremises, head] at selected
      | some input =>
          cases tail : lookupPremises before roots with
          | none => simp [lookupPremises, head, tail] at selected
          | some remaining =>
              have same : input :: remaining = inputs := by
                simpa [lookupPremises, head, tail] using selected
              rw [← same]
              rw [lookupPremises, kept root input head, ih tail]
              rfl



/-- Discharge an authored premise list using actual implication blocks and
physical roots. The expected intermediate formulas guide the compilation;
each actual premise and implication shape is checked before emission. -/
def emitImplications (axiomPolicy : AxiomPolicy) [DecidablePred axiomPolicy] :
    Theorem → List (HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) →
    HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol → List Theorem → List Nat →
    Nat → Origin → ProofExecution.State → Option (ProofExecution.State × Nat)
  | input, [], goal, [], [], inputRoot, _, state =>
      if input.sequent.hyp = ∅ ∧ input.sequent.concl = render goal then some (state, inputRoot) else none
  | input, antecedent :: antecedents, goal, premise :: premises, premiseRoot :: premiseRoots,
      inputRoot, origin, state => do
      let left := render antecedent
      let right := render (HOL.hypChain antecedents goal)
      if fullShape : input.sequent.concl = render (.imp antecedent (HOL.hypChain antecedents goal)) then
        if matching : premise.sequent.concl = left then
          let shape := (congrArg CanonicalTerm.term fullShape).trans (render_imp_shape _ _)
          let block ← ImplicationExpansion.mpTypedBlock? axiomPolicy input premise left right
            (render_isBool _) (render_isBool _) shape matching origin
          let (result, root) ← emitBlock axiomPolicy [inputRoot, premiseRoot] block state
          emitImplications axiomPolicy (ImplicationExpansion.mpResult input premise right)
            antecedents goal premises premiseRoots root origin result
        else none
      else none
  | _, _, _, _, _, _, _, _ => none

/-- The complete ordered premise chain preserves the exact theorem data and
its existing physical roots. Every MP is an explicit checked primitive graph. -/
theorem emitImplications_checked (axiomPolicy : AxiomPolicy) [DecidablePred axiomPolicy]
    {external : List Theorem} {state : ProofExecution.State}
    (earlier : BuildChecked axiomPolicy external state)
    (input : Theorem) (antecedents : List (HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol))
    (goal : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) (premises : List Theorem)
    (premiseRoots : List Nat) (inputRoot : Nat) (origin : Origin)
    (inputFound : state.cache[inputRoot]? = some input)
    (selected : lookupPremises state.cache premiseRoots = some premises)
    (inputHyp : input.sequent.hyp = ∅)
    (inputShape : input.sequent.concl = render (HOL.hypChain antecedents goal))
    (related : List.Forall₂ (fun antecedent premise =>
      premise.sequent.hyp = ∅ ∧ premise.sequent.concl = render antecedent) antecedents premises) :
    ∃ result root out,
      emitImplications axiomPolicy input antecedents goal premises premiseRoots inputRoot origin state =
        some (result, root) ∧
      BuildChecked axiomPolicy external result ∧ result.cache[root]? = some out ∧
      out.axioms = input.axioms ∪ premiseAxioms premises ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = render goal ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → result.cache[index]? = some fact := by
  induction related generalizing input premiseRoots inputRoot state with
  | nil =>
      have length := lookupPremises_length state.cache selected
      have rootsNil : premiseRoots = [] := List.eq_nil_of_length_eq_zero (by simpa using length.symm)
      subst premiseRoots
      exact ⟨state, inputRoot, input,
        by simp [emitImplications, inputHyp, inputShape, HOL.hypChain], earlier, inputFound,
        by simp [premiseAxioms], inputHyp, inputShape, fun _ _ found => found⟩
  | @cons antecedent premise antecedents premises firstRelated restRelated ih =>
      cases premiseRoots with
      | nil => simp [lookupPremises] at selected
      | cons premiseRoot premiseRoots =>
          have premiseFound : state.cache[premiseRoot]? = some premise := by
            simpa using lookupPremises_at selected 0 (by simp)
          have restSelected : lookupPremises state.cache premiseRoots = some premises := by
            cases found : lookupPremises state.cache premiseRoots with
            | none => simp [lookupPremises, premiseFound, found] at selected
            | some remaining =>
                have same : premise :: remaining = premise :: premises := by
                  simpa [lookupPremises, premiseFound, found] using selected
                exact congrArg some (List.cons.inj same).2
          let left := render antecedent
          let right := render (HOL.hypChain antecedents goal)
          have fullShape : input.sequent.concl = render (.imp antecedent (HOL.hypChain antecedents goal)) :=
            inputShape
          have shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term := by
            rw [inputShape]
            exact render_imp_shape _ _
          obtain ⟨block, computed, blockChecked⟩ := ImplicationExpansion.mpTypedBlock?_checked
            axiomPolicy input premise left right (render_isBool _) (render_isBool _) shape firstRelated.2 origin
          have blockSelected : lookupPremises state.cache [inputRoot, premiseRoot] = some [input, premise] := by
            simp [lookupPremises, inputFound, premiseFound]
          obtain ⟨nextState, nextRoot, emitted, nextChecked, nextFound, _, kept⟩ :=
            emitBlock_checked earlier blockSelected blockChecked
          let next := ImplicationExpansion.mpResult input premise right
          have nextHyp : next.sequent.hyp = ∅ := by
            simp [next, ImplicationExpansion.mpResult, Theorem.unionResult, inputHyp, firstRelated.1]
          obtain ⟨result, root, out, continued, checked, rootFound, tags, hypotheses, conclusion, retained⟩ :=
            ih nextChecked next premiseRoots nextRoot nextFound (selected_kept kept restSelected) nextHyp rfl
          refine ⟨result, root, out, ?_, checked, rootFound, ?_, hypotheses, conclusion, ?_⟩
          · simpa [emitImplications, left, right, fullShape, firstRelated.2, computed, emitted, next] using continued
          · simpa only [next, ImplicationExpansion.mpResult, Theorem.unionResult, premiseAxioms,
              Finset.union_assoc] using tags
          · intro index fact found
            exact retained index fact (kept index fact found)



/-- Compute a concrete primitive graph for one original admitted source rule.
The original instantiator remains the admission boundary. The output stores
one finite axiom, universal-elimination blocks and ordered implication blocks. -/
def emitRule? (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (inputs : List Theorem) (origin : Origin) : Option ProofSystem.Certificate := do
  let (premises, conclusion) ← instantiateRule? definition ruleInstance
  if inputs.length = premises.length then
    let rule ← definition.1.lookupRule? ruleInstance.ruleId
    let axiomPolicy := policy (inferenceRules definition.1)
    let (afterAxiom, axiomRoot) ← emit axiomPolicy (RuleRequest.axiom (ruleSequent rule)) [] origin (start inputs)
    let arguments := instantiationArguments ruleInstance.arguments
    let instantiated ← QuantifierExpansion.instantiateMany? (ruleTheorem rule) arguments
    let (afterSpec, specRoot) ← QuantifierExpansion.emitSpecChain axiomPolicy (ruleTheorem rule)
      arguments axiomRoot origin afterAxiom
    let (result, root) ← emitImplications axiomPolicy instantiated (premises.map judgment)
      (judgment conclusion) inputs (List.range inputs.length) specRoot origin afterSpec
    pure (finish result root)
  else none

/-- The general concrete emitter realizes every original first-order rule
instance and its ordered theorem premises, retaining their precise axiom tags. -/
theorem emitRule?_checked {definition : ValidatedCalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern) (inputs : List Theorem) (origin : Origin)
    (admitted : instantiateRule? definition ruleInstance = some (premises, conclusion))
    (related : List.Forall₂ (fun goal input =>
      input.sequent.hyp = ∅ ∧ input.sequent.concl = render (judgment goal)) premises inputs) :
    ∃ rule block out,
      definition.1.lookupRule? ruleInstance.ruleId = some rule ∧
      emitRule? definition ruleInstance inputs origin = some block ∧
      BlockChecked (policy (inferenceRules definition.1)) inputs out block ∧
      out.axioms = {ruleSequent rule} ∪ premiseAxioms inputs ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = render (judgment conclusion) := by
  obtain ⟨rule, found, member, arity, premisesSame, conclusionSame⟩ := instantiated_rule firstOrder admitted
  let axiomPolicy := policy (inferenceRules definition.1)
  let initial := start inputs
  let afterAxiom : ProofExecution.State :=
    ⟨initial.cache.push (ruleTheorem rule),
      initial.receipts.push ⟨ruleTheorem rule, RuleRequest.axiom (ruleSequent rule), [], origin⟩⟩
  have axiomComputed : emit axiomPolicy (RuleRequest.axiom (ruleSequent rule)) [] origin initial =
      some (afterAxiom, initial.cache.size) :=
    emit_of_checked (ruleTheorem_checked member) rfl
  have axiomChecked := (emit_checked (start_checked axiomPolicy inputs) axiomComputed).1
  have axiomFound : afterAxiom.cache[initial.cache.size]? = some (ruleTheorem rule) :=
    Array.getElem?_push_size
  let instantiated := Theorem.preserveAxiomsResult (ruleTheorem rule) ∅
    (render (HOL.hypChain (premises.map judgment) (judgment conclusion)))
  have substituted : QuantifierExpansion.instantiateMany? (ruleTheorem rule)
      (instantiationArguments ruleInstance.arguments) = some instantiated := by
    have computed := instantiateMany?_rule firstOrder member ruleInstance.arguments arity
    rw [← premisesSame, ← conclusionSame] at computed
    exact computed
  obtain ⟨afterSpec, specRoot, specComputed, specChecked, specFound, specKept⟩ :=
    QuantifierExpansion.emitSpecChain_checked axiomPolicy axiomChecked (ruleTheorem rule)
      (instantiationArguments ruleInstance.arguments) initial.cache.size origin axiomFound substituted
  have axiomInputs : lookupPremises afterAxiom.cache (List.range inputs.length) = some inputs :=
    selected_kept (fun index fact present => emit_preserves_lookup axiomComputed present)
      (lookupPremises_range inputs)
  have specInputs := selected_kept specKept axiomInputs
  have formulasRelated : List.Forall₂ (fun goal input =>
      input.sequent.hyp = ∅ ∧ input.sequent.concl = render goal) (premises.map judgment) inputs :=
    List.forall₂_map_left_iff.mpr related
  obtain ⟨result, root, out, implicationsComputed, checked, rootFound, tags, hypotheses, claim, _⟩ :=
    emitImplications_checked axiomPolicy specChecked instantiated (premises.map judgment)
      (judgment conclusion) inputs (List.range inputs.length) specRoot origin specFound specInputs rfl rfl formulasRelated
  have length : inputs.length = premises.length := related.length_eq.symm
  refine ⟨rule, finish result root, out, found, ?_, finish_checked checked rootFound, tags, hypotheses, claim⟩
  simp only [emitRule?, admitted, found]
  change (if inputs.length = premises.length then
    (emit axiomPolicy (RuleRequest.axiom (ruleSequent rule)) [] origin initial).bind
      (fun axiomPair =>
        (QuantifierExpansion.instantiateMany? (ruleTheorem rule)
          (instantiationArguments ruleInstance.arguments)).bind (fun instanceTheorem =>
          (QuantifierExpansion.emitSpecChain axiomPolicy (ruleTheorem rule)
            (instantiationArguments ruleInstance.arguments) axiomPair.2 origin axiomPair.1).bind (fun specPair =>
            (emitImplications axiomPolicy instanceTheorem (premises.map judgment)
              (judgment conclusion) inputs (List.range inputs.length) specPair.2 origin specPair.1).bind
                (fun finalPair => some (finish finalPair.1 finalPair.2)))))
    else none) = _
  rw [if_pos length, axiomComputed, Option.bind_some, substituted, Option.bind_some,
    specComputed, Option.bind_some, implicationsComputed]
  rfl

/-- Failure of the original source instantiator refuses before emitting any
HOL axiom or derived-rule block. -/
theorem emitRule?_refused {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    (inputs : List Theorem) (origin : Origin)
    (refused : instantiateRule? definition ruleInstance = none) :
    emitRule? definition ruleInstance inputs origin = none := by
  simp [emitRule?, refused]

/-- Missing or excess theorem premises cannot leave a partial implication as
a successful local source-rule output. -/
theorem emitRule?_wrong_premise_count {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern} (inputs : List Theorem) (origin : Origin)
    (admitted : instantiateRule? definition ruleInstance = some (premises, conclusion))
    (mismatched : inputs.length ≠ premises.length) :
    emitRule? definition ruleInstance inputs origin = none := by
  simp [emitRule?, admitted, mismatched]



/-- Successful discharge stores exactly fifty-eight primitive occurrences per
ordered premise. Incoming roots are reused rather than unfolded as trees. -/
theorem emitImplications_size {axiomPolicy : AxiomPolicy} [DecidablePred axiomPolicy]
    {input : Theorem} {antecedents : List (HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol)}
    {goal : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol}
    {premises : List Theorem} {premiseRoots : List Nat} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (computed : emitImplications axiomPolicy input antecedents goal premises premiseRoots inputRoot origin state =
      some (result, root)) :
    result.receipts.size = state.receipts.size + 58 * premises.length := by
  induction antecedents generalizing input premises premiseRoots inputRoot state with
  | nil =>
      cases premises with
      | cons premise premises => simp [emitImplications] at computed
      | nil =>
          cases premiseRoots with
          | cons premiseRoot premiseRoots => simp [emitImplications] at computed
          | nil =>
              by_cases valid : input.sequent.hyp = ∅ ∧ input.sequent.concl = render goal
              · have same : (state, inputRoot) = (result, root) := by
                  simpa [emitImplications, valid] using computed
                cases same
                simp
              · simp [emitImplications, valid] at computed
  | cons antecedent antecedents ih =>
      cases premises with
      | nil => simp [emitImplications] at computed
      | cons premise premises =>
          cases premiseRoots with
          | nil => simp [emitImplications] at computed
          | cons premiseRoot premiseRoots =>
              let left := render antecedent
              let right := render (HOL.hypChain antecedents goal)
              by_cases fullShape : input.sequent.concl = render (.imp antecedent (HOL.hypChain antecedents goal))
              · by_cases matching : premise.sequent.concl = left
                · let shape := (congrArg CanonicalTerm.term fullShape).trans (render_imp_shape _ _)
                  cases blockComputed : ImplicationExpansion.mpTypedBlock? axiomPolicy input premise left right
                      (render_isBool _) (render_isBool _) shape matching origin with
                  | none => simp [emitImplications, fullShape, left, right, matching, blockComputed] at computed
                  | some block =>
                      cases emitted : emitBlock axiomPolicy [inputRoot, premiseRoot] block state with
                      | none => simp [emitImplications, fullShape, left, right, matching, blockComputed, emitted] at computed
                      | some pair =>
                          obtain ⟨nextState, nextRoot⟩ := pair
                          have continued : emitImplications axiomPolicy
                              (ImplicationExpansion.mpResult input premise right) antecedents goal premises premiseRoots
                              nextRoot origin nextState = some (result, root) := by
                            simpa [emitImplications, fullShape, left, right, matching, blockComputed, emitted] using computed
                          have remaining := ih continued
                          have count := ImplicationExpansion.mpTypedBlock?_size axiomPolicy input premise left right
                            (render_isBool _) (render_isBool _) shape matching origin blockComputed
                          have added := (emitBlock_size emitted).2
                          rw [added, count] at remaining
                          simpa only [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
                            Nat.add_left_comm] using remaining
                · simp [emitImplications, fullShape, left, matching] at computed
              · simp [emitImplications, fullShape] at computed

/-- Every successful rule expansion retains the original instance's premise
count; mismatched theorem vectors refuse before emitting a graph. -/
theorem emitRule?_premise_count {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {inputs : List Theorem} {origin : Origin} {block : ProofSystem.Certificate}
    (computed : emitRule? definition ruleInstance inputs origin = some block) :
    ∃ premises conclusion, instantiateRule? definition ruleInstance = some (premises, conclusion) ∧
      inputs.length = premises.length := by
  cases admitted : instantiateRule? definition ruleInstance with
  | none => simp [emitRule?, admitted] at computed
  | some pair =>
      obtain ⟨premises, conclusion⟩ := pair
      by_cases length : inputs.length = premises.length
      · exact ⟨premises, conclusion, rfl, length⟩
      · simp [emitRule?, admitted, length] at computed

/-- A successful computation exposes its actual admission and checked
primitive-emission stages. The same stages support size and origin accounting. -/
theorem emitRule?_parts {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {inputs : List Theorem} {origin : Origin} {block : ProofSystem.Certificate}
    (computed : emitRule? definition ruleInstance inputs origin = some block) :
    ∃ premises conclusion rule afterAxiom axiomRoot instanceTheorem afterSpec specRoot result root,
      instantiateRule? definition ruleInstance = some (premises, conclusion) ∧
      inputs.length = premises.length ∧ definition.1.lookupRule? ruleInstance.ruleId = some rule ∧
      emit (policy (inferenceRules definition.1)) (RuleRequest.axiom (ruleSequent rule)) [] origin (start inputs) =
        some (afterAxiom, axiomRoot) ∧
      QuantifierExpansion.instantiateMany? (ruleTheorem rule) (instantiationArguments ruleInstance.arguments) =
        some instanceTheorem ∧
      QuantifierExpansion.emitSpecChain (policy (inferenceRules definition.1)) (ruleTheorem rule)
        (instantiationArguments ruleInstance.arguments) axiomRoot origin afterAxiom = some (afterSpec, specRoot) ∧
      emitImplications (policy (inferenceRules definition.1)) instanceTheorem (premises.map judgment)
        (judgment conclusion) inputs (List.range inputs.length) specRoot origin afterSpec = some (result, root) ∧
      finish result root = block := by
  cases admitted : instantiateRule? definition ruleInstance with
  | none => simp [emitRule?, admitted] at computed
  | some pair =>
      obtain ⟨premises, conclusion⟩ := pair
      by_cases length : inputs.length = premises.length
      · cases found : definition.1.lookupRule? ruleInstance.ruleId with
        | none => simp [emitRule?, admitted, found] at computed
        | some rule =>
            let axiomPolicy := policy (inferenceRules definition.1)
            cases axiomComputed : emit axiomPolicy (RuleRequest.axiom (ruleSequent rule)) [] origin (start inputs) with
            | none => simp [emitRule?, admitted, found, axiomPolicy, axiomComputed] at computed
            | some axiomPair =>
                obtain ⟨afterAxiom, axiomRoot⟩ := axiomPair
                cases instantiated : QuantifierExpansion.instantiateMany? (ruleTheorem rule)
                    (instantiationArguments ruleInstance.arguments) with
                | none => simp [emitRule?, admitted, found, axiomPolicy, axiomComputed, instantiated] at computed
                | some instanceTheorem =>
                    cases specComputed : QuantifierExpansion.emitSpecChain axiomPolicy (ruleTheorem rule)
                        (instantiationArguments ruleInstance.arguments) axiomRoot origin afterAxiom with
                    | none => simp [emitRule?, admitted, found, axiomPolicy, axiomComputed,
                        instantiated, specComputed] at computed
                    | some specPair =>
                        obtain ⟨afterSpec, specRoot⟩ := specPair
                        cases implicationsComputed : emitImplications axiomPolicy instanceTheorem (premises.map judgment)
                            (judgment conclusion) inputs (List.range inputs.length) specRoot origin afterSpec with
                        | none => simp [emitRule?, admitted, found, axiomPolicy, axiomComputed,
                            instantiated, specComputed, implicationsComputed] at computed
                        | some finalPair =>
                            obtain ⟨result, root⟩ := finalPair
                            have same : finish result root = block := by
                              simpa [emitRule?, admitted, if_pos length, found, axiomPolicy, axiomComputed,
                                instantiated, specComputed, implicationsComputed] using computed
                            refine ⟨premises, conclusion, rule, afterAxiom, axiomRoot, instanceTheorem,
                              afterSpec, specRoot, result, root, ?_, length, ?_, ?_, ?_, ?_, ?_, same⟩
                            all_goals first | assumption | rfl
      · simp [emitRule?, admitted, length] at computed

/-- The concrete successful graph has one axiom occurrence, eighteen nodes
per source argument and fifty-eight nodes per original ordered premise. This
counts physical primitive nodes, independently of payload and running time. -/
theorem emitRule?_size {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {inputs : List Theorem} {origin : Origin} {block : ProofSystem.Certificate}
    (computed : emitRule? definition ruleInstance inputs origin = some block) :
    block.1.length = 1 + 18 * ruleInstance.arguments.length + 58 * inputs.length := by
  obtain ⟨premises, conclusion, rule, afterAxiom, axiomRoot, instanceTheorem, afterSpec, specRoot,
    result, root, _, _, _, axiomComputed, _, specComputed, implicationsComputed, same⟩ := emitRule?_parts computed
  obtain ⟨axiomOutput, _, _, _, receiptsSame, _⟩ := (emit_eq_some_iff _ _ _ _ _ _).mp axiomComputed
  have axiomCount : afterAxiom.receipts.size = 1 := by
    rw [receiptsSame]
    simp [start]
  have specCount := (QuantifierExpansion.emitSpecChain_size specComputed).2
  have implicationCount := emitImplications_size implicationsComputed
  rw [axiomCount] at specCount
  rw [specCount] at implicationCount
  rw [← same]
  simpa only [finish, Array.length_toList, instantiationArguments,
    List.length_reverse, List.length_map] using implicationCount


/-- Every primitive occurrence produced by ordered premise discharge retains
the supplied source origin; earlier receipt origins stay unchanged. -/
theorem emitImplications_origins {axiomPolicy : AxiomPolicy} [DecidablePred axiomPolicy]
    {input : Theorem} {antecedents : List (HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol)}
    {goal : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol}
    {premises : List Theorem} {premiseRoots : List Nat} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (computed : emitImplications axiomPolicy input antecedents goal premises premiseRoots inputRoot origin state =
      some (result, root)) :
    result.receipts.toList.map (·.origin) =
      state.receipts.toList.map (·.origin) ++ List.replicate (58 * premises.length) origin := by
  induction antecedents generalizing input premises premiseRoots inputRoot state with
  | nil =>
      cases premises with
      | cons premise premises => simp [emitImplications] at computed
      | nil =>
          cases premiseRoots with
          | cons premiseRoot premiseRoots => simp [emitImplications] at computed
          | nil =>
              by_cases valid : input.sequent.hyp = ∅ ∧ input.sequent.concl = render goal
              · have same : (state, inputRoot) = (result, root) := by
                  simpa [emitImplications, valid] using computed
                cases same
                simp
              · simp [emitImplications, valid] at computed
  | cons antecedent antecedents ih =>
      cases premises with
      | nil => simp [emitImplications] at computed
      | cons premise premises =>
          cases premiseRoots with
          | nil => simp [emitImplications] at computed
          | cons premiseRoot premiseRoots =>
              let left := render antecedent
              let right := render (HOL.hypChain antecedents goal)
              by_cases fullShape : input.sequent.concl = render (.imp antecedent (HOL.hypChain antecedents goal))
              · by_cases matching : premise.sequent.concl = left
                · let shape := (congrArg CanonicalTerm.term fullShape).trans (render_imp_shape _ _)
                  cases blockComputed : ImplicationExpansion.mpTypedBlock? axiomPolicy input premise left right
                      (render_isBool _) (render_isBool _) shape matching origin with
                  | none => simp [emitImplications, fullShape, left, right, matching, blockComputed] at computed
                  | some block =>
                      cases emitted : emitBlock axiomPolicy [inputRoot, premiseRoot] block state with
                      | none => simp [emitImplications, fullShape, left, right, matching, blockComputed, emitted] at computed
                      | some pair =>
                          obtain ⟨nextState, nextRoot⟩ := pair
                          have continued : emitImplications axiomPolicy
                              (ImplicationExpansion.mpResult input premise right) antecedents goal premises premiseRoots
                              nextRoot origin nextState = some (result, root) := by
                            simpa [emitImplications, fullShape, left, right, matching, blockComputed, emitted] using computed
                          have preserved := ih continued
                          have originParts := congrArg (List.map (fun pair => pair.2)) (emitBlock_witnesses emitted)
                          have appended : nextState.receipts.toList.map (·.origin) =
                              state.receipts.toList.map (·.origin) ++ block.1.map (·.origin) := by
                            simpa only [List.map_append, List.map_map, Function.comp_def] using originParts
                          have origins := ImplicationExpansion.mpTypedBlock?_origins axiomPolicy input premise left right
                            (render_isBool _) (render_isBool _) shape matching origin blockComputed
                          rw [appended, origins] at preserved
                          simpa only [List.append_assoc, ← List.replicate_add, List.length_cons,
                            Nat.mul_succ, Nat.add_comm] using preserved
                · simp [emitImplications, fullShape, left, matching] at computed
              · simp [emitImplications, fullShape] at computed

/-- The assembled source-rule expansion retains its source origin on every
physical primitive node, in the same chronological list used by HOL replay. -/
theorem emitRule?_origins {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {inputs : List Theorem} {origin : Origin} {block : ProofSystem.Certificate}
    (computed : emitRule? definition ruleInstance inputs origin = some block) :
    block.1.map (·.origin) =
      List.replicate (1 + 18 * ruleInstance.arguments.length + 58 * inputs.length) origin := by
  obtain ⟨premises, conclusion, rule, afterAxiom, axiomRoot, instanceTheorem, afterSpec, specRoot,
    result, root, _, _, _, axiomComputed, _, specComputed, implicationsComputed, same⟩ := emitRule?_parts computed
  obtain ⟨axiomOutput, _, _, _, receiptsSame, _⟩ := (emit_eq_some_iff _ _ _ _ _ _).mp axiomComputed
  have axiomOrigins : afterAxiom.receipts.toList.map (·.origin) = [origin] := by
    rw [receiptsSame]
    simp [start]
  have specOrigins := QuantifierExpansion.emitSpecChain_origins specComputed
  have implicationOrigins := emitImplications_origins implicationsComputed
  rw [axiomOrigins] at specOrigins
  rw [specOrigins] at implicationOrigins
  rw [← same]
  simpa only [finish, instantiationArguments, List.length_reverse, List.length_map,
    ← List.replicate_one, ← List.replicate_add] using implicationOrigins




namespace Emission

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open _root_.Computability Turing Polynomial
open ProofDataEncoding Mettapedia.Languages.OpenTheory.SyntaxEncoding
attribute [local implicit_reducible] machine

/-- The original AXIOM receipt, with its complete theorem, request and origin.
The finite source row is fixed by the compiled program; provenance remains
variable-sized input on the physical stack. -/
def axiomNode (rule : RuleSchema) (origin : Origin) : ProofExecution.Receipt :=
  ⟨ruleTheorem rule, .axiom (ruleSequent rule), [], origin⟩

/-- The fixed prefix contains original product markers and complete original
kernel fields. It neither decodes nor invents a logical result at run time. -/
def axiomPrefix (rule : RuleSchema) : List Alphabet :=
  [4] ++ encodeWith theoremCodec (ruleTheorem rule) ++
    [4] ++ encodeWith requestCodec (.axiom (ruleSequent rule)) ++
    [4] ++ encodeWith (Codec.list Codec.nat) []

def axiomTemplate (rule : RuleSchema) : Template Alphabet :=
  (axiomPrefix rule).map some ++ [none]

theorem axiom_exact (rule : RuleSchema) (origin : Origin) :
    instantiate (axiomTemplate rule) (encodeWith originCodec origin) =
      encodeWith receiptCodec (axiomNode rule origin) := by
  simp [axiomTemplate, instantiate_append, instantiate_literals, axiomPrefix,
    axiomNode, receiptCodec, Codec.prod, Codec.mapped, Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith, encodeData_pair,
    List.append_assoc]

/-- The physical single-hole copier emits the entire original receipt and
clears its temporary and output stacks within this executed transition bound. -/
def axiomOutputs (rule : RuleSchema) (origin : Origin) :
    TM2OutputsInTime (machine (axiomTemplate rule)) (encodeWith originCodec origin)
      (some (encodeWith receiptCodec (axiomNode rule origin)))
      (4 * ((axiomPrefix rule).length + 2) * ((encodeWith originCodec origin).length + 1)) := by
  have ran := outputs (axiomTemplate rule) (encodeWith originCodec origin)
  rw [axiom_exact] at ran
  simpa [axiomTemplate] using ran

/-- This is a genuine executed polynomial-time emitter for each fixed rule.
Its input includes every UTF-8 origin byte and every binary origin index. -/
noncomputable def axiomRealization (rule : RuleSchema) :
    TM2ComputableInPolyTime (encodeWith originCodec)
      (fun node : ProofExecution.Receipt => encodeWith receiptCodec node) (axiomNode rule) where
  tm := machine (axiomTemplate rule)
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C (4 * ((axiomPrefix rule).length + 2)) * (X + C 1)
  outputsFun origin := by
    change TM2OutputsInTime (machine (axiomTemplate rule)) ((encodeWith originCodec origin).map id)
      (some ((encodeWith receiptCodec (axiomNode rule origin)).map id)) _
    simp only [List.map_id_fun]
    simpa using axiomOutputs rule origin

/-- Storage has not introduced a second authority: decoding returns the
original complete receipt, which the existing primitive checker validates. -/
theorem axiom_decodes (rule : RuleSchema) (origin : Origin) :
    decodeWith receiptCodec (instantiate (axiomTemplate rule) (encodeWith originCodec origin)) =
      some (axiomNode rule origin) := by
  rw [axiom_exact]
  exact decodeWith_encodeWith receiptCodec _

theorem axiom_emitted {definition : CalculusLanguageDef} {rule : RuleSchema}
    (member : rule ∈ definition.rules) (origin : Origin) (state : ProofExecution.State) :
    emit (policy (inferenceRules definition)) (.axiom (ruleSequent rule)) [] origin state =
      some (⟨state.cache.push (ruleTheorem rule),
        state.receipts.push (axiomNode rule origin)⟩, state.cache.size) := by
  exact emit_of_checked (ruleTheorem_checked member) rfl


/-- The emitted node is replayed by the original rule witness. Origin labels
are retained evidence metadata; they do not substitute for axiom authorization. -/
theorem axiom_replays {definition : CalculusLanguageDef} {rule : RuleSchema}
    (member : rule ∈ definition.rules) (origin : Origin) (cache : Array Theorem) :
    (axiomNode rule origin).replay (ruleWitness (policy (inferenceRules definition))) cache =
      some (cache.push (ruleTheorem rule)) := by
  apply (ProofSystem.node_replay_iff _ _ _ _).mpr
  exact ⟨rfl, ruleTheorem_checked member, rfl⟩

end Emission

end Mettapedia.Languages.HOLLight.InferenceRuleExpansion
