import Mettapedia.Languages.HOLLight.InferenceHosting
import Mettapedia.Languages.HOLLight.StorageSize
import Mettapedia.Languages.HOLLight.InferenceRuleExpansion
import Mettapedia.Languages.HOLLight.ImplicationStorageBounds
import Mettapedia.Languages.HOLLight.QuantifierStorageBounds
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Source-data storage in the concrete HOL inference presentation

Constructor names keep their authored UTF-8 bytes and binary arity. Opaque
canonical values use the shared flat pattern tokens. The resulting names and
fully applied data terms have linear storage bounds in the original pattern
account, including binder metadata and residual captures.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.InferenceStorageBounds

open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Logic.HOL.Embedding.InferenceRules

private theorem stringList_tokens (values : List String) :
    OpenTheory.StorageSize.list OpenTheory.StorageSize.string values =
      1 + Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [OpenTheory.StorageSize.list_cons, OpenTheory.StorageSize.string,
        Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize, ih]
      omega

theorem name_storage (value : Name) :
    OpenTheory.StorageSize.name value = nameSize value + 2 := by
  unfold OpenTheory.StorageSize.name nameSize
  rw [stringList_tokens]
  unfold OpenTheory.StorageSize.string
  omega

theorem literal_name_storage (value : Data) :
    OpenTheory.StorageSize.name (functionName (.literal value)) ≤
      21 + 6 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight value.val := by
  rw [name_storage]
  have bound := literal_name_size value
  omega

theorem constructor_name_storage (value : String) (arity : Nat) :
    OpenTheory.StorageSize.name (functionName (.constructor value arity)) =
      25 + 2 * (Nat.digits 2 arity).length + value.utf8ByteSize := by
  rw [name_storage, constructor_name_size]
  omega

theorem binaryDigits_le (value : Nat) : (Nat.digits 2 value).length ≤ value := by
  apply (Nat.digits_length_le_iff (by decide : 1 < 2) value).mpr
  exact Nat.lt_two_pow_self

/-- The original curried constructor type, with no change of term carrier. -/
def dataArrow : Nat → Ty
  | 0 => dataType
  | arity + 1 => .function dataType (dataArrow arity)

theorem dataType_storage : OpenTheory.StorageSize.ty dataType = 21 := by decide +kernel


theorem dataArrow_storage (arity : Nat) :
    OpenTheory.StorageSize.ty (dataArrow arity) = 21 + 30 * arity := by
  induction arity with
  | zero => exact dataType_storage
  | succ arity ih =>
      rw [dataArrow, OpenTheory.StorageSize.functionType_storage, dataType_storage, ih]
      omega

def literalTerm (value : Data) : DBTerm :=
  .const (.mk (functionName (.literal value)) .undefined) dataType

def constructorTerm (value : String) (arity : Nat) : DBTerm :=
  .const (.mk (functionName (.constructor value arity)) .undefined) (dataArrow arity)

theorem literalTerm_storage (value : Data) :
    OpenTheory.StorageSize.term (literalTerm value) ≤
      45 + 6 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight value.val := by
  have bound := literal_name_storage value
  simp only [literalTerm, OpenTheory.StorageSize.term, OpenTheory.StorageSize.constant,
    OpenTheory.StorageSize.constantProvenance, dataType_storage]
  omega

theorem constructorTerm_storage (value : String) (arity : Nat) :
    OpenTheory.StorageSize.term (constructorTerm value arity) ≤
      60 * (arity + 1) + value.utf8ByteSize := by
  simp only [constructorTerm, OpenTheory.StorageSize.term, OpenTheory.StorageSize.constant,
    OpenTheory.StorageSize.constantProvenance]
  rw [constructor_name_storage, dataArrow_storage]
  have digits := binaryDigits_le arity
  omega

/-- Applying a constructor retains the authored child order. -/
def applyTerms (head : DBTerm) (arguments : List DBTerm) : DBTerm :=
  arguments.foldl DBTerm.app head

theorem applyTerms_storage (head : DBTerm) (arguments : List DBTerm) :
    OpenTheory.StorageSize.term (applyTerms head arguments) =
      OpenTheory.StorageSize.term head + arguments.length +
        (arguments.map OpenTheory.StorageSize.term).sum := by
  induction arguments generalizing head with
  | nil => simp [applyTerms]
  | cons argument arguments ih =>
      rw [applyTerms, List.foldl_cons]
      change OpenTheory.StorageSize.term (applyTerms (.app head argument) arguments) = _
      rw [ih]
      simp only [OpenTheory.StorageSize.term, List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- The direct data expression used by the typed HOL presentation. -/
def dataTerm : Pattern → DBTerm
  | .fvar _ => literalTerm Data.default
  | .apply value arguments => applyTerms (constructorTerm value arguments.length) (arguments.map dataTerm)
  | pattern => literalTerm (Data.opaque pattern)
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem pattern_weight_positive (pattern : Pattern) :
    0 < Mettapedia.OSLF.MeTTaIL.PatternTokens.weight pattern := by
  cases pattern <;> simp only [Mettapedia.OSLF.MeTTaIL.PatternTokens.weight] <;> omega

theorem pattern_list_weight (patterns : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight patterns =
      1 + patterns.length + (patterns.map Mettapedia.OSLF.MeTTaIL.PatternTokens.weight).sum := by
  induction patterns with
  | nil => rfl
  | cons first rest ih =>
      simp only [Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight, List.length_cons,
        List.map_cons, List.sum_cons, ih]
      omega

private theorem sum_data_storage (patterns : List Pattern)
    (bounded : ∀ pattern ∈ patterns, OpenTheory.StorageSize.term (dataTerm pattern) ≤
      100 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight pattern) :
    ((patterns.map dataTerm).map OpenTheory.StorageSize.term).sum ≤
      100 * (patterns.map Mettapedia.OSLF.MeTTaIL.PatternTokens.weight).sum := by
  induction patterns with
  | nil => simp
  | cons first rest ih =>
      have firstBound := bounded first (by simp)
      have restBound := ih (fun value member => bounded value (by simp [member]))
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem opaqueTerm_storage (pattern : Pattern) :
    OpenTheory.StorageSize.term (literalTerm (Data.opaque pattern)) ≤
      100 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight pattern := by
  have positive := pattern_weight_positive pattern
  unfold Data.opaque
  split
  · rename_i valid
    have bound := literalTerm_storage ⟨pattern, valid⟩
    dsimp only at bound
    omega
  · have bound := literalTerm_storage Data.default
    have sized : Mettapedia.OSLF.MeTTaIL.PatternTokens.weight Data.default.val = 2 := rfl
    rw [sized] at bound
    omega

/-- Full UTF-8 and opaque binder payloads remain linear in source data size. -/
theorem dataTerm_storage (pattern : Pattern) :
    OpenTheory.StorageSize.term (dataTerm pattern) ≤
      100 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight pattern := by
  cases pattern with
  | fvar value =>
      have bound := literalTerm_storage Data.default
      have sized : Mettapedia.OSLF.MeTTaIL.PatternTokens.weight Data.default.val = 2 := rfl
      rw [sized] at bound
      simp only [dataTerm, Mettapedia.OSLF.MeTTaIL.PatternTokens.weight]
      omega
  | apply value arguments =>
      have children := sum_data_storage arguments (fun child member => dataTerm_storage child)
      have headBound := constructorTerm_storage value arguments.length
      simp only [dataTerm, applyTerms_storage, List.length_map,
        Mettapedia.OSLF.MeTTaIL.PatternTokens.weight]
      rw [pattern_list_weight]
      omega
  | _ => simpa only [dataTerm] using opaqueTerm_storage _
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- Mapping the typed curried application keeps the same ordered app spine. -/
theorem render_mkApps {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy}
    {result : HOL.Ty HOL.Embedding.FirstOrder.BaseTy} :
    ∀ {arity : Nat}
      (head : HOL.Term HOL.Embedding.InferenceRules.Symbol context (HOL.iterArrow arity dataTy result))
      (arguments : Fin arity → HOL.Term HOL.Embedding.InferenceRules.Symbol context dataTy),
      ReverseTranslation.reverseTermOpen (term
        (HOL.Embedding.FirstOrder.Term.mkApps (L := language) head arguments)) =
      applyTerms (ReverseTranslation.reverseTermOpen (term head))
        (List.ofFn (fun index => ReverseTranslation.reverseTermOpen (term (arguments index))))
  | 0, head, arguments => by simp [HOL.Embedding.FirstOrder.Term.mkApps, applyTerms]
  | arity + 1, head, arguments => by
      rw [HOL.Embedding.FirstOrder.Term.mkApps, render_mkApps, List.ofFn_succ]
      rfl

theorem reverse_dataArrow (arity : Nat) :
    ReverseTranslation.reverseTy (type (HOL.iterArrow arity dataTy dataTy)) = dataArrow arity := by
  induction arity with
  | zero => rfl
  | succ arity ih =>
      change Ty.function dataType (ReverseTranslation.reverseTy (type
        (HOL.iterArrow arity dataTy dataTy))) = _
      rw [ih]
      rfl

/-- This is a size bound for the actual typed translation, rather than a
second source-data interpreter. -/
theorem render_encode (pattern : Pattern) :
    ReverseTranslation.reverseTermOpen (term (encode pattern)) = dataTerm pattern := by
  cases pattern with
  | fvar value =>
      simp only [encode, encodeWith, term, HOL.mapTypes, ReverseTranslation.reverseTermOpen,
        ReverseTranslation.reverseTermWith, symbol, symbolName, ReverseTranslation.reverseSymbol,
        dataTerm, literalTerm]
      rfl
  | apply value arguments =>
      unfold encode encodeWith
      rw [render_mkApps]
      have head : ReverseTranslation.reverseTermOpen
          (term (context := []) (HOL.Term.const (HOL.Embedding.FirstOrder.Const.func (L := language) (Function.constructor value arguments.length)))) =
            constructorTerm value arguments.length := by
        change DBTerm.const (.mk (functionName (.constructor value arguments.length)) .undefined)
          (ReverseTranslation.reverseTy (type (HOL.iterArrow arguments.length dataTy dataTy))) = _
        rw [reverse_dataArrow]
        rfl
      rw [head]
      unfold dataTerm
      congr 1
      calc
        List.ofFn (fun index : Fin arguments.length =>
            ReverseTranslation.reverseTermOpen (term (encode arguments[index.val]))) =
          List.ofFn (fun index : Fin arguments.length => dataTerm arguments[index.val]) := by
            congr 1
            funext index
            have member : arguments[index.val] ∈ arguments := List.getElem_mem index.isLt
            exact render_encode arguments[index.val]
        _ = arguments.map dataTerm := List.ofFn_getElem_eq_map arguments dataTerm
  | _ =>
      simp only [encode, encodeWith, term, HOL.mapTypes, ReverseTranslation.reverseTermOpen,
        ReverseTranslation.reverseTermWith, symbol, symbolName, ReverseTranslation.reverseSymbol,
        dataTerm, literalTerm]
      rfl
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec


/-- The actual typed argument carrier includes its retained type annotation. -/
theorem encoded_argument_storage (pattern : Pattern) :
    OpenTheory.StorageSize.canonical
      (ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term (encode pattern))) ≤
      122 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight pattern := by
  change 1 + OpenTheory.StorageSize.term
    (ReverseTranslation.reverseTerm ReverseTranslation.Naming.empty (term (encode pattern))) +
      OpenTheory.StorageSize.ty dataType ≤ _
  rw [ReverseTranslation.reverseTerm_eq_reverseTermOpen, render_encode, dataType_storage]
  have bound := dataTerm_storage pattern
  have positive := pattern_weight_positive pattern
  omega

def holdsTerm : DBTerm := .const (.mk holdsName .undefined) (.function dataType Ty.bool)

theorem render_judgment_term (pattern : Pattern) :
    (render (judgment pattern)).term = .app holdsTerm (dataTerm pattern) := by
  change ReverseTranslation.reverseTerm ReverseTranslation.Naming.empty (term (holds (encode pattern))) = _
  rw [ReverseTranslation.reverseTerm_eq_reverseTermOpen]
  change DBTerm.app holdsTerm (ReverseTranslation.reverseTermOpen (term (encode pattern))) = _
  rw [render_encode]

theorem holdsTerm_storage : OpenTheory.StorageSize.term holdsTerm = 71 := by decide +kernel

/-- The actual source-judgment formula and its type have a linear full-data
bound, including the unchanged canonical payload of opaque source binders. -/
theorem render_judgment_storage (pattern : Pattern) :
    OpenTheory.StorageSize.canonical (render (judgment pattern)) ≤
      184 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight pattern := by
  have typed : (render (judgment pattern)).ty = Ty.bool := rfl
  simp only [OpenTheory.StorageSize.canonical, typed, render_judgment_term, OpenTheory.StorageSize.term]
  rw [holdsTerm_storage]
  have boolean : OpenTheory.StorageSize.ty Ty.bool = 11 := by decide +kernel
  rw [boolean]
  have bound := dataTerm_storage pattern
  have positive := pattern_weight_positive pattern
  omega

/-- All accepted theorem tags come from the fixed finite generated theory. -/
def theoryPayload (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) : Nat :=
  OpenTheory.StorageSize.finset OpenTheory.StorageSize.sequent
    (((axioms rules).map (fun formula => (⟨∅, render formula⟩ : Sequent))).toFinset)

theorem theorem_tag_storage (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    (value : Theorem) (allowed : (policy rules).AllowsTheorem value) :
    OpenTheory.StorageSize.finset OpenTheory.StorageSize.sequent value.axioms ≤ theoryPayload rules := by
  apply OpenTheory.StorageSize.finset_mono
  intro tagged member
  obtain ⟨empty, admitted⟩ := allowed tagged member
  simp only [List.mem_toFinset, List.mem_map]
  obtain ⟨formula, declared, exactConclusion⟩ := List.mem_map.mp admitted
  refine ⟨formula, declared, ?_⟩
  apply Sequent.ext
  · exact empty.symm
  · exact exactConclusion

theorem theorem_storage (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    (value : Theorem) (allowed : (policy rules).AllowsTheorem value)
    (empty : value.sequent.hyp = ∅) :
    OpenTheory.StorageSize.theoremData value ≤
      theoryPayload rules + 3 + OpenTheory.StorageSize.canonical value.sequent.concl := by
  have bound := theorem_tag_storage rules value allowed
  simp only [OpenTheory.StorageSize.theoremData, OpenTheory.StorageSize.sequent,
    empty, OpenTheory.StorageSize.finset_empty]
  omega


open InferenceRuleExpansion GraphExpansion
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open ProofExecution (Origin)

/-- Actual ordered implication discharge retains a quartic full-packet
bound, with the coefficient determined by the finite premise count. -/
theorem emitImplications_payload {axiomPolicy : AxiomPolicy} [DecidablePred axiomPolicy]
    {input : Theorem} {antecedents : List (HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol)}
    {goal : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol}
    {premises : List Theorem} {premiseRoots : List Nat} {inputRoot : Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (computed : emitImplications axiomPolicy input antecedents goal premises premiseRoots inputRoot origin state =
      some (result, root)) :
    graphWeight StorageSize.receiptPayload result.receipts.toList ≤
      graphWeight StorageSize.receiptPayload state.receipts.toList +
        ImplicationStorageBounds.chainCoefficient premises.length *
          ImplicationStorageBounds.chainInputUnits input premises origin ^ 4 := by
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
                simp [ImplicationStorageBounds.chainCoefficient]
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
                          have localPayload := ImplicationStorageBounds.mpTypedBlock?_actual_payload axiomPolicy input premise
                            left right (render_isBool _) (render_isBool _) shape matching origin blockComputed
                          have singlePacket : ImplicationStorageBounds.chainInputUnits input [premise] origin ≤
                              ImplicationStorageBounds.chainInputUnits input (premise :: premises) origin := by
                            simp only [ImplicationStorageBounds.chainInputUnits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
                            omega
                          have localBound := localPayload.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left singlePacket 4))
                          have packetStep := ImplicationStorageBounds.chainInputUnits_step input premise left right
                            (render_isBool _) shape premises origin
                          have remainingBound := Nat.mul_le_mul_left (ImplicationStorageBounds.chainCoefficient premises.length)
                            (Nat.pow_le_pow_left packetStep 4)
                          have appended := StorageSize.emitBlock_payload emitted
                          calc
                            graphWeight StorageSize.receiptPayload result.receipts.toList ≤
                                graphWeight StorageSize.receiptPayload nextState.receipts.toList +
                                  ImplicationStorageBounds.chainCoefficient premises.length *
                                    ImplicationStorageBounds.chainInputUnits (ImplicationExpansion.mpResult input premise right) premises origin ^ 4 := remaining
                            _ ≤ graphWeight StorageSize.receiptPayload state.receipts.toList +
                                ImplicationStorageBounds.payloadCoefficient * ImplicationStorageBounds.chainInputUnits input (premise :: premises) origin ^ 4 +
                                  ImplicationStorageBounds.chainCoefficient premises.length *
                                    (16 * ImplicationStorageBounds.chainInputUnits input (premise :: premises) origin) ^ 4 := by
                              rw [appended]
                              exact Nat.add_le_add (Nat.add_le_add_left localBound _) remainingBound
                            _ = _ := by
                              simp only [List.length_cons, ImplicationStorageBounds.chainCoefficient]
                              ring
                · simp [emitImplications, fullShape, left, matching] at computed
              · simp [emitImplications, fullShape] at computed

/-- Complete fixed schema payload, including each original universally
closed axiom and its actual singleton dependency tag. -/
def ruleTheoremsPayload (definition : CalculusLanguageDef) : Nat :=
  1 + (definition.rules.map fun rule => OpenTheory.StorageSize.theoremData (ruleTheorem rule)).sum

/-- The actual local source packet used by the concrete emitter. -/
def sourcePacketUnits (definition : CalculusLanguageDef) (ruleInstance : RuleInstance)
    (inputs : List Theorem) (origin : Origin) : Nat :=
  1 + ruleTheoremsPayload definition + 122 * Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight ruleInstance.arguments +
    (inputs.map OpenTheory.StorageSize.theoremData).sum + StorageSize.origin origin

theorem ruleTheorem_payload_le {definition : CalculusLanguageDef} {rule : RuleSchema}
    (member : rule ∈ definition.rules) :
    OpenTheory.StorageSize.theoremData (ruleTheorem rule) ≤ ruleTheoremsPayload definition := by
  have bounded := List.le_sum_of_mem (List.mem_map.mpr ⟨rule, member, rfl⟩ :
    OpenTheory.StorageSize.theoremData (ruleTheorem rule) ∈
      (definition.rules.map fun stored => OpenTheory.StorageSize.theoremData (ruleTheorem stored)))
  unfold ruleTheoremsPayload
  omega

theorem instantiationArguments_payload (arguments : List Pattern) :
    ((instantiationArguments arguments).map OpenTheory.StorageSize.canonical).sum ≤
      122 * Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight arguments := by
  unfold instantiationArguments
  rw [List.map_reverse, List.sum_reverse]
  induction arguments with
  | nil => simp [Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight]
  | cons argument rest ih =>
      have value := encoded_argument_storage argument
      simp only [List.map_cons, List.sum_cons, Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight]
      omega

/-- A fixed admitted arity and premise count determine one polynomial for
all successful concrete local certificates. -/
def ruleEmissionCoefficient (arity premises : Nat) : Nat :=
  4 + QuantifierStorageBounds.chainCoefficient arity +
    ImplicationStorageBounds.chainCoefficient premises * (QuantifierStorageBounds.chainCoefficient arity + 1) ^ 4


/-- Every byte-bearing local request emitted by the actual rule compiler is
bounded by one fixed-arity polynomial in its complete supplied data packet. -/
theorem emitRule?_payload (definition : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) (inputs : List Theorem) (origin : Origin)
    (arity premiseCap : Nat) (argsBound : ruleInstance.arguments.length ≤ arity)
    (inputsBound : inputs.length ≤ premiseCap) {block : ProofSystem.Certificate}
    (computed : emitRule? definition ruleInstance inputs origin = some block) :
    graphWeight StorageSize.receiptPayload block.1 ≤
      ruleEmissionCoefficient arity premiseCap *
        sourcePacketUnits definition.1 ruleInstance inputs origin ^ (4 * 2 ^ arity) := by
  obtain ⟨premises, conclusion, rule, afterAxiom, axiomRoot, instanceTheorem, afterSpec, specRoot,
    result, root, _, _, found, axiomComputed, instantiated, specComputed, implicationsComputed, same⟩ :=
    emitRule?_parts computed
  have member : rule ∈ definition.1.rules := List.mem_of_find?_eq_some found
  let units := sourcePacketUnits definition.1 ruleInstance inputs origin
  let degree := 2 ^ arity
  let qCoefficient := QuantifierStorageBounds.chainCoefficient arity
  let mCoefficient := ImplicationStorageBounds.chainCoefficient premiseCap
  have positive : 1 ≤ units := by unfold units sourcePacketUnits; omega
  have degreePositive : 1 ≤ degree := by unfold degree; exact Nat.one_le_pow arity 2 (by decide)
  have axiomSize := ruleTheorem_payload_le member
  have argumentSize := instantiationArguments_payload ruleInstance.arguments
  have quantifierPacket : QuantifierStorageBounds.chainInputUnits (ruleTheorem rule)
      (instantiationArguments ruleInstance.arguments) origin ≤ units := by
    unfold QuantifierStorageBounds.chainInputUnits units sourcePacketUnits
    omega
  have argumentArity : (instantiationArguments ruleInstance.arguments).length ≤ arity := by
    simpa only [instantiationArguments, List.length_reverse, List.length_map] using argsBound
  obtain ⟨axiomOutput, axiomChecked, _, _, receiptsSame, _⟩ :=
    (emit_eq_some_iff _ _ _ _ _ _).mp axiomComputed
  have outputSame : axiomOutput = ruleTheorem rule :=
    Option.some.inj (axiomChecked.symm.trans (ruleTheorem_checked member))
  have sequentSize : OpenTheory.StorageSize.sequent (ruleSequent rule) ≤
      OpenTheory.StorageSize.theoremData (ruleTheorem rule) := by
    unfold OpenTheory.StorageSize.theoremData
    change _ ≤ 1 + _ + OpenTheory.StorageSize.sequent (ruleSequent rule)
    omega
  have axiomPayload : graphWeight StorageSize.receiptPayload afterAxiom.receipts.toList ≤ 4 * units := by
    rw [receiptsSame, outputSame]
    simp only [start, Array.toList_push, List.nil_append, graphWeight, receiptWeight,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil]
    simp only [StorageSize.receiptPayload, StorageSize.request]
    unfold units sourcePacketUnits
    omega
  have specPayload := QuantifierStorageBounds.emitSpecChain_payload_of_arity arity argumentArity specComputed
  have specSize := QuantifierStorageBounds.instantiateMany?_size_of_arity (ruleTheorem rule)
    (instantiationArguments ruleInstance.arguments) origin arity argumentArity instantiated
  have specPayloadBound : graphWeight StorageSize.receiptPayload afterSpec.receipts.toList ≤
      4 * units + qCoefficient * units ^ degree :=
    specPayload.trans (Nat.add_le_add axiomPayload
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left quantifierPacket degree)))
  have instanceSize : OpenTheory.StorageSize.theoremData instanceTheorem ≤ qCoefficient * units ^ degree :=
    specSize.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left quantifierPacket degree))
  have inputPower : units ≤ units ^ degree := by
    have powers := Nat.pow_le_pow_right positive degreePositive
    simpa only [pow_one] using powers
  have implicationPacket : ImplicationStorageBounds.chainInputUnits instanceTheorem inputs origin ≤
      (qCoefficient + 1) * units ^ degree := by
    unfold ImplicationStorageBounds.chainInputUnits
    have inputPart : 1 + (inputs.map OpenTheory.StorageSize.theoremData).sum + StorageSize.origin origin ≤ units := by
      unfold units sourcePacketUnits
      omega
    calc
      _ ≤ qCoefficient * units ^ degree + units := by omega
      _ ≤ (qCoefficient + 1) * units ^ degree := by nlinarith
  have implicationPayload := emitImplications_payload implicationsComputed
  have coefficientBound : ImplicationStorageBounds.chainCoefficient inputs.length ≤ mCoefficient :=
    ImplicationStorageBounds.chainCoefficient_mono inputsBound
  have implicationPayloadBound : graphWeight StorageSize.receiptPayload result.receipts.toList ≤
      graphWeight StorageSize.receiptPayload afterSpec.receipts.toList +
        mCoefficient * ((qCoefficient + 1) * units ^ degree) ^ 4 :=
    implicationPayload.trans (Nat.add_le_add_left
      (Nat.mul_le_mul coefficientBound (Nat.pow_le_pow_left implicationPacket 4)) _)
  have exponentBound : degree ≤ 4 * degree := by omega
  have lowerPower : units ^ degree ≤ units ^ (4 * degree) := Nat.pow_le_pow_right positive exponentBound
  have firstPower : units ≤ units ^ (4 * degree) := inputPower.trans lowerPower
  rw [← same]
  change graphWeight StorageSize.receiptPayload result.receipts.toList ≤ _
  calc
    _ ≤ 4 * units + qCoefficient * units ^ degree +
        mCoefficient * ((qCoefficient + 1) * units ^ degree) ^ 4 := by
      exact implicationPayloadBound.trans (Nat.add_le_add_right specPayloadBound _)
    _ ≤ 4 * units ^ (4 * degree) + qCoefficient * units ^ (4 * degree) +
        mCoefficient * (qCoefficient + 1) ^ 4 * units ^ (4 * degree) := by
      rw [mul_pow, ← pow_mul]
      have commute : degree * 4 = 4 * degree := Nat.mul_comm _ _
      rw [commute]
      rw [← Nat.mul_assoc]
      exact Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left 4 firstPower) (Nat.mul_le_mul_left qCoefficient lowerPower)) _
    _ = _ := by unfold ruleEmissionCoefficient qCoefficient mCoefficient degree; ring

end Mettapedia.Languages.HOLLight.InferenceStorageBounds
