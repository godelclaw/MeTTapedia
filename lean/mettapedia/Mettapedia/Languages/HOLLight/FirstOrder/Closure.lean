import Mettapedia.Languages.HOLLight.FirstOrder.Meaning
import Mathlib.Tactic.Ring

/-!
# Every rule of HOL Light's calculus preserves the meaning of its judgments

A rule built by `rule` with first-order schemas instantiates by plain substitution of its
arguments for its names (`rule_application`). Each group of rules is then checked against
`holMeaning`, the conclusion's meaning from the premises' meanings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules (checkSchema checkSchemas checkSchema_iff checkSchemas_iff)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
  (substSchema substSchemas bindingValue instantiateSchemaAt?_eq instantiateSchemasAt?_eq)
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)
open Mettapedia.Logic (Derives)

/-- **A rule's application is substitution of its arguments for its names.** -/
theorem rule_application {id : String} {names : List String} {premises : List Pattern} {conclusion : Pattern}
    (checked : checkSchemas names premises = true ∧ checkSchema names conclusion = true)
    {arguments instantiatedPremises : List Pattern} {instantiatedConclusion : Pattern}
    (valid : argumentsValidAt (rule id names premises conclusion).metavariables arguments = true)
    (premisesInstantiate : InstantiatesList (rule id names premises conclusion).metavariables arguments
      (rule id names premises conclusion).premises instantiatedPremises)
    (conclusionInstantiates : Instantiates (rule id names premises conclusion).metavariables arguments
      (rule id names premises conclusion).conclusion instantiatedConclusion) :
    arguments.length = names.length ∧
      instantiatedPremises = substSchemas (bindingValue (names.zip arguments)) premises ∧
      instantiatedConclusion = substSchema (bindingValue (names.zip arguments)) conclusion := by
  have arity : arguments.length = names.length := by
    have lengths := argumentsValidAt_length valid
    simpa [rule] using lengths.symm
  refine ⟨arity, ?_, ?_⟩
  · have computed := instantiateSchemasAt?_complete premisesInstantiate
    change instantiateSchemasAt? (names.map fun entry => (entry, 0)) arguments 0 premises = _ at computed
    rw [instantiateSchemasAt?_eq arity ((checkSchemas_iff _ _).mp checked.1)] at computed
    exact (Option.some.inj computed).symm
  · have computed := instantiateSchemaAt?_complete conclusionInstantiates
    change instantiateSchemaAt? (names.map fun entry => (entry, 0)) arguments 0 conclusion = _ at computed
    rw [instantiateSchemaAt?_eq arity ((checkSchema_iff _ _).mp checked.2)] at computed
    exact (Option.some.inj computed).symm

/-- The data a closure proof receives for one rule. -/
structure Applied (policy : AxiomPolicy) (rule : RuleSchema) (arguments premises : List Pattern)
    (conclusion : Pattern) : Prop where
  valid : argumentsValidAt rule.metavariables arguments = true
  premisesInstantiate : InstantiatesList rule.metavariables arguments rule.premises premises
  conclusionInstantiates : Instantiates rule.metavariables arguments rule.conclusion conclusion
  premisesHold : ∀ premise ∈ premises, holMeaning policy premise

theorem substSchema_functionOpP (values : String → Pattern) : substSchema values functionOpP = functionOpP :=
  substSchema_groundP values _

theorem substSchema_boolP (values : String → Pattern) : substSchema values boolP = boolP :=
  substSchema_groundP values _

theorem substSchema_equalityConstP (values : String → Pattern) :
    substSchema values equalityConstP = equalityConstP :=
  substSchema_groundP values _

/-- Compute an instantiated rule: substitution through the builders, lookups of the names,
and the meanings of the judgments. -/
macro "rule_simp" : tactic => `(tactic| simp only [substSchemas, substSchema, substSchema_treeP,
  substSchema_nodeP, substSchema_consP, substSchema_nilP, substSchema_numeralP, substSchema_fvar,
  substSchema_groundP, substSchema_listP, substSchema_functionOpP, substSchema_boolP, substSchema_equalityConstP,
  bindingValue, List.zip, List.zipWith, List.find?, List.map,
  List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, wfJ, mv,
  String.reduceAppend, String.reduceBEq, beq_self_eq_true, tyVarP, tyOpP, listNodeP, typeMapletP, termMapletP, pairP,
  constTermP, freeTermP, boundTermP, appTermP, absTermP, equalityTermP, functionTyP, sourceConstP,
  sourceVarP, sourceAppP, sourceAbsP, unaryZeroP, unarySuccP, bitP, charP, thmJ, neqJ, nthJ, typeOfJ,
  boundIndexJ, notBoundJ, toDBJ, notFreeJ, notFreeAllJ, closeJ, instantiateJ, unionJ, eraseJ, insertJ,
  sortJ, varTypeJ, tyActJ, tyActListJ, termTyActJ, termTyActListJ, admitTmJ, tmLookupJ, tmNoKeyJ,
  tmApplyJ, tmApplyListJ, ltJudgment, ltListJudgment, belowJudgment, holMeaning_treeBelow, holMeaning_treeLt, holMeaning_treeLtList, holMeaning_Neq, holMeaning_WfBit, holMeaning_WfPlane, holMeaning_WfChar, holMeaning_WfChars, holMeaning_WfString, holMeaning_WfStrings, holMeaning_WfName, holMeaning_WfNames, holMeaning_WfTy, holMeaning_WfTys, holMeaning_WfTypeOp, holMeaning_WfTypeOpProv, holMeaning_WfConst, holMeaning_WfConstProv, holMeaning_WfSource, holMeaning_WfTypeMaplets, holMeaning_Nth, holMeaning_TypeOf, holMeaning_BoundIndex, holMeaning_NotBound, holMeaning_ToDB, holMeaning_NotFree, holMeaning_NotFreeAll, holMeaning_Close, holMeaning_Instantiate, holMeaning_Union, holMeaning_Erase, holMeaning_Insert, holMeaning_Sort, holMeaning_VarType, holMeaning_TyAct, holMeaning_TyActList, holMeaning_TermTyAct, holMeaning_TermTyActList, holMeaning_AdmitTm, holMeaning_TmLookup, holMeaning_TmNoKey, holMeaning_TmApply, holMeaning_TmApplyList, holMeaning_Thm] at *)

/-! ## Well-formed strings and names -/

theorem textRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ textRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [textRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [], _ => rule_simp; exact ⟨[], rfl⟩
  · match arguments, arity with
    | [c, cs], _ =>
        rule_simp
        obtain ⟨⟨character, rfl⟩, ⟨characters, rfl⟩⟩ := premisesHold
        exact ⟨character :: characters, rfl⟩
  · match arguments, arity with
    | [cs], _ =>
        rule_simp
        obtain ⟨characters, rfl⟩ := premisesHold
        refine ⟨String.ofList characters, ?_⟩
        simp only [encodeString, groundP_node, treeP, String.toList_ofList, charsP, List.map_map]
        rfl
  · match arguments, arity with
    | [], _ => rule_simp; exact ⟨[], rfl⟩
  · match arguments, arity with
    | [t, ts], _ =>
        rule_simp
        obtain ⟨⟨text, rfl⟩, ⟨texts, rfl⟩⟩ := premisesHold
        exact ⟨text :: texts, rfl⟩
  · match arguments, arity with
    | [ss, t], _ =>
        rule_simp
        obtain ⟨⟨texts, rfl⟩, ⟨component, rfl⟩⟩ := premisesHold
        refine ⟨⟨texts, component⟩, ?_⟩
        simp only [encodeName, groundP_node, treeP, stringsP, List.map_map, List.map_cons, List.map_nil]
        rfl
  · match arguments, arity with
    | [], _ => rule_simp; exact ⟨[], rfl⟩
  · match arguments, arity with
    | [x, xs], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨names, rfl⟩⟩ := premisesHold
        exact ⟨name :: names, rfl⟩

/-! ## Well-formed types, constants and source terms -/

theorem syntaxRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ syntaxRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [syntaxRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [x], _ =>
        rule_simp
        obtain ⟨name, rfl⟩ := premisesHold
        exact ⟨.var name, rfl⟩
  · match arguments, arity with
    | [o, as], _ =>
        rule_simp
        obtain ⟨⟨operator, rfl⟩, ⟨types, rfl⟩⟩ := premisesHold
        exact ⟨.op operator types, by simp only [encodeTy, groundP_node, List.map_cons, List.map_nil, tysP, treeP]⟩
  · match arguments, arity with
    | [], _ => rule_simp; exact ⟨[], rfl⟩
  · match arguments, arity with
    | [a, as], _ =>
        rule_simp
        obtain ⟨⟨type, rfl⟩, ⟨types, rfl⟩⟩ := premisesHold
        exact ⟨type :: types, rfl⟩
  · match arguments, arity with
    | [x, p], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨provenance, rfl⟩⟩ := premisesHold
        exact ⟨.mk name provenance, rfl⟩
  · match arguments, arity with
    | [], _ => rule_simp; exact ⟨.undefined, rfl⟩
  · match arguments, arity with
    | [source, xs], _ =>
        rule_simp
        obtain ⟨⟨predicate, rfl⟩, ⟨names, rfl⟩⟩ := premisesHold
        exact ⟨.defined predicate names, by
          simp only [encodeTypeOpProvenance, groundP_node, List.map_cons, List.map_nil, List.map_map, namesP, treeP]
          rfl⟩
  · match arguments, arity with
    | [x, p], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨provenance, rfl⟩⟩ := premisesHold
        exact ⟨.mk name provenance, rfl⟩
  · match arguments, arity with
    | [], _ => rule_simp; exact ⟨.undefined, rfl⟩
  · match arguments, arity with
    | [source], _ =>
        rule_simp
        obtain ⟨definition, rfl⟩ := premisesHold
        exact ⟨.defined definition, rfl⟩
  · match arguments, arity with
    | [o], _ =>
        rule_simp
        obtain ⟨operator, rfl⟩ := premisesHold
        exact ⟨.abstraction operator, rfl⟩
  · match arguments, arity with
    | [o], _ =>
        rule_simp
        obtain ⟨operator, rfl⟩ := premisesHold
        exact ⟨.representation operator, rfl⟩
  · match arguments, arity with
    | [c, a], _ =>
        rule_simp
        obtain ⟨⟨constant, rfl⟩, ⟨type, rfl⟩⟩ := premisesHold
        exact ⟨.const constant type, rfl⟩
  · match arguments, arity with
    | [x, a], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨type, rfl⟩⟩ := premisesHold
        exact ⟨.var name type, rfl⟩
  · match arguments, arity with
    | [f, e], _ =>
        rule_simp
        obtain ⟨⟨function, rfl⟩, ⟨argument, rfl⟩⟩ := premisesHold
        exact ⟨.app function argument, rfl⟩
  · match arguments, arity with
    | [x, a, t], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨type, rfl⟩, ⟨body, rfl⟩⟩ := premisesHold
        exact ⟨.abs name type body, rfl⟩
  · match arguments, arity with
    | [], _ => rule_simp; exact ⟨[], rfl⟩
  · match arguments, arity with
    | [rr, k, rest], _ =>
        rule_simp
        obtain ⟨⟨replacement, rfl⟩, ⟨key, rfl⟩, ⟨entries, rfl⟩⟩ := premisesHold
        exact ⟨(replacement, key) :: entries, rfl⟩

/-! ## Bits, planes and characters -/

theorem valueDown_lt : ∀ digits : List Nat, (∀ digit ∈ digits, digit < 2) →
    valueDown digits < 2 ^ digits.length
  | [], _ => by simp [valueDown]
  | digit :: rest, binary => by
      have digitSmall := binary digit (by simp)
      have restSmall := valueDown_lt rest (fun other member => binary other (by simp [member]))
      simp only [valueDown, List.length_cons, Nat.pow_succ]
      have : digit ≤ 1 := by omega
      calc digit * 2 ^ rest.length + valueDown rest < digit * 2 ^ rest.length + 2 ^ rest.length := by omega
        _ ≤ 1 * 2 ^ rest.length + 2 ^ rest.length := by
            have := Nat.mul_le_mul_right (2 ^ rest.length) this
            omega
        _ = 2 ^ rest.length * 2 := by ring

/-- The bits of `high · 2^k + value` below position `k` are the digits of `value`. -/
theorem bitsDown_digits : ∀ (digits : List Nat) (high : Nat), (∀ digit ∈ digits, digit < 2) →
    bitsDown (high * 2 ^ digits.length + valueDown digits) digits.length = digits
  | [], _, _ => rfl
  | digit :: rest, high, binary => by
      have digitSmall := binary digit (by simp)
      have restBinary : ∀ other ∈ rest, other < 2 := fun other member => binary other (by simp [member])
      have restSmall := valueDown_lt rest restBinary
      have regroup : high * 2 ^ (rest.length + 1) + (digit * 2 ^ rest.length + valueDown rest) =
          (2 * high + digit) * 2 ^ rest.length + valueDown rest := by
        rw [Nat.pow_succ]; ring
      simp only [List.length_cons, valueDown, bitsDown]
      rw [regroup, bitsDown_digits rest (2 * high + digit) restBinary]
      congr 1
      have divided : ((2 * high + digit) * 2 ^ rest.length + valueDown rest) / 2 ^ rest.length =
          2 * high + digit := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt restSmall, Nat.zero_add]
      rw [divided]
      omega

theorem toNat_ofNatAux (number : Nat) (valid : number.isValidChar) :
    (Char.ofNatAux number valid).toNat = number := by
  simp [Char.ofNatAux, Char.toNat, UInt32.toNat, BitVec.toNat_ofNatLT]

/-- **A character pattern with a valid value is the encoding of that character.** -/
theorem charP_digits (plane : Nat) (digits : List Nat) (length : digits.length = 16)
    (binary : ∀ digit ∈ digits, digit < 2) (valid : (plane * 65536 + valueDown digits).isValidChar) :
    charP (groundP (encodeUnary plane)) (digits.map bitP) =
      groundP (encodeChar (Char.ofNatAux (plane * 65536 + valueDown digits) valid)) := by
  have small := valueDown_lt digits binary
  rw [length] at small
  have small' : valueDown digits < 65536 := by simpa using small
  have bits := bitsDown_digits digits plane binary
  rw [length] at bits
  have planeEq : (plane * 65536 + valueDown digits) / 65536 = plane := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt small', Nat.zero_add]
  simp only [encodeChar, toNat_ofNatAux, planeEq, groundP_node, charP, treeP, List.map_cons, List.map_map]
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, bits]
  rfl

/-! ## The character rules, written out -/

theorem checkSchema_numeralP (names : List String) : ∀ count, checkSchema names (numeralP count) = true
  | 0 => by simp [numeralP, zeroP, checkSchema, checkSchemas]
  | count + 1 => by simp [numeralP, succP, checkSchema, checkSchemas, checkSchema_numeralP names count]

mutual
  theorem checkSchema_toPattern (names : List String) : ∀ tree : LabeledTree, checkSchema names tree.toPattern = true
    | .node label children => by
        simp [LabeledTree.toPattern, nodeP, checkSchema, checkSchemas, checkSchema_numeralP,
          checkSchema_toPatternList names children]

  theorem checkSchema_toPatternList (names : List String) : ∀ trees : List LabeledTree,
      checkSchema names (LabeledTree.toPatternList trees) = true
    | [] => by simp [LabeledTree.toPatternList, nilP, checkSchema, checkSchemas]
    | tree :: rest => by
        simp [LabeledTree.toPatternList, consP, checkSchema, checkSchemas, checkSchema_toPattern names tree,
          checkSchema_toPatternList names rest]
end

theorem bitNames_eq : bitNames = ["b15", "b14", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"] := rfl

theorem planeZeroRule_15_eq : planeZeroRule 15 0 =
    rule "hol.wf-char-zero-15" ["b14", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"]
      (["b14", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].map fun name => wfJ "Bit" (mv name))
      (wfJ "Char" (charP (groundP (encodeUnary 0)) [bitP 0, mv "b14", mv "b13", mv "b12", mv "b11", mv "b10", mv "b9", mv "b8", mv "b7", mv "b6", mv "b5", mv "b4", mv "b3", mv "b2", mv "b1", mv "b0"])) := rfl

theorem planeZeroRule_14_eq : planeZeroRule 14 0 =
    rule "hol.wf-char-zero-14" ["b15", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"]
      (["b15", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].map fun name => wfJ "Bit" (mv name))
      (wfJ "Char" (charP (groundP (encodeUnary 0)) [mv "b15", bitP 0, mv "b13", mv "b12", mv "b11", mv "b10", mv "b9", mv "b8", mv "b7", mv "b6", mv "b5", mv "b4", mv "b3", mv "b2", mv "b1", mv "b0"])) := rfl

theorem planeZeroRule_13_eq : planeZeroRule 13 1 =
    rule "hol.wf-char-zero-13" ["b15", "b14", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"]
      (["b15", "b14", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].map fun name => wfJ "Bit" (mv name))
      (wfJ "Char" (charP (groundP (encodeUnary 0)) [mv "b15", mv "b14", bitP 1, mv "b12", mv "b11", mv "b10", mv "b9", mv "b8", mv "b7", mv "b6", mv "b5", mv "b4", mv "b3", mv "b2", mv "b1", mv "b0"])) := rfl

theorem planeZeroRule_12_eq : planeZeroRule 12 0 =
    rule "hol.wf-char-zero-12" ["b15", "b14", "b13", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"]
      (["b15", "b14", "b13", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].map fun name => wfJ "Bit" (mv name))
      (wfJ "Char" (charP (groundP (encodeUnary 0)) [mv "b15", mv "b14", mv "b13", bitP 0, mv "b11", mv "b10", mv "b9", mv "b8", mv "b7", mv "b6", mv "b5", mv "b4", mv "b3", mv "b2", mv "b1", mv "b0"])) := rfl

theorem planeZeroRule_11_eq : planeZeroRule 11 0 =
    rule "hol.wf-char-zero-11" ["b15", "b14", "b13", "b12", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"]
      (["b15", "b14", "b13", "b12", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].map fun name => wfJ "Bit" (mv name))
      (wfJ "Char" (charP (groundP (encodeUnary 0)) [mv "b15", mv "b14", mv "b13", mv "b12", bitP 0, mv "b10", mv "b9", mv "b8", mv "b7", mv "b6", mv "b5", mv "b4", mv "b3", mv "b2", mv "b1", mv "b0"])) := rfl

theorem bit_digit {pattern : Pattern} (bit : pattern = bitP 0 ∨ pattern = bitP 1) :
    ∃ digit, digit < 2 ∧ pattern = bitP digit := by
  rcases bit with rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩

theorem bitPlaneRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ bitPlaneRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [bitPlaneRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at member
  rcases member with (rfl | rfl) | ⟨plane, bounded, rfl⟩
  · obtain ⟨arity, -, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
    match arguments, arity with
    | [], _ => exact Or.inl rfl
  · obtain ⟨arity, -, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
    match arguments, arity with
    | [], _ => exact Or.inr rfl
  · obtain ⟨arity, -, rfl⟩ := rule_application
      ⟨by simp [checkSchemas], by simp [wfJ, checkSchema, checkSchemas, groundP, checkSchema_toPattern]⟩
      valid premisesInstantiate conclusionInstantiates
    match arguments, arity with
    | [], _ =>
        clear valid premisesInstantiate conclusionInstantiates
        rule_simp
        exact ⟨plane + 1, by omega, by omega, rfl⟩

set_option maxHeartbeats 1000000 in
theorem charPlane_closed (policy : AxiomPolicy) {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy (charRules[0]'(by decide)) arguments premises conclusion) :
    holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [charRules, List.getElem_cons_zero, bitNames_eq, List.map_cons, List.map_nil] at valid premisesInstantiate conclusionInstantiates
  obtain ⟨-, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
  clear valid premisesInstantiate conclusionInstantiates
  generalize bindingValue (["p", "b15", "b14", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].zip arguments) = values at premisesHold ⊢
  rule_simp
  obtain ⟨⟨plane, low, high, hp⟩, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0⟩ := premisesHold
  obtain ⟨d15, s15, e15⟩ := bit_digit h15
  obtain ⟨d14, s14, e14⟩ := bit_digit h14
  obtain ⟨d13, s13, e13⟩ := bit_digit h13
  obtain ⟨d12, s12, e12⟩ := bit_digit h12
  obtain ⟨d11, s11, e11⟩ := bit_digit h11
  obtain ⟨d10, s10, e10⟩ := bit_digit h10
  obtain ⟨d9, s9, e9⟩ := bit_digit h9
  obtain ⟨d8, s8, e8⟩ := bit_digit h8
  obtain ⟨d7, s7, e7⟩ := bit_digit h7
  obtain ⟨d6, s6, e6⟩ := bit_digit h6
  obtain ⟨d5, s5, e5⟩ := bit_digit h5
  obtain ⟨d4, s4, e4⟩ := bit_digit h4
  obtain ⟨d3, s3, e3⟩ := bit_digit h3
  obtain ⟨d2, s2, e2⟩ := bit_digit h2
  obtain ⟨d1, s1, e1⟩ := bit_digit h1
  obtain ⟨d0, s0, e0⟩ := bit_digit h0
  rw [hp, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  clear h15 h14 h13 h12 h11 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 hp e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  have small : valueDown [d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] < 65536 := by
    have bounded := valueDown_lt [d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] (by simp; omega)
    simpa using bounded
  have valid : (plane * 65536 + valueDown [d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0]).isValidChar := Or.inr ⟨by omega, by omega⟩
  have encoded := charP_digits plane [d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] rfl (by simp; omega) valid
  exact ⟨_, encoded⟩

set_option maxHeartbeats 1000000 in
theorem charZero15_closed (policy : AxiomPolicy) {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy (planeZeroRule 15 0) arguments premises conclusion) :
    holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  rw [planeZeroRule_15_eq] at valid premisesInstantiate conclusionInstantiates
  simp only [List.map_cons, List.map_nil] at valid premisesInstantiate conclusionInstantiates
  obtain ⟨-, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
  clear valid premisesInstantiate conclusionInstantiates
  generalize bindingValue (["b14", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].zip arguments) = values at premisesHold ⊢
  rule_simp
  obtain ⟨h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0⟩ := premisesHold
  obtain ⟨d14, s14, e14⟩ := bit_digit h14
  obtain ⟨d13, s13, e13⟩ := bit_digit h13
  obtain ⟨d12, s12, e12⟩ := bit_digit h12
  obtain ⟨d11, s11, e11⟩ := bit_digit h11
  obtain ⟨d10, s10, e10⟩ := bit_digit h10
  obtain ⟨d9, s9, e9⟩ := bit_digit h9
  obtain ⟨d8, s8, e8⟩ := bit_digit h8
  obtain ⟨d7, s7, e7⟩ := bit_digit h7
  obtain ⟨d6, s6, e6⟩ := bit_digit h6
  obtain ⟨d5, s5, e5⟩ := bit_digit h5
  obtain ⟨d4, s4, e4⟩ := bit_digit h4
  obtain ⟨d3, s3, e3⟩ := bit_digit h3
  obtain ⟨d2, s2, e2⟩ := bit_digit h2
  obtain ⟨d1, s1, e1⟩ := bit_digit h1
  obtain ⟨d0, s0, e0⟩ := bit_digit h0
  rw [e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  clear h14 h13 h12 h11 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  have valid : (0 * 65536 + valueDown [0, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0]).isValidChar := by
    simp only [valueDown, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow, Nat.isValidChar]
    omega
  have encoded := charP_digits 0 [0, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] rfl (by simp; omega) valid
  exact ⟨_, encoded⟩

set_option maxHeartbeats 1000000 in
theorem charZero14_closed (policy : AxiomPolicy) {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy (planeZeroRule 14 0) arguments premises conclusion) :
    holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  rw [planeZeroRule_14_eq] at valid premisesInstantiate conclusionInstantiates
  simp only [List.map_cons, List.map_nil] at valid premisesInstantiate conclusionInstantiates
  obtain ⟨-, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
  clear valid premisesInstantiate conclusionInstantiates
  generalize bindingValue (["b15", "b13", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].zip arguments) = values at premisesHold ⊢
  rule_simp
  obtain ⟨h15, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0⟩ := premisesHold
  obtain ⟨d15, s15, e15⟩ := bit_digit h15
  obtain ⟨d13, s13, e13⟩ := bit_digit h13
  obtain ⟨d12, s12, e12⟩ := bit_digit h12
  obtain ⟨d11, s11, e11⟩ := bit_digit h11
  obtain ⟨d10, s10, e10⟩ := bit_digit h10
  obtain ⟨d9, s9, e9⟩ := bit_digit h9
  obtain ⟨d8, s8, e8⟩ := bit_digit h8
  obtain ⟨d7, s7, e7⟩ := bit_digit h7
  obtain ⟨d6, s6, e6⟩ := bit_digit h6
  obtain ⟨d5, s5, e5⟩ := bit_digit h5
  obtain ⟨d4, s4, e4⟩ := bit_digit h4
  obtain ⟨d3, s3, e3⟩ := bit_digit h3
  obtain ⟨d2, s2, e2⟩ := bit_digit h2
  obtain ⟨d1, s1, e1⟩ := bit_digit h1
  obtain ⟨d0, s0, e0⟩ := bit_digit h0
  rw [e15, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  clear h15 h13 h12 h11 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 e15 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  have valid : (0 * 65536 + valueDown [d15, 0, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0]).isValidChar := by
    simp only [valueDown, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow, Nat.isValidChar]
    omega
  have encoded := charP_digits 0 [d15, 0, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] rfl (by simp; omega) valid
  exact ⟨_, encoded⟩

set_option maxHeartbeats 1000000 in
theorem charZero13_closed (policy : AxiomPolicy) {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy (planeZeroRule 13 1) arguments premises conclusion) :
    holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  rw [planeZeroRule_13_eq] at valid premisesInstantiate conclusionInstantiates
  simp only [List.map_cons, List.map_nil] at valid premisesInstantiate conclusionInstantiates
  obtain ⟨-, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
  clear valid premisesInstantiate conclusionInstantiates
  generalize bindingValue (["b15", "b14", "b12", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].zip arguments) = values at premisesHold ⊢
  rule_simp
  obtain ⟨h15, h14, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0⟩ := premisesHold
  obtain ⟨d15, s15, e15⟩ := bit_digit h15
  obtain ⟨d14, s14, e14⟩ := bit_digit h14
  obtain ⟨d12, s12, e12⟩ := bit_digit h12
  obtain ⟨d11, s11, e11⟩ := bit_digit h11
  obtain ⟨d10, s10, e10⟩ := bit_digit h10
  obtain ⟨d9, s9, e9⟩ := bit_digit h9
  obtain ⟨d8, s8, e8⟩ := bit_digit h8
  obtain ⟨d7, s7, e7⟩ := bit_digit h7
  obtain ⟨d6, s6, e6⟩ := bit_digit h6
  obtain ⟨d5, s5, e5⟩ := bit_digit h5
  obtain ⟨d4, s4, e4⟩ := bit_digit h4
  obtain ⟨d3, s3, e3⟩ := bit_digit h3
  obtain ⟨d2, s2, e2⟩ := bit_digit h2
  obtain ⟨d1, s1, e1⟩ := bit_digit h1
  obtain ⟨d0, s0, e0⟩ := bit_digit h0
  rw [e15, e14, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  clear h15 h14 h12 h11 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 e15 e14 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  have valid : (0 * 65536 + valueDown [d15, d14, 1, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0]).isValidChar := by
    simp only [valueDown, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow, Nat.isValidChar]
    omega
  have encoded := charP_digits 0 [d15, d14, 1, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] rfl (by simp; omega) valid
  exact ⟨_, encoded⟩

set_option maxHeartbeats 1000000 in
theorem charZero12_closed (policy : AxiomPolicy) {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy (planeZeroRule 12 0) arguments premises conclusion) :
    holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  rw [planeZeroRule_12_eq] at valid premisesInstantiate conclusionInstantiates
  simp only [List.map_cons, List.map_nil] at valid premisesInstantiate conclusionInstantiates
  obtain ⟨-, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
  clear valid premisesInstantiate conclusionInstantiates
  generalize bindingValue (["b15", "b14", "b13", "b11", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].zip arguments) = values at premisesHold ⊢
  rule_simp
  obtain ⟨h15, h14, h13, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0⟩ := premisesHold
  obtain ⟨d15, s15, e15⟩ := bit_digit h15
  obtain ⟨d14, s14, e14⟩ := bit_digit h14
  obtain ⟨d13, s13, e13⟩ := bit_digit h13
  obtain ⟨d11, s11, e11⟩ := bit_digit h11
  obtain ⟨d10, s10, e10⟩ := bit_digit h10
  obtain ⟨d9, s9, e9⟩ := bit_digit h9
  obtain ⟨d8, s8, e8⟩ := bit_digit h8
  obtain ⟨d7, s7, e7⟩ := bit_digit h7
  obtain ⟨d6, s6, e6⟩ := bit_digit h6
  obtain ⟨d5, s5, e5⟩ := bit_digit h5
  obtain ⟨d4, s4, e4⟩ := bit_digit h4
  obtain ⟨d3, s3, e3⟩ := bit_digit h3
  obtain ⟨d2, s2, e2⟩ := bit_digit h2
  obtain ⟨d1, s1, e1⟩ := bit_digit h1
  obtain ⟨d0, s0, e0⟩ := bit_digit h0
  rw [e15, e14, e13, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  clear h15 h14 h13 h11 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 e15 e14 e13 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  have valid : (0 * 65536 + valueDown [d15, d14, d13, 0, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0]).isValidChar := by
    simp only [valueDown, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow, Nat.isValidChar]
    omega
  have encoded := charP_digits 0 [d15, d14, d13, 0, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] rfl (by simp; omega) valid
  exact ⟨_, encoded⟩

set_option maxHeartbeats 1000000 in
theorem charZero11_closed (policy : AxiomPolicy) {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy (planeZeroRule 11 0) arguments premises conclusion) :
    holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  rw [planeZeroRule_11_eq] at valid premisesInstantiate conclusionInstantiates
  simp only [List.map_cons, List.map_nil] at valid premisesInstantiate conclusionInstantiates
  obtain ⟨-, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates
  clear valid premisesInstantiate conclusionInstantiates
  generalize bindingValue (["b15", "b14", "b13", "b12", "b10", "b9", "b8", "b7", "b6", "b5", "b4", "b3", "b2", "b1", "b0"].zip arguments) = values at premisesHold ⊢
  rule_simp
  obtain ⟨h15, h14, h13, h12, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0⟩ := premisesHold
  obtain ⟨d15, s15, e15⟩ := bit_digit h15
  obtain ⟨d14, s14, e14⟩ := bit_digit h14
  obtain ⟨d13, s13, e13⟩ := bit_digit h13
  obtain ⟨d12, s12, e12⟩ := bit_digit h12
  obtain ⟨d10, s10, e10⟩ := bit_digit h10
  obtain ⟨d9, s9, e9⟩ := bit_digit h9
  obtain ⟨d8, s8, e8⟩ := bit_digit h8
  obtain ⟨d7, s7, e7⟩ := bit_digit h7
  obtain ⟨d6, s6, e6⟩ := bit_digit h6
  obtain ⟨d5, s5, e5⟩ := bit_digit h5
  obtain ⟨d4, s4, e4⟩ := bit_digit h4
  obtain ⟨d3, s3, e3⟩ := bit_digit h3
  obtain ⟨d2, s2, e2⟩ := bit_digit h2
  obtain ⟨d1, s1, e1⟩ := bit_digit h1
  obtain ⟨d0, s0, e0⟩ := bit_digit h0
  rw [e15, e14, e13, e12, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  clear h15 h14 h13 h12 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 e15 e14 e13 e12 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  have valid : (0 * 65536 + valueDown [d15, d14, d13, d12, 0, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0]).isValidChar := by
    simp only [valueDown, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow, Nat.isValidChar]
    omega
  have encoded := charP_digits 0 [d15, d14, d13, d12, 0, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0] rfl (by simp; omega) valid
  exact ⟨_, encoded⟩

theorem charRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ charRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  simp only [charRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact charPlane_closed policy applied
  · exact charZero15_closed policy applied
  · exact charZero14_closed policy applied
  · exact charZero13_closed policy applied
  · exact charZero12_closed policy applied
  · exact charZero11_closed policy applied

theorem wellFormedRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ wellFormedRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  simp only [wellFormedRules, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact bitPlaneRules_closed policy member applied
  · exact charRules_closed policy member applied
  · exact textRules_closed policy member applied
  · exact syntaxRules_closed policy member applied

/-! ## Disequality, context lookup and type inference -/

theorem neqRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ neqRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [neqRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [x, y], _ =>
        rule_simp
        exact PLt.ne premisesHold
  · match arguments, arity with
    | [x, y], _ =>
        rule_simp
        exact (PLt.ne premisesHold).symm

theorem contextP_eq_consP {context : List Ty} {head tail : Pattern} (same : contextP context = consP head tail) :
    ∃ type rest, context = type :: rest ∧ head = groundP (encodeTy type) ∧ tail = contextP rest := by
  cases context with
  | nil => simp [contextP, listP, nilP, consP] at same
  | cons type rest =>
      simp only [contextP, listP, List.map_cons, consP, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨type, rest, rfl, same.1.symm, same.2.symm⟩

theorem nthRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ nthRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [nthRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [t, ts], _ =>
        rule_simp
        intro context same
        obtain ⟨type, rest, rfl, rfl, rfl⟩ := contextP_eq_consP same.symm
        exact ⟨0, type, rfl, rfl, rfl⟩
  · match arguments, arity with
    | [t, ts, n, u], _ =>
        rule_simp
        intro context same
        obtain ⟨type, rest, rfl, rfl, rfl⟩ := contextP_eq_consP same.symm
        obtain ⟨position, found, rfl, lookup, rfl⟩ := premisesHold rest rfl
        exact ⟨position + 1, found, rfl, lookup, rfl⟩

theorem groundP_encodeTy_function (domain codomain : Ty) :
    groundP (encodeTy (Ty.function domain codomain)) =
      functionTyP (groundP (encodeTy domain)) (groundP (encodeTy codomain)) := rfl

theorem typeRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ typeRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [typeRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [c, a, g], _ =>
        rule_simp
        obtain ⟨⟨constant, rfl⟩, ⟨type, rfl⟩⟩ := premisesHold
        intro types _
        exact ⟨.const constant type, type, rfl, rfl, by simp [DBTerm.inferType]⟩
  · match arguments, arity with
    | [x, a, g], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨type, rfl⟩⟩ := premisesHold
        intro types _
        exact ⟨.free ⟨name, type⟩, type, rfl, rfl, by simp [DBTerm.inferType]⟩
  · match arguments, arity with
    | [i, a, g], _ =>
        rule_simp
        intro types same
        obtain ⟨position, type, rfl, lookup, rfl⟩ := premisesHold types same
        exact ⟨.bound position, type, rfl, rfl, by simpa [DBTerm.inferType] using lookup⟩
  · match arguments, arity with
    | [f, e, a, b, g], _ =>
        rule_simp
        obtain ⟨functionTyped, argumentTyped⟩ := premisesHold
        intro types same
        obtain ⟨functionTerm, functionType, rfl, functionTypeSame, functionInferred⟩ := functionTyped types same
        obtain ⟨argumentTerm, argumentType, rfl, rfl, argumentInferred⟩ := argumentTyped types same
        obtain ⟨domain, codomain, rfl, domainSame, rfl⟩ := encodeTy_eq_function functionTypeSame.symm
        have domains : domain = argumentType :=
          encodeTy_injective _ _ (LabeledTree.toPattern_injective _ _ domainSame.symm)
        subst domains
        exact ⟨.app functionTerm argumentTerm, codomain, rfl, rfl, by
          simp [DBTerm.inferType, functionInferred, argumentInferred, Ty.destFunction?_function]⟩
  · match arguments, arity with
    | [a, t, b, g], _ =>
        rule_simp
        obtain ⟨⟨domain, rfl⟩, bodyTyped⟩ := premisesHold
        intro types same
        obtain ⟨body, bodyType, rfl, rfl, bodyInferred⟩ := bodyTyped (domain :: types) (by rw [same]; rfl)
        exact ⟨.abs domain body, Ty.function domain bodyType, rfl, rfl, by
          simp [DBTerm.inferType, bodyInferred]⟩

/-! ## Binders, conversion to de Bruijn form, free variables, closing and instantiation -/

theorem freeVarP_injective : Function.Injective freeVarP := by
  intro first second same
  have terms := encodeTerm_injective (LabeledTree.toPattern_injective _ _ same)
  simpa using terms

theorem freeTermP_eq_freeVarP (name : Name) (typeValue : Ty) :
    freeTermP (groundP (encodeName name)) (groundP (encodeTy typeValue)) = freeVarP ⟨name, typeValue⟩ := rfl

theorem bindersP_eq_consP {binders : List SourceVar} {head tail : Pattern}
    (same : consP head tail = bindersP binders) :
    ∃ sourceVar rest, binders = sourceVar :: rest ∧ head = freeVarP sourceVar ∧ tail = bindersP rest := by
  cases binders with
  | nil => simp [bindersP, listP, nilP, consP] at same
  | cons sourceVar rest =>
      simp only [bindersP, listP, List.map_cons, consP, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨sourceVar, rest, rfl, same.1, same.2⟩

theorem bindersP_eq_nilP {binders : List SourceVar} (same : nilP = bindersP binders) : binders = [] := by
  cases binders with
  | nil => rfl
  | cons _ _ => simp [bindersP, listP, nilP, consP] at same

theorem termsP_eq_consP {terms : List DBTerm} {head tail : Pattern} (same : consP head tail = termsP terms) :
    ∃ term rest, terms = term :: rest ∧ head = groundP (encodeTerm term) ∧ tail = termsP rest := by
  cases terms with
  | nil => simp [termsP, listP, nilP, consP] at same
  | cons term rest =>
      simp only [termsP, listP, List.map_cons, consP, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨term, rest, rfl, same.1, same.2⟩

theorem termsP_eq_nilP {terms : List DBTerm} (same : nilP = termsP terms) : terms = [] := by
  cases terms with
  | nil => rfl
  | cons _ _ => simp [termsP, listP, nilP, consP] at same

theorem unarySuccP_encode (count : Nat) :
    unarySuccP (groundP (encodeUnary count)) = groundP (encodeUnary (count + 1)) := rfl

theorem unaryZeroP_encode : unaryZeroP = groundP (encodeUnary 0) := rfl

theorem binderRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ binderRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [binderRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [v, vs], _ =>
        rule_simp
        intro binders sourceVar same needle
        obtain ⟨binder, rest, rfl, rfl, rfl⟩ := bindersP_eq_consP same
        have binderEq := freeVarP_injective needle.symm
        subst binderEq
        exact ⟨0, rfl, by simp [boundIndex]⟩
  · match arguments, arity with
    | [w, vs, v, i], _ =>
        rule_simp
        obtain ⟨different, found⟩ := premisesHold
        intro binders sourceVar same needle
        obtain ⟨binder, rest, rfl, rfl, rfl⟩ := bindersP_eq_consP same
        obtain ⟨position, rfl, lookup⟩ := found rest sourceVar rfl needle
        have distinct : sourceVar ≠ binder := fun equal => different (by rw [needle, equal])
        refine ⟨position + 1, rfl, ?_⟩
        simp [boundIndex, lookup, distinct]
  · match arguments, arity with
    | [v], _ =>
        rule_simp
        intro binders sourceVar same _
        rw [bindersP_eq_nilP same]
        rfl
  · match arguments, arity with
    | [w, vs, v], _ =>
        rule_simp
        obtain ⟨different, absent⟩ := premisesHold
        intro binders sourceVar same needle
        obtain ⟨binder, rest, rfl, rfl, rfl⟩ := bindersP_eq_consP same
        have distinct : sourceVar ≠ binder := fun equal => different (by rw [needle, equal])
        simp [boundIndex, absent rest sourceVar rfl needle, distinct]

theorem toDBRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ toDBRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [toDBRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [bs, c, a], _ =>
        rule_simp
        obtain ⟨⟨constant, rfl⟩, ⟨type, rfl⟩⟩ := premisesHold
        intro binders _
        exact ⟨.const constant type, .const constant type, rfl, rfl, by simp [SourceTerm.toDB]⟩
  · match arguments, arity with
    | [bs, x, a, i], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨type, rfl⟩, found⟩ := premisesHold
        intro binders same
        obtain ⟨position, rfl, lookup⟩ := found binders ⟨name, type⟩ same rfl
        exact ⟨.var name type, .bound position, rfl, rfl, by simp [SourceTerm.toDB, lookup]⟩
  · match arguments, arity with
    | [bs, x, a], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨type, rfl⟩, absent⟩ := premisesHold
        intro binders same
        exact ⟨.var name type, .free ⟨name, type⟩, rfl, rfl, by
          simp [SourceTerm.toDB, absent binders ⟨name, type⟩ same rfl]⟩
  · match arguments, arity with
    | [bs, f, e, f2, e2], _ =>
        rule_simp
        obtain ⟨functionConverted, argumentConverted⟩ := premisesHold
        intro binders same
        obtain ⟨functionSource, functionTerm, rfl, rfl, functionEq⟩ := functionConverted binders same
        obtain ⟨argumentSource, argumentTerm, rfl, rfl, argumentEq⟩ := argumentConverted binders same
        exact ⟨.app functionSource argumentSource, .app functionTerm argumentTerm, rfl, rfl, by
          simp [SourceTerm.toDB, functionEq, argumentEq]⟩
  · match arguments, arity with
    | [bs, x, a, t, t2], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, ⟨type, rfl⟩, bodyConverted⟩ := premisesHold
        intro binders same
        obtain ⟨bodySource, bodyTerm, rfl, rfl, bodyEq⟩ :=
          bodyConverted (⟨name, type⟩ :: binders) (by rw [same]; rfl)
        exact ⟨.abs name type bodySource, .abs type bodyTerm, rfl, rfl, by simp [SourceTerm.toDB, bodyEq]⟩

theorem notFreeRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ notFreeRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [notFreeRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [v, c, a], _ =>
        rule_simp
        intro sourceVar termValue _ termEq
        obtain ⟨constant, type, rfl, rfl, rfl⟩ := encodeTerm_eq_const termEq.symm
        simp only [DBTerm.hasFree]
  · match arguments, arity with
    | [v, x, a], _ =>
        rule_simp
        intro sourceVar termValue needle termEq
        obtain ⟨other, rfl, rfl, rfl⟩ := encodeTerm_eq_free termEq.symm
        cases same : sourceVarSame sourceVar other
        · simp only [DBTerm.hasFree, same]
        · have equal := (sourceVarSame_eq_true_iff _ _).mp same
          subst equal
          exact (premisesHold (needle.trans rfl)).elim
  · match arguments, arity with
    | [v, i], _ =>
        rule_simp
        intro sourceVar termValue _ termEq
        obtain ⟨index, rfl, rfl⟩ := encodeTerm_eq_bound termEq.symm
        simp only [DBTerm.hasFree]
  · match arguments, arity with
    | [v, f, e], _ =>
        rule_simp
        obtain ⟨functionFree, argumentFree⟩ := premisesHold
        intro sourceVar termValue needle termEq
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := encodeTerm_eq_app termEq.symm
        simp only [DBTerm.hasFree, functionFree sourceVar functionTerm needle rfl,
          argumentFree sourceVar argumentTerm needle rfl, Bool.or_self]
  · match arguments, arity with
    | [v, a, t], _ =>
        rule_simp
        intro sourceVar termValue needle termEq
        obtain ⟨domain, body, rfl, rfl, rfl⟩ := encodeTerm_eq_abs termEq.symm
        simp only [DBTerm.hasFree, premisesHold sourceVar body needle rfl]
  · match arguments, arity with
    | [v], _ =>
        rule_simp
        intro sourceVar termValues _ termsEq
        obtain rfl := termsP_eq_nilP termsEq
        simp
  · match arguments, arity with
    | [v, t, ts], _ =>
        rule_simp
        obtain ⟨headFree, tailFree⟩ := premisesHold
        intro sourceVar termValues needle termsEq
        obtain ⟨term, rest, rfl, rfl, rfl⟩ := termsP_eq_consP termsEq
        intro other member
        rcases List.mem_cons.mp member with rfl | inTail
        · exact headFree sourceVar _ needle rfl
        · exact tailFree sourceVar rest needle rfl other inTail

theorem closeRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ closeRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [closeRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [v, d, c, a], _ =>
        rule_simp
        intro sourceVar level termValue _ _ termEq
        obtain ⟨constant, type, rfl, rfl, rfl⟩ := encodeTerm_eq_const termEq.symm
        simp only [DBTerm.closeFreeAt]
        rfl
  · match arguments, arity with
    | [x, a, d], _ =>
        rule_simp
        intro sourceVar level termValue needle depthEq termEq
        obtain ⟨other, rfl, rfl, rfl⟩ := encodeTerm_eq_free termEq.symm
        have equal : sourceVar = other := freeVarP_injective (needle.symm.trans termEq)
        subst equal depthEq
        rw [DBTerm.closeFreeAt_exact]
        rfl
  · match arguments, arity with
    | [v, d, x, a], _ =>
        rule_simp
        intro sourceVar level termValue needle _ termEq
        obtain ⟨other, rfl, rfl, rfl⟩ := encodeTerm_eq_free termEq.symm
        have different : sourceVar ≠ other := by
          rintro rfl
          exact premisesHold (needle.trans rfl)
        rw [DBTerm.closeFreeAt_other _ _ _ different]
        rfl
  · match arguments, arity with
    | [v, d, i], _ =>
        rule_simp
        intro sourceVar level termValue _ _ termEq
        obtain ⟨index, rfl, rfl⟩ := encodeTerm_eq_bound termEq.symm
        simp only [DBTerm.closeFreeAt]
        rfl
  · match arguments, arity with
    | [v, d, f, e, f2, e2], _ =>
        rule_simp
        obtain ⟨functionClosed, argumentClosed⟩ := premisesHold
        intro sourceVar level termValue needle depthEq termEq
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := encodeTerm_eq_app termEq.symm
        obtain rfl := functionClosed sourceVar level functionTerm needle depthEq rfl
        obtain rfl := argumentClosed sourceVar level argumentTerm needle depthEq rfl
        simp only [DBTerm.closeFreeAt]
        rfl
  · match arguments, arity with
    | [v, d, a, t, t2], _ =>
        rule_simp
        intro sourceVar level termValue needle depthEq termEq
        obtain ⟨domain, body, rfl, rfl, rfl⟩ := encodeTerm_eq_abs termEq.symm
        subst depthEq
        obtain rfl := premisesHold sourceVar (level + 1) body needle rfl rfl
        simp only [DBTerm.closeFreeAt]
        rfl

theorem instantiateRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ instantiateRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [instantiateRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [s, d, c, a], _ =>
        rule_simp
        intro replacementValue level termValue _ _ termEq
        obtain ⟨constant, type, rfl, rfl, rfl⟩ := encodeTerm_eq_const termEq.symm
        simp only [DBTerm.instantiateAt]
        rfl
  · match arguments, arity with
    | [s, d, x, a], _ =>
        rule_simp
        intro replacementValue level termValue _ _ termEq
        obtain ⟨other, rfl, rfl, rfl⟩ := encodeTerm_eq_free termEq.symm
        simp only [DBTerm.instantiateAt]
        rfl
  · match arguments, arity with
    | [s, d], _ =>
        rule_simp
        intro replacementValue level termValue replacementEq depthEq termEq
        obtain ⟨index, rfl, indexEq⟩ := encodeTerm_eq_bound termEq.symm
        have same : index = level :=
          encodeUnary_injective (LabeledTree.toPattern_injective _ _ (indexEq.symm.trans depthEq))
        subst same
        rw [DBTerm.instantiateAt_target]
        exact replacementEq
  · match arguments, arity with
    | [s, d, i], _ =>
        rule_simp
        intro replacementValue level termValue _ depthEq termEq
        obtain ⟨index, rfl, rfl⟩ := encodeTerm_eq_bound termEq.symm
        have different : index ≠ level := by
          rintro rfl
          exact premisesHold depthEq.symm
        rw [DBTerm.instantiateAt_other _ _ _ different]
        rfl
  · match arguments, arity with
    | [s, d, f, e, f2, e2], _ =>
        rule_simp
        obtain ⟨functionDone, argumentDone⟩ := premisesHold
        intro replacementValue level termValue replacementEq depthEq termEq
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := encodeTerm_eq_app termEq.symm
        obtain rfl := functionDone replacementValue level functionTerm replacementEq depthEq rfl
        obtain rfl := argumentDone replacementValue level argumentTerm replacementEq depthEq rfl
        simp only [DBTerm.instantiateAt]
        rfl
  · match arguments, arity with
    | [s, d, a, t, t2], _ =>
        rule_simp
        intro replacementValue level termValue replacementEq depthEq termEq
        obtain ⟨domain, body, rfl, rfl, rfl⟩ := encodeTerm_eq_abs termEq.symm
        subst depthEq
        obtain rfl := premisesHold replacementValue (level + 1) body replacementEq rfl rfl
        simp only [DBTerm.instantiateAt]
        rfl

/-! ## Finite sets: union, erase, insertion and sorting -/

theorem treesP_eq_consP {trees : List LabeledTree} {head tail : Pattern} (same : consP head tail = treesP trees) :
    ∃ tree rest, trees = tree :: rest ∧ head = groundP tree ∧ tail = treesP rest := by
  cases trees with
  | nil => simp [treesP, listP, nilP, consP] at same
  | cons tree rest =>
      simp only [treesP, listP, List.map_cons, consP, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨tree, rest, rfl, same.1, same.2⟩

theorem treesP_eq_nilP {trees : List LabeledTree} (same : nilP = treesP trees) : trees = [] := by
  cases trees with
  | nil => rfl
  | cons _ _ => simp [treesP, listP, nilP, consP] at same

theorem groundP_injective : Function.Injective groundP := fun first second same =>
  LabeledTree.toPattern_injective first second same

theorem pLt_groundP_iff (first second : LabeledTree) : PLt (groundP first) (groundP second) ↔ first < second :=
  pLt_toPattern_iff first second

theorem setRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ setRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [setRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [h], _ =>
        rule_simp
        intro firstTrees secondTrees firstEq secondEq _ secondIncreasing
        obtain rfl := treesP_eq_nilP firstEq
        exact ⟨secondTrees, secondEq, secondIncreasing, fun tree => by simp⟩
  · match arguments, arity with
    | [x, xs], _ =>
        rule_simp
        intro firstTrees secondTrees firstEq secondEq firstIncreasing _
        obtain rfl := treesP_eq_nilP secondEq
        exact ⟨firstTrees, firstEq, firstIncreasing, fun tree => by simp⟩
  · match arguments, arity with
    | [x, xs, y, ys, zs], _ =>
        rule_simp
        obtain ⟨lower, restUnion⟩ := premisesHold
        intro firstTrees secondTrees firstEq secondEq firstIncreasing secondIncreasing
        obtain ⟨first, firstRest, rfl, rfl, rfl⟩ := treesP_eq_consP firstEq
        obtain ⟨second, secondRest, rfl, rfl, rfl⟩ := treesP_eq_consP secondEq
        have firstBelow : first < second := (pLt_groundP_iff first second).mp lower
        obtain ⟨firstAbove, firstRestIncreasing⟩ := List.pairwise_cons.mp firstIncreasing
        obtain ⟨secondAbove, _⟩ := List.pairwise_cons.mp secondIncreasing
        obtain ⟨merged, rfl, mergedIncreasing, mergedMembers⟩ :=
          restUnion firstRest (second :: secondRest) rfl rfl firstRestIncreasing secondIncreasing
        refine ⟨first :: merged, rfl, List.pairwise_cons.mpr ⟨?_, mergedIncreasing⟩, ?_⟩
        · intro other otherMember
          rcases (mergedMembers other).mp otherMember with inFirst | inSecond
          · exact firstAbove other inFirst
          · rcases List.mem_cons.mp inSecond with rfl | inSecondRest
            · exact firstBelow
            · exact lt_trans firstBelow (secondAbove other inSecondRest)
        · intro other
          simp only [List.mem_cons, mergedMembers]
          tauto
  · match arguments, arity with
    | [x, xs, y, ys, zs], _ =>
        rule_simp
        obtain ⟨lower, restUnion⟩ := premisesHold
        intro firstTrees secondTrees firstEq secondEq firstIncreasing secondIncreasing
        obtain ⟨first, firstRest, rfl, rfl, rfl⟩ := treesP_eq_consP firstEq
        obtain ⟨second, secondRest, rfl, rfl, rfl⟩ := treesP_eq_consP secondEq
        have secondBelow : second < first := (pLt_groundP_iff second first).mp lower
        obtain ⟨firstAbove, _⟩ := List.pairwise_cons.mp firstIncreasing
        obtain ⟨secondAbove, secondRestIncreasing⟩ := List.pairwise_cons.mp secondIncreasing
        obtain ⟨merged, rfl, mergedIncreasing, mergedMembers⟩ :=
          restUnion (first :: firstRest) secondRest rfl rfl firstIncreasing secondRestIncreasing
        refine ⟨second :: merged, rfl, List.pairwise_cons.mpr ⟨?_, mergedIncreasing⟩, ?_⟩
        · intro other otherMember
          rcases (mergedMembers other).mp otherMember with inFirst | inSecond
          · rcases List.mem_cons.mp inFirst with rfl | inFirstRest
            · exact secondBelow
            · exact lt_trans secondBelow (firstAbove other inFirstRest)
          · exact secondAbove other inSecond
        · intro other
          simp only [List.mem_cons, mergedMembers]
          tauto
  · match arguments, arity with
    | [x, xs, ys, zs], _ =>
        rule_simp
        intro firstTrees secondTrees firstEq secondEq firstIncreasing secondIncreasing
        obtain ⟨first, firstRest, rfl, rfl, rfl⟩ := treesP_eq_consP firstEq
        obtain ⟨second, secondRest, rfl, secondHead, rfl⟩ := treesP_eq_consP secondEq
        obtain rfl := groundP_injective secondHead
        obtain ⟨firstAbove, firstRestIncreasing⟩ := List.pairwise_cons.mp firstIncreasing
        obtain ⟨secondAbove, secondRestIncreasing⟩ := List.pairwise_cons.mp secondIncreasing
        obtain ⟨merged, rfl, mergedIncreasing, mergedMembers⟩ :=
          premisesHold firstRest secondRest rfl rfl firstRestIncreasing secondRestIncreasing
        refine ⟨_ :: merged, rfl, List.pairwise_cons.mpr ⟨?_, mergedIncreasing⟩, ?_⟩
        · intro other otherMember
          rcases (mergedMembers other).mp otherMember with inFirst | inSecond
          · exact firstAbove other inFirst
          · exact secondAbove other inSecond
        · intro other
          simp only [List.mem_cons, mergedMembers]
          tauto
  · match arguments, arity with
    | [t], _ =>
        rule_simp
        intro tree trees _ treesEq _
        obtain rfl := treesP_eq_nilP treesEq
        exact ⟨[], rfl, List.Pairwise.nil, fun other => by simp⟩
  · match arguments, arity with
    | [t, xs], _ =>
        rule_simp
        intro tree trees termEq treesEq increasing
        obtain ⟨head, rest, rfl, headEq, rfl⟩ := treesP_eq_consP treesEq
        obtain rfl := groundP_injective (headEq.symm.trans termEq)
        obtain ⟨headBelow, restIncreasing⟩ := List.pairwise_cons.mp increasing
        refine ⟨rest, rfl, restIncreasing, fun other => ⟨fun member => ⟨List.mem_cons_of_mem _ member, ?_⟩, ?_⟩⟩
        · rintro rfl
          exact lt_irrefl _ (headBelow _ member)
        · rintro ⟨member, different⟩
          rcases List.mem_cons.mp member with rfl | inRest
          · exact absurd rfl different
          · exact inRest
  · match arguments, arity with
    | [t, x, xs, ys], _ =>
        rule_simp
        obtain ⟨different, restErase⟩ := premisesHold
        intro tree trees termEq treesEq increasing
        obtain ⟨head, rest, rfl, rfl, rfl⟩ := treesP_eq_consP treesEq
        obtain ⟨headBelow, restIncreasing⟩ := List.pairwise_cons.mp increasing
        obtain ⟨kept, rfl, keptIncreasing, keptMembers⟩ := restErase tree rest termEq rfl restIncreasing
        have headDifferent : head ≠ tree := fun same => different (by rw [termEq, same])
        refine ⟨head :: kept, rfl,
          List.pairwise_cons.mpr ⟨fun other member => headBelow other ((keptMembers other).mp member).1,
            keptIncreasing⟩, ?_⟩
        intro other
        simp only [List.mem_cons, keptMembers]
        constructor
        · rintro (rfl | ⟨member, otherDifferent⟩)
          · exact ⟨Or.inl rfl, headDifferent⟩
          · exact ⟨Or.inr member, otherDifferent⟩
        · rintro ⟨rfl | member, otherDifferent⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨member, otherDifferent⟩

theorem sortRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ sortRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [sortRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [t], _ =>
        rule_simp
        intro tree trees termEq treesEq _
        obtain rfl := treesP_eq_nilP treesEq
        subst termEq
        exact ⟨[tree], rfl, by simp [Increasing], fun other => by simp⟩
  · match arguments, arity with
    | [t, xs], _ =>
        rule_simp
        intro tree trees termEq treesEq increasing
        obtain ⟨head, rest, rfl, headEq, rfl⟩ := treesP_eq_consP treesEq
        obtain rfl := groundP_injective (headEq.symm.trans termEq)
        refine ⟨_, treesEq, increasing, fun other => ?_⟩
        simp only [List.mem_cons]
        tauto
  · match arguments, arity with
    | [t, x, xs], _ =>
        rule_simp
        intro tree trees termEq treesEq increasing
        obtain ⟨head, rest, rfl, rfl, rfl⟩ := treesP_eq_consP treesEq
        subst termEq
        have below : tree < head := (pLt_groundP_iff tree head).mp premisesHold
        obtain ⟨headBelow, _⟩ := List.pairwise_cons.mp increasing
        refine ⟨tree :: head :: rest, rfl, List.pairwise_cons.mpr ⟨?_, increasing⟩, fun other => List.mem_cons⟩
        intro other member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact below
        · exact lt_trans below (headBelow other inRest)
  · match arguments, arity with
    | [t, x, xs, ys], _ =>
        rule_simp
        obtain ⟨lower, restInsert⟩ := premisesHold
        intro tree trees termEq treesEq increasing
        obtain ⟨head, rest, rfl, rfl, rfl⟩ := treesP_eq_consP treesEq
        obtain ⟨headBelow, restIncreasing⟩ := List.pairwise_cons.mp increasing
        obtain ⟨inserted, rfl, insertedIncreasing, insertedMembers⟩ :=
          restInsert tree rest termEq rfl restIncreasing
        subst termEq
        have below : head < tree := (pLt_groundP_iff head tree).mp lower
        refine ⟨head :: inserted, rfl, List.pairwise_cons.mpr ⟨?_, insertedIncreasing⟩, fun other => ?_⟩
        · intro other member
          rcases (insertedMembers other).mp member with rfl | inRest
          · exact below
          · exact headBelow other inRest
        · simp only [List.mem_cons, insertedMembers]
          tauto
  · match arguments, arity with
    | [], _ =>
        rule_simp
        intro trees treesEq
        obtain rfl := treesP_eq_nilP treesEq
        exact ⟨[], rfl, List.Pairwise.nil, fun other => Iff.rfl⟩
  · match arguments, arity with
    | [x, xs, ys, zs], _ =>
        rule_simp
        obtain ⟨restSorted, inserted⟩ := premisesHold
        intro trees treesEq
        obtain ⟨head, rest, rfl, rfl, rfl⟩ := treesP_eq_consP treesEq
        obtain ⟨sorted, rfl, sortedIncreasing, sortedMembers⟩ := restSorted rest rfl
        obtain ⟨result, rfl, resultIncreasing, resultMembers⟩ := inserted head sorted rfl rfl sortedIncreasing
        refine ⟨result, rfl, resultIncreasing, fun other => ?_⟩
        rw [resultMembers, sortedMembers, List.mem_cons]

/-! ## Type instantiation -/

theorem tysP_eq_consP {types : List Ty} {head tail : Pattern} (same : consP head tail = tysP types) :
    ∃ type rest, types = type :: rest ∧ head = groundP (encodeTy type) ∧ tail = tysP rest := by
  cases types with
  | nil => simp [tysP, encodeTys, listP, nilP, consP] at same
  | cons type rest =>
      simp only [tysP, encodeTys, listP, List.map_cons, consP, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨type, rest, rfl, same.1, same.2⟩

theorem tysP_eq_nilP {types : List Ty} (same : nilP = tysP types) : types = [] := by
  cases types with
  | nil => rfl
  | cons _ _ => simp [tysP, encodeTys, listP, nilP, consP] at same

theorem typeMapletsP_eq_consP {entries : List (Ty × Ty)} {head tail : Pattern}
    (same : consP head tail = typeMapletsP entries) :
    ∃ replacement key rest, entries = (replacement, key) :: rest ∧
      head = typeMapletP (groundP (encodeTy replacement)) (groundP (encodeTy key)) ∧
        tail = typeMapletsP rest := by
  cases entries with
  | nil => simp [typeMapletsP, listP, nilP, consP] at same
  | cons entry rest =>
      obtain ⟨replacement, key⟩ := entry
      simp only [typeMapletsP, listP, List.map_cons, consP, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨replacement, key, rest, rfl, same.1, same.2⟩

theorem typeMapletsP_eq_nilP {entries : List (Ty × Ty)} (same : nilP = typeMapletsP entries) : entries = [] := by
  cases entries with
  | nil => rfl
  | cons _ _ => simp [typeMapletsP, listP, nilP, consP] at same

/-- A maplet's two sides, read back from its rendering. -/
theorem typeMaplet_sides {replacement key : Ty} {first second : Pattern}
    (same : typeMapletP first second = typeMapletP (groundP (encodeTy replacement)) (groundP (encodeTy key))) :
    first = groundP (encodeTy replacement) ∧ second = groundP (encodeTy key) := by
  obtain ⟨-, children⟩ := treeP_injective same
  simpa only [List.cons.injEq, and_true] using children

theorem typeActionRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ typeActionRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [typeActionRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [x], _ =>
        rule_simp
        intro entryValues nameValue entriesEq nameEq
        obtain rfl := typeMapletsP_eq_nilP entriesEq
        subst nameEq
        rfl
  · match arguments, arity with
    | [r, x, rest], _ =>
        rule_simp
        intro entryValues nameValue entriesEq nameEq
        obtain ⟨replacement, key, restEntries, rfl, headEq, rfl⟩ := typeMapletsP_eq_consP entriesEq
        obtain ⟨rfl, keyEq⟩ := typeMaplet_sides headEq
        obtain ⟨keyName, rfl, rfl⟩ := encodeTy_eq_var keyEq.symm
        obtain rfl := encodeName_injective (groundP_injective nameEq)
        simp [SourceSubstitution.variableType]
  · match arguments, arity with
    | [r, k, rest, x, t], _ =>
        rule_simp
        obtain ⟨different, restType⟩ := premisesHold
        intro entryValues nameValue entriesEq nameEq
        obtain ⟨replacement, key, restEntries, rfl, headEq, rfl⟩ := typeMapletsP_eq_consP entriesEq
        obtain ⟨rfl, keyEq⟩ := typeMaplet_sides headEq
        obtain ⟨keyName, rfl, rfl⟩ := encodeTy_eq_var keyEq.symm
        have distinct : nameValue ≠ keyName := fun same => different (by rw [nameEq, same])
        rw [restType restEntries nameValue rfl nameEq]
        simp [SourceSubstitution.variableType, distinct]
  · match arguments, arity with
    | [r, o, as, rest, x, t], _ =>
        rule_simp
        intro entryValues nameValue entriesEq nameEq
        obtain ⟨replacement, key, restEntries, rfl, headEq, rfl⟩ := typeMapletsP_eq_consP entriesEq
        obtain ⟨rfl, keyEq⟩ := typeMaplet_sides headEq
        obtain ⟨operator, argumentValues, rfl, -, -⟩ := encodeTy_eq_op keyEq.symm
        rw [premisesHold restEntries nameValue rfl nameEq]
        simp [SourceSubstitution.variableType]
  · match arguments, arity with
    | [es, x, t], _ =>
        rule_simp
        intro entryValues typeValue entriesEq typeEq
        obtain ⟨name, rfl, rfl⟩ := encodeTy_eq_var typeEq.symm
        rw [premisesHold entryValues name entriesEq rfl]
        simp [SourceSubstitution.typeAction]
  · match arguments, arity with
    | [es, o, as, bs], _ =>
        rule_simp
        intro entryValues typeValue entriesEq typeEq
        obtain ⟨operator, argumentValues, rfl, rfl, rfl⟩ := encodeTy_eq_op typeEq.symm
        rw [premisesHold entryValues argumentValues entriesEq rfl]
        simp only [SourceSubstitution.typeAction, groundP_encodeTy_op]
        rfl
  · match arguments, arity with
    | [es], _ =>
        rule_simp
        intro entryValues typeValues _ typesEq
        obtain rfl := tysP_eq_nilP typesEq
        rfl
  · match arguments, arity with
    | [es, a, as, b, bs], _ =>
        rule_simp
        obtain ⟨headActs, restActs⟩ := premisesHold
        intro entryValues typeValues entriesEq typesEq
        obtain ⟨type, rest, rfl, rfl, rfl⟩ := tysP_eq_consP typesEq
        obtain rfl := headActs entryValues type entriesEq rfl
        obtain rfl := restActs entryValues rest entriesEq rfl
        rfl
  · match arguments, arity with
    | [es, c, a, b], _ =>
        rule_simp
        intro entryValues termValue entriesEq termEq
        obtain ⟨constant, type, rfl, rfl, rfl⟩ := encodeTerm_eq_const termEq.symm
        obtain rfl := premisesHold entryValues type entriesEq rfl
        rfl
  · match arguments, arity with
    | [es, x, a, b], _ =>
        rule_simp
        intro entryValues termValue entriesEq termEq
        obtain ⟨sourceVar, rfl, rfl, rfl⟩ := encodeTerm_eq_free termEq.symm
        obtain rfl := premisesHold entryValues sourceVar.ty entriesEq rfl
        rfl
  · match arguments, arity with
    | [es, i], _ =>
        rule_simp
        intro entryValues termValue _ termEq
        obtain ⟨index, rfl, rfl⟩ := encodeTerm_eq_bound termEq.symm
        rfl
  · match arguments, arity with
    | [es, f, e, f2, e2], _ =>
        rule_simp
        obtain ⟨functionActs, argumentActs⟩ := premisesHold
        intro entryValues termValue entriesEq termEq
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := encodeTerm_eq_app termEq.symm
        obtain rfl := functionActs entryValues functionTerm entriesEq rfl
        obtain rfl := argumentActs entryValues argumentTerm entriesEq rfl
        rfl
  · match arguments, arity with
    | [es, a, t, b, t2], _ =>
        rule_simp
        obtain ⟨typeActs, bodyActs⟩ := premisesHold
        intro entryValues termValue entriesEq termEq
        obtain ⟨domain, body, rfl, rfl, rfl⟩ := encodeTerm_eq_abs termEq.symm
        obtain rfl := typeActs entryValues domain entriesEq rfl
        obtain rfl := bodyActs entryValues body entriesEq rfl
        rfl
  · match arguments, arity with
    | [es], _ =>
        rule_simp
        intro entryValues termValues _ termsEq
        obtain rfl := termsP_eq_nilP termsEq
        rfl
  · match arguments, arity with
    | [es, t, ts, u, us], _ =>
        rule_simp
        obtain ⟨headActs, restActs⟩ := premisesHold
        intro entryValues termValues entriesEq termsEq
        obtain ⟨term, rest, rfl, rfl, rfl⟩ := termsP_eq_consP termsEq
        obtain rfl := headActs entryValues term entriesEq rfl
        obtain rfl := restActs entryValues rest entriesEq rfl
        rfl

/-! ## Term instantiation -/

theorem tableP_eq_consP {entries : List (SourceVar × CheckedSourceTerm)} {head tail : Pattern}
    (same : consP head tail = tableP entries) :
    ∃ key replacement rest, entries = (key, replacement) :: rest ∧
      head = pairP (freeVarP key) (groundP (encodeTerm replacement.canonical.term)) ∧ tail = tableP rest := by
  cases entries with
  | nil => simp [tableP, listP, nilP, consP] at same
  | cons entry rest =>
      obtain ⟨key, replacement⟩ := entry
      simp only [tableP, listP, List.map_cons, consP, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨key, replacement, rest, rfl, same.1, same.2⟩

theorem tableP_eq_nilP {entries : List (SourceVar × CheckedSourceTerm)} (same : nilP = tableP entries) :
    entries = [] := by
  cases entries with
  | nil => rfl
  | cons _ _ => simp [tableP, listP, nilP, consP] at same

/-- A table entry's key and value, read back from its rendering. -/
theorem pair_sides {key : SourceVar} {replacement : CheckedSourceTerm} {first second : Pattern}
    (same : pairP first second = pairP (freeVarP key) (groundP (encodeTerm replacement.canonical.term))) :
    first = freeVarP key ∧ second = groundP (encodeTerm replacement.canonical.term) := by
  obtain ⟨-, children⟩ := treeP_injective same
  simpa only [List.cons.injEq, and_true] using children

theorem lookup_cons_same (key : SourceVar) (replacement : CheckedSourceTerm)
    (rest : List (SourceVar × CheckedSourceTerm)) :
    TermSubst.lookup ⟨TypeSubst.empty, (key, replacement) :: rest⟩ key = some replacement := by
  simp [TermSubst.lookup, TermSubst.keySame]

theorem lookup_cons_other {key sourceVar : SourceVar} (different : key ≠ sourceVar)
    (replacement : CheckedSourceTerm) (rest : List (SourceVar × CheckedSourceTerm)) :
    TermSubst.lookup ⟨TypeSubst.empty, (key, replacement) :: rest⟩ sourceVar =
      TermSubst.lookup ⟨TypeSubst.empty, rest⟩ sourceVar := by
  simp [TermSubst.lookup, TermSubst.keySame, different]

theorem applyVar_empty (sourceVar : SourceVar) : TypeSubst.empty.applyVar sourceVar = sourceVar := by
  cases sourceVar
  simp [TypeSubst.applyVar]

theorem tableAction_free_of_lookup_some {entries : List (SourceVar × CheckedSourceTerm)} {sourceVar : SourceVar}
    {replacement : CheckedSourceTerm}
    (found : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ sourceVar = some replacement) :
    tableAction entries (.free sourceVar) = replacement.canonical.term := by
  have found' : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ (TypeSubst.empty.applyVar sourceVar) =
      some replacement := by
    rw [applyVar_empty]
    exact found
  exact TermSubst.applyDB_free_of_lookup_some ⟨TypeSubst.empty, entries⟩ sourceVar replacement found'

theorem tableAction_free_of_lookup_none {entries : List (SourceVar × CheckedSourceTerm)} {sourceVar : SourceVar}
    (missing : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ sourceVar = none) :
    tableAction entries (.free sourceVar) = .free sourceVar := by
  have missing' : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ (TypeSubst.empty.applyVar sourceVar) = none := by
    rw [applyVar_empty]
    exact missing
  calc tableAction entries (.free sourceVar)
      = .free (TypeSubst.empty.applyVar sourceVar) :=
        TermSubst.applyDB_free_of_lookup_none ⟨TypeSubst.empty, entries⟩ sourceVar missing'
    _ = .free sourceVar := by rw [applyVar_empty]

theorem termActionRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ termActionRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [termActionRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [], _ =>
        rule_simp
        exact ⟨[], rfl, fun _ member => by simp at member, rfl⟩
  · match arguments, arity with
    | [s, x, a, c, rest, table], _ =>
        rule_simp
        obtain ⟨⟨name, rfl⟩, converted, typed, ⟨mapletValues, rfl, admissible, rfl⟩⟩ := premisesHold
        obtain ⟨sourceValue, termValue, rfl, rfl, toDBEq⟩ := converted [] rfl
        subst toDBEq
        obtain ⟨termValue', typeValue, termEq, rfl, inferred⟩ := typed [] rfl
        obtain rfl := encodeTerm_injective (groundP_injective termEq)
        have checked : sourceValue.inferType = some typeValue := by
          rw [← DBTerm.inferType_toDB [] sourceValue]
          exact inferred
        refine ⟨(⟨sourceValue, typeValue, checked⟩, .var name typeValue) :: mapletValues, rfl, ?_, rfl⟩
        intro entry member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact rfl
        · exact admissible entry inRest
  · match arguments, arity with
    | [v, r, rest], _ =>
        rule_simp
        intro entries sourceVar tableEq needle
        obtain ⟨key, replacement, restEntries, rfl, headEq, rfl⟩ := tableP_eq_consP tableEq
        obtain ⟨keyEq, rfl⟩ := pair_sides headEq
        obtain rfl := freeVarP_injective (needle.symm.trans keyEq)
        exact ⟨replacement, lookup_cons_same _ _ _, rfl⟩
  · match arguments, arity with
    | [w, s, rest, v, r], _ =>
        rule_simp
        obtain ⟨different, restLookup⟩ := premisesHold
        intro entries sourceVar tableEq needle
        obtain ⟨key, replacement, restEntries, rfl, headEq, rfl⟩ := tableP_eq_consP tableEq
        obtain ⟨rfl, -⟩ := pair_sides headEq
        have distinct : key ≠ sourceVar := by
          rintro rfl
          exact different needle
        rw [lookup_cons_other distinct]
        exact restLookup restEntries sourceVar rfl needle
  · match arguments, arity with
    | [v], _ =>
        rule_simp
        intro entries sourceVar tableEq _
        obtain rfl := tableP_eq_nilP tableEq
        rfl
  · match arguments, arity with
    | [w, s, rest, v], _ =>
        rule_simp
        obtain ⟨different, restMissing⟩ := premisesHold
        intro entries sourceVar tableEq needle
        obtain ⟨key, replacement, restEntries, rfl, headEq, rfl⟩ := tableP_eq_consP tableEq
        obtain ⟨rfl, -⟩ := pair_sides headEq
        have distinct : key ≠ sourceVar := by
          rintro rfl
          exact different needle
        rw [lookup_cons_other distinct]
        exact restMissing restEntries sourceVar rfl needle
  · match arguments, arity with
    | [table, c, a], _ =>
        rule_simp
        intro entries termValue _ termEq
        obtain ⟨constant, type, rfl, rfl, rfl⟩ := encodeTerm_eq_const termEq.symm
        simp only [tableAction, TermSubst.applyDB_const, TypeSubst.apply_empty]
        rfl
  · match arguments, arity with
    | [table, x, a, r], _ =>
        rule_simp
        intro entries termValue tableEq termEq
        obtain ⟨sourceVar, rfl, rfl, rfl⟩ := encodeTerm_eq_free termEq.symm
        obtain ⟨replacement, found, rfl⟩ := premisesHold entries sourceVar tableEq rfl
        rw [tableAction_free_of_lookup_some found]
  · match arguments, arity with
    | [table, x, a], _ =>
        rule_simp
        intro entries termValue tableEq termEq
        obtain ⟨sourceVar, rfl, rfl, rfl⟩ := encodeTerm_eq_free termEq.symm
        rw [tableAction_free_of_lookup_none (premisesHold entries sourceVar tableEq rfl)]
        rfl
  · match arguments, arity with
    | [table, i], _ =>
        rule_simp
        intro entries termValue _ termEq
        obtain ⟨index, rfl, rfl⟩ := encodeTerm_eq_bound termEq.symm
        simp only [tableAction, TermSubst.applyDB_bound]
        rfl
  · match arguments, arity with
    | [table, f, e, f2, e2], _ =>
        rule_simp
        obtain ⟨functionDone, argumentDone⟩ := premisesHold
        intro entries termValue tableEq termEq
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := encodeTerm_eq_app termEq.symm
        obtain rfl := functionDone entries functionTerm tableEq rfl
        obtain rfl := argumentDone entries argumentTerm tableEq rfl
        simp only [tableAction, TermSubst.applyDB_app]
        rfl
  · match arguments, arity with
    | [table, a, t, t2], _ =>
        rule_simp
        intro entries termValue tableEq termEq
        obtain ⟨domain, body, rfl, rfl, rfl⟩ := encodeTerm_eq_abs termEq.symm
        obtain rfl := premisesHold entries body tableEq rfl
        simp only [tableAction, TermSubst.applyDB_abs, TypeSubst.apply_empty]
        rfl
  · match arguments, arity with
    | [table], _ =>
        rule_simp
        intro entries termValues _ termsEq
        obtain rfl := termsP_eq_nilP termsEq
        rfl
  · match arguments, arity with
    | [table, t, ts, u, us], _ =>
        rule_simp
        obtain ⟨headDone, restDone⟩ := premisesHold
        intro entries termValues tableEq termsEq
        obtain ⟨term, rest, rfl, rfl, rfl⟩ := termsP_eq_consP termsEq
        obtain rfl := headDone entries term tableEq rfl
        obtain rfl := restDone entries rest tableEq rfl
        rfl

/-! ## Rendered hypothesis sets -/

/-- The encodings of a hypothesis set, in sorted order. -/
def hypothesisTrees (hypotheses : Finset CanonicalTerm) : List LabeledTree :=
  (sortedHypotheses hypotheses).map encodeCanonical

theorem sequentHypothesesP_eq_treesP (sequent : Sequent) :
    sequentHypothesesP sequent = treesP (hypothesisTrees sequent.hyp) := by
  simp [sequentHypothesesP, treesP, hypothesisTrees, Function.comp_def]

theorem sequentHypothesesP_eq_termsP (sequent : Sequent) :
    sequentHypothesesP sequent = termsP ((sortedHypotheses sequent.hyp).map CanonicalTerm.term) := by
  simp [sequentHypothesesP, termsP, encodeCanonical, Function.comp_def]

theorem termsP_eq_treesP (terms : List DBTerm) : termsP terms = treesP (terms.map encodeTerm) := by
  simp [termsP, treesP, Function.comp_def]

theorem mem_hypothesisTrees {hypotheses : Finset CanonicalTerm} {tree : LabeledTree} :
    tree ∈ hypothesisTrees hypotheses ↔ ∃ term ∈ hypotheses, encodeCanonical term = tree := by
  simp [hypothesisTrees, sortedHypotheses]

theorem hypothesisTrees_empty : hypothesisTrees ∅ = [] := by
  simp [hypothesisTrees, sortedHypotheses]

theorem hypothesisTrees_singleton (term : CanonicalTerm) : hypothesisTrees {term} = [encodeCanonical term] := by
  simp [hypothesisTrees, sortedHypotheses]

theorem hypothesisTrees_increasing (hypotheses : Finset CanonicalTerm) :
    Increasing (hypothesisTrees hypotheses) := by
  have sorted := Finset.pairwise_sort hypotheses CanonicalLe
  have distinct := Finset.sort_nodup hypotheses CanonicalLe
  unfold Increasing hypothesisTrees sortedHypotheses
  rw [List.pairwise_map]
  exact (sorted.and distinct).imp fun ⟨below, different⟩ =>
    lt_of_le_of_ne below fun same => different (encodeCanonical_injective same)

/-- **A rendered hypothesis set is unique**: an increasing list of trees with the members of a
hypothesis set's encodings is its rendering. -/
theorem hypothesisTrees_unique {trees : List LabeledTree} {hypotheses : Finset CanonicalTerm}
    (increasing : Increasing trees)
    (members : ∀ tree, tree ∈ trees ↔ ∃ term ∈ hypotheses, encodeCanonical term = tree) :
    trees = hypothesisTrees hypotheses :=
  haveI : Std.Antisymm (α := LabeledTree) (· < ·) := Std.Asymm.antisymm _
  List.Pairwise.eq_of_mem_iff increasing (hypothesisTrees_increasing hypotheses)
    fun tree => (members tree).trans mem_hypothesisTrees.symm

theorem treesP_injective : Function.Injective treesP := by
  intro first second same
  have lists := listP_injective same
  exact List.map_injective_iff.mpr groundP_injective lists

/-- The rendering of a sequent determines the sequent. -/
theorem sequent_of_rendering {first second : Sequent}
    (hypotheses : sequentHypothesesP first = sequentHypothesesP second)
    (conclusions : sequentConclusionP first = sequentConclusionP second) : first = second := by
  rw [sequentHypothesesP_eq_treesP, sequentHypothesesP_eq_treesP] at hypotheses
  have sorted := List.map_injective_iff.mpr encodeCanonical_injective (treesP_injective hypotheses)
  exact Sequent.ext (sortedHypotheses_injective sorted)
    (encodeCanonical_injective (groundP_injective conclusions))

theorem union_hypotheses {first second result : Pattern} {left right : Finset CanonicalTerm}
    (union : UnionMeaning first second result)
    (firstEq : first = treesP (hypothesisTrees left)) (secondEq : second = treesP (hypothesisTrees right)) :
    result = treesP (hypothesisTrees (left ∪ right)) := by
  obtain ⟨trees, rfl, increasing, members⟩ := union _ _ firstEq secondEq
    (hypothesisTrees_increasing left) (hypothesisTrees_increasing right)
  refine congrArg treesP (hypothesisTrees_unique increasing fun tree => ?_)
  rw [members, mem_hypothesisTrees, mem_hypothesisTrees]
  simp only [Finset.mem_union]
  constructor
  · rintro (⟨term, member, rfl⟩ | ⟨term, member, rfl⟩)
    · exact ⟨term, Or.inl member, rfl⟩
    · exact ⟨term, Or.inr member, rfl⟩
  · rintro ⟨term, member | member, rfl⟩
    · exact Or.inl ⟨term, member, rfl⟩
    · exact Or.inr ⟨term, member, rfl⟩

theorem erase_hypotheses {term terms result : Pattern} {hypotheses : Finset CanonicalTerm}
    {removed : CanonicalTerm} (erase : EraseMeaning term terms result)
    (termEq : term = groundP (encodeCanonical removed))
    (termsEq : terms = treesP (hypothesisTrees hypotheses)) :
    result = treesP (hypothesisTrees (hypotheses.erase removed)) := by
  obtain ⟨trees, rfl, increasing, members⟩ := erase _ _ termEq termsEq (hypothesisTrees_increasing hypotheses)
  refine congrArg treesP (hypothesisTrees_unique increasing fun tree => ?_)
  rw [members, mem_hypothesisTrees]
  constructor
  · rintro ⟨⟨source, member, rfl⟩, different⟩
    exact ⟨source, Finset.mem_erase.mpr ⟨fun same => different (congrArg encodeCanonical same), member⟩, rfl⟩
  · rintro ⟨source, member, rfl⟩
    obtain ⟨different, member⟩ := Finset.mem_erase.mp member
    exact ⟨⟨source, member, rfl⟩, fun same => different (encodeCanonical_injective same)⟩

/-- The rendered image of a hypothesis set under a term action, sorted, is the rendering of the
image set. -/
theorem image_hypotheses {mapped sorted : Pattern} {hypotheses : Finset CanonicalTerm}
    {action : DBTerm → DBTerm} {apply : CanonicalTerm → CanonicalTerm}
    (applied : ∀ term, (apply term).term = action term.term)
    (mappedEq : mapped = termsP (((sortedHypotheses hypotheses).map CanonicalTerm.term).map action))
    (sortedMeaning : SortMeaning mapped sorted) :
    sorted = treesP (hypothesisTrees (hypotheses.image apply)) := by
  obtain ⟨trees, rfl, increasing, members⟩ := sortedMeaning _ (mappedEq.trans (termsP_eq_treesP _))
  refine congrArg treesP (hypothesisTrees_unique increasing fun tree => ?_)
  rw [members]
  simp only [List.map_map, List.mem_map, Function.comp_apply, sortedHypotheses, Finset.mem_sort,
    Finset.mem_image, encodeCanonical]
  constructor
  · rintro ⟨term, member, rfl⟩
    exact ⟨apply term, ⟨term, member, rfl⟩, by rw [applied]⟩
  · rintro ⟨_, ⟨term, member, rfl⟩, rfl⟩
    exact ⟨term, member, by rw [applied]⟩

/-! ## Checked terms built by the inference rules -/

/-- The equality of two checked terms of one type. -/
def equalityTerm (left right : CanonicalTerm) (types : left.ty = right.ty) : CanonicalTerm :=
  ⟨CanonicalTerm.equalityDB left.ty left.term right.term, Ty.bool,
    DBTerm.inferType_equalityDB_iff.mpr ⟨left.checked, right.checked.trans (congrArg some types.symm), rfl⟩⟩

theorem equalityTerm_construction (left right : CanonicalTerm) (types : left.ty = right.ty) :
    CanonicalTerm.EqualityConstructionSemantics left right (equalityTerm left right types) := ⟨types, rfl⟩

/-- A checked application of a function to an argument of its domain. -/
def applicationTerm (function argument : CanonicalTerm) (codomain : Ty)
    (typed : function.ty = Ty.function argument.ty codomain) : CanonicalTerm :=
  ⟨.app function.term argument.term, codomain,
    DBTerm.inferType_app_eq_some_iff.mpr
      ⟨argument.ty, function.checked.trans (congrArg some typed), argument.checked⟩⟩

theorem applicationTerm_semantics (function argument : CanonicalTerm) (codomain : Ty)
    (typed : function.ty = Ty.function argument.ty codomain) :
    CanonicalTerm.ApplicationSemantics function argument (applicationTerm function argument codomain typed) :=
  ⟨argument.ty, codomain, by rw [typed, Ty.destFunction?_function], rfl, rfl⟩

/-- A theorem whose rendered conclusion has the shape of an equality: its checked operands. -/
theorem conclusion_equality {out : Theorem} {type left right : Pattern}
    (same : equalityTermP type left right = sequentConclusionP out.sequent) :
    ∃ first second : CanonicalTerm, CanonicalTerm.EqualityViewSemantics out.sequent.concl first second ∧
      type = groundP (encodeTy first.ty) ∧ left = groundP (encodeCanonical first) ∧
        right = groundP (encodeCanonical second) := by
  obtain ⟨operand, leftTerm, rightTerm, shape, rfl, rfl, rfl⟩ :=
    groundP_encodeTerm_eq_equalityTermP same.symm
  have typed := out.sequent.concl.checked
  rw [shape] at typed
  obtain ⟨leftTyped, rightTyped, -⟩ := DBTerm.inferType_equalityDB_iff.mp typed
  exact ⟨⟨leftTerm, operand, leftTyped⟩, ⟨rightTerm, operand, rightTyped⟩, ⟨rfl, shape⟩, rfl, rfl, rfl⟩

/-- An encoded term with the shape of a trivial beta redex. -/
theorem encodeTerm_eq_betaRedex {term : DBTerm} {type body name : Pattern}
    (same : groundP (encodeTerm term) = appTermP (absTermP type body) (freeTermP name type)) :
    ∃ (bodyTerm : DBTerm) (argument : SourceVar), term = .app (.abs argument.ty bodyTerm) (.free argument) ∧
      type = groundP (encodeTy argument.ty) ∧ body = groundP (encodeTerm bodyTerm) ∧
        name = groundP (encodeName argument.name) := by
  obtain ⟨functionTerm, argumentTerm, rfl, functionEq, argumentEq⟩ := encodeTerm_eq_app same
  obtain ⟨domain, bodyTerm, rfl, rfl, rfl⟩ := encodeTerm_eq_abs functionEq.symm
  obtain ⟨argument, rfl, nameEq, typeEq⟩ := encodeTerm_eq_free argumentEq.symm
  obtain rfl := encodeTy_injective _ _ (groundP_injective typeEq)
  exact ⟨bodyTerm, argument, rfl, rfl, rfl, nameEq⟩

theorem applyDB_typeOnly (entries : List (Ty × Ty)) : ∀ term : DBTerm,
    (TermSubst.mk (SourceSubstitution.typeSubstitution entries) []).applyDB term = termTypeAction entries term
  | .const constant type => by simp [SourceSubstitution.apply_type, termTypeAction]
  | .free sourceVar => by
      rw [TermSubst.applyDB_free_of_lookup_none _ _ rfl]
      simp [TypeSubst.applyVar, SourceSubstitution.apply_type, termTypeAction]
  | .bound index => by simp [termTypeAction]
  | .app function argument => by
      simp only [TermSubst.applyDB_app, applyDB_typeOnly entries function, applyDB_typeOnly entries argument,
        termTypeAction]
  | .abs domain body => by
      simp only [TermSubst.applyDB_abs, applyDB_typeOnly entries body, SourceSubstitution.apply_type,
        termTypeAction]

/-! ## Derivations of HOL Light -/

theorem derives_inference {policy : AxiomPolicy} (request : InferenceRequest) {out : Theorem}
    (semantics : request.Semantics out)
    (children : ∀ premise ∈ request.premises, Derives (Rule policy) premise) : Derives (Rule policy) out :=
  Derives.node request.premises out (Or.inl ⟨request, rfl, semantics⟩) children

theorem children_nil {rules : List Theorem → Theorem → Prop} :
    ∀ premise ∈ ([] : List Theorem), Derives rules premise := fun _ member => by simp at member

theorem children_one {rules : List Theorem → Theorem → Prop} {first : Theorem} (derived : Derives rules first) :
    ∀ premise ∈ [first], Derives rules premise := by
  intro premise member
  rcases List.mem_singleton.mp member with rfl
  exact derived

theorem children_two {rules : List Theorem → Theorem → Prop} {first second : Theorem}
    (firstDerived : Derives rules first) (secondDerived : Derives rules second) :
    ∀ premise ∈ [first, second], Derives rules premise := by
  intro premise member
  rcases List.mem_cons.mp member with rfl | member
  · exact firstDerived
  · rcases List.mem_singleton.mp member with rfl
    exact secondDerived

/-! ## The meaning of each inference rule -/

theorem refl_meaning (policy : AxiomPolicy) {t a : Pattern} (typed : TypeOfMeaning nilP t a) :
    ThmMeaning policy nilP (equalityTermP a t t) := by
  obtain ⟨termValue, typeValue, rfl, rfl, typedValue⟩ := typed [] rfl
  let term : CanonicalTerm := ⟨termValue, typeValue, typedValue⟩
  refine ⟨Theorem.emptyResult ∅ (equalityTerm term term rfl),
    derives_inference (.refl term) ⟨_, equalityTerm_construction term term rfl, rfl, rfl, rfl⟩ children_nil,
    ?_, rfl⟩
  rw [sequentHypothesesP_eq_treesP]
  show nilP = treesP (hypothesisTrees ∅)
  rw [hypothesisTrees_empty]
  rfl

theorem assume_meaning (policy : AxiomPolicy) {t : Pattern} (typed : TypeOfMeaning nilP t boolP) :
    ThmMeaning policy (consP t nilP) t := by
  obtain ⟨termValue, typeValue, rfl, boolEq, typedValue⟩ := typed [] rfl
  obtain rfl : typeValue = Ty.bool := encodeTy_injective _ _ (groundP_injective boolEq.symm)
  let term : CanonicalTerm := ⟨termValue, Ty.bool, typedValue⟩
  refine ⟨Theorem.emptyResult {term} term,
    derives_inference (.assume term) ⟨rfl, rfl, rfl, rfl⟩ children_nil, ?_, rfl⟩
  rw [sequentHypothesesP_eq_treesP]
  show _ = treesP (hypothesisTrees {term})
  rw [hypothesisTrees_singleton]
  rfl

theorem trans_meaning (policy : AxiomPolicy) {h1 h2 h a l m r : Pattern}
    (leftHolds : ThmMeaning policy h1 (equalityTermP a l m)) (rightHolds : ThmMeaning policy h2 (equalityTermP a m r))
    (union : UnionMeaning h1 h2 h) : ThmMeaning policy h (equalityTermP a l r) := by
  obtain ⟨left, leftDerived, rfl, leftConcl⟩ := leftHolds
  obtain ⟨right, rightDerived, rfl, rightConcl⟩ := rightHolds
  obtain ⟨first, middle, firstView, rfl, rfl, rfl⟩ := conclusion_equality leftConcl
  obtain ⟨middle', last, lastView, -, middleEq, rfl⟩ := conclusion_equality rightConcl
  obtain rfl : middle = middle' := encodeCanonical_injective (groundP_injective middleEq)
  have types : first.ty = last.ty := firstView.1.trans lastView.1
  let out := Theorem.unionResult left right (left.sequent.hyp ∪ right.sequent.hyp) (equalityTerm first last types)
  refine ⟨out,
    derives_inference (.trans left right)
      ⟨first, middle, middle, last, _, firstView, lastView, rfl, equalityTerm_construction first last types,
        rfl, rfl, rfl⟩
      (children_two leftDerived rightDerived), ?_, rfl⟩
  exact (union_hypotheses union (sequentHypothesesP_eq_treesP _) (sequentHypothesesP_eq_treesP _)).trans
    (sequentHypothesesP_eq_treesP out.sequent).symm

theorem mkComb_meaning (policy : AxiomPolicy) {h1 h2 h a b f g x y : Pattern}
    (functionHolds : ThmMeaning policy h1 (equalityTermP (functionTyP a b) f g))
    (argumentHolds : ThmMeaning policy h2 (equalityTermP a x y)) (union : UnionMeaning h1 h2 h) :
    ThmMeaning policy h (equalityTermP b (appTermP f x) (appTermP g y)) := by
  obtain ⟨functionTheorem, functionDerived, rfl, functionConcl⟩ := functionHolds
  obtain ⟨argumentTheorem, argumentDerived, rfl, argumentConcl⟩ := argumentHolds
  obtain ⟨leftFunction, rightFunction, functionView, functionType, rfl, rfl⟩ := conclusion_equality functionConcl
  obtain ⟨domain, codomain, functionTyEq, rfl, rfl⟩ := encodeTy_eq_function functionType.symm
  obtain ⟨leftArgument, rightArgument, argumentView, argumentType, rfl, rfl⟩ := conclusion_equality argumentConcl
  have domainEq : leftArgument.ty = domain := (encodeTy_injective _ _ (groundP_injective argumentType)).symm
  have leftTyped : leftFunction.ty = Ty.function leftArgument.ty codomain := by rw [functionTyEq, domainEq]
  have rightTyped : rightFunction.ty = Ty.function rightArgument.ty codomain := by
    rw [← functionView.1, functionTyEq, ← argumentView.1, domainEq]
  let leftApplication := applicationTerm leftFunction leftArgument codomain leftTyped
  let rightApplication := applicationTerm rightFunction rightArgument codomain rightTyped
  let out := Theorem.unionResult functionTheorem argumentTheorem
    (functionTheorem.sequent.hyp ∪ argumentTheorem.sequent.hyp) (equalityTerm leftApplication rightApplication rfl)
  refine ⟨out,
    derives_inference (.mkComb functionTheorem argumentTheorem)
      ⟨leftFunction, rightFunction, leftArgument, rightArgument, leftApplication, rightApplication, _,
        functionView, argumentView, applicationTerm_semantics _ _ _ _, applicationTerm_semantics _ _ _ _,
        equalityTerm_construction leftApplication rightApplication rfl, rfl, rfl, rfl⟩
      (children_two functionDerived argumentDerived), ?_, rfl⟩
  exact (union_hypotheses union (sequentHypothesesP_eq_treesP _) (sequentHypothesesP_eq_treesP _)).trans
    (sequentHypothesesP_eq_treesP out.sequent).symm

theorem abs_meaning (policy : AxiomPolicy) {h a s t x b s2 t2 : Pattern}
    (inputHolds : ThmMeaning policy h (equalityTermP a s t)) (named : ∃ name : Name, x = groundP (encodeName name))
    (typedBinder : ∃ type : Ty, b = groundP (encodeTy type)) (fresh : NotFreeAllMeaning (freeTermP x b) h)
    (leftClosed : CloseMeaning (freeTermP x b) unaryZeroP s s2)
    (rightClosed : CloseMeaning (freeTermP x b) unaryZeroP t t2) :
    ThmMeaning policy h (equalityTermP (functionTyP b a) (absTermP b s2) (absTermP b t2)) := by
  obtain ⟨input, inputDerived, rfl, inputConcl⟩ := inputHolds
  obtain ⟨name, rfl⟩ := named
  obtain ⟨binderType, rfl⟩ := typedBinder
  obtain ⟨left, right, view, rfl, rfl, rfl⟩ := conclusion_equality inputConcl
  let binder : SourceVar := ⟨name, binderType⟩
  obtain rfl := leftClosed binder 0 left.term rfl rfl rfl
  obtain rfl := rightClosed binder 0 right.term rfl rfl rfl
  have notFree : ¬ FreeInHypotheses binder input.sequent.hyp := by
    rintro ⟨term, member, occurs⟩
    have absent := fresh binder ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term)
      rfl (sequentHypothesesP_eq_termsP _) term.term
      (List.mem_map.mpr ⟨term, by simpa [sortedHypotheses] using member, rfl⟩)
    have present := (DBTerm.hasFree_eq_true_iff _ _).mpr occurs
    rw [absent] at present
    cases present
  have types : (left.abstractFree binder).ty = (right.abstractFree binder).ty :=
    congrArg (Ty.function binderType) view.1
  refine ⟨Theorem.preserveAxiomsResult input input.sequent.hyp
      (equalityTerm (left.abstractFree binder) (right.abstractFree binder) types),
    derives_inference (.abs binder input)
      ⟨notFree, left, right, left.abstractFree binder, right.abstractFree binder,
        _, view, rfl, rfl, equalityTerm_construction _ _ types, rfl, rfl, rfl⟩
      (children_one inputDerived), rfl, rfl⟩

theorem beta_meaning (policy : AxiomPolicy) {x a t body u reduced : Pattern}
    (converted : ToDBMeaning nilP (sourceAppP (sourceAbsP x a t) (sourceVarP x a))
      (appTermP (absTermP a body) (freeTermP x a)))
    (typed : TypeOfMeaning nilP (appTermP (absTermP a body) (freeTermP x a)) u)
    (instantiated : InstantiateMeaning (freeTermP x a) unaryZeroP body reduced) :
    ThmMeaning policy nilP (equalityTermP u (appTermP (absTermP a body) (freeTermP x a)) reduced) := by
  obtain ⟨sourceValue, termValue, sourceEq, termEq, toDBEq⟩ := converted [] rfl
  obtain ⟨bodyTerm, argument, rfl, rfl, rfl, rfl⟩ := encodeTerm_eq_betaRedex termEq.symm
  obtain ⟨redexTerm, resultType, redexEq, rfl, inferred⟩ := typed [] rfl
  have redexEq' : groundP (encodeTerm (.app (.abs argument.ty bodyTerm) (.free argument))) =
      groundP (encodeTerm redexTerm) := redexEq
  obtain rfl := encodeTerm_injective (groundP_injective redexEq')
  obtain rfl := instantiated (.free argument) 0 bodyTerm rfl rfl rfl
  obtain ⟨functionSource, argumentSource, rfl, functionEq, argumentEq⟩ := encodeSourceTerm_eq_app sourceEq.symm
  obtain ⟨name, binderType, bodySource, rfl, nameEq, typeEq, rfl⟩ := encodeSourceTerm_eq_abs functionEq.symm
  obtain rfl := encodeName_injective (groundP_injective nameEq)
  obtain rfl := encodeTy_injective _ _ (groundP_injective typeEq)
  obtain ⟨name', binderType', rfl, nameEq', typeEq'⟩ := encodeSourceTerm_eq_var argumentEq.symm
  obtain rfl := encodeName_injective (groundP_injective nameEq')
  obtain rfl := encodeTy_injective _ _ (groundP_injective typeEq')
  have checked : SourceTerm.inferType (.app (.abs argument.name argument.ty bodySource)
      (.var argument.name argument.ty)) = some resultType := by
    rw [← DBTerm.inferType_toDB [] _, toDBEq]
    exact inferred
  let source : CheckedSourceTerm := ⟨_, resultType, checked⟩
  obtain ⟨domain, absTyped, -⟩ := DBTerm.inferType_app_eq_some_iff.mp inferred
  obtain ⟨codomain, bodyTyped, functionTypes⟩ := DBTerm.inferType_abs_eq_some_iff.mp absTyped
  obtain ⟨-, rfl⟩ := Ty.function_inj functionTypes
  have argumentChecked : DBTerm.inferType [] (.free argument) = some argument.ty := by
    simp [DBTerm.inferType]
  let argumentTerm : CanonicalTerm := ⟨.free argument, argument.ty, argumentChecked⟩
  let reducedTerm : CanonicalTerm :=
    ⟨DBTerm.instantiateAt (.free argument) 0 bodyTerm, resultType,
      DBTerm.inferType_instantiateAt (.free argument) bodyTerm argument.ty argumentChecked [] bodyTyped⟩
  refine ⟨Theorem.emptyResult ∅ (equalityTerm source.canonical reducedTerm rfl),
    derives_inference (.beta source)
      ⟨⟨rfl, rfl⟩, reducedTerm, _, ⟨argument.ty, bodyTerm, argumentTerm, toDBEq, rfl⟩,
        equalityTerm_construction source.canonical reducedTerm rfl, rfl, rfl, rfl⟩ children_nil, ?_, ?_⟩
  · rw [sequentHypothesesP_eq_treesP]
    show nilP = treesP (hypothesisTrees ∅)
    rw [hypothesisTrees_empty]
    rfl
  · show _ = groundP (encodeTerm (CanonicalTerm.equalityDB resultType source.canonical.term reducedTerm.term))
    rw [show source.canonical.term = _ from toDBEq]
    rfl

theorem eqMp_meaning (policy : AxiomPolicy) {h1 h2 h a p q : Pattern}
    (equalityHolds : ThmMeaning policy h1 (equalityTermP a p q)) (premiseHolds : ThmMeaning policy h2 p)
    (union : UnionMeaning h1 h2 h) : ThmMeaning policy h q := by
  obtain ⟨equality, equalityDerived, rfl, equalityConcl⟩ := equalityHolds
  obtain ⟨premise, premiseDerived, rfl, premiseConcl⟩ := premiseHolds
  obtain ⟨left, right, view, -, rfl, rfl⟩ := conclusion_equality equalityConcl
  have same : left = premise.sequent.concl := encodeCanonical_injective (groundP_injective premiseConcl)
  let out := Theorem.unionResult equality premise (equality.sequent.hyp ∪ premise.sequent.hyp) right
  refine ⟨out,
    derives_inference (.eqMp equality premise) ⟨left, right, view, same, rfl, rfl, rfl⟩
      (children_two equalityDerived premiseDerived), ?_, rfl⟩
  exact (union_hypotheses union (sequentHypothesesP_eq_treesP _) (sequentHypothesesP_eq_treesP _)).trans
    (sequentHypothesesP_eq_treesP out.sequent).symm

theorem deductAntisym_meaning (policy : AxiomPolicy) {h1 h2 k1 k2 h p q a : Pattern}
    (leftHolds : ThmMeaning policy h1 p) (rightHolds : ThmMeaning policy h2 q)
    (leftTyped : TypeOfMeaning nilP p a) (rightTyped : TypeOfMeaning nilP q a)
    (leftErase : EraseMeaning q h1 k1) (rightErase : EraseMeaning p h2 k2) (union : UnionMeaning k1 k2 h) :
    ThmMeaning policy h (equalityTermP a p q) := by
  obtain ⟨left, leftDerived, rfl, rfl⟩ := leftHolds
  obtain ⟨right, rightDerived, rfl, rfl⟩ := rightHolds
  obtain ⟨leftTerm, leftType, leftEq, rfl, leftInferred⟩ := leftTyped [] rfl
  obtain rfl : left.sequent.concl.term = leftTerm := encodeTerm_injective (groundP_injective leftEq)
  obtain rfl : left.sequent.concl.ty = leftType :=
    Option.some.inj (left.sequent.concl.checked.symm.trans leftInferred)
  obtain ⟨rightTerm, rightType, rightEq, rightTypeEq, rightInferred⟩ := rightTyped [] rfl
  obtain rfl : right.sequent.concl.term = rightTerm := encodeTerm_injective (groundP_injective rightEq)
  obtain rfl : right.sequent.concl.ty = rightType :=
    Option.some.inj (right.sequent.concl.checked.symm.trans rightInferred)
  have types : left.sequent.concl.ty = right.sequent.concl.ty :=
    encodeTy_injective _ _ (groundP_injective rightTypeEq)
  have leftKept := erase_hypotheses leftErase rfl (sequentHypothesesP_eq_treesP _)
  have rightKept := erase_hypotheses rightErase rfl (sequentHypothesesP_eq_treesP _)
  let out := Theorem.unionResult left right
    ((left.sequent.hyp.erase right.sequent.concl) ∪ (right.sequent.hyp.erase left.sequent.concl))
    (equalityTerm left.sequent.concl right.sequent.concl types)
  refine ⟨out,
    derives_inference (.deductAntisym left right) ⟨_, equalityTerm_construction _ _ types, rfl, rfl, rfl⟩
      (children_two leftDerived rightDerived), ?_, rfl⟩
  exact (union_hypotheses union leftKept rightKept).trans (sequentHypothesesP_eq_treesP out.sequent).symm

theorem inst_meaning (policy : AxiomPolicy) {h c ms table h1 h2 c2 : Pattern}
    (inputHolds : ThmMeaning policy h c) (admittedMaplets : AdmitTmMeaning ms table)
    (appliedHypotheses : TmApplyListMeaning table h h1) (sorted : SortMeaning h1 h2)
    (appliedConclusion : TmApplyMeaning table c c2) : ThmMeaning policy h2 c2 := by
  obtain ⟨input, inputDerived, rfl, rfl⟩ := inputHolds
  obtain ⟨maplets, rfl, admissible, rfl⟩ := admittedMaplets
  obtain ⟨substitution, admitted⟩ := Option.isSome_iff_exists.mp
    ((SourceSubstitution.admitTermSubstitution_isSome_iff maplets).mpr admissible)
  have action : ∀ term : DBTerm,
      substitution.raw.applyDB term = tableAction (SourceSubstitution.termEntries maplets) term := by
    intro term
    rw [SourceSubstitution.admittedTermSubstitution_raw admitted]
    rfl
  obtain rfl := appliedHypotheses (SourceSubstitution.termEntries maplets)
    ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term) rfl (sequentHypothesesP_eq_termsP _)
  obtain rfl := appliedConclusion (SourceSubstitution.termEntries maplets) input.sequent.concl.term rfl rfl
  obtain rfl := image_hypotheses (apply := substitution.apply) (fun term => action term.term) rfl sorted
  let out := substituteTheorem substitution input
  refine ⟨out,
    derives_inference (.inst maplets input) ⟨substitution, admitted, substituteTheorem_semantics substitution input⟩
      (children_one inputDerived), (sequentHypothesesP_eq_treesP out.sequent).symm, ?_⟩
  show _ = groundP (encodeTerm (substitution.raw.applyDB input.sequent.concl.term))
  rw [action]

theorem instType_meaning (policy : AxiomPolicy) {h c es h1 h2 c2 : Pattern}
    (inputHolds : ThmMeaning policy h c) (entriesHold : ∃ entries : List (Ty × Ty), es = typeMapletsP entries)
    (appliedHypotheses : TermTyActListMeaning es h h1) (sorted : SortMeaning h1 h2)
    (appliedConclusion : TermTyActMeaning es c c2) : ThmMeaning policy h2 c2 := by
  obtain ⟨input, inputDerived, rfl, rfl⟩ := inputHolds
  obtain ⟨entries, rfl⟩ := entriesHold
  obtain rfl := appliedHypotheses entries ((sortedHypotheses input.sequent.hyp).map CanonicalTerm.term) rfl
    (sequentHypothesesP_eq_termsP _)
  obtain rfl := appliedConclusion entries input.sequent.concl.term rfl rfl
  let substitution := SourceSubstitution.typeOnlySubstitution entries
  obtain rfl := image_hypotheses (apply := substitution.apply)
    (fun term => applyDB_typeOnly entries term.term) rfl sorted
  let out := substituteTheorem substitution input
  refine ⟨out,
    derives_inference (.instType entries input) (substituteTheorem_semantics substitution input)
      (children_one inputDerived), (sequentHypothesesP_eq_treesP out.sequent).symm, ?_⟩
  show _ = groundP (encodeTerm (substitution.raw.applyDB input.sequent.concl.term))
  rw [show substitution.raw.applyDB input.sequent.concl.term = termTypeAction entries input.sequent.concl.term
    from applyDB_typeOnly entries _]

/-! ## The inference rules -/

theorem inferenceRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ inferenceRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [inferenceRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [t, a], _ => rule_simp; exact refl_meaning policy premisesHold
  · match arguments, arity with
    | [t], _ => rule_simp; exact assume_meaning policy premisesHold
  · match arguments, arity with
    | [h1, h2, h, a, l, m, r], _ =>
        rule_simp
        obtain ⟨leftHolds, rightHolds, union⟩ := premisesHold
        exact trans_meaning policy leftHolds rightHolds union
  · match arguments, arity with
    | [h1, h2, h, a, b, f, g, x, y], _ =>
        rule_simp
        obtain ⟨functionHolds, argumentHolds, union⟩ := premisesHold
        exact mkComb_meaning policy functionHolds argumentHolds union
  · match arguments, arity with
    | [h, a, s, t, x, b, s2, t2], _ =>
        rule_simp
        obtain ⟨inputHolds, named, typedBinder, fresh, leftClosed, rightClosed⟩ := premisesHold
        exact abs_meaning policy inputHolds named typedBinder fresh leftClosed rightClosed
  · match arguments, arity with
    | [x, a, t, body, u, reduced], _ =>
        rule_simp
        obtain ⟨converted, typed, instantiated⟩ := premisesHold
        exact beta_meaning policy converted typed instantiated
  · match arguments, arity with
    | [h1, h2, h, a, p, q], _ =>
        rule_simp
        obtain ⟨equalityHolds, premiseHolds, union⟩ := premisesHold
        exact eqMp_meaning policy equalityHolds premiseHolds union
  · match arguments, arity with
    | [h1, h2, k1, k2, h, p, q, a], _ =>
        rule_simp
        obtain ⟨leftHolds, rightHolds, leftTyped, rightTyped, leftErase, rightErase, union⟩ := premisesHold
        exact deductAntisym_meaning policy leftHolds rightHolds leftTyped rightTyped leftErase rightErase union

theorem instantiationRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ instantiationRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩ := applied
  simp only [instantiationRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    obtain ⟨arity, rfl, rfl⟩ := rule_application (by decide +kernel) valid premisesInstantiate conclusionInstantiates <;>
    clear valid premisesInstantiate conclusionInstantiates
  · match arguments, arity with
    | [h, c, ms, table, h1, h2, c2], _ =>
        rule_simp
        obtain ⟨inputHolds, admittedMaplets, appliedHypotheses, sorted, appliedConclusion⟩ := premisesHold
        exact inst_meaning policy inputHolds admittedMaplets appliedHypotheses sorted appliedConclusion
  · match arguments, arity with
    | [h, c, es, h1, h2, c2], _ =>
        rule_simp
        obtain ⟨inputHolds, entriesHold, appliedHypotheses, sorted, appliedConclusion⟩ := premisesHold
        exact instType_meaning policy inputHolds entriesHold appliedHypotheses sorted appliedConclusion

/-! ## Axioms and the order rules -/

theorem treesP_eq_toPatternList (trees : List LabeledTree) : treesP trees = LabeledTree.toPatternList trees :=
  (toPatternList_eq_listP trees).symm

theorem substSchema_sequentJ (values : String → Pattern) (sequent : Sequent) :
    substSchema values (sequentJ sequent) = sequentJ sequent := by
  simp only [sequentJ, thmJ, substSchema, substSchemas, sequentHypothesesP_eq_treesP, treesP_eq_toPatternList,
    substSchema_toPatternList, sequentConclusionP, substSchema_groundP]

theorem checkSchema_sequentJ (names : List String) (sequent : Sequent) :
    checkSchema names (sequentJ sequent) = true := by
  simp [sequentJ, thmJ, checkSchema, checkSchemas, sequentHypothesesP_eq_treesP, treesP_eq_toPatternList,
    checkSchema_toPatternList, sequentConclusionP, groundP, checkSchema_toPattern]

/-- **The axiom rules are sound for the policy that admits their sequents.** -/
theorem axiomRules_closed (policy : AxiomPolicy) {axioms : List Sequent}
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    {r : RuleSchema} (member : r ∈ axiomRules axioms)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  obtain ⟨valid, premisesInstantiate, conclusionInstantiates, -⟩ := applied
  simp only [axiomRules, List.mem_map] at member
  obtain ⟨⟨sequent, index⟩, sequentMember, rfl⟩ := member
  obtain ⟨-, -, rfl⟩ := rule_application ⟨by simp [checkSchemas], checkSchema_sequentJ [] sequent⟩ valid premisesInstantiate
    conclusionInstantiates
  obtain ⟨empty, allowed, isBool⟩ := admitted sequent (List.fst_mem_of_mem_zipIdx sequentMember)
  rw [substSchema_sequentJ, sequentJ, thmJ, holMeaning_Thm]
  refine ⟨⟨{sequent}, fun tagged member => by rw [Finset.mem_singleton.mp member]; exact isBool, sequent⟩,
    Derives.node [] _ (Or.inr ⟨sequent, rfl, empty, allowed, isBool, rfl, rfl, rfl⟩) children_nil, rfl, rfl⟩

theorem orderRules_closed (policy : AxiomPolicy) {r : RuleSchema} (member : r ∈ orderRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion :=
  orderRule_closed (meaning := holMeaning policy) (holMeaning_treeBelow policy) (holMeaning_treeLt policy)
    (holMeaning_treeLtList policy) member applied.valid applied.premisesInstantiate applied.conclusionInstantiates
    applied.premisesHold

/-! ## Soundness -/

/-- **Every rule of the calculus preserves the meaning of its judgments.** -/
theorem holRules_closed (policy : AxiomPolicy) {axioms : List Sequent}
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    {r : RuleSchema} (member : r ∈ holRules axioms)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (applied : Applied policy r arguments premises conclusion) : holMeaning policy conclusion := by
  simp only [holRules, List.mem_append, or_assoc] at member
  rcases member with member | member | member | member | member | member | member | member | member |
    member | member | member | member | member | member | member | member
  · exact orderRules_closed policy member applied
  · exact neqRules_closed policy member applied
  · exact nthRules_closed policy member applied
  · exact typeRules_closed policy member applied
  · exact binderRules_closed policy member applied
  · exact toDBRules_closed policy member applied
  · exact notFreeRules_closed policy member applied
  · exact wellFormedRules_closed policy member applied
  · exact closeRules_closed policy member applied
  · exact instantiateRules_closed policy member applied
  · exact setRules_closed policy member applied
  · exact sortRules_closed policy member applied
  · exact typeActionRules_closed policy member applied
  · exact termActionRules_closed policy member applied
  · exact inferenceRules_closed policy member applied
  · exact instantiationRules_closed policy member applied
  · exact axiomRules_closed policy admitted member applied

/-- **Soundness.** Every judgment derivable in HOL Light's first-order calculus holds; in
particular every derivable `Thm` judgment renders a sequent that HOL Light's kernel derives. -/
theorem holCalculus_sound (policy : AxiomPolicy) {axioms : List Sequent}
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    {definition : ValidatedCalculusLanguageDef} (calculus : definition.1 = holCalculus axioms)
    {goal : Pattern} (derivation : Derivation definition goal) : holMeaning policy goal := by
  refine Derivation.sound_of_ruleApplications (holMeaning policy) ?_ derivation
  rintro ruleInstance premises conclusion ⟨rule, lookup, valid, -, premisesInstantiate, conclusionInstantiates⟩
    premisesHold
  have member : rule ∈ holRules axioms := by
    have found := List.mem_of_find?_eq_some lookup
    rw [calculus] at found
    exact found
  exact holRules_closed policy admitted member ⟨valid, premisesInstantiate, conclusionInstantiates, premisesHold⟩

/-- **A derivable rendered sequent is a theorem of HOL Light.** -/
theorem holCalculus_sound_sequent (policy : AxiomPolicy) {axioms : List Sequent}
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    {definition : ValidatedCalculusLanguageDef} (calculus : definition.1 = holCalculus axioms)
    {sequent : Sequent} (derivation : Derivation definition (sequentJ sequent)) :
    ∃ out : Theorem, Derives (Rule policy) out ∧ out.sequent = sequent := by
  obtain ⟨out, derived, hypotheses, conclusions⟩ :=
    (holMeaning_Thm policy _ _).mp (holCalculus_sound policy admitted calculus derivation)
  exact ⟨out, derived, (sequent_of_rendering hypotheses conclusions).symm⟩

end Mettapedia.Languages.HOLLight.FirstOrder
