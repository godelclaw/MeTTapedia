import Mettapedia.Languages.MM0.Translation.CertificateEquivalence
import Mettapedia.GSLT.LanguageDef.PartialRecursivePresentation
import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

/-!
# MM0 and the first-order calculi of the inference checker

The generic inference checker of `GSLT.LanguageDef` reads a raw proof tree of rule
instances over a validated calculus (`InferenceChecker.checkRaw`). On first-order calculi,
it and MM0 check the same claims with certificates of linearly related size: they
p-simulate each other (`pEquivalent`).

A calculus is first-order when every metavariable has arity zero, every premise and
conclusion schema is built from constructors and metavariables, no rule has side
conditions, and rule identifiers are distinct (`FirstOrderCalculus`, checked by
`firstOrderCheck`). Its claims are first-order patterns. The arguments of its proofs may
still be any ground patterns, binders included.

* **One grammar for all patterns.** Patterns are encoded as terms of one fixed sorted
  grammar: a constructor name is a list of character codes in bijective binary, and
  arguments form a list (`universalLanguage`, `patP`). Every node that is not a
  constructor application becomes the empty application. Decoding is total and inverts
  the encoding on first-order patterns (`patValue_patP`).
* **One presentation per calculus.** Each rule becomes a sorted first-order rule over the
  grammar, with its metavariables of sort `pat` (`encodeRule`). The rules are admitted for
  every first-order calculus (`presentation_check`), so MM0 compiles them.
* **The same proofs.** A proof the checker accepts encodes to a tree the presentation
  accepts (`encode_accepted`). Binder nodes inside arguments may collapse in the encoding:
  a first-order rule never looks inside them, so the encoded tree still proves the same
  claim. A tree the presentation accepts decodes to a proof the checker accepts
  (`decode_accepted`); decoded arguments are constructor applications, hence ground.
* **Sizes.** A proof is measured by its nodes, its argument edges and the characters of its
  constructor names, with binder nodes counted once (`proofWeight`). An encoded tree is at
  most twenty-two times the proof, since a character code has at most twenty-one bits
  (`rawSize_encodeProof`), and a decoded proof is at most twice the tree
  (`proofWeight_decodeProof`). Translation times are charged one unit per node read and
  per node written.
* **MM0.** Composing with `CertificateSimulation.compileSimulation` and
  `CertificateEquivalence.decompileSimulation` gives the two p-simulations with MM0
  (`mm0Simulation`, `calculusSimulation`). A checker whose certificates translate into
  such a calculus within polynomial bounds is therefore p-simulated by MM0
  (`traceSimulation`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.CalculusSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules
open CertificateSimulation (patternSize patternSizes rawSize rawSizes)

/-! ## The grammar -/

abbrev numSort : TypeExpr := .base "num"
abbrev strSort : TypeExpr := .base "str"
abbrev patSort : TypeExpr := .base "pat"
abbrev patsSort : TypeExpr := .base "pats"
abbrev wffSort : TypeExpr := .base "wff"

/-- Numerals in bijective binary, strings of character codes, first-order patterns and
their lists, and one sort of judgments. -/
def universalLanguage : LanguageDef :=
  { name := "FirstOrderPatterns"
    types := [TypeDecl.plain "num", TypeDecl.plain "str", TypeDecl.plain "pat",
      TypeDecl.plain "pats", TypeDecl.plain "wff"]
    terms := [
      PartialRecursive.former "nz" "num" [],
      PartialRecursive.former "n1" "num" [numSort],
      PartialRecursive.former "n2" "num" [numSort],
      PartialRecursive.former "snil" "str" [],
      PartialRecursive.former "scons" "str" [numSort, strSort],
      PartialRecursive.former "papply" "pat" [strSort, patsSort],
      PartialRecursive.former "pnil" "pats" [],
      PartialRecursive.former "pcons" "pats" [patSort, patsSort],
      PartialRecursive.former "holds" "wff" [patSort]]
    equations := []
    rewrites := [] }

/-! ## Numerals -/

/-- The bijective binary numeral of a number: `n1 k` is `2k + 1`, `n2 k` is `2k + 2`. -/
def numP : ℕ → Pattern
  | 0 => .apply "nz" []
  | n + 1 =>
      if n % 2 = 0 then .apply "n1" [numP (n / 2)] else .apply "n2" [numP (n / 2)]
termination_by n => n
decreasing_by all_goals omega

/-- The number a numeral denotes; other patterns denote zero. -/
def numValue : Pattern → ℕ
  | .apply "n1" [k] => 2 * numValue k + 1
  | .apply "n2" [k] => 2 * numValue k + 2
  | _ => 0
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem numValue_numP (n : ℕ) : numValue (numP n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => simp [numP, numValue]
      | succ n =>
          rw [numP]
          split
          · rw [numValue, ih (n / 2) (by omega)]
            omega
          · rw [numValue, ih (n / 2) (by omega)]
            omega

/-! ## Strings -/

/-- The string of a list of characters, one numeral per character code. -/
def strP : List Char → Pattern
  | [] => .apply "snil" []
  | c :: cs => .apply "scons" [numP c.toNat, strP cs]

/-- The characters a string term denotes. -/
def strValue : Pattern → List Char
  | .apply "scons" [c, rest] => Char.ofNat (numValue c) :: strValue rest
  | _ => []
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem strValue_strP : ∀ cs : List Char, strValue (strP cs) = cs
  | [] => by simp [strP, strValue]
  | c :: cs => by rw [strP, strValue, numValue_numP, Char.ofNat_toNat, strValue_strP cs]

/-! ## Patterns -/

mutual
  /-- The encoding of a pattern. Constructor applications are encoded faithfully; every
  other node becomes the encoding of the empty application. -/
  def patP : Pattern → Pattern
    | .apply name arguments => .apply "papply" [strP name.toList, patsP arguments]
    | _ => .apply "papply" [strP [], .apply "pnil" []]

  def patsP : List Pattern → Pattern
    | [] => .apply "pnil" []
    | pattern :: patterns => .apply "pcons" [patP pattern, patsP patterns]
end

mutual
  /-- The first-order pattern a term of the grammar denotes. -/
  def patValue : Pattern → Pattern
    | .apply "papply" [name, arguments] =>
        .apply (String.ofList (strValue name)) (patsValue arguments)
    | _ => .apply "" []
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def patsValue : Pattern → List Pattern
    | .apply "pcons" [first, rest] => patValue first :: patsValue rest
    | _ => []
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- Constructor applications all the way down. -/
  inductive FirstOrder : Pattern → Prop where
    | apply {name : String} {arguments : List Pattern} :
        FirstOrderList arguments → FirstOrder (.apply name arguments)

  inductive FirstOrderList : List Pattern → Prop where
    | nil : FirstOrderList []
    | cons {pattern : Pattern} {patterns : List Pattern} :
        FirstOrder pattern → FirstOrderList patterns → FirstOrderList (pattern :: patterns)
end

mutual
  theorem patValue_patP {pattern : Pattern} (firstOrder : FirstOrder pattern) :
      patValue (patP pattern) = pattern := by
    cases firstOrder with
    | @apply name arguments rest =>
        rw [patP, patValue, strValue_strP, String.ofList_toList, patsValue_patsP rest]

  theorem patsValue_patsP {patterns : List Pattern} (firstOrder : FirstOrderList patterns) :
      patsValue (patsP patterns) = patterns := by
    cases firstOrder with
    | nil => simp [patsP, patsValue]
    | cons head tail =>
        rw [patsP, patsValue, patValue_patP head, patsValue_patsP tail]
end

mutual
  theorem firstOrder_patValue (pattern : Pattern) : FirstOrder (patValue pattern) := by
    unfold patValue
    split
    · exact .apply (firstOrderList_patsValue _)
    · exact .apply .nil
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem firstOrderList_patsValue (pattern : Pattern) : FirstOrderList (patsValue pattern) := by
    unfold patsValue
    split
    · exact .cons (firstOrder_patValue _) (firstOrderList_patsValue _)
    · exact .nil
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## First-order calculi -/

/-- The metavariable names of a rule, in order. -/
def ruleNames (rule : RuleSchema) : List String := rule.metavariables.map Prod.fst

/-- A first-order calculus: metavariables of arity zero with distinct names, schemas built
from constructors and metavariables, no side conditions, and distinct rule identifiers. -/
structure FirstOrderCalculus (definition : CalculusLanguageDef) : Prop where
  arities : ∀ rule ∈ definition.rules, ∀ entry ∈ rule.metavariables, entry.2 = 0
  distinctNames : ∀ rule ∈ definition.rules, (ruleNames rule).Nodup
  premiseSchemas : ∀ rule ∈ definition.rules, Schemas (ruleNames rule) rule.premises
  conclusionSchema : ∀ rule ∈ definition.rules, Schema (ruleNames rule) rule.conclusion
  noSideConditions : ∀ rule ∈ definition.rules, rule.sideConditions = []
  distinctRules : (definition.rules.map fun rule => rule.id.value).Nodup

/-- The executable check of the class. -/
def firstOrderCheck (definition : CalculusLanguageDef) : Bool :=
  definition.rules.all (fun rule =>
      rule.metavariables.all (fun entry => entry.2 == 0) && decide (ruleNames rule).Nodup &&
        checkSchemas (ruleNames rule) rule.premises &&
        checkSchema (ruleNames rule) rule.conclusion && rule.sideConditions.isEmpty) &&
    decide (definition.rules.map fun rule => rule.id.value).Nodup

theorem firstOrderCheck_sound {definition : CalculusLanguageDef}
    (checked : firstOrderCheck definition = true) : FirstOrderCalculus definition := by
  simp only [firstOrderCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.isEmpty_iff, checkSchemas_iff, checkSchema_iff] at checked
  obtain ⟨rules, distinct⟩ := checked
  exact ⟨fun rule member => (rules rule member).1.1.1.1,
    fun rule member => (rules rule member).1.1.1.2,
    fun rule member => (rules rule member).1.1.2,
    fun rule member => (rules rule member).1.2,
    fun rule member => (rules rule member).2, distinct⟩

/-! ## Encoded rules -/

mutual
  /-- The encoding of a schema: constructors are encoded, metavariables stay. -/
  def encodeSchema : Pattern → Pattern
    | .apply name arguments => .apply "papply" [strP name.toList, encodeSchemas arguments]
    | .fvar name => .fvar name
    | pattern => pattern

  def encodeSchemas : List Pattern → Pattern
    | [] => .apply "pnil" []
    | pattern :: patterns => .apply "pcons" [encodeSchema pattern, encodeSchemas patterns]
end

/-- The judgment that a pattern holds. -/
def holdsP (pattern : Pattern) : Pattern := .apply "holds" [pattern]

/-- A rule of the calculus as a sorted first-order rule over the grammar. -/
def encodeRule (rule : RuleSchema) : Rule where
  row :=
    { id := rule.id.value
      vars := ruleNames rule
      premises := rule.premises.map fun premise => holdsP (encodeSchema premise)
      conclusion := holdsP (encodeSchema rule.conclusion) }
  variableTypes := (ruleNames rule).map fun _ => patSort

def encodedRules (definition : CalculusLanguageDef) : List Rule := definition.rules.map encodeRule

/-! ## Typing -/

theorem hasType_former {bound : List TypeExpr} {label category : String}
    {sorts : List TypeExpr} {arguments : List Pattern}
    (member : PartialRecursive.former label category sorts ∈ universalLanguage.terms)
    (simple : ∀ sort ∈ sorts, ∃ name, sort = .base name)
    (typed : ArgumentsHaveTypes universalLanguage FreeTypeContext.empty bound arguments
      (PartialRecursive.former label category sorts).params) :
    HasType universalLanguage FreeTypeContext.empty bound (.apply label arguments) (.base category) :=
  HasType.constructor member (PartialRecursive.former_notBare label category sorts simple) typed

theorem hasType_numP (bound : List TypeExpr) (n : ℕ) :
    HasType universalLanguage FreeTypeContext.empty bound (numP n) numSort := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero =>
          rw [numP]
          exact hasType_former (sorts := []) (by simp [universalLanguage]) (by simp) .nil
      | succ n =>
          rw [numP]
          split
          · exact hasType_former (sorts := [numSort]) (by simp [universalLanguage]) (by simp)
              (.cons trivial rfl (ih _ (by omega)) .nil)
          · exact hasType_former (sorts := [numSort]) (by simp [universalLanguage]) (by simp)
              (.cons trivial rfl (ih _ (by omega)) .nil)

theorem hasType_strP (bound : List TypeExpr) :
    ∀ cs : List Char, HasType universalLanguage FreeTypeContext.empty bound (strP cs) strSort
  | [] => hasType_former (sorts := []) (by simp [universalLanguage]) (by simp) .nil
  | c :: cs => hasType_former (sorts := [numSort, strSort]) (by simp [universalLanguage]) (by simp)
      (.cons trivial rfl (hasType_numP bound c.toNat) (.cons trivial rfl (hasType_strP bound cs) .nil))

theorem applyBindings_numP (bindings : Bindings) (n : ℕ) :
    applyBindings bindings (numP n) = numP n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => simp [numP, applyBindings]
      | succ n =>
          rw [numP]
          split <;> simp [applyBindings, ih (n / 2) (by omega)]

theorem applyBindings_strP (bindings : Bindings) :
    ∀ cs : List Char, applyBindings bindings (strP cs) = strP cs
  | [] => by simp [strP, applyBindings]
  | c :: cs => by simp [strP, applyBindings, applyBindings_numP, applyBindings_strP bindings cs]

mutual
  theorem hasType_encodeSchema {names : List String} (distinct : names.Nodup) {pattern : Pattern}
      (schema : Schema names pattern) :
      HasType universalLanguage FreeTypeContext.empty (names.map fun _ => patSort)
        (numbered names (encodeSchema pattern)) patSort := by
    cases schema with
    | @metavariable name member =>
        have lookup := numberedBindings_lookup distinct (List.getElem?_idxOf member)
        simp only [encodeSchema, numbered, applyBindings, lookup]
        exact HasType.bvar (by rw [List.getElem?_map, List.getElem?_idxOf member]; rfl)
    | @constructor name arguments children =>
        simp only [encodeSchema, numbered, applyBindings, List.map, applyBindings_strP]
        exact hasType_former (sorts := [strSort, patsSort]) (by simp [universalLanguage]) (by simp)
          (.cons trivial rfl (hasType_strP _ _)
            (.cons trivial rfl (hasType_encodeSchemas distinct children) .nil))
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem hasType_encodeSchemas {names : List String} (distinct : names.Nodup)
      {patterns : List Pattern} (schemas : Schemas names patterns) :
      HasType universalLanguage FreeTypeContext.empty (names.map fun _ => patSort)
        (numbered names (encodeSchemas patterns)) patsSort := by
    cases schemas with
    | nil =>
        simp only [encodeSchemas, numbered, applyBindings, List.map]
        exact hasType_former (sorts := []) (by simp [universalLanguage]) (by simp) .nil
    | cons first rest =>
        simp only [encodeSchemas, numbered, applyBindings, List.map]
        exact hasType_former (sorts := [patSort, patsSort]) (by simp [universalLanguage]) (by simp)
          (.cons trivial rfl (hasType_encodeSchema distinct first)
            (.cons trivial rfl (hasType_encodeSchemas distinct rest) .nil))
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem hasType_holds {names : List String} (distinct : names.Nodup) {pattern : Pattern}
    (schema : Schema names pattern) :
    HasType universalLanguage FreeTypeContext.empty (names.map fun _ => patSort)
      (numbered names (holdsP (encodeSchema pattern))) wffSort := by
  simp only [holdsP, numbered, applyBindings, List.map]
  exact hasType_former (sorts := [patSort]) (by simp [universalLanguage]) (by simp)
    (.cons trivial rfl (hasType_encodeSchema distinct schema) .nil)

/-! ## Schemas -/

theorem schema_numP (names : List String) (n : ℕ) : Schema names (numP n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero =>
          rw [numP]
          exact .constructor .nil
      | succ n =>
          rw [numP]
          split <;> exact .constructor (.cons (ih _ (by omega)) .nil)

theorem schema_strP (names : List String) : ∀ cs : List Char, Schema names (strP cs)
  | [] => .constructor .nil
  | c :: cs => .constructor (.cons (schema_numP names c.toNat) (.cons (schema_strP names cs) .nil))

mutual
  theorem schema_encodeSchema {names : List String} {pattern : Pattern}
      (schema : Schema names pattern) : Schema names (encodeSchema pattern) := by
    cases schema with
    | @metavariable name member =>
        simp only [encodeSchema]
        exact .metavariable member
    | @constructor name arguments children =>
        simp only [encodeSchema]
        exact .constructor (.cons (schema_strP names _) (.cons (schemas_encodeSchemas children) .nil))
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem schemas_encodeSchemas {names : List String} {patterns : List Pattern}
      (schemas : Schemas names patterns) : Schema names (encodeSchemas patterns) := by
    cases schemas with
    | nil =>
        simp only [encodeSchemas]
        exact .constructor .nil
    | cons first rest =>
        simp only [encodeSchemas]
        exact .constructor (.cons (schema_encodeSchema first) (.cons (schemas_encodeSchemas rest) .nil))
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem schemas_holds {names : List String} :
    ∀ {patterns : List Pattern}, Schemas names patterns →
      Schemas names (patterns.map fun pattern => holdsP (encodeSchema pattern))
  | [], _ => .nil
  | _ :: _, .cons first rest =>
      .cons (.constructor (.cons (schema_encodeSchema first) .nil)) (schemas_holds rest)

/-! ## Admission -/

theorem encodeRule_wellFormed {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) {rule : RuleSchema}
    (member : rule ∈ definition.rules) :
    (encodeRule rule).WellFormed universalLanguage ["wff"] where
  distinctNames := firstOrder.distinctNames rule member
  arity := by simp [encodeRule]
  declaredTypes := by
    intro type typeMember
    simp only [encodeRule, List.mem_map] at typeMember
    obtain ⟨_, _, rfl⟩ := typeMember
    exact ⟨"pat", rfl, by decide⟩
  premiseSchemas := schemas_holds (firstOrder.premiseSchemas rule member)
  conclusionSchema :=
    .constructor (.cons (schema_encodeSchema (firstOrder.conclusionSchema rule member)) .nil)
  hypotheses := by
    intro pattern patternMember
    simp only [encodeRule, List.mem_map] at patternMember
    obtain ⟨premise, premiseMember, rfl⟩ := patternMember
    exact ⟨"wff", by simp, hasType_holds (firstOrder.distinctNames rule member)
      ((firstOrder.premiseSchemas rule member).member premiseMember)⟩
  conclusion := ⟨"wff", by simp, hasType_holds (firstOrder.distinctNames rule member)
    (firstOrder.conclusionSchema rule member)⟩

theorem universalSignature_check : Signature.check universalLanguage = true := by
  decide +kernel

theorem universalDefinitional :
    DefinitionalLanguage universalLanguage (DefinitionalEquations.definitions universalLanguage) :=
  (checkDefinitional_iff_definitions universalLanguage).mp (by decide +kernel)

theorem presentation_check {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) :
    Presentation.check universalLanguage ["wff"] (encodedRules definition) = true := by
  rw [Presentation.check, universalSignature_check, Bool.true_and]
  refine (Presentation.checkBody_iff _ _ _).mpr
    ⟨universalDefinitional, rfl, by decide, by decide, ?_, ?_⟩
  · simpa [encodedRules, encodeRule, Function.comp_def] using firstOrder.distinctRules
  · intro rule member
    simp only [encodedRules, List.mem_map] at member
    obtain ⟨source, sourceMember, rfl⟩ := member
    exact encodeRule_wellFormed firstOrder sourceMember

/-- The admitted presentation of a first-order calculus over the grammar. -/
def presentation (definition : CalculusLanguageDef) (firstOrder : FirstOrderCalculus definition) :
    Presentation :=
  (Presentation.admit? universalLanguage ["wff"] (encodedRules definition)).get
    ((Presentation.admit?_isSome_iff _ _ _).mpr (presentation_check firstOrder))

theorem presentation_retains {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) :
    (presentation definition firstOrder).syntaxSignature.language = universalLanguage ∧
      (presentation definition firstOrder).judgmentSorts = ["wff"] ∧
        (presentation definition firstOrder).rules = encodedRules definition :=
  Presentation.admit?_retains (Option.some_get _).symm

/-! ## Substitution in first-order schemas -/

mutual
  /-- Substitute values for the metavariables of a first-order schema. -/
  def substSchema (values : String → Pattern) : Pattern → Pattern
    | .apply name arguments => .apply name (substSchemas values arguments)
    | .fvar name => values name
    | pattern => pattern

  def substSchemas (values : String → Pattern) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => substSchema values pattern :: substSchemas values patterns
end

mutual
  /-- Encode a schema, putting values of the grammar at its metavariables. -/
  def encodeWith (values : String → Pattern) : Pattern → Pattern
    | .apply name arguments => .apply "papply" [strP name.toList, encodeWiths values arguments]
    | .fvar name => values name
    | pattern => pattern

  def encodeWiths (values : String → Pattern) : List Pattern → Pattern
    | [] => .apply "pnil" []
    | pattern :: patterns => .apply "pcons" [encodeWith values pattern, encodeWiths values patterns]
end

/-- The value a list of bindings gives a name, as `applyBindings` reads it. -/
def bindingValue (bindings : Bindings) (name : String) : Pattern :=
  match bindings.find? (·.1 == name) with
  | some (_, value) => value
  | none => .fvar name

mutual
  /-- Binding the metavariables of an encoded schema encodes with the bound values. -/
  theorem applyBindings_encodeSchema (bindings : Bindings) {names : List String}
      {pattern : Pattern} (schema : Schema names pattern) :
      applyBindings bindings (encodeSchema pattern) = encodeWith (bindingValue bindings) pattern := by
    cases schema with
    | @metavariable name _ =>
        simp only [encodeSchema, encodeWith]
        rw [applyBindings]
        rfl
    | @constructor name arguments children =>
        simp only [encodeSchema, encodeWith, applyBindings, List.map, applyBindings_strP,
          applyBindings_encodeSchemas bindings children]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem applyBindings_encodeSchemas (bindings : Bindings) {names : List String}
      {patterns : List Pattern} (schemas : Schemas names patterns) :
      applyBindings bindings (encodeSchemas patterns) = encodeWiths (bindingValue bindings) patterns := by
    cases schemas with
    | nil => simp only [encodeSchemas, encodeWiths, applyBindings, List.map]
    | cons first rest =>
        simp only [encodeSchemas, encodeWiths, applyBindings, List.map,
          applyBindings_encodeSchema bindings first, applyBindings_encodeSchemas bindings rest]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- Encoding commutes with substitution when the encoded values agree on the names. -/
  theorem encodeWith_eq_patP {names : List String} {encodedValues values : String → Pattern}
      (agree : ∀ name ∈ names, encodedValues name = patP (values name)) {pattern : Pattern}
      (schema : Schema names pattern) :
      encodeWith encodedValues pattern = patP (substSchema values pattern) := by
    cases schema with
    | @metavariable name member =>
        simp only [encodeWith, substSchema]
        exact agree name member
    | @constructor name arguments children =>
        simp only [encodeWith, substSchema, patP, encodeWiths_eq_patsP agree children]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodeWiths_eq_patsP {names : List String} {encodedValues values : String → Pattern}
      (agree : ∀ name ∈ names, encodedValues name = patP (values name)) {patterns : List Pattern}
      (schemas : Schemas names patterns) :
      encodeWiths encodedValues patterns = patsP (substSchemas values patterns) := by
    cases schemas with
    | nil => simp only [encodeWiths, substSchemas, patsP]
    | cons first rest =>
        simp only [encodeWiths, substSchemas, patsP, encodeWith_eq_patP agree first,
          encodeWiths_eq_patsP agree rest]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- Decoding commutes with substitution when the decoded values agree on the names. -/
  theorem patValue_encodeWith {names : List String} {encodedValues values : String → Pattern}
      (agree : ∀ name ∈ names, values name = patValue (encodedValues name)) {pattern : Pattern}
      (schema : Schema names pattern) :
      patValue (encodeWith encodedValues pattern) = substSchema values pattern := by
    cases schema with
    | @metavariable name member =>
        simp only [encodeWith, substSchema]
        exact (agree name member).symm
    | @constructor name arguments children =>
        simp only [encodeWith, substSchema]
        rw [patValue, strValue_strP, String.ofList_toList, patsValue_encodeWiths agree children]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem patsValue_encodeWiths {names : List String} {encodedValues values : String → Pattern}
      (agree : ∀ name ∈ names, values name = patValue (encodedValues name)) {patterns : List Pattern}
      (schemas : Schemas names patterns) :
      patsValue (encodeWiths encodedValues patterns) = substSchemas values patterns := by
    cases schemas with
    | nil => simp [encodeWiths, substSchemas, patsValue]
    | cons first rest =>
        simp only [encodeWiths, substSchemas]
        rw [patsValue, patValue_encodeWith agree first, patsValue_encodeWiths agree rest]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- With formals of depth zero, the checker's argument lookup is the first binding of the
name. -/
theorem lookupArgumentAt?_zero :
    ∀ (names : List String) (arguments : List Pattern) (name : String),
      lookupArgumentAt? (names.map fun entry => (entry, 0)) arguments name 0 =
        ((names.zip arguments).find? (·.1 == name)).map Prod.snd
  | [], _, _ => by simp [lookupArgumentAt?]
  | _ :: _, [], _ => by simp [lookupArgumentAt?]
  | first :: names, argument :: arguments, name => by
      simp only [List.map_cons, lookupArgumentAt?, List.zip_cons_cons, List.find?_cons]
      by_cases same : first = name
      · subst same
        simp
      · have different : (first == name) = false := by simpa using same
        rw [if_neg (by simpa using same), different]
        exact lookupArgumentAt?_zero names arguments name

/-- A name of the list is found in its zip with as many values. -/
theorem find?_zip_isSome {names : List String} {arguments : List Pattern} {name : String}
    (member : name ∈ names) (arity : arguments.length = names.length) :
    ∃ value, (names.zip arguments).find? (·.1 == name) = some (name, value) := by
  induction names generalizing arguments with
  | nil => cases member
  | cons first names ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          simp only [List.zip_cons_cons, List.find?_cons]
          by_cases same : first = name
          · subst same
            exact ⟨argument, by simp⟩
          · have different : (first == name) = false := by simpa using same
            rw [different]
            rcases List.mem_cons.mp member with rfl | member
            · exact absurd rfl same
            · exact ih member (by simpa using arity)

theorem bindingValue_map (f : Pattern → Pattern) {names : List String} {arguments : List Pattern}
    {name : String} (member : name ∈ names) (arity : arguments.length = names.length) :
    bindingValue (names.zip (arguments.map f)) name = f (bindingValue (names.zip arguments) name) := by
  obtain ⟨value, found⟩ := find?_zip_isSome member arity
  have mapped : (names.zip (arguments.map f)).find? (·.1 == name) = some (name, f value) := by
    rw [List.zip_map_right, List.find?_map]
    have same : ((fun entry : String × Pattern => entry.1 == name) ∘ Prod.map id f) =
        (fun entry => entry.1 == name) := by
      funext entry
      rfl
    rw [same, found]
    rfl
  simp only [bindingValue, found, mapped]

mutual
  /-- On a first-order schema, the checker's instantiation is substitution. -/
  theorem instantiateSchemaAt?_eq {names : List String} {arguments : List Pattern}
      (arity : arguments.length = names.length) {pattern : Pattern}
      (schema : Schema names pattern) :
      instantiateSchemaAt? (names.map fun entry => (entry, 0)) arguments 0 pattern =
        some (substSchema (bindingValue (names.zip arguments)) pattern) := by
    cases schema with
    | @metavariable name member =>
        obtain ⟨value, found⟩ := find?_zip_isSome member arity
        rw [instantiateSchemaAt?, lookupArgumentAt?_zero, found]
        simp [substSchema, bindingValue, found]
    | @constructor name arguments' children =>
        rw [instantiateSchemaAt?, instantiateSchemasAt?_eq arity children]
        simp [substSchema]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem instantiateSchemasAt?_eq {names : List String} {arguments : List Pattern}
      (arity : arguments.length = names.length) {patterns : List Pattern}
      (schemas : Schemas names patterns) :
      instantiateSchemasAt? (names.map fun entry => (entry, 0)) arguments 0 patterns =
        some (substSchemas (bindingValue (names.zip arguments)) patterns) := by
    cases schemas with
    | nil => simp [instantiateSchemasAt?, substSchemas]
    | cons first rest =>
        rw [instantiateSchemasAt?, instantiateSchemaAt?_eq arity first,
          instantiateSchemasAt?_eq arity rest]
        simp [substSchemas]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Arguments -/

mutual
  theorem hasType_patP (bound : List TypeExpr) (pattern : Pattern) :
      HasType universalLanguage FreeTypeContext.empty bound (patP pattern) patSort := by
    cases pattern with
    | apply name arguments =>
        rw [patP]
        exact hasType_former (sorts := [strSort, patsSort]) (by simp [universalLanguage]) (by simp)
          (.cons trivial rfl (hasType_strP _ _) (.cons trivial rfl (hasType_patsP bound arguments) .nil))
    | _ =>
        simp only [patP]
        exact hasType_former (sorts := [strSort, patsSort]) (by simp [universalLanguage]) (by simp)
          (.cons trivial rfl (hasType_strP _ _)
            (.cons trivial rfl (hasType_former (sorts := []) (by simp [universalLanguage]) (by simp) .nil)
              .nil))

  theorem hasType_patsP (bound : List TypeExpr) (patterns : List Pattern) :
      HasType universalLanguage FreeTypeContext.empty bound (patsP patterns) patsSort := by
    cases patterns with
    | nil =>
        rw [patsP]
        exact hasType_former (sorts := []) (by simp [universalLanguage]) (by simp) .nil
    | cons pattern patterns =>
        rw [patsP]
        exact hasType_former (sorts := [patSort, patsSort]) (by simp [universalLanguage]) (by simp)
          (.cons trivial rfl (hasType_patP bound pattern) (.cons trivial rfl (hasType_patsP bound patterns) .nil))
end

theorem matchCorrect_numP (n : ℕ) : isMatchCorrectAux (numP n) = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => simp [numP, isMatchCorrectAux, isMatchCorrectListAux]
      | succ n =>
          rw [numP]
          split <;> simp [isMatchCorrectAux, isMatchCorrectListAux, ih (n / 2) (by omega)]

theorem matchCorrect_strP : ∀ cs : List Char, isMatchCorrectAux (strP cs) = true
  | [] => by simp [strP, isMatchCorrectAux, isMatchCorrectListAux]
  | c :: cs => by
      simp [strP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_numP, matchCorrect_strP cs]

mutual
  theorem matchCorrect_patP (pattern : Pattern) : isMatchCorrectAux (patP pattern) = true := by
    cases pattern with
    | apply name arguments =>
        rw [patP]
        simp [isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_strP, matchCorrect_patsP arguments]
    | _ => simp [patP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_strP]

  theorem matchCorrect_patsP (patterns : List Pattern) : isMatchCorrectAux (patsP patterns) = true := by
    cases patterns with
    | nil => simp [patsP, isMatchCorrectAux, isMatchCorrectListAux]
    | cons pattern patterns =>
        rw [patsP]
        simp [isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_patP pattern,
          matchCorrect_patsP patterns]
end

mutual
  theorem FirstOrder.ground {pattern : Pattern} (firstOrder : FirstOrder pattern) (depth : Nat) :
      pattern.isGroundAt depth = true := by
    cases firstOrder with
    | apply rest => simp [Pattern.isGroundAt, FirstOrderList.ground rest depth]

  theorem FirstOrderList.ground {patterns : List Pattern} (firstOrder : FirstOrderList patterns)
      (depth : Nat) : Pattern.isGroundListAt depth patterns = true := by
    cases firstOrder with
    | nil => simp [Pattern.isGroundListAt]
    | cons head tail =>
        simp [Pattern.isGroundListAt, FirstOrder.ground head depth, FirstOrderList.ground tail depth]
end

mutual
  theorem FirstOrder.canonical {pattern : Pattern} (firstOrder : FirstOrder pattern) :
      Pattern.hasCanonicalBinderMetadata pattern = true := by
    cases firstOrder with
    | apply rest => simp [Pattern.hasCanonicalBinderMetadata, FirstOrderList.canonical rest]

  theorem FirstOrderList.canonical {patterns : List Pattern} (firstOrder : FirstOrderList patterns) :
      Pattern.hasCanonicalBinderMetadataList patterns = true := by
    cases firstOrder with
    | nil => simp [Pattern.hasCanonicalBinderMetadataList]
    | cons head tail =>
        simp [Pattern.hasCanonicalBinderMetadataList, FirstOrder.canonical head,
          FirstOrderList.canonical tail]
end

/-- Decoded arguments are valid for metavariables of arity zero. -/
theorem argumentsValidAt_patValue :
    ∀ (names : List String) (arguments : List Pattern), arguments.length = names.length →
      argumentsValidAt (names.map fun name => (name, 0)) (arguments.map patValue) = true
  | [], [], _ => rfl
  | _ :: names, argument :: arguments, arity => by
      simp only [List.map_cons, argumentsValidAt, argumentValidAt, Bool.and_eq_true]
      exact ⟨⟨(firstOrder_patValue argument).ground 0, (firstOrder_patValue argument).canonical⟩,
        argumentsValidAt_patValue names arguments (by simpa using arity)⟩
  | [], _ :: _, arity => by simp at arity
  | _ :: _, [], arity => by simp at arity

theorem forall₂_patP {names : List String} :
    ∀ {arguments : List Pattern}, arguments.length = names.length →
      List.Forall₂ (fun argument type => HasType universalLanguage FreeTypeContext.empty [] argument type)
        (arguments.map patP) (names.map fun _ => patSort)
  | [], arity => by
      cases names with
      | nil => exact .nil
      | cons _ _ => simp at arity
  | argument :: arguments, arity => by
      cases names with
      | nil => simp at arity
      | cons name names =>
          exact .cons (hasType_patP [] argument) (forall₂_patP (names := names) (by simpa using arity))

/-! ## Rules -/

theorem metavariables_eq {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) {rule : RuleSchema} (member : rule ∈ definition.rules) :
    rule.metavariables = (ruleNames rule).map fun name => (name, 0) := by
  have arities := firstOrder.arities rule member
  simp only [ruleNames, List.map_map]
  conv_lhs => rw [← List.map_id rule.metavariables]
  apply List.map_congr_left
  intro entry entryMember
  exact Prod.ext rfl (arities entry entryMember)

theorem lookupRule?_encoded (definition : CalculusLanguageDef) (id : RuleId) :
    SortedFirstOrderRules.lookupRule? (encodedRules definition) id.value =
      (definition.lookupRule? id).map encodeRule := by
  simp only [SortedFirstOrderRules.lookupRule?, CalculusLanguageDef.lookupRule?, encodedRules,
    List.find?_map]
  congr 2
  funext rule
  obtain ⟨⟨ruleValue⟩, _, _, _, _⟩ := rule
  obtain ⟨idValue⟩ := id
  rcases decEq ruleValue idValue with different | same
  · simp [encodeRule, different]
  · simp [encodeRule, same]

theorem lookupRule?_member {definition : CalculusLanguageDef} {id : RuleId} {rule : RuleSchema}
    (lookup : definition.lookupRule? id = some rule) : rule ∈ definition.rules :=
  List.mem_of_find?_eq_some lookup

/-- The checker's rule instantiation, taken apart. -/
theorem instantiateRule?_some {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (instantiated : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    ∃ rule, definition.1.lookupRule? ruleInstance.ruleId = some rule ∧
      argumentsValidAt rule.metavariables ruleInstance.arguments = true ∧
      instantiateSchemas? rule.metavariables ruleInstance.arguments rule.premises = some premises ∧
      instantiateSchema? rule.metavariables ruleInstance.arguments rule.conclusion = some conclusion := by
  unfold instantiateRule? at instantiated
  split at instantiated
  · simp at instantiated
  · rename_i rule lookup
    split_ifs at instantiated with valid sides
    cases schemas : instantiateSchemas? rule.metavariables ruleInstance.arguments rule.premises with
    | none => simp [schemas] at instantiated
    | some results =>
        cases schema : instantiateSchema? rule.metavariables ruleInstance.arguments rule.conclusion with
        | none => simp [schemas, schema] at instantiated
        | some result =>
            simp only [schemas, schema] at instantiated
            obtain ⟨rfl, rfl⟩ := instantiated
            exact ⟨rule, lookup, valid, schemas, schema⟩

/-- The checker's rule instantiation, put together. -/
theorem instantiateRule?_of {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {rule : RuleSchema} {premises : List Pattern} {conclusion : Pattern}
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some rule)
    (valid : argumentsValidAt rule.metavariables ruleInstance.arguments = true)
    (sides : RuleSchema.sideConditionsHold rule ruleInstance.arguments = true)
    (schemas : instantiateSchemas? rule.metavariables ruleInstance.arguments rule.premises = some premises)
    (schema : instantiateSchema? rule.metavariables ruleInstance.arguments rule.conclusion = some conclusion) :
    instantiateRule? definition ruleInstance = some (premises, conclusion) := by
  unfold instantiateRule?
  rw [lookup]
  simp only [valid, sides, if_true, schemas, schema]
  rfl

/-! ## Proofs as trees, and back -/

mutual
  /-- A raw proof of the checker as a tree of the presentation, with encoded arguments. -/
  def encodeProof : RawProof → RawOpenProof
    | .node ruleInstance children =>
        .node { ruleId := ruleInstance.ruleId, arguments := ruleInstance.arguments.map patP }
          (encodeProofs children)

  def encodeProofs : List RawProof → List RawOpenProof
    | [] => []
    | proof :: proofs => encodeProof proof :: encodeProofs proofs
end

mutual
  /-- A tree of the presentation as a raw proof of the checker, with decoded arguments. -/
  def decodeProof : RawOpenProof → RawProof
    | .premise _ => .node { ruleId := ⟨""⟩, arguments := [] } []
    | .node invocation children =>
        .node { ruleId := invocation.ruleId, arguments := invocation.arguments.map patValue }
          (decodeProofs children)

  def decodeProofs : List RawOpenProof → List RawProof
    | [] => []
    | proof :: proofs => decodeProof proof :: decodeProofs proofs
end

theorem substSchemas_eq_map (values : String → Pattern) :
    ∀ patterns : List Pattern, substSchemas values patterns = patterns.map (substSchema values)
  | [] => rfl
  | pattern :: patterns => by rw [substSchemas, substSchemas_eq_map values patterns, List.map_cons]

theorem encodeRule_instConclusion (rule : RuleSchema) (arguments : List Pattern) :
    (encodeRule rule).row.instConclusion arguments =
      holdsP (applyBindings ((ruleNames rule).zip arguments) (encodeSchema rule.conclusion)) := by
  simp only [encodeRule, FORule.instConclusion, FORule.bindings, holdsP]
  rw [applyBindings]
  rfl

theorem encodeRule_instPremises (rule : RuleSchema) (arguments : List Pattern) :
    (encodeRule rule).row.instPremises arguments =
      rule.premises.map fun premise =>
        holdsP (applyBindings ((ruleNames rule).zip arguments) (encodeSchema premise)) := by
  simp only [encodeRule, FORule.instPremises, FORule.bindings, holdsP, List.map_map]
  apply List.map_congr_left
  intro premise _
  simp only [Function.comp_apply]
  rw [applyBindings]
  rfl

theorem instPremises_encodeWith {names : List String} {rule : RuleSchema}
    (names_eq : ruleNames rule = names) (schemas : Schemas names rule.premises)
    (arguments : List Pattern) :
    (encodeRule rule).row.instPremises arguments =
      rule.premises.map fun premise =>
        holdsP (encodeWith (bindingValue (names.zip arguments)) premise) := by
  rw [encodeRule_instPremises, names_eq]
  apply List.map_congr_left
  intro premise member
  rw [applyBindings_encodeSchema _ (schemas.member member)]

theorem map_patValue_encodeWith {names : List String} {encodedValues values : String → Pattern}
    (agree : ∀ name ∈ names, values name = patValue (encodedValues name)) :
    ∀ {patterns : List Pattern}, Schemas names patterns →
      (patterns.map (encodeWith encodedValues)).map patValue = substSchemas values patterns
  | [], _ => rfl
  | _ :: _, .cons first rest => by
      rw [List.map_cons, List.map_cons, patValue_encodeWith agree first,
        map_patValue_encodeWith agree rest, substSchemas]

mutual
  /-- **A proof the checker accepts encodes to a tree the presentation accepts.** -/
  theorem encode_accepted {definition : ValidatedCalculusLanguageDef}
      (firstOrder : FirstOrderCalculus definition.1) :
      ∀ (goal : Pattern) (proof : RawProof), checkRaw definition goal proof = true →
        SortedFirstOrderRules.Checks universalLanguage (encodedRules definition.1) [] []
          (encodeProof proof) (holdsP (patP goal))
    | goal, .node ruleInstance children, accepted => by
        rw [checkRaw] at accepted
        cases instantiated : instantiateRule? definition ruleInstance with
        | none => simp [instantiated] at accepted
        | some result =>
            obtain ⟨premises, conclusion⟩ := result
            simp only [instantiated, Bool.and_eq_true, decide_eq_true_eq] at accepted
            obtain ⟨concluded, childrenAccepted⟩ := accepted
            obtain ⟨rule, lookup, valid, schemas, schema⟩ := instantiateRule?_some instantiated
            have member := lookupRule?_member lookup
            have formals := metavariables_eq firstOrder member
            have arity : ruleInstance.arguments.length = (ruleNames rule).length := by
              have counted := argumentsValidAt_length valid
              rw [formals, List.length_map] at counted
              exact counted.symm
            have premiseSchemas := firstOrder.premiseSchemas rule member
            have conclusionSchema := firstOrder.conclusionSchema rule member
            rw [formals, instantiateSchemas?, instantiateSchemasAt?_eq arity premiseSchemas,
              Option.some.injEq] at schemas
            rw [formals, instantiateSchema?, instantiateSchemaAt?_eq arity conclusionSchema,
              Option.some.injEq] at schema
            have agree : ∀ name ∈ ruleNames rule,
                bindingValue ((ruleNames rule).zip (ruleInstance.arguments.map patP)) name =
                  patP (bindingValue ((ruleNames rule).zip ruleInstance.arguments) name) :=
              fun name nameMember => bindingValue_map patP nameMember arity
            have conclusionEq :
                (encodeRule rule).row.instConclusion (ruleInstance.arguments.map patP) =
                  holdsP (patP goal) := by
              rw [encodeRule_instConclusion, applyBindings_encodeSchema _ conclusionSchema,
                encodeWith_eq_patP agree conclusionSchema, schema, concluded]
            have premisesEq :
                (encodeRule rule).row.instPremises (ruleInstance.arguments.map patP) =
                  premises.map fun premise => holdsP (patP premise) := by
              rw [instPremises_encodeWith rfl premiseSchemas, ← schemas, substSchemas_eq_map,
                List.map_map]
              apply List.map_congr_left
              intro premise premiseMember
              simp only [Function.comp_apply]
              rw [encodeWith_eq_patP agree (premiseSchemas.member premiseMember)]
            rw [← conclusionEq, encodeProof]
            exact SortedFirstOrderRules.Checks.rule
              (by rw [lookupRule?_encoded, lookup]; rfl)
              (by simpa [encodeRule] using arity)
              (by simpa [encodeRule] using forall₂_patP arity)
              (fun argument argumentMember => by
                obtain ⟨source, _, rfl⟩ := List.mem_map.mp argumentMember
                exact matchCorrect_patP source)
              (by rw [premisesEq]; exact encode_acceptedList firstOrder premises children childrenAccepted)

  theorem encode_acceptedList {definition : ValidatedCalculusLanguageDef}
      (firstOrder : FirstOrderCalculus definition.1) :
      ∀ (premises : List Pattern) (proofs : List RawProof),
        checkRawChildren definition premises proofs = true →
          SortedFirstOrderRules.ChecksList universalLanguage (encodedRules definition.1) [] []
            (encodeProofs proofs) (premises.map fun premise => holdsP (patP premise))
    | [], [], _ => .nil
    | premise :: premises, proof :: proofs, accepted => by
        rw [checkRawChildren, Bool.and_eq_true] at accepted
        rw [encodeProofs, List.map_cons]
        exact .cons (encode_accepted firstOrder premise proof accepted.1)
          (encode_acceptedList firstOrder premises proofs accepted.2)
    | [], _ :: _, accepted => by simp [checkRawChildren] at accepted
    | _ :: _, [], accepted => by simp [checkRawChildren] at accepted
end

/-- **A tree the presentation accepts decodes to a proof the checker accepts.** -/
theorem decode_accepted {definition : ValidatedCalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition.1) {tree : RawOpenProof} {pattern : Pattern}
    (checked : SortedFirstOrderRules.Checks universalLanguage (encodedRules definition.1) [] []
      tree pattern) :
    ∀ X, pattern = holdsP X → checkRaw definition (patValue X) (decodeProof tree) = true := by
  induction checked using SortedFirstOrderRules.Checks.rec
      (motive_2 := fun trees patterns _ => ∀ Xs : List Pattern, patterns = Xs.map holdsP →
        checkRawChildren definition (Xs.map patValue) (decodeProofs trees) = true) with
  | premise lookup => simp at lookup
  | @rule invocation encoded children lookup arity _ _ _ childrenIH =>
      intro X shape
      rw [lookupRule?_encoded] at lookup
      obtain ⟨rule, ruleLookup, rfl⟩ := Option.map_eq_some_iff.mp lookup
      have member := lookupRule?_member ruleLookup
      have formals := metavariables_eq firstOrder member
      have arity' : invocation.arguments.length = (ruleNames rule).length := by
        simpa [encodeRule] using arity
      have premiseSchemas := firstOrder.premiseSchemas rule member
      have conclusionSchema := firstOrder.conclusionSchema rule member
      have agree : ∀ name ∈ ruleNames rule,
          bindingValue ((ruleNames rule).zip (invocation.arguments.map patValue)) name =
            patValue (bindingValue ((ruleNames rule).zip invocation.arguments) name) :=
        fun name nameMember => bindingValue_map patValue nameMember arity'
      rw [encodeRule_instConclusion, applyBindings_encodeSchema _ conclusionSchema] at shape
      have conclusionValue : patValue X =
          substSchema (bindingValue ((ruleNames rule).zip (invocation.arguments.map patValue)))
            rule.conclusion := by
        simp only [holdsP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        rw [← shape]
        exact patValue_encodeWith agree conclusionSchema
      have childrenAccepted := childrenIH
        (rule.premises.map (encodeWith (bindingValue ((ruleNames rule).zip invocation.arguments))))
        (by rw [instPremises_encodeWith rfl premiseSchemas, List.map_map]; rfl)
      rw [map_patValue_encodeWith agree premiseSchemas] at childrenAccepted
      have instantiated :
          instantiateRule? definition
              { ruleId := invocation.ruleId, arguments := invocation.arguments.map patValue } =
            some (substSchemas (bindingValue ((ruleNames rule).zip (invocation.arguments.map patValue)))
              rule.premises,
              substSchema (bindingValue ((ruleNames rule).zip (invocation.arguments.map patValue)))
                rule.conclusion) := by
        refine instantiateRule?_of
          (ruleInstance := { ruleId := invocation.ruleId, arguments := invocation.arguments.map patValue })
          (rule := rule) ruleLookup ?_ ?_ ?_ ?_
        · rw [formals]
          exact argumentsValidAt_patValue _ _ arity'
        · simp [RuleSchema.sideConditionsHold, firstOrder.noSideConditions rule member]
        · rw [formals, instantiateSchemas?]
          exact instantiateSchemasAt?_eq (by simpa using arity') premiseSchemas
        · rw [formals, instantiateSchema?]
          exact instantiateSchemaAt?_eq (by simpa using arity') conclusionSchema
      rw [decodeProof, checkRaw, instantiated]
      simp only [conclusionValue, decide_true, Bool.true_and]
      exact childrenAccepted
  | nil =>
      rename_i Xs shape
      cases Xs with
      | nil => simp [decodeProofs, checkRawChildren]
      | cons _ _ => simp at shape
  | cons _ _ headIH tailIH =>
      rename_i Xs shape
      cases Xs with
      | nil => simp at shape
      | cons X Xs =>
          simp only [List.map_cons, List.cons.injEq] at shape
          rw [decodeProofs, List.map_cons, checkRawChildren, Bool.and_eq_true]
          exact ⟨headIH X shape.1, tailIH Xs shape.2⟩

/-! ## Sizes -/

mutual
  /-- The size of a pattern: one per node and per argument edge, plus the characters of its
  constructor names. Binder nodes count one, as first-order rules never look inside them. -/
  def weight : Pattern → ℕ
    | .apply name arguments => 1 + name.length + weights arguments
    | _ => 1

  def weights : List Pattern → ℕ
    | [] => 0
    | pattern :: patterns => 1 + weight pattern + weights patterns
end

mutual
  /-- The size of a raw proof of the checker. -/
  def proofWeight : RawProof → ℕ
    | .node ruleInstance children => weights ruleInstance.arguments + proofWeights children + 1

  def proofWeights : List RawProof → ℕ
    | [] => 0
    | proof :: proofs => proofWeight proof + proofWeights proofs
end

theorem char_toNat_lt (c : Char) : c.toNat < 0x110000 := by
  have valid := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at valid
  change c.val.toNat < 0x110000
  omega

theorem patternSize_numP : ∀ (k n : ℕ), n + 1 < 2 ^ k → patternSize (numP n) ≤ k
  | 0, _, small => by simp at small
  | k + 1, 0, _ => by simp [numP, patternSize, patternSizes]
  | k + 1, n + 1, small => by
      have half : n / 2 + 1 < 2 ^ k := by
        rw [Nat.pow_succ] at small
        omega
      have previous := patternSize_numP k (n / 2) half
      rw [numP]
      split <;> simp only [patternSize, patternSizes] <;> omega

theorem patternSize_strP : ∀ cs : List Char, patternSize (strP cs) ≤ 1 + 22 * cs.length
  | [] => by simp [strP, patternSize, patternSizes]
  | c :: cs => by
      have code := patternSize_numP 21 c.toNat (by have := char_toNat_lt c; omega)
      have rest := patternSize_strP cs
      simp only [strP, patternSize, patternSizes, List.length_cons] at rest ⊢
      omega

mutual
  /-- The encoding of a pattern is at most twenty-two times its size. -/
  theorem patternSize_patP (pattern : Pattern) : patternSize (patP pattern) ≤ 22 * weight pattern := by
    cases pattern with
    | apply name arguments =>
        have nameSize := patternSize_strP name.toList
        have argumentSize := patternSize_patsP arguments
        rw [patP, weight]
        simp only [patternSize, patternSizes, String.length_toList] at nameSize ⊢
        omega
    | _ => simp [patP, weight, strP, patternSize, patternSizes]

  theorem patternSize_patsP (patterns : List Pattern) :
      patternSize (patsP patterns) ≤ 1 + 22 * weights patterns := by
    cases patterns with
    | nil => simp [patsP, weights, patternSize, patternSizes]
    | cons pattern patterns =>
        have first := patternSize_patP pattern
        have rest := patternSize_patsP patterns
        rw [patsP, weights]
        simp only [patternSize, patternSizes] at rest ⊢
        omega
end

theorem one_le_patternSize (pattern : Pattern) : 1 ≤ patternSize pattern := by
  cases pattern <;> simp [patternSize]

/-- A string term has at least one node more than characters. -/
theorem length_strValue (pattern : Pattern) : (strValue pattern).length + 1 ≤ patternSize pattern := by
  unfold strValue
  split
  · rename_i c rest
    have restBound := length_strValue rest
    have codeBound := one_le_patternSize c
    simp only [List.length_cons, patternSize, patternSizes]
    omega
  · simp only [List.length_nil]
    exact one_le_patternSize _
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

mutual
  /-- Decoding never grows: a decoded pattern is no larger than the term it came from. -/
  theorem weight_patValue (pattern : Pattern) : weight (patValue pattern) ≤ patternSize pattern := by
    unfold patValue
    split
    · rename_i name arguments
      have nameBound := length_strValue name
      have argumentBound := weights_patsValue arguments
      simp only [weight, String.length_ofList, patternSize, patternSizes]
      omega
    · simp only [weight]
      exact one_le_patternSize _
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem weights_patsValue (pattern : Pattern) : weights (patsValue pattern) ≤ patternSize pattern := by
    unfold patsValue
    split
    · rename_i first rest
      have firstBound := weight_patValue first
      have restBound := weights_patsValue rest
      simp only [weights, patternSize, patternSizes]
      omega
    · simp only [weights]
      exact Nat.zero_le _
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  theorem rawSize_encodeProof (proof : RawProof) :
      rawSize (encodeProof proof) ≤ 22 * proofWeight proof := by
    cases proof with
    | node ruleInstance children =>
        have arguments := patternSizes_map_patP ruleInstance.arguments
        have rest := rawSizes_encodeProofs children
        rw [encodeProof, proofWeight]
        simp only [rawSize]
        omega

  theorem rawSizes_encodeProofs (proofs : List RawProof) :
      rawSizes (encodeProofs proofs) ≤ 22 * proofWeights proofs := by
    cases proofs with
    | nil => simp [encodeProofs, rawSizes, proofWeights]
    | cons proof proofs =>
        have first := rawSize_encodeProof proof
        have rest := rawSizes_encodeProofs proofs
        rw [encodeProofs, proofWeights]
        simp only [rawSizes]
        omega

  theorem patternSizes_map_patP (patterns : List Pattern) :
      patternSizes (patterns.map patP) ≤ 22 * weights patterns := by
    cases patterns with
    | nil => simp [patternSizes, weights]
    | cons pattern patterns =>
        have first := patternSize_patP pattern
        have rest := patternSizes_map_patP patterns
        simp only [List.map_cons, patternSizes, weights]
        omega
end

theorem weights_map_patValue : ∀ patterns : List Pattern,
    weights (patterns.map patValue) ≤ patternSizes patterns + patterns.length
  | [] => by simp [weights, patternSizes]
  | pattern :: patterns => by
      have first := weight_patValue pattern
      have rest := weights_map_patValue patterns
      simp only [List.map_cons, weights, patternSizes, List.length_cons]
      omega

theorem length_le_patternSizes : ∀ patterns : List Pattern, patterns.length ≤ patternSizes patterns
  | [] => by simp
  | pattern :: patterns => by
      have first := one_le_patternSize pattern
      have rest := length_le_patternSizes patterns
      simp only [List.length_cons, patternSizes]
      omega

mutual
  theorem proofWeight_decodeProof (tree : RawOpenProof) :
      proofWeight (decodeProof tree) ≤ 2 * rawSize tree := by
    cases tree with
    | premise index => simp [decodeProof, proofWeight, weights, proofWeights, rawSize]
    | node invocation children =>
        have arguments := weights_map_patValue invocation.arguments
        have counted := length_le_patternSizes invocation.arguments
        have rest := proofWeights_decodeProofs children
        rw [decodeProof, proofWeight]
        simp only [rawSize]
        omega

  theorem proofWeights_decodeProofs (trees : List RawOpenProof) :
      proofWeights (decodeProofs trees) ≤ 2 * rawSizes trees := by
    cases trees with
    | nil => simp [decodeProofs, proofWeights, rawSizes]
    | cons tree trees =>
        have first := proofWeight_decodeProof tree
        have rest := proofWeights_decodeProofs trees
        rw [decodeProofs, proofWeights]
        simp only [rawSizes]
        omega
end

/-! ## Claims as MM0 terms -/

/-- The constructor names of the grammar, in order. -/
abbrev universalNames : List String := constructorNames universalLanguage

/-- The MM0 term of a numeral. -/
def numTerm : ℕ → Preterm
  | 0 => .term 0
  | n + 1 =>
      if n % 2 = 0 then Preterm.applyArgs (.term 1) [numTerm (n / 2)]
      else Preterm.applyArgs (.term 2) [numTerm (n / 2)]
termination_by n => n
decreasing_by all_goals omega

def strTerm : List Char → Preterm
  | [] => .term 3
  | c :: cs => Preterm.applyArgs (.term 4) [numTerm c.toNat, strTerm cs]

mutual
  def patTerm : Pattern → Preterm
    | .apply name arguments => Preterm.applyArgs (.term 5) [strTerm name.toList, patsTerm arguments]
    | _ => Preterm.applyArgs (.term 5) [strTerm [], .term 6]

  def patsTerm : List Pattern → Preterm
    | [] => .term 6
    | pattern :: patterns => Preterm.applyArgs (.term 7) [patTerm pattern, patsTerm patterns]
end

/-- The MM0 term of the judgment that a pattern holds. -/
def holdsTerm (pattern : Pattern) : Preterm := Preterm.applyArgs (.term 8) [patTerm pattern]

theorem encodes_numP (n : ℕ) : Encodes universalNames (numP n) (numTerm n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero =>
          rw [numP, numTerm]
          exact Encodes.constructor (encoded := []) (by decide) .nil
      | succ n =>
          rw [numP, numTerm]
          by_cases parity : n % 2 = 0
          · rw [if_pos parity, if_pos parity]
            exact Encodes.constructor (by decide) (.cons (ih _ (by omega)) .nil)
          · rw [if_neg parity, if_neg parity]
            exact Encodes.constructor (by decide) (.cons (ih _ (by omega)) .nil)

theorem encodes_strP : ∀ cs : List Char, Encodes universalNames (strP cs) (strTerm cs)
  | [] => Encodes.constructor (encoded := []) (by decide) .nil
  | c :: cs => Encodes.constructor (by decide)
      (.cons (encodes_numP c.toNat) (.cons (encodes_strP cs) .nil))

mutual
  theorem encodes_patP (pattern : Pattern) : Encodes universalNames (patP pattern) (patTerm pattern) := by
    cases pattern with
    | apply name arguments =>
        rw [patP, patTerm]
        exact Encodes.constructor (by decide)
          (.cons (encodes_strP _) (.cons (encodes_patsP arguments) .nil))
    | _ =>
        simp only [patP, patTerm]
        exact Encodes.constructor (by decide)
          (.cons (encodes_strP []) (.cons (Encodes.constructor (encoded := []) (by decide) .nil) .nil))

  theorem encodes_patsP (patterns : List Pattern) :
      Encodes universalNames (patsP patterns) (patsTerm patterns) := by
    cases patterns with
    | nil =>
        rw [patsP, patsTerm]
        exact Encodes.constructor (encoded := []) (by decide) .nil
    | cons pattern patterns =>
        rw [patsP, patsTerm]
        exact Encodes.constructor (by decide)
          (.cons (encodes_patP pattern) (.cons (encodes_patsP patterns) .nil))
end

theorem encodes_holds (pattern : Pattern) :
    Encodes universalNames (holdsP (patP pattern)) (holdsTerm pattern) :=
  Encodes.constructor (by decide) (.cons (encodes_patP pattern) .nil)

/-! ## Claims and checkers -/

/-- A claim of a first-order calculus: a first-order pattern. -/
abbrev FirstOrderClaim := { goal : Pattern // FirstOrder goal }

/-- A checker read through a map of claims. -/
def comapChecker {Claim Claim' Certificate : Type} (f : Claim' → Claim)
    (checker : SizedChecker Claim Certificate) : SizedChecker Claim' Certificate where
  check claim certificate := checker.check (f claim) certificate
  claimSize claim := checker.claimSize (f claim)
  certificateSize := checker.certificateSize

/-- A p-simulation read through a map of claims. -/
def comapSimulation {Claim Claim' First Second : Type} (f : Claim' → Claim)
    {target : SizedChecker Claim First} {source : SizedChecker Claim Second}
    (simulation : PSimulation target source) :
    PSimulation (comapChecker f target) (comapChecker f source) where
  translate claim certificate := simulation.translate (f claim) certificate
  preserves claim certificate accepted := simulation.preserves (f claim) certificate accepted
  sizeBound := by
    obtain ⟨p, bound⟩ := simulation.sizeBound
    exact ⟨p, fun input => bound (f input.1, input.2)⟩
  translationTime claim certificate := simulation.translationTime (f claim) certificate
  timeBound := by
    obtain ⟨p, bound⟩ := simulation.timeBound
    exact ⟨p, fun input => bound (f input.1, input.2)⟩

section Checkers

variable {definition : ValidatedCalculusLanguageDef} (firstOrder : FirstOrderCalculus definition.1)

theorem equationFree :
    (presentation definition.1 firstOrder).syntaxSignature.language.equations = [] := by
  rw [(presentation_retains firstOrder).1]
  rfl

/-- The sequent of the presentation that renders a claim. -/
def toSequent (claim : FirstOrderClaim) :
    CertificateSimulation.EncodedSequent (presentation definition.1 firstOrder) where
  bound := []
  hypotheses := []
  pattern := holdsP (patP claim.1)
  context := []
  targetHypotheses := []
  expression := holdsTerm claim.1
  contexts := by
    rw [Signature.sorts, (presentation_retains firstOrder).1]
    exact .nil
  localScope := .nil
  encoded := by
    rw [Signature.names, (presentation_retains firstOrder).1]
    exact encodes_holds claim.1

/-- The inference checker on first-order claims. -/
def calculusChecker : SizedChecker FirstOrderClaim RawProof where
  check claim proof := checkRaw definition claim.1 proof
  claimSize claim := (toSequent firstOrder claim).size
  certificateSize := proofWeight

/-- The presentation's tree checker on the rendering of first-order claims. -/
def treeChecker : SizedChecker FirstOrderClaim RawOpenProof :=
  comapChecker (toSequent firstOrder)
    (CertificateSimulation.sourceChecker (presentation definition.1 firstOrder))

/-- The MM0 kernel on the rendering of first-order claims. -/
def mm0Checker : SizedChecker FirstOrderClaim ProofWitness :=
  comapChecker (toSequent firstOrder)
    (CertificateSimulation.targetChecker (presentation definition.1 firstOrder))

theorem treeChecker_check (claim : FirstOrderClaim) (tree : RawOpenProof) :
    (treeChecker firstOrder).check claim tree = true ↔
      SortedFirstOrderRules.Checks universalLanguage (encodedRules definition.1) [] [] tree
        (holdsP (patP claim.1)) := by
  obtain ⟨sameLanguage, -, sameRules⟩ := presentation_retains firstOrder
  change decide (SortedFirstOrderRules.proof? (presentation definition.1 firstOrder).syntaxSignature.language
    (presentation definition.1 firstOrder).rules [] [] tree = some (holdsP (patP claim.1))) = true ↔ _
  rw [sameLanguage, sameRules, decide_eq_true_eq]
  exact ⟨SortedFirstOrderRules.proof?_sound, SortedFirstOrderRules.Checks.eval⟩

/-- The presentation's trees p-simulate the inference checker: proofs encode, and the tree
is at most twenty-two times the proof. -/
def encodeSimulation : PSimulation (treeChecker firstOrder) (calculusChecker firstOrder) where
  translate _ proof := encodeProof proof
  preserves claim proof accepted :=
    (treeChecker_check firstOrder claim (encodeProof proof)).mpr
      (encode_accepted firstOrder claim.1 proof accepted)
  sizeBound := ⟨Polynomial.C 22 * Polynomial.X, fun input => by
    have bound := rawSize_encodeProof input.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change rawSize (encodeProof input.2) ≤
      22 * ((toSequent firstOrder input.1).size + proofWeight input.2)
    omega⟩
  translationTime _ proof := rawSize (encodeProof proof) + proofWeight proof
  timeBound := ⟨Polynomial.C 23 * Polynomial.X, fun input => by
    have bound := rawSize_encodeProof input.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change rawSize (encodeProof input.2) + proofWeight input.2 ≤
      23 * ((toSequent firstOrder input.1).size + proofWeight input.2)
    omega⟩

/-- The inference checker p-simulates the presentation's trees: trees decode, and the proof
is at most twice the tree. -/
def decodeSimulation : PSimulation (calculusChecker firstOrder) (treeChecker firstOrder) where
  translate _ tree := decodeProof tree
  preserves claim tree accepted := by
    have checked := (treeChecker_check firstOrder claim tree).mp accepted
    have decoded := decode_accepted firstOrder checked (patP claim.1) rfl
    rw [patValue_patP claim.2] at decoded
    exact decoded
  sizeBound := ⟨Polynomial.C 2 * Polynomial.X, fun input => by
    have bound := proofWeight_decodeProof input.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change proofWeight (decodeProof input.2) ≤
      2 * ((toSequent firstOrder input.1).size + rawSize input.2)
    omega⟩
  translationTime _ tree := rawSize tree + proofWeight (decodeProof tree)
  timeBound := ⟨Polynomial.C 3 * Polynomial.X, fun input => by
    have bound := proofWeight_decodeProof input.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change rawSize input.2 + proofWeight (decodeProof input.2) ≤
      3 * ((toSequent firstOrder input.1).size + rawSize input.2)
    omega⟩

/-- **MM0 p-simulates every first-order calculus of the inference checker.** -/
def mm0Simulation : PSimulation (mm0Checker firstOrder) (calculusChecker firstOrder) :=
  (comapSimulation (toSequent firstOrder)
    (CertificateSimulation.compileSimulation (presentation definition.1 firstOrder))).trans
    (encodeSimulation firstOrder) rfl

/-- **Every first-order calculus of the inference checker p-simulates MM0.** -/
def calculusSimulation : PSimulation (calculusChecker firstOrder) (mm0Checker firstOrder) :=
  (decodeSimulation firstOrder).trans
    (comapSimulation (toSequent firstOrder)
      (CertificateEquivalence.decompileSimulation (presentation definition.1 firstOrder)
        (equationFree firstOrder))) rfl

/-- **MM0 and a first-order calculus of the inference checker p-simulate each other.** -/
def pEquivalent :
    PSimulation (mm0Checker firstOrder) (calculusChecker firstOrder) ×
      PSimulation (calculusChecker firstOrder) (mm0Checker firstOrder) :=
  (mm0Simulation firstOrder, calculusSimulation firstOrder)

/-- **A checker with a polynomial trace into a first-order calculus is p-simulated by MM0.**
The checker's claims are rendered as claims of the calculus and measured by their
rendering, and the trace translates the checker's certificates into proofs of the
calculus within polynomial size and time. -/
def traceSimulation {Claim Certificate : Type} {checker : SizedChecker Claim Certificate}
    (render : Claim → FirstOrderClaim)
    (trace : PSimulation (comapChecker render (calculusChecker firstOrder)) checker)
    (measured : (comapChecker render (calculusChecker firstOrder)).claimSize = checker.claimSize) :
    PSimulation (comapChecker render (mm0Checker firstOrder)) checker :=
  (comapSimulation render (mm0Simulation firstOrder)).trans trace measured

end Checkers

/-! ## Controls -/

namespace Controls

open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

/-- The modus ponens calculus is first-order. -/
theorem mp_firstOrder : FirstOrderCalculus mpValidated.1 :=
  firstOrderCheck_sound (by decide +kernel)

/-- The claim `P(B)`. -/
def claimB : FirstOrderClaim := ⟨judgmentP formulaB, .apply (.cons (.apply .nil) .nil)⟩

/-- MM0 accepts the translation of the certificate of `P(B)`. -/
theorem mm0_accepts_B :
    (mm0Checker mp_firstOrder).check claimB
      ((mm0Simulation mp_firstOrder).translate claimB mpCertificate) = true :=
  (mm0Simulation mp_firstOrder).preserves claimB mpCertificate mp_accepts

/-- The same certificate does not prove `P(A)`. -/
example : checkRaw mpValidated (judgmentP formulaA) mpCertificate = false := mp_rejects_wrong_goal

/-- A rule with a metavariable of arity one is outside the class: that is the binder tier. -/
def binderRule : RuleSchema where
  id := ⟨"b"⟩
  metavariables := [("x", 1)]
  premises := []
  conclusion := judgmentP (.fvar "x")

example : firstOrderCheck (modusPonens [binderRule]) = false := by decide +kernel

/-- Bijective binary: five is `n1 (n2 nz)`. -/
example : numP 5 = .apply "n1" [.apply "n2" [.apply "nz" []]] := by
  simp [numP]

example : numValue (numP 5) = 5 := numValue_numP 5

end Controls

end Mettapedia.Languages.MM0.Translation.CalculusSimulation
