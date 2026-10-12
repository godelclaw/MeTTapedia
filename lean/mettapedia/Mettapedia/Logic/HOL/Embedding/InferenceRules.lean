import Mettapedia.Logic.HOL.Embedding.FirstOrder
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mettapedia.Logic.HOL.PublishedFacts
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Finite schematic inference rules in HOL

Rule schemas use the existing first-order constructor/metavariable fragment.
Their HOL representation consists of data constructors, one `holds` predicate,
and universally closed implication chains. The interpretation uses closed
canonical source patterns as its data domain; closed binder-bearing values may
be supplied as opaque data, without changing the rule-schema fragment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.Embedding.InferenceRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

abbrev Data := {pattern : Pattern // argumentValidAt 0 pattern = true}

theorem valid_apply_iff (name : String) (arguments : List Pattern) :
    argumentValidAt 0 (.apply name arguments) = true ↔
      ∀ argument ∈ arguments, argumentValidAt 0 argument = true := by
  induction arguments with
  | nil => simp [argumentValidAt, Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  | cons first rest ih =>
      simp only [argumentValidAt, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        Bool.and_eq_true] at ih ⊢
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

def Data.default : Data := ⟨.apply "" [], (valid_apply_iff "" []).mpr (by simp)⟩

def Data.constructor (name : String) (arguments : List Data) : Data :=
  ⟨.apply name (arguments.map Subtype.val), (valid_apply_iff _ _).mpr (by
    intro argument member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    exact value.property)⟩

def Data.opaque (pattern : Pattern) : Data :=
  if valid : argumentValidAt 0 pattern = true then ⟨pattern, valid⟩ else Data.default

inductive Function : Nat → Type where
  | constructor (name : String) (arity : Nat) : Function arity
  | literal (value : Data) : Function 0

inductive Relation : Nat → Type where
  | holds : Relation 1

abbrev language : LO.FirstOrder.Language where
  Func := Function
  Rel := Relation

abbrev Symbol := FirstOrder.Const language
abbrev dataTy := FirstOrder.indTy

/-- Interpret all constructor operations in the existing canonical source carrier. -/
@[instance_reducible] def sourceStructure (rules : List FORule) :
    LO.FirstOrder.Structure language Data where
  func := fun {_} symbol values => match symbol with
    | .constructor name _ => Data.constructor name (List.ofFn values)
    | .literal value => value
  rel := fun {_} symbol values => match symbol with
    | .holds => FODerivable rules (values 0).val

abbrev model (rules : List FORule) : HenkinModel FirstOrder.BaseTy Symbol :=
  FirstOrder.standardModel (sourceStructure rules)

def encodeWith {Γ : Ctx FirstOrder.BaseTy}
    (values : String → Term Symbol Γ dataTy) : Pattern → Term Symbol Γ dataTy
  | .fvar name => values name
  | .apply name arguments =>
      FirstOrder.Term.mkApps (L := language)
        (.const (.func (Function.constructor name arguments.length)))
        (fun index => encodeWith values arguments[index.val])
  | pattern => .const (FirstOrder.Const.func (L := language) (k := 0)
      (Function.literal (Data.opaque pattern)))
termination_by pattern => sizeOf pattern
decreasing_by
  have member : arguments[index.val] ∈ arguments := List.getElem_mem (l := arguments) index.isLt
  sizeOf_pattern_dec

def realizeWith (values : String → Data) : Pattern → Data
  | .fvar name => values name
  | .apply name arguments => Data.constructor name (arguments.map (realizeWith values))
  | pattern => Data.opaque pattern
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

def holds {Γ : Ctx FirstOrder.BaseTy} (value : Term Symbol Γ dataTy) : Formula Symbol Γ :=
  .app (.const (FirstOrder.Const.rel (L := language) (k := 1) Relation.holds)) value

def encode (pattern : Pattern) : Term Symbol [] dataTy :=
  encodeWith (fun _ => .const (FirstOrder.Const.func (L := language) (k := 0)
    (Function.literal Data.default))) pattern

def judgment (pattern : Pattern) : ClosedFormula Symbol := holds (encode pattern)

/-- Numbered formals retain the source rule's authored order. -/
def formalValues (names : List String) (name : String) :
    Term Symbol (FirstOrder.CtxOfArity names.length) dataTy :=
  if member : name ∈ names then
    .var (Var.ofFinRepeat dataTy names.length
      ⟨names.idxOf name, List.idxOf_lt_length_iff.mpr member⟩)
  else .const (FirstOrder.Const.func (L := language) (k := 0) (Function.literal Data.default))

def openRule (rule : FORule) : Formula Symbol (FirstOrder.CtxOfArity rule.vars.length) :=
  hypChain (rule.premises.map (fun premise => holds (encodeWith (formalValues rule.vars) premise)))
    (holds (encodeWith (formalValues rule.vars) rule.conclusion))

def ruleFormula (rule : FORule) : ClosedFormula Symbol :=
  closeAll (FirstOrder.CtxOfArity rule.vars.length) (openRule rule)

/-- Exactly one closed HOL axiom per source rule row. -/
def axioms (rules : List FORule) : List (ClosedFormula Symbol) := rules.map ruleFormula

def theory (rules : List FORule) : ClosedTheorySet Symbol := {formula | formula ∈ axioms rules}

/-- The target term interpretation follows the source constructor algebra. -/
theorem denote_encodeWith (rules : List FORule) {Γ : Ctx FirstOrder.BaseTy}
    (values : String → Term Symbol Γ dataTy) (valuation : (model rules).Valuation Γ)
    (pattern : Pattern) :
    (model rules).denote (encodeWith values pattern) valuation =
      ULift.up (realizeWith (fun name => ((model rules).denote (values name) valuation).down)
        pattern) := by
  cases pattern with
  | fvar name =>
      simp only [encodeWith, realizeWith]
      apply ULift.down_injective
      rfl
  | apply name arguments =>
      rw [encodeWith, FirstOrder.denote_mkApps (sourceStructure rules)]
      change FirstOrder.Const.applyCurried
          (FirstOrder.Const.curryVec (τ := dataTy)
            (fun values => ULift.up (Data.constructor name
              (List.ofFn (fun index => (values index).down)))))
          (fun index => (model rules).denote (encodeWith values arguments[index.val]) valuation) = _
      rw [FirstOrder.Const.applyCurried_curryVec]
      simp only [realizeWith]
      apply congrArg ULift.up
      apply congrArg (Data.constructor name)
      have children : (fun index : Fin arguments.length =>
          ((model rules).denote (encodeWith values arguments[index.val]) valuation).down) =
          (fun index : Fin arguments.length =>
            realizeWith (fun variableName =>
              ((model rules).denote (values variableName) valuation).down) arguments[index.val]) := by
        funext index
        rw [denote_encodeWith rules values valuation arguments[index.val]]
      rw [children]
      exact List.ofFn_getElem_eq_map arguments _
  | _ =>
      simp only [encodeWith, realizeWith]
      rfl
termination_by sizeOf pattern
decreasing_by
  have member : arguments[index.val] ∈ arguments := List.getElem_mem (l := arguments) index.isLt
  sizeOf_pattern_dec

theorem denote_holds (rules : List FORule) {Γ : Ctx FirstOrder.BaseTy}
    (value : Term Symbol Γ dataTy) (valuation : (model rules).Valuation Γ) :
    ((model rules).denote (holds value) valuation).down ↔
      FODerivable rules (((model rules).denote value valuation).down.val) := Iff.rfl

theorem realizeWith_eq_self {pattern : Pattern} (valid : argumentValidAt 0 pattern = true)
    (values : String → Data) : (realizeWith values pattern).val = pattern := by
  cases pattern with
  | fvar name => simp [argumentValidAt, Pattern.isGroundAt] at valid
  | apply name arguments =>
      simp only [realizeWith, Data.constructor, List.map_map]
      apply congrArg (Pattern.apply name)
      have same : arguments.map (fun child => (realizeWith values child).val) =
          arguments.map id := List.map_congr_left (fun child member =>
            realizeWith_eq_self ((valid_apply_iff _ _).mp valid child member) values)
      simpa only [List.map_id, Function.comp_def] using same
  | _ => simp [realizeWith, Data.opaque, valid]
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem models_judgment_iff (rules : List FORule) {pattern : Pattern}
    (valid : argumentValidAt 0 pattern = true) :
    (model rules).models (judgment pattern) ↔ FODerivable rules pattern := by
  change ((model rules).denote (holds (encode pattern)) _).down ↔ _
  rw [denote_holds, encode, denote_encodeWith, realizeWith_eq_self valid]

/-- Ordinary schemas expose precisely the supplied metavariable assignment. -/
theorem realizeWith_applyBindings {names : List String} {pattern : Pattern}
    (schema : Schema names pattern) (values : String → Data) (bindings : Bindings)
    (agree : ∀ name ∈ names, bindings.find? (fun entry => entry.1 == name) =
      some (name, (values name).val)) :
    (realizeWith values pattern).val = applyBindings bindings pattern := by
  cases schema with
  | metavariable member => simp only [realizeWith, applyBindings, agree _ member]
  | @constructor name arguments children =>
      simp only [realizeWith, Data.constructor, applyBindings, List.map_map]
      apply congrArg (Pattern.apply name)
      apply List.map_congr_left
      intro argument member
      exact realizeWith_applyBindings (children.member member) values bindings agree
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

def valuationArguments (rules : List FORule) (names : List String)
    (valuation : (model rules).Valuation (FirstOrder.CtxOfArity names.length)) : List Pattern :=
  List.ofFn (fun index : Fin names.length =>
    (valuation (Var.ofFinRepeat dataTy names.length index)).down.val)

theorem valuationArguments_length (rules : List FORule) (names : List String)
    (valuation : (model rules).Valuation (FirstOrder.CtxOfArity names.length)) :
    (valuationArguments rules names valuation).length = names.length := List.length_ofFn

theorem valuationArguments_valid (rules : List FORule) (names : List String)
    (valuation : (model rules).Valuation (FirstOrder.CtxOfArity names.length)) :
    ∀ argument ∈ valuationArguments rules names valuation, argumentValidAt 0 argument = true := by
  intro argument member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact (valuation (Var.ofFinRepeat dataTy names.length index)).down.property

theorem formalBindings_agree (rules : List FORule) {names : List String}
    (distinct : names.Nodup)
    (valuation : (model rules).Valuation (FirstOrder.CtxOfArity names.length)) :
    ∀ name ∈ names,
      (names.zip (valuationArguments rules names valuation)).find? (fun entry => entry.1 == name) =
        some (name, ((model rules).denote (formalValues names name) valuation).down.val) := by
  intro name member
  have found := find?_zip distinct (List.getElem?_idxOf member)
    (arguments := valuationArguments rules names valuation)
    (argument := (valuation (Var.ofFinRepeat dataTy names.length
      ⟨names.idxOf name, List.idxOf_lt_length_iff.mpr member⟩)).down.val)
    (by simp [valuationArguments, List.idxOf_lt_length_iff.mpr member])
  simpa only [formalValues, dif_pos member, HenkinModel.denote, PreModel.denote] using found

/-- Admission of the ordinary first-order rule schemas, independently of a checker. -/
structure SchemaPackage (rules : List FORule) : Prop where
  nodup : ∀ rule ∈ rules, rule.vars.Nodup
  premises : ∀ rule ∈ rules, Schemas rule.vars rule.premises
  conclusion : ∀ rule ∈ rules, Schema rule.vars rule.conclusion

theorem model_openRule (rules : List FORule) (package : SchemaPackage rules)
    {rule : FORule} (member : rule ∈ rules)
    (valuation : (model rules).Valuation (FirstOrder.CtxOfArity rule.vars.length)) :
    ((model rules).denote (openRule rule) valuation).down := by
  rw [openRule, denote_hypChain_iff]
  intro premiseProofs
  let arguments := valuationArguments rules rule.vars valuation
  have instances (pattern : Pattern) (schema : Schema rule.vars pattern) :
      (((model rules).denote (encodeWith (formalValues rule.vars) pattern) valuation).down.val) =
        applyBindings (rule.vars.zip arguments) pattern := by
    rw [denote_encodeWith]
    exact realizeWith_applyBindings schema _ _
      (formalBindings_agree rules (package.nodup rule member) valuation)
  apply (denote_holds rules _ valuation).mpr
  rw [instances _ (package.conclusion rule member)]
  apply FODerivable.rule rule member arguments
    (valuationArguments_length rules rule.vars valuation)
    (valuationArguments_valid rules rule.vars valuation)
  intro premise premiseMember
  obtain ⟨pattern, patternMember, rfl⟩ := List.mem_map.mp premiseMember
  have proved := premiseProofs (holds (encodeWith (formalValues rule.vars) pattern))
    (List.mem_map.mpr ⟨pattern, patternMember, rfl⟩)
  apply (instances pattern ((package.premises rule member).member patternMember)) ▸
    ((denote_holds rules _ valuation).mp proved)

theorem model_ruleFormula (rules : List FORule) (package : SchemaPackage rules)
    {rule : FORule} (member : rule ∈ rules) : (model rules).models (ruleFormula rule) := by
  apply (models_closeAll_iff_of_fullDomains (model rules)
    (HenkinModel.fullDomains_standard _ _) _ _).mpr
  exact model_openRule rules package member

theorem model_theory (rules : List FORule) (package : SchemaPackage rules)
    {formula : ClosedFormula Symbol} (member : formula ∈ theory rules) :
    (model rules).models formula := by
  obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
  exact model_ruleFormula rules package ruleMember

/-- Arbitrary target HOL reasoning cannot introduce a new source judgment. -/
theorem reflects {rules : List FORule} (package : SchemaPackage rules) {pattern : Pattern}
    (valid : argumentValidAt 0 pattern = true)
    (proof : (theory rules).Provable (judgment pattern)) : FODerivable rules pattern := by
  obtain ⟨hypotheses, members, derivation⟩ := proof
  have satisfied := Soundness.extDerivation_sound derivation (M := model rules)
    (HenkinModel.functionsRespectEqv_of_fullDomains _ (HenkinModel.fullDomains_standard _ _))
    (fun index => nomatch index)
    (fun formula member => model_theory rules package (members formula member))
  exact (models_judgment_iff rules valid).mp satisfied

theorem not_provable_of_not_derivable {rules : List FORule} (package : SchemaPackage rules)
    {pattern : Pattern} (valid : argumentValidAt 0 pattern = true)
    (underivable : ¬ FODerivable rules pattern) : ¬ (theory rules).Provable (judgment pattern) :=
  fun proof => underivable (reflects package valid proof)

theorem subst_encodeWith {Γ Δ : Ctx FirstOrder.BaseTy}
    (substitution : Subst Symbol Γ Δ) (values : String → Term Symbol Γ dataTy)
    (pattern : Pattern) :
    subst substitution (encodeWith values pattern) =
      encodeWith (fun name => subst substitution (values name)) pattern := by
  cases pattern with
  | fvar name => simp only [encodeWith]
  | apply name arguments =>
      rw [encodeWith, FirstOrder.Term.subst_mkApps]
      simp only [subst, encodeWith]
      congr 1
      funext index
      exact subst_encodeWith substitution values arguments[index.val]
  | _ => simp only [encodeWith, subst]
termination_by sizeOf pattern
decreasing_by
  have member : arguments[index.val] ∈ arguments := List.getElem_mem (l := arguments) index.isLt
  sizeOf_pattern_dec

theorem encodeWith_congr {names : List String} {pattern : Pattern}
    (schema : Schema names pattern) {Γ : Ctx FirstOrder.BaseTy}
    {first second : String → Term Symbol Γ dataTy}
    (agree : ∀ name ∈ names, first name = second name) :
    encodeWith first pattern = encodeWith second pattern := by
  cases schema with
  | metavariable member => simpa only [encodeWith] using agree _ member
  | @constructor name arguments children =>
      simp only [encodeWith]
      congr 1
      funext index
      exact encodeWith_congr (children.member (List.getElem_mem (l := arguments) index.isLt)) agree
termination_by sizeOf pattern
decreasing_by
  have member : arguments[index.val] ∈ arguments := List.getElem_mem (l := arguments) index.isLt
  sizeOf_pattern_dec

theorem encode_applyBindings {names : List String} {pattern : Pattern}
    (schema : Schema names pattern) (values : String → Pattern) (bindings : Bindings)
    (agree : ∀ name ∈ names, bindings.find? (fun entry => entry.1 == name) =
      some (name, values name)) :
    encode (applyBindings bindings pattern) = encodeWith (fun name => encode (values name)) pattern := by
  cases schema with
  | metavariable member => simp only [applyBindings, agree _ member, encodeWith]
  | @constructor name arguments children =>
      rw [applyBindings, encode, encodeWith, encodeWith]
      rw [FirstOrder.Term.mkApps_map
        (fun arity => .const (FirstOrder.Const.func (L := language)
          (Function.constructor name arity))) arguments (applyBindings bindings)]
      congr 1
      funext index
      simpa only [encode] using
        encode_applyBindings (children.member (List.getElem_mem (l := arguments) index.isLt))
          values bindings agree
termination_by sizeOf pattern
decreasing_by
  have member : arguments[index.val] ∈ arguments := List.getElem_mem (l := arguments) index.isLt
  sizeOf_pattern_dec

namespace Controls

def atom : Pattern := .apply "fact" []

def fact : FORule := ⟨"fact", [], [], atom⟩

theorem fact_package : SchemaPackage [fact] := by
  constructor
  · intro rule member
    have same : rule = fact := by simpa using member
    subst rule
    exact List.nodup_nil
  · intro rule member
    have same : rule = fact := by simpa using member
    subst rule
    exact .nil
  · intro rule member
    have same : rule = fact := by simpa using member
    subst rule
    exact .constructor .nil

theorem fact_valid : argumentValidAt 0 atom = true := by
  apply (valid_apply_iff _ _).mpr
  simp

theorem fact_formula : ruleFormula fact = judgment atom := by
  simp [ruleFormula, openRule, fact, atom, judgment, holds, encode, encodeWith,
    closeAll, hypChain, FirstOrder.Term.mkApps]

theorem fact_provable : (theory [fact]).Provable (judgment atom) := by
  apply ClosedTheorySet.provable_of_mem
  change judgment atom ∈ [ruleFormula fact]
  rw [fact_formula]
  simp

theorem fact_derivable : FODerivable [fact] atom := reflects fact_package fact_valid fact_provable

theorem empty_underivable (pattern : Pattern) : ¬ FODerivable [] pattern := by
  intro proof
  cases proof with
  | rule _ member _ _ _ _ => cases member

theorem empty_package : SchemaPackage [] := by
  constructor <;> intro rule member <;> cases member

theorem empty_refuses : ¬ (theory []).Provable (judgment atom) :=
  not_provable_of_not_derivable empty_package fact_valid (empty_underivable atom)

/-- Adding a conclusion as an axiom invalidates reflection for the original rules. -/
theorem unauthorized_atom :
    (theory [] ∪ {judgment atom}).Provable (judgment atom) ∧ ¬ FODerivable [] atom :=
  ⟨ClosedTheorySet.provable_of_mem (Or.inr rfl), empty_underivable atom⟩

def opaqueBinder : Pattern := .lambda none (.bvar 0)

theorem opaqueBinder_valid : argumentValidAt 0 opaqueBinder = true := by decide

theorem opaqueBinder_retained (values : String → Data) :
    (realizeWith values opaqueBinder).val = opaqueBinder := realizeWith_eq_self opaqueBinder_valid values

theorem escapingBinder_invalid : argumentValidAt 0 (.lambda none (.bvar 1)) = false := by decide

end Controls

end Mettapedia.Logic.HOL.Embedding.InferenceRules
