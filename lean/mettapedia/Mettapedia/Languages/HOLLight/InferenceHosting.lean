import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.OpenTheory.DerivedRulesConnectives
import Mettapedia.Logic.HOL.Embedding.InferenceRules
import Mettapedia.Logic.HOL.TypeDerivedSignature
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence
import Mettapedia.OSLF.MeTTaIL.PatternTokens
import Mathlib.Data.Nat.Digits.Defs

/-!
# Concrete HOL Light symbols for schematic inference presentations

Data has one fixed atomic type. Constructors retain their authored names and
arity; closed literal values retain a flat structural token encoding. Numeric
fields use binary components; literal names have a proved linear storage bound. Every symbol denotes an
ordinary undefined source constant, separate from primitive equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.InferenceHosting

open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory
open Mettapedia.OSLF.MeTTaIL.Syntax


def natComponents (value : Nat) : List String :=
  Mettapedia.OSLF.MeTTaIL.PatternTokens.bits value

def decodeNatComponents (components : List String) : Nat :=
  Nat.ofDigits 2 (components.map fun component => if component = "0" then 0 else 1)

theorem decodeNatComponents_natComponents (value : Nat) :
    decodeNatComponents (natComponents value) = value := by
  unfold decodeNatComponents natComponents Mettapedia.OSLF.MeTTaIL.PatternTokens.bits
  rw [List.map_map]
  have roundtrip : (Nat.digits 2 value).map
      ((fun component : String => if component = "0" then 0 else 1) ∘
        (fun digit => if digit = 0 then "0" else "1")) = Nat.digits 2 value := by
    calc
      _ = (Nat.digits 2 value).map id := by
        apply List.map_congr_left
        intro digit member
        have bound := Nat.digits_lt_base (by decide : 1 < 2) member
        by_cases zero : digit = 0
        · simp [zero]
        · have one : digit = 1 := by omega
          simp [one]
      _ = _ := List.map_id _
  rw [roundtrip, Nat.ofDigits_digits]

theorem natComponents_injective : Function.Injective natComponents :=
  Function.LeftInverse.injective decodeNatComponents_natComponents

def functionName : {arity : Nat} → HOL.Embedding.InferenceRules.Function arity → Name
  | _, .constructor name arity =>
      ⟨["inference", "constructor"] ++ natComponents arity, name⟩
  | _, .literal value =>
      ⟨["inference", "literal"] ++
        Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value.val, ""⟩

/-- Storage of a qualified name, including its component boundaries. -/
def nameSize (name : Name) : Nat :=
  Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize name.namespaceComponents +
    name.component.utf8ByteSize + 1

theorem literal_name_size
    (value : HOL.Embedding.InferenceRules.Data) :
    nameSize (functionName (.literal value)) ≤
      19 + 6 * Mettapedia.OSLF.MeTTaIL.PatternTokens.weight value.val := by
  have prefix : Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize
      ["inference", "literal"] = 18 := by decide
  have empty : "".utf8ByteSize = 0 := by decide
  have bound := Mettapedia.OSLF.MeTTaIL.PatternTokens.encode_size value.val
  simp only [nameSize, functionName, Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize_append,
    prefix, empty]
  omega

theorem constructor_name_size (name : String) (arity : Nat) :
    nameSize (functionName (.constructor name arity)) =
      23 + 2 * (Nat.digits 2 arity).length + name.utf8ByteSize := by
  have prefix : Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize
      ["inference", "constructor"] = 22 := by decide
  simp only [nameSize, functionName, natComponents,
    Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize_append,
    Mettapedia.OSLF.MeTTaIL.PatternTokens.tokenSize_bits, prefix]
  omega

def holdsName : Name := ⟨["inference", "relation"], "holds"⟩

theorem functionName_injective {arity otherArity : Nat}
    (first : HOL.Embedding.InferenceRules.Function arity) (second : HOL.Embedding.InferenceRules.Function otherArity)
    (same : functionName first = functionName second) : HEq first second := by
  cases first with
  | constructor name arity =>
      cases second with
      | constructor other otherArity =>
          have names := congrArg Name.component same
          change name = other at names
          have arities := congrArg Name.namespaceComponents same
          simp only [functionName, List.cons_append, List.nil_append,
            List.cons.injEq] at arities
          have arityEq := natComponents_injective arities.2.2
          subst otherArity
          subst other
          rfl
      | literal value =>
          have namespaces := congrArg Name.namespaceComponents same
          simp [functionName] at namespaces
  | literal value =>
      cases second with
      | constructor name arity =>
          have namespaces := congrArg Name.namespaceComponents same
          simp [functionName] at namespaces
      | literal other =>
          have codes := congrArg Name.namespaceComponents same
          simp only [functionName, List.cons_append, List.nil_append,
            List.cons.injEq] at codes
          have patterns := Mettapedia.OSLF.MeTTaIL.PatternTokens.encode_injective codes.2.2
          have values : value = other := Subtype.ext patterns
          subst other
          rfl

theorem functionName_ne_holds {arity : Nat} (symbol : HOL.Embedding.InferenceRules.Function arity) :
    functionName symbol ≠ holdsName := by
  intro same
  have namespaces := congrArg Name.namespaceComponents same
  cases symbol <;> simp [functionName, holdsName] at namespaces

def dataType : OpenTheory.Ty := .op (.mk ⟨["inference"], "data"⟩ .undefined) []

theorem dataType_atomic : dataType.IsAtomic := by
  constructor
  · rfl
  · apply Bool.eq_false_iff.mpr
    intro positive
    have equal := (OpenTheory.Ty.isBool_eq_true_iff dataType).mp positive
    simp [dataType, OpenTheory.Ty.bool, TypeOp.bool, Name.global] at equal

def dataAtomic : AtomicTy := ⟨dataType, dataType_atomic⟩

def baseMap : HOL.Embedding.FirstOrder.BaseTy → HOL.Ty AtomicTy
  | .ind => .base dataAtomic

abbrev type (source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy) : HOL.Ty AtomicTy :=
  HOL.Ty.substitute baseMap source

def symbolName : {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy} → HOL.Embedding.InferenceRules.Symbol source → Name
  | _, .func function => functionName function
  | _, .rel .holds => holdsName

def symbol : {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy} → HOL.Embedding.InferenceRules.Symbol source → OpenTheory.Symbol (type source)
  | source, constant => .constant (.mk (symbolName constant) .undefined)
      (ReverseTranslation.reverseTy (type source)) (ReverseTranslation.toHOL_reverseTy _)

def term {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy} {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (input : HOL.Term HOL.Embedding.InferenceRules.Symbol context source) :
    HOL.Term OpenTheory.Symbol (context.map (HOL.Ty.substitute baseMap)) (type source) :=
  HOL.mapTypes baseMap symbol input

def render (formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) : CanonicalTerm :=
  ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term formula)

theorem render_isBool (formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) :
    (render formula).IsBool := ReverseTranslation.reverseCanonical_isBool _ _

/-- Ordinary implication elimination is realized by the ten-rule kernel. -/
theorem render_mp (policy : AxiomPolicy) {hyp hyp' : Finset CanonicalTerm}
    {premise conclusion : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol}
    (implication : KernelProvable policy hyp (render (.imp premise conclusion)).term)
    (proof : KernelProvable policy hyp' (render premise).term) :
    KernelProvable policy (hyp ∪ hyp') (render conclusion).term :=
  KernelProvable.mp implication proof

/-- A typed universal instance is replayed by definition unfolding, BETA and INST. -/
theorem render_spec (policy : AxiomPolicy) {hyp : Finset CanonicalTerm}
    {inputType : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (argument : HOL.ClosedTerm HOL.Embedding.InferenceRules.Symbol inputType)
    (body : HOL.Formula HOL.Embedding.InferenceRules.Symbol [inputType])
    (proof : KernelProvable policy hyp (render (.all body)).term) :
    KernelProvable policy hyp (render (HOL.instantiate argument body)).term := by
  have eliminated := KernelProvable.spec proof
    (ReverseTranslation.inferType_reverseTerm ReverseTranslation.Naming.empty [] (term argument))
  change KernelProvable policy hyp
    (ReverseTranslation.reverseTerm ReverseTranslation.Naming.empty
      (term (HOL.instantiate argument body)))
  rw [term, HOL.mapTypes_instantiate, ReverseTranslation.reverseTerm_instantiate]
  exact eliminated

/-- The source's universally closed axiom retains every typed substitution instance. -/
theorem render_closeAll_elim (policy : AxiomPolicy) {hyp : Finset CanonicalTerm}
    {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy}
    (formula : HOL.Formula HOL.Embedding.InferenceRules.Symbol context)
    (substitution : HOL.Subst HOL.Embedding.InferenceRules.Symbol context [])
    (proof : KernelProvable policy hyp (render (HOL.closeAll context formula)).term) :
    KernelProvable policy hyp (render (HOL.subst substitution formula)).term := by
  induction context with
  | nil =>
      have equal : HOL.subst substitution formula = formula := by
        have closed := HOL.subst_weakenCtx substitution formula
        simpa only [HOL.weakenCtx_nil] using closed
      rw [equal]
      exact proof
  | cons inputType context ih =>
      let tail : HOL.Subst HOL.Embedding.InferenceRules.Symbol context [] :=
        fun {_} index => substitution (.vs index)
      have quantified : KernelProvable policy hyp
          (render (.all (HOL.subst (HOL.Subst.lift tail) formula))).term :=
        ih (.all formula) tail proof
      have eliminated := render_spec policy (substitution .vz)
        (HOL.subst (HOL.Subst.lift tail) formula) quantified
      have equal : HOL.instantiate (substitution .vz)
          (HOL.subst (HOL.Subst.lift tail) formula) = HOL.subst substitution formula := by
        rw [HOL.instantiate, HOL.subst_comp]
        apply HOL.subst_ext
        intro indexType index
        cases index with
        | vz => rfl
        | vs index =>
            exact HOL.instantiate_weaken _ _
      rw [equal] at eliminated
      exact eliminated

/-- Every premise is replayed in authored order; no rule conclusion is admitted separately. -/
theorem render_hypChain_elim (policy : AxiomPolicy) {hyp : Finset CanonicalTerm}
    (premises : List (HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol))
    (conclusion : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol)
    (chain : KernelProvable policy hyp (render (HOL.hypChain premises conclusion)).term)
    (proofs : ∀ premise ∈ premises, KernelProvable policy ∅ (render premise).term) :
    KernelProvable policy hyp (render conclusion).term := by
  induction premises with
  | nil => exact chain
  | cons premise rest ih =>
      apply ih
      · exact (render_mp policy chain (proofs premise (by simp))).congr_hyp
          (Finset.union_empty hyp)
      · intro next member
        exact proofs next (by simp [member])

/-- The generated target admits exactly its finite rendered rule axioms. -/
def policy (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) : AxiomPolicy :=
  fun sequent => sequent.hyp = ∅ ∧
    sequent.concl ∈ (HOL.Embedding.InferenceRules.axioms rules).map render

instance policy_decidable
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) :
    DecidablePred (policy rules) := by
  unfold policy
  infer_instance

theorem policy_hypothesisFree
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) :
    ∀ sequent, policy rules sequent → sequent.hyp = ∅ := fun _ admitted => admitted.1

/-- A source rule contributes one actual HOL Light axiom sequent. -/
theorem render_axiom
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    {formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol}
    (member : formula ∈ HOL.Embedding.InferenceRules.theory rules) :
    KernelProvable (policy rules) ∅ (render formula).term := by
  apply KernelProvable.axiom ⟨∅, render formula⟩
  · exact ⟨rfl, List.mem_map.mpr ⟨formula, member, rfl⟩⟩
  · exact ⟨render_isBool formula, by simp⟩

/-- The checked ten-rule certificate retains its complete theorem object. -/
theorem checked_of_render_provable
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    (formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol)
    (proof : KernelProvable (policy rules) ∅ (render formula).term) :
    ∃ (out : Theorem) (certificate : Mettapedia.Logic.Derivation Theorem RuleRequest),
      certificate.valid (ruleWitness (policy rules)) = true ∧
      certificate.concl = out ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = render formula := by
  obtain ⟨out, derivation, hypotheses, conclusion⟩ := proof
  have canonical : out.sequent.concl = render formula := CanonicalTerm.ext_term conclusion
  obtain ⟨certificate, valid, sameConclusion⟩ :=
    (PrimitiveTransport.checked_iff_shared (policy rules) (policy_hypothesisFree rules) out).mpr
      derivation
  exact ⟨out, certificate, valid, sameConclusion, hypotheses, canonical⟩

/-- The data alphabet is fixed, so source type instantiation cannot alter it. -/
theorem baseMap_substitution (types : TypeSubst)
    (base : HOL.Embedding.FirstOrder.BaseTy) :
    HOL.Ty.substitute types.baseInstance (baseMap base) = baseMap base := by
  cases base
  change (types.apply dataType).toHOL = .base dataAtomic
  have fixed : types.apply dataType = dataType := by
    simp [dataType]
  rw [fixed]
  exact OpenTheory.Ty.toHOL_of_isAtomic dataType_atomic

theorem type_substitution (types : TypeSubst)
    (source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy) :
    HOL.Ty.substitute types.baseInstance (type source) = type source := by
  induction source with
  | prop => rfl
  | base base => exact baseMap_substitution types base
  | arr domain codomain ihDomain ihCodomain =>
      simp only [type, HOL.Ty.substitute_arr] at *
      rw [ihDomain, ihCodomain]

theorem symbol_typeSubstitution (types : TypeSubst)
    {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (constant : HOL.Embedding.InferenceRules.Symbol source) :
    HEq (types.symbolInstance (symbol constant)) (symbol constant) := by
  have fixed : types.apply (ReverseTranslation.reverseTy (type source)) =
      ReverseTranslation.reverseTy (type source) := by
    rw [← ReverseTranslation.reverseTy_substitute, type_substitution]
  simp only [symbol, TypeSubst.symbolInstance, fixed]
  exact OpenTheory.Symbol.constant_heq _ _ _ _

/-- No generated object-language symbol is an OpenTheory free variable. -/
theorem term_variableFree {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy}
    {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (input : HOL.Term HOL.Embedding.InferenceRules.Symbol context source)
    (sourceVar : SourceVar) : HOL.NoConstOccurrence (OpenTheory.Symbol.ofVar sourceVar) (term input) := by
  induction input <;> simp only [term, HOL.mapTypes]
  case const constant =>
    exact OpenTheory.Symbol.noConstOccurrence_const _ _
      (OpenTheory.Symbol.sigma_constant_ne_ofVar _ _ _ _)
  all_goals constructor <;> assumption

/-- Typed signature interpretation into the concrete HOL Light symbol alphabet. -/
def signatureInterpretation :
    HOL.TypeDerivedSignature.Hom
      ⟨HOL.Embedding.FirstOrder.BaseTy, ⟨HOL.Embedding.InferenceRules.Symbol⟩⟩
      ⟨AtomicTy, ⟨OpenTheory.Symbol⟩⟩ where
  base := baseMap
  constants := symbol

/-- The signature interpretation is unchanged by target type instantiation. -/
theorem signatureInterpretation_typeSubstitution (types : TypeSubst) :
    HOL.TypeDerivedSignature.Hom.comp signatureInterpretation
      ⟨types.baseInstance, types.symbolInstance⟩ = signatureInterpretation := by
  apply HOL.TypeDerivedSignature.Hom.ext_data
  · funext base
    exact baseMap_substitution types base
  · intro source constant
    exact (eqRec_heq _ _).trans (symbol_typeSubstitution types constant)

/-- Closed HOL formulas retain their precise syntax after INST_TYPE. -/
theorem term_typeSubstitution (types : TypeSubst)
    (formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) :
    HOL.mapTypes types.baseInstance types.symbolInstance (term formula) = term formula := by
  have invariant := congrArg
    (fun interpretation : HOL.TypeDerivedSignature.Hom
      ⟨HOL.Embedding.FirstOrder.BaseTy, ⟨HOL.Embedding.InferenceRules.Symbol⟩⟩
      ⟨AtomicTy, ⟨OpenTheory.Symbol⟩⟩ =>
      HOL.TypeDerivedSignature.sentence.map interpretation formula)
    (signatureInterpretation_typeSubstitution types)
  dsimp only [HOL.TypeDerivedSignature.sentence, HOL.TypeDerivedSignature.Hom.comp,
    signatureInterpretation] at invariant
  exact (HOL.mapTypes_comp_closed baseMap types.baseInstance symbol types.symbolInstance formula).trans
    invariant

theorem symbol_not_equality {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (constant : HOL.Embedding.InferenceRules.Symbol source) :
    (Const.mk (symbolName constant) .undefined) ≠ Const.equality := by
  cases constant with
  | func function =>
      cases function <;> simp [symbolName, functionName, Const.equality, Name.global]
  | rel relation =>
      cases relation; simp [symbolName, holdsName, Const.equality, Name.global]

/-- Term substitution fixes every generated ordinary constant. -/
theorem symbolImage_symbol (substitution : TypeCorrectTermSubstitution)
    {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (constant : HOL.Embedding.InferenceRules.Symbol source) :
    substitution.symbolImage (symbol constant) = .const (symbol constant) := by
  have selected := closedTranslation_spec _
    (TermSubst.symbolReplacement_translatable substitution.typeCorrect (symbol constant))
  have direct : TranslatesCompositionally []
      (substitution.raw.symbolReplacement (symbol constant)) (type source)
      (.const (symbol constant)) := by
    apply TranslatesCompositionally.constant
    · unfold equalityOperand?
      rw [if_neg]
      intro same
      exact symbol_not_equality constant ((Const.same_eq_true_iff _ _).mp same)
  exact eq_of_heq (selected.unique direct).2

/-- Closed source formulas retain their precise syntax after INST. -/
theorem term_termSubstitution (substitution : TypeCorrectTermSubstitution)
    {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy}
    {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (input : HOL.Term HOL.Embedding.InferenceRules.Symbol context source) :
    HOL.substConst substitution.symbolImage (term input) = term input := by
  induction input <;> simp only [term, HOL.mapTypes, HOL.substConst]
  case const constant =>
    rw [symbolImage_symbol, HOL.weakenCtx_const]
  all_goals congr 1

/-- All permitted source substitutions leave the finite generated background fixed. -/
theorem term_targetMap (substitution : TypeCorrectTermSubstitution)
    (formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) :
    substitution.targetMap (term formula) = term formula := by
  rw [TypeCorrectTermSubstitution.targetMap, term_typeSubstitution]
  exact term_termSubstitution substitution formula

theorem type_injective : Function.Injective type := by
  intro first
  induction first with
  | prop =>
      intro second equal
      cases second <;> simp only [type, HOL.Ty.substitute] at equal
      · rfl
      · cases equal
      · cases equal
  | base base =>
      intro second equal
      cases base
      cases second with
      | prop => cases equal
      | base other => cases other; rfl
      | arr domain codomain => cases equal
  | arr domain codomain ihDomain ihCodomain =>
      intro second equal
      cases second with
      | prop => cases equal
      | base base => cases base; cases equal
      | arr otherDomain otherCodomain =>
          obtain ⟨domains, codomains⟩ := HOL.Ty.arr.inj equal
          rw [ihDomain domains, ihCodomain codomains]

private theorem functionName_arity {firstArity secondArity : Nat}
    (first : HOL.Embedding.InferenceRules.Function firstArity)
    (second : HOL.Embedding.InferenceRules.Function secondArity)
    (same : functionName first = functionName second) : firstArity = secondArity := by
  cases first with
  | constructor name arity =>
      cases second with
      | constructor other otherArity =>
          have parts := congrArg Name.namespaceComponents same
          simp only [functionName, List.cons_append, List.nil_append, List.cons.injEq] at parts
          exact natComponents_injective parts.2.2
      | literal value =>
          have parts := congrArg Name.namespaceComponents same
          simp [functionName] at parts
  | literal value =>
      cases second with
      | constructor name arity =>
          have parts := congrArg Name.namespaceComponents same
          simp [functionName] at parts
      | literal other => rfl

theorem symbolName_injective {firstType secondType : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (first : HOL.Embedding.InferenceRules.Symbol firstType)
    (second : HOL.Embedding.InferenceRules.Symbol secondType)
    (same : symbolName first = symbolName second) : HEq first second := by
  cases first with
  | func first =>
      cases second with
      | func second =>
          have arities := functionName_arity first second same
          cases arities
          have functions := eq_of_heq (functionName_injective first second same)
          rw [functions]
      | rel relation =>
          cases relation
          exact False.elim (functionName_ne_holds first same)
  | rel relation =>
      cases relation
      cases second with
      | func second => exact False.elim (functionName_ne_holds second same.symm)
      | rel other => cases other; rfl

/-- The complete typed symbol embedding is injective, including its source type. -/
def packedSymbol (constant : Sigma HOL.Embedding.InferenceRules.Symbol) : Sigma OpenTheory.Symbol :=
  ⟨type constant.1, symbol constant.2⟩

private def symbolHead (constant : Sigma OpenTheory.Symbol) : Option Name :=
  match constant.2 with
  | .constant (.mk name _) _ _ => some name
  | .variable _ _ => none

theorem packedSymbol_injective : Function.Injective packedSymbol := by
  rintro ⟨firstType, first⟩ ⟨secondType, second⟩ same
  have names : symbolName first = symbolName second := by
    simpa only [packedSymbol, symbol, symbolHead, Option.some.injEq] using
      congrArg symbolHead same
  have types : firstType = secondType := type_injective (congrArg Sigma.fst same)
  cases types
  have symbols : first = second := eq_of_heq (symbolName_injective first second names)
  rw [symbols]

/-- A full target carrier extends the source data domain to every atomic type. -/
abbrev modelCarrier (_ : AtomicTy) : Type 1 := ULift.{1} HOL.Embedding.InferenceRules.Data

def defaultValue : (targetType : HOL.Ty AtomicTy) → HOL.Ty.denote.{0, 0} modelCarrier targetType
  | .prop => ULift.up True
  | .base _ => ULift.up HOL.Embedding.InferenceRules.Data.default
  | .arr _ codomain => fun _ => defaultValue codomain

def imageValue (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    (constant : Sigma HOL.Embedding.InferenceRules.Symbol) :
    HOL.Ty.denote.{0, 0} modelCarrier (type constant.1) :=
  HOL.Ty.denoteSubstituteEquiv.{0, 0} baseMap modelCarrier constant.1
    ((HOL.Embedding.InferenceRules.model rules).constDen constant.2)

/-- Extend the source interpretation along the proved typed symbol injection. -/
noncomputable def modelMeaning
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    {targetType : HOL.Ty AtomicTy} (constant : OpenTheory.Symbol targetType) :
    HOL.Ty.denote.{0, 0} modelCarrier targetType :=
  by
    classical
    exact if image : ∃ original, packedSymbol original = ⟨targetType, constant⟩ then
      cast (congrArg (HOL.Ty.denote.{0, 0} modelCarrier)
        (congrArg Sigma.fst (Classical.choose_spec image)))
          (imageValue rules (Classical.choose image))
    else defaultValue targetType

theorem modelMeaning_symbol
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (constant : HOL.Embedding.InferenceRules.Symbol source) :
    modelMeaning rules (symbol constant) = imageValue rules ⟨source, constant⟩ := by
  have image : ∃ original, packedSymbol original = ⟨type source, symbol constant⟩ :=
    ⟨⟨source, constant⟩, rfl⟩
  rw [modelMeaning, dif_pos image]
  have selected : Classical.choose image = ⟨source, constant⟩ :=
    packedSymbol_injective (Classical.choose_spec image)
  have values : HEq (imageValue rules (Classical.choose image))
      (imageValue rules ⟨source, constant⟩) := by
    generalize choosing : Classical.choose image = original at selected ⊢
    cases selected
    rfl
  exact eq_of_heq ((cast_heq _ _).trans values)

noncomputable def model (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) :
    HOL.HenkinModel.{0, 0, 0} AtomicTy OpenTheory.Symbol :=
  HOL.HenkinModel.standard modelCarrier (modelMeaning rules)

theorem model_fullDomains (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) :
    (model rules).FullDomains := HOL.HenkinModel.fullDomains_standard _ _

/-- The target model's reduct is the independently constructed source model. -/
theorem model_reduct (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) :
    HOL.HenkinModel.standardTypeReduct baseMap symbol (model rules) =
      HOL.Embedding.InferenceRules.model rules := by
  unfold HOL.HenkinModel.standardTypeReduct model HOL.Embedding.InferenceRules.model
    HOL.Embedding.FirstOrder.standardModel
  apply HOL.HenkinModel.standard_ext
  · funext base
    cases base
    rfl
  · intro source constant
    simp only [HOL.HenkinModel.standard, modelMeaning_symbol, imageValue]
    rw [Equiv.symm_apply_apply]
    rfl

theorem model_term (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    (formula : HOL.ClosedFormula HOL.Embedding.InferenceRules.Symbol) :
    (model rules).models (term formula) ↔
      (HOL.Embedding.InferenceRules.model rules).models formula := by
  rw [← model_reduct rules]
  exact (HOL.HenkinModel.models_mapTypes baseMap symbol (model rules)
    (model_fullDomains rules) formula).symm

/-- Object-language constants remain distinct from the primitive equality symbol. -/
theorem term_equalityFree {context : HOL.Ctx HOL.Embedding.FirstOrder.BaseTy}
    {source : HOL.Ty HOL.Embedding.FirstOrder.BaseTy}
    (input : HOL.Term HOL.Embedding.InferenceRules.Symbol context source) :
    ReverseTranslation.EqualitySymbolFree (term input) := by
  intro operand
  induction input <;> simp only [term, HOL.mapTypes]
  case const constant =>
    apply OpenTheory.Symbol.noConstOccurrence_const
    intro same
    have names : symbolName constant = Name.global "=" := by
      simpa only [symbolHead, symbol, ReverseTranslation.equalitySymbol, Const.equality,
        Option.some.injEq] using congrArg symbolHead same
    exact symbol_not_equality constant (by rw [names]; rfl)
  all_goals constructor <;> assumption

/-- The finite HOL theory is mapped into the actual target alphabet. -/
def theory (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) :
    HOL.ClosedTheorySet OpenTheory.Symbol :=
  {formula | ∃ original ∈ HOL.Embedding.InferenceRules.theory rules, term original = formula}

theorem theory_background (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule) :
    VariableFreeSubstitutionClosed (theory rules) where
  variableFree := by
    rintro _ ⟨original, _, rfl⟩ sourceVar
    exact term_variableFree original sourceVar
  substitutionClosed := by
    rintro substitution _ ⟨original, member, rfl⟩
    exact ⟨original, member, (term_targetMap substitution original).symm⟩

theorem model_theory
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    (package : HOL.Embedding.InferenceRules.SchemaPackage rules)
    {formula : HOL.ClosedFormula OpenTheory.Symbol} (member : formula ∈ theory rules) :
    (model rules).models formula := by
  obtain ⟨original, originalMember, rfl⟩ := member
  exact (model_term rules original).mpr (HOL.Embedding.InferenceRules.model_theory
    rules package originalMember)

/-- A generated axiom is provable under exactly the mapped finite background. -/
theorem policy_translatedProvable
    (rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule)
    {sequent : Sequent} (admitted : policy rules sequent) :
    TranslatedProvable (theory rules) sequent := by
  obtain ⟨hypotheses, member⟩ := admitted
  obtain ⟨original, originalMember, conclusion⟩ := List.mem_map.mp member
  obtain ⟨translated, translation, back, forward⟩ :=
    ReverseTranslation.exists_translates_reverseTermOpen_derivable (term original)
      (term_equalityFree original)
  have rendering : (render original).term = ReverseTranslation.reverseTermOpen (term original) :=
    ReverseTranslation.reverseTerm_eq_reverseTermOpen _
  rw [← rendering, conclusion] at translation
  refine ⟨translated, translation, ?_⟩
  apply provable_of_extDerivation forward
  intro premise premiseMember
  simp only [List.mem_singleton] at premiseMember
  subst premise
  exact HOL.ClosedTheorySet.provable_of_mem (Or.inl ⟨original, originalMember, rfl⟩)

/-- Every actual target proof of an encoded source judgment reflects to the source calculus. -/
theorem reflects
    {rules : List Mettapedia.GSLT.LanguageDef.FirstOrderRules.FORule}
    (package : HOL.Embedding.InferenceRules.SchemaPackage rules)
    {pattern : Pattern}
    (valid : Mettapedia.GSLT.LanguageDef.InferenceChecker.argumentValidAt 0 pattern = true)
    {out : Theorem} (proof : Derives (Rule (policy rules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = render (HOL.Embedding.InferenceRules.judgment pattern)) :
    Mettapedia.GSLT.LanguageDef.FirstOrderRules.FODerivable rules pattern := by
  have shared := HOLLight.derives_shared (policy rules) proof
  obtain ⟨translated, translation, holds⟩ := derives_models (theory_background rules) shared
    (fun tagged member => policy_translatedProvable rules
      (derives_only_authorized_axioms (policy rules) shared tagged member))
    (model rules) (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (model_fullDomains rules))
    (fun formula member => model_theory rules package member)
  have translatedHolds : (model rules).models translated := holds (by
    intro formula member
    obtain ⟨source, sourceMember, _⟩ := member
    rw [hypotheses] at sourceMember
    exact False.elim (Finset.notMem_empty source sourceMember))
  obtain ⟨target, targetTranslation, back, _⟩ :=
    ReverseTranslation.exists_translates_reverseTermOpen_derivable
      (term (HOL.Embedding.InferenceRules.judgment pattern))
      (term_equalityFree (HOL.Embedding.InferenceRules.judgment pattern))
  rw [← ReverseTranslation.reverseTerm_eq_reverseTermOpen] at targetTranslation
  change Translates [] (render (HOL.Embedding.InferenceRules.judgment pattern)).term .prop target
    at targetTranslation
  rw [conclusion] at translation
  have same : translated = target := eq_of_heq (Translates.unique translation targetTranslation).2
  rw [same] at translatedHolds
  have originalHolds := HOL.Soundness.extDerivation_sound back
    (M := model rules)
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (model_fullDomains rules))
    (fun index => nomatch index) (fun formula member => by
      simp only [List.mem_singleton] at member
      exact member ▸ translatedHolds)
  exact (HOL.Embedding.InferenceRules.models_judgment_iff rules valid).mp
    ((model_term rules _).mp originalHolds)

namespace Controls

open HOL.Embedding.InferenceRules.Controls

/-- The finite fact theory yields a certificate accepted by the actual ten-rule checker. -/
theorem fact_checked :
    ∃ (out : Theorem) (certificate : Mettapedia.Logic.Derivation Theorem RuleRequest),
      certificate.valid (ruleWitness (policy [fact])) = true ∧
      certificate.concl = out ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = render (HOL.Embedding.InferenceRules.judgment atom) := by
  apply checked_of_render_provable
  apply render_axiom
  change HOL.Embedding.InferenceRules.judgment atom ∈ [HOL.Embedding.InferenceRules.ruleFormula fact]
  rw [fact_formula]
  simp

/-- Arbitrary HOL Light reasoning cannot manufacture a missing source fact. -/
theorem empty_refuses :
    ¬ ∃ out : Theorem, Derives (Rule (policy [])) out ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = render (HOL.Embedding.InferenceRules.judgment atom) := by
  rintro ⟨out, proof, hypotheses, conclusion⟩
  exact empty_underivable atom (reflects empty_package fact_valid proof hypotheses conclusion)

/-- Closed binder-bearing values remain literal data under every admitted substitution. -/
theorem opaqueBinder_substitution (substitution : TypeCorrectTermSubstitution) :
    substitution.targetMap (term (HOL.Embedding.InferenceRules.judgment opaqueBinder)) =
      term (HOL.Embedding.InferenceRules.judgment opaqueBinder) :=
  term_targetMap substitution _

/-- Canonical literal names distinguish different underlying pattern values. -/
theorem literal_name_reflects
    (first second : HOL.Embedding.InferenceRules.Data)
    (same : functionName (.literal first) = functionName (.literal second)) : first = second := by
  have functions := eq_of_heq (functionName_injective (.literal first) (.literal second) same)
  exact HOL.Embedding.InferenceRules.Function.literal.inj functions

end Controls

end Mettapedia.Languages.HOLLight.InferenceHosting
