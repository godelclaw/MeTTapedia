import Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderAdmission

/-!
# Certificates for deduction modulo definitions

A proof tree cites a hypothesis, applies a rule to typed arguments, or
converts the conclusion of its child to a named term. The conversion node
carries no evidence. The checker recomputes it: the two terms must be typed
at one type and have the same full unfolding. A backend that wants the
evidence spelled out can produce it from the same two terms.

The executable checker accepts exactly the trees of the checking relation,
and a statement has an accepted tree exactly when it is derivable modulo the
definitions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations

/-- Untrusted proof trees. A conversion names the statement it converts to. -/
inductive ModuloProof where
  | premise (index : Nat)
  | node (invocation : RuleInstance) (children : List ModuloProof)
  | convert (target : Pattern) (child : ModuloProof)
  deriving Repr

/-- The types a first-order term can have: the types of the context and the
result sorts of the constructor declarations. -/
def candidateTypes (language : LanguageDef) (context : List TypeExpr) : List TypeExpr :=
  context ++ language.terms.map (fun rule => TypeExpr.base rule.category)

theorem type_mem_candidateTypes {language : LanguageDef} {context : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty context pattern type)
    (fragment : isMatchCorrectAux pattern = true) :
    type ∈ candidateTypes language context := by
  cases typed with
  | bvar lookup => exact List.mem_append_left _ (List.mem_of_getElem? lookup)
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | constructor member _ _ =>
    exact List.mem_append_right _
      (List.mem_map_of_mem (f := fun rule => TypeExpr.base rule.category) member)
  | lambda _ => simp [isMatchCorrectAux] at fragment
  | multiLambda _ => simp [isMatchCorrectAux] at fragment
  | subst _ _ => simp [isMatchCorrectAux] at fragment
  | collection _ => simp [isMatchCorrectAux] at fragment
  | collectionConstructor _ _ _ => simp [isMatchCorrectAux] at fragment

/-- Both terms are typed, at one type. -/
def checkSameType (language : LanguageDef) (context : List TypeExpr)
    (source target : Pattern) : Bool :=
  (candidateTypes language context).any (fun type =>
    checkHasType language FreeTypeContext.empty context source type &&
      checkHasType language FreeTypeContext.empty context target type)

theorem checkSameType_iff (language : LanguageDef) (context : List TypeExpr)
    {source target : Pattern} (sourceFragment : isMatchCorrectAux source = true)
    (targetFragment : isMatchCorrectAux target = true) :
    checkSameType language context source target = true ↔
      ∃ type, HasType language FreeTypeContext.empty context source type ∧
        HasType language FreeTypeContext.empty context target type := by
  simp only [checkSameType, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨type, -, sourceChecked, targetChecked⟩
    exact ⟨type, checkHasType_sound sourceChecked, checkHasType_sound targetChecked⟩
  · rintro ⟨type, sourceTyped, targetTyped⟩
    exact ⟨type, type_mem_candidateTypes sourceTyped sourceFragment,
      checkHasType_complete_of_object sourceTyped (firstOrder_object sourceFragment),
      checkHasType_complete_of_object targetTyped (firstOrder_object targetFragment)⟩

mutual
  /-- Ordered, typed checking of a proof tree, with conversion decided by
  full unfolding. -/
  inductive ChecksModulo (rows : List Row) (language : LanguageDef)
      (rules : List Rule) (context : List TypeExpr)
      (hypotheses : List Pattern) : ModuloProof → Pattern → Prop where
    | premise {index : Nat} {pattern : Pattern} : hypotheses[index]? = some pattern →
        ChecksModulo rows language rules context hypotheses (.premise index)
          pattern
    | rule {invocation : RuleInstance} {rule : Rule} {children : List ModuloProof} :
        lookupRule? rules invocation.ruleId.value = some rule →
        invocation.arguments.length = rule.row.vars.length →
        List.Forall₂ (fun argument type =>
          HasType language FreeTypeContext.empty context argument type)
          invocation.arguments rule.variableTypes →
        (∀ argument ∈ invocation.arguments, isMatchCorrectAux argument = true) →
        ChecksModuloList rows language rules context hypotheses children
          (rule.row.instPremises invocation.arguments) →
        ChecksModulo rows language rules context hypotheses
          (.node invocation children) (rule.row.instConclusion invocation.arguments)
    | convert {target source : Pattern} {child : ModuloProof} {type : TypeExpr} :
        ChecksModulo rows language rules context hypotheses child source →
        expand rows source = expand rows target →
        isMatchCorrectAux source = true →
        isMatchCorrectAux target = true →
        HasType language FreeTypeContext.empty context source type →
        HasType language FreeTypeContext.empty context target type →
        ChecksModulo rows language rules context hypotheses
          (.convert target child) target

  inductive ChecksModuloList (rows : List Row) (language : LanguageDef)
      (rules : List Rule) (context : List TypeExpr)
      (hypotheses : List Pattern) : List ModuloProof → List Pattern → Prop where
    | nil : ChecksModuloList rows language rules context hypotheses [] []
    | cons {child : ModuloProof} {children : List ModuloProof}
        {pattern : Pattern} {patterns : List Pattern} :
        ChecksModulo rows language rules context hypotheses child pattern →
        ChecksModuloList rows language rules context hypotheses children
          patterns →
        ChecksModuloList rows language rules context hypotheses
          (child :: children) (pattern :: patterns)
end

mutual
  /-- The executable checker. -/
  def proofModulo? (rows : List Row) (language : LanguageDef)
      (rules : List Rule) (context : List TypeExpr) (hypotheses : List Pattern) :
      ModuloProof → Option Pattern
    | .premise index => hypotheses[index]?
    | .node invocation children => do
        let rule ← lookupRule? rules invocation.ruleId.value
        if invocation.arguments.length = rule.row.vars.length ∧
            checkArgumentTypes language context invocation.arguments rule.variableTypes = true
        then
          let premises ← childrenModulo? rows language rules context hypotheses
            children
          if premises = rule.row.instPremises invocation.arguments then
            some (rule.row.instConclusion invocation.arguments)
          else none
        else none
    | .convert target child => do
        let source ← proofModulo? rows language rules context hypotheses child
        if expand rows source = expand rows target ∧ isMatchCorrectAux source = true ∧
            isMatchCorrectAux target = true ∧
            checkSameType language context source target = true then
          some target
        else none
  termination_by proof => sizeOf proof

  def childrenModulo? (rows : List Row) (language : LanguageDef)
      (rules : List Rule) (context : List TypeExpr) (hypotheses : List Pattern) :
      List ModuloProof → Option (List Pattern)
    | [] => some []
    | child :: children => do
        let first ← proofModulo? rows language rules context hypotheses child
        let rest ← childrenModulo? rows language rules context hypotheses children
        pure (first :: rest)
  termination_by children => sizeOf children
end

section Exactness

variable {rows : List Row} {language : LanguageDef}
  {rules : List Rule} {context : List TypeExpr} {hypotheses : List Pattern}

mutual
  theorem ChecksModulo.eval {proof : ModuloProof} {pattern : Pattern}
      (checked : ChecksModulo rows language rules context hypotheses proof
        pattern) :
      proofModulo? rows language rules context hypotheses proof = some pattern := by
    cases checked with
    | premise lookup => simpa only [proofModulo?] using lookup
    | rule lookup arity typed fragments children =>
      simp [proofModulo?, lookup, arity,
        (checkArgumentTypes_iff _ _ _ _).mpr ⟨typed, fragments⟩, children.eval]
    | convert child same sourceFragment targetFragment sourceTyped targetTyped =>
      simp [proofModulo?, child.eval, same, sourceFragment, targetFragment,
        (checkSameType_iff language context sourceFragment targetFragment).mpr
          ⟨_, sourceTyped, targetTyped⟩]
  termination_by sizeOf proof

  theorem ChecksModuloList.eval {proofs : List ModuloProof} {patterns : List Pattern}
      (checked : ChecksModuloList rows language rules context hypotheses proofs
        patterns) :
      childrenModulo? rows language rules context hypotheses proofs =
        some patterns := by
    cases checked with
    | nil => simp [childrenModulo?]
    | cons first rest => simp [childrenModulo?, first.eval, rest.eval]
  termination_by sizeOf proofs
end

mutual
  theorem proofModulo?_sound {proof : ModuloProof} {pattern : Pattern}
      (accepted : proofModulo? rows language rules context hypotheses proof =
        some pattern) :
      ChecksModulo rows language rules context hypotheses proof pattern := by
    cases proof with
    | premise index => exact .premise (by simpa only [proofModulo?] using accepted)
    | node invocation children =>
      cases found : lookupRule? rules invocation.ruleId.value with
      | none => simp [proofModulo?, found] at accepted
      | some rule =>
        by_cases valid : invocation.arguments.length = rule.row.vars.length ∧
            checkArgumentTypes language context invocation.arguments rule.variableTypes = true
        · cases returned : childrenModulo? rows language rules context hypotheses
              children with
          | none => simp [proofModulo?, found, valid, returned] at accepted
          | some premises =>
            have data : premises = rule.row.instPremises invocation.arguments ∧
                rule.row.instConclusion invocation.arguments = pattern := by
              simpa [proofModulo?, found, valid, returned] using accepted
            obtain ⟨typed, fragment⟩ := (checkArgumentTypes_iff _ _ _ _).mp valid.2
            rw [← data.2]
            exact .rule found valid.1 typed fragment (data.1 ▸ childrenModulo?_sound returned)
        · simp [proofModulo?, found, valid] at accepted
    | convert target child =>
      cases returned : proofModulo? rows language rules context hypotheses child with
      | none => simp [proofModulo?, returned] at accepted
      | some source =>
        by_cases valid : expand rows source = expand rows target ∧
            isMatchCorrectAux source = true ∧ isMatchCorrectAux target = true ∧
            checkSameType language context source target = true
        · have same : target = pattern := by
            simpa [proofModulo?, returned, valid] using accepted
          subst same
          obtain ⟨type, sourceTyped, targetTyped⟩ :=
            (checkSameType_iff language context valid.2.1 valid.2.2.1).mp valid.2.2.2
          exact .convert (proofModulo?_sound returned) valid.1 valid.2.1 valid.2.2.1
            sourceTyped targetTyped
        · simp [proofModulo?, returned, valid] at accepted
  termination_by sizeOf proof

  theorem childrenModulo?_sound {proofs : List ModuloProof} {patterns : List Pattern}
      (accepted : childrenModulo? rows language rules context hypotheses proofs =
        some patterns) :
      ChecksModuloList rows language rules context hypotheses proofs patterns := by
    cases proofs with
    | nil =>
      simp only [childrenModulo?, Option.some.injEq] at accepted
      subst patterns
      exact .nil
    | cons proof proofs =>
      cases first : proofModulo? rows language rules context hypotheses proof with
      | none => simp [childrenModulo?, first] at accepted
      | some pattern =>
        cases rest : childrenModulo? rows language rules context hypotheses
            proofs with
        | none => simp [childrenModulo?, first, rest] at accepted
        | some tail =>
          have same : pattern :: tail = patterns := by
            simpa [childrenModulo?, first, rest] using accepted
          subst patterns
          exact .cons (proofModulo?_sound first) (childrenModulo?_sound rest)
  termination_by sizeOf proofs
end

/-- The executable checker accepts exactly the checked trees. -/
theorem proofModulo?_eq_some_iff (proof : ModuloProof) (pattern : Pattern) :
    proofModulo? rows language rules context hypotheses proof = some pattern ↔
      ChecksModulo rows language rules context hypotheses proof pattern :=
  ⟨proofModulo?_sound, ChecksModulo.eval⟩

/-- A checked tree is a derivation modulo the definitions. -/
theorem ChecksModulo.derivesModulo {base : BasePremiseEvaluator}
    (definitional : DefinitionalLanguage language rows) {proof : ModuloProof}
    {pattern : Pattern}
    (checked : ChecksModulo rows language rules context hypotheses proof
      pattern) :
    DerivesModulo base language rules context hypotheses pattern := by
  induction checked using ChecksModulo.rec
      (motive_2 := fun _ patterns _ => ∀ pattern ∈ patterns,
        DerivesModulo base language rules context hypotheses pattern) with
  | premise lookup => exact .hypothesis (List.mem_of_getElem? lookup)
  | rule lookup arity typed fragments _ inductionHypothesis =>
    exact .rule (lookupRule?_member lookup).1 _ arity typed fragments inductionHypothesis
  | convert _ same sourceFragment targetFragment sourceTyped targetTyped inductionHypothesis =>
    exact .conversion ((definitional.equationEquiv_iff _ _).mpr same) sourceFragment
      targetFragment sourceTyped targetTyped inductionHypothesis
  | nil => rename_i pattern member; cases member
  | cons _ _ first rest =>
    rename_i pattern member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact rest pattern member

private theorem certificates_for_children (patterns : List Pattern)
    (children : ∀ pattern ∈ patterns, ∃ proof,
      ChecksModulo rows language rules context hypotheses proof pattern) :
    ∃ proofs,
      ChecksModuloList rows language rules context hypotheses proofs patterns := by
  induction patterns with
  | nil => exact ⟨[], .nil⟩
  | cons pattern patterns inductionHypothesis =>
    obtain ⟨proof, checked⟩ := children pattern (by simp)
    obtain ⟨proofs, checks⟩ :=
      inductionHypothesis (fun pattern member => children pattern (List.mem_cons_of_mem _ member))
    exact ⟨proof :: proofs, .cons checked checks⟩

/-- Every derivation modulo the definitions has a checked tree. -/
theorem DerivesModulo.certificate_exists {base : BasePremiseEvaluator}
    (definitional : DefinitionalLanguage language rows)
    (distinct : (rules.map (fun rule => rule.row.id)).Nodup) {pattern : Pattern}
    (derived : DerivesModulo base language rules context hypotheses pattern) :
    ∃ proof, ChecksModulo rows language rules context hypotheses proof pattern := by
  induction derived with
  | hypothesis member =>
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact ⟨.premise index, .premise lookup⟩
  | @rule rule member arguments arity typed fragments _ inductionHypothesis =>
    obtain ⟨children, checked⟩ := certificates_for_children _ inductionHypothesis
    exact ⟨.node ⟨⟨rule.row.id⟩, arguments⟩ children,
      .rule (lookupRule?_of_member distinct member) arity typed fragments checked⟩
  | conversion equivalent leftFragment rightFragment leftTyped rightTyped _
      inductionHypothesis =>
    obtain ⟨child, checked⟩ := inductionHypothesis
    exact ⟨.convert _ child,
      .convert checked ((definitional.equationEquiv_iff _ _).mp equivalent) leftFragment
        rightFragment leftTyped rightTyped⟩

/-- **Certificates are exact.** A term is derivable modulo the definitions
exactly when the executable checker accepts some proof tree for it. -/
theorem derivesModulo_iff_accepted {base : BasePremiseEvaluator}
    (definitional : DefinitionalLanguage language rows)
    (distinct : (rules.map (fun rule => rule.row.id)).Nodup) (pattern : Pattern) :
    DerivesModulo base language rules context hypotheses pattern ↔
      ∃ proof, proofModulo? rows language rules context hypotheses proof =
        some pattern := by
  constructor
  · intro derived
    obtain ⟨proof, checked⟩ := derived.certificate_exists definitional distinct
    exact ⟨proof, checked.eval⟩
  · rintro ⟨proof, accepted⟩
    exact (proofModulo?_sound accepted).derivesModulo definitional

/-! ## The conclusion a tree claims -/

/-- The conclusion of a proof tree, read off its root without checking it. -/
def conclusion? (rules : List Rule) (hypotheses : List Pattern) : ModuloProof → Option Pattern
  | .premise index => hypotheses[index]?
  | .node invocation _ =>
      (lookupRule? rules invocation.ruleId.value).map
        (fun rule => rule.row.instConclusion invocation.arguments)
  | .convert target _ => some target

theorem ChecksModulo.conclusion {proof : ModuloProof} {pattern : Pattern}
    (checked : ChecksModulo rows language rules context hypotheses proof pattern) :
    conclusion? rules hypotheses proof = some pattern := by
  cases checked with
  | premise lookup => simpa only [conclusion?] using lookup
  | rule lookup _ _ _ _ => simp [conclusion?, lookup]
  | convert _ _ _ _ _ _ => rfl

/-! ## Certificates without conversion steps -/

mutual
/-- A certificate without conversion steps is a certificate modulo. -/
def ModuloProof.ofRaw : RawOpenProof → ModuloProof
  | .premise index => .premise index
  | .node invocation children => .node invocation (ModuloProof.ofRawList children)

def ModuloProof.ofRawList : List RawOpenProof → List ModuloProof
  | [] => []
  | child :: children => ModuloProof.ofRaw child :: ModuloProof.ofRawList children
end

mutual
  /-- On a certificate without conversion steps, checking modulo the
  definitions is the checking that ignores them. -/
  theorem proofModulo?_ofRaw (proof : RawOpenProof) :
      proofModulo? rows language rules context hypotheses (ModuloProof.ofRaw proof) =
        proof? language rules context hypotheses proof := by
    cases proof with
    | premise index => simp only [ModuloProof.ofRaw, proofModulo?, proof?]
    | node invocation children =>
      simp only [ModuloProof.ofRaw, proofModulo?, proof?, childrenModulo?_ofRawList children]
  termination_by sizeOf proof

  theorem childrenModulo?_ofRawList (proofs : List RawOpenProof) :
      childrenModulo? rows language rules context hypotheses (ModuloProof.ofRawList proofs) =
        children? language rules context hypotheses proofs := by
    cases proofs with
    | nil => simp only [ModuloProof.ofRawList, childrenModulo?, children?]
    | cons proof proofs =>
      simp only [ModuloProof.ofRawList, childrenModulo?, children?, proofModulo?_ofRaw proof,
        childrenModulo?_ofRawList proofs]
  termination_by sizeOf proofs
end

/-- A certificate without conversion steps is accepted modulo the
definitions exactly when it is accepted by the rules alone. -/
theorem checksModulo_ofRaw_iff (proof : RawOpenProof) (pattern : Pattern) :
    ChecksModulo rows language rules context hypotheses (ModuloProof.ofRaw proof) pattern ↔
      Checks language rules context hypotheses proof pattern := by
  rw [← proofModulo?_eq_some_iff, proofModulo?_ofRaw, proof?_eq_some_iff]

end Exactness

end Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
