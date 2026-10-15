import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker

/-!
# Certificates for many-sorted first-order inference

The wire tree is the existing `RawOpenProof`: a reference to an ordered local
assumption or a named rule with an argument vector and ordered children.
Checking uses the declaration-derived typing checker at every rule application.
The independent certificate judgment erases to `SortedFirstOrderRules.Derives`;
it does not obtain its meaning from a backend checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open FirstOrderRules WellSorted InferenceChecker CertificateGSLT

mutual
  theorem firstOrder_object {pattern : Pattern}
      (fragment : isMatchCorrectAux pattern = true) : isObjectPattern pattern = true := by
    cases pattern with
    | bvar _ | fvar _ => rfl
    | apply name arguments => exact firstOrder_objects fragment
    | _ => simp [isMatchCorrectAux] at fragment
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem firstOrder_objects {patterns : List Pattern}
      (fragment : isMatchCorrectListAux patterns = true) : isObjectPatternList patterns = true := by
    cases patterns with
    | nil => rfl
    | cons first rest =>
        have parts : isMatchCorrectAux first = true ∧ isMatchCorrectListAux rest = true := by
          simpa only [isMatchCorrectListAux, Bool.and_eq_true] using fragment
        simp only [isObjectPatternList, Bool.and_eq_true]
        exact ⟨firstOrder_object parts.1, firstOrder_objects parts.2⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The vector checker reuses the sole authored typing judgment. -/
def checkArgumentTypes (language : LanguageDef) (context : List TypeExpr) :
    List Pattern → List TypeExpr → Bool
  | [], [] => true
  | argument :: arguments, type :: types =>
      isMatchCorrectAux argument &&
        checkHasType language FreeTypeContext.empty context argument type &&
        checkArgumentTypes language context arguments types
  | _, _ => false

theorem checkArgumentTypes_iff (language : LanguageDef) (context : List TypeExpr)
    (arguments : List Pattern) (types : List TypeExpr) :
    checkArgumentTypes language context arguments types = true ↔
      List.Forall₂ (fun argument type =>
        HasType language FreeTypeContext.empty context argument type) arguments types ∧
      (∀ argument ∈ arguments, isMatchCorrectAux argument = true) := by
  induction arguments generalizing types with
  | nil =>
      cases types with
      | nil => simp [checkArgumentTypes]
      | cons type types => simp [checkArgumentTypes]
  | cons argument arguments ih =>
      cases types with
      | nil => simp [checkArgumentTypes]
      | cons type types =>
          simp only [checkArgumentTypes, Bool.and_eq_true]
          constructor
          · rintro ⟨⟨firstFragment, firstTyped⟩, rest⟩
            obtain ⟨restTyped, restFragment⟩ := (ih types).mp rest
            exact ⟨.cons (checkHasType_sound firstTyped) restTyped,
              fun value member => by
                rcases List.mem_cons.mp member with rfl | member
                · exact firstFragment
                · exact restFragment value member⟩
          · rintro ⟨typed, fragments⟩
            cases typed with
            | cons first rest =>
                have firstFragment := fragments argument (by simp)
                exact ⟨⟨firstFragment,
                  checkHasType_complete_of_object first (firstOrder_object firstFragment)⟩,
                  (ih types).mpr ⟨rest, fun value member =>
                    fragments value (List.mem_cons_of_mem _ member)⟩⟩

def lookupRule? (rules : List Rule) (id : String) : Option Rule :=
  rules.find? fun rule => rule.row.id == id

theorem lookupRule?_member {rules : List Rule} {id : String} {rule : Rule}
    (lookup : lookupRule? rules id = some rule) : rule ∈ rules ∧ rule.row.id = id := by
  exact ⟨List.mem_of_find?_eq_some lookup,
    by simpa only [beq_iff_eq] using List.find?_some lookup⟩

theorem lookupRule?_of_member {rules : List Rule}
    (distinct : (rules.map (fun rule => rule.row.id)).Nodup)
    {rule : Rule} (member : rule ∈ rules) : lookupRule? rules rule.row.id = some rule := by
  induction rules with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [lookupRule?]
      · have different : first.row.id ≠ rule.row.id := by
          intro equal
          have inNames : rule.row.id ∈ rest.map (fun value => value.row.id) :=
            List.mem_map.mpr ⟨rule, member, rfl⟩
          apply (List.nodup_cons.mp distinct).1
          simpa only [equal] using inNames
        simpa only [lookupRule?, List.find?_cons, beq_eq_false_iff_ne.mpr different,
          Bool.false_eq_true, ↓reduceIte] using ih (List.nodup_cons.mp distinct).2 member

mutual
  /-- Ordered, typed certificate checking independently of an executable backend. -/
  inductive Checks (language : LanguageDef) (rules : List Rule)
      (context : List TypeExpr) (hypotheses : List Pattern) : RawOpenProof → Pattern → Prop where
    | premise {index : Nat} {pattern : Pattern} : hypotheses[index]? = some pattern →
        Checks language rules context hypotheses (.premise index) pattern
    | rule {invocation : RuleInstance} {rule : Rule} {children : List RawOpenProof} :
        lookupRule? rules invocation.ruleId.value = some rule →
        invocation.arguments.length = rule.row.vars.length →
        List.Forall₂ (fun argument type =>
          HasType language FreeTypeContext.empty context argument type)
          invocation.arguments rule.variableTypes →
        (∀ argument ∈ invocation.arguments, isMatchCorrectAux argument = true) →
        ChecksList language rules context hypotheses children (rule.row.instPremises invocation.arguments) →
        Checks language rules context hypotheses (.node invocation children)
          (rule.row.instConclusion invocation.arguments)

  inductive ChecksList (language : LanguageDef) (rules : List Rule)
      (context : List TypeExpr) (hypotheses : List Pattern) :
      List RawOpenProof → List Pattern → Prop where
    | nil : ChecksList language rules context hypotheses [] []
    | cons {child : RawOpenProof} {children : List RawOpenProof}
        {pattern : Pattern} {patterns : List Pattern} :
        Checks language rules context hypotheses child pattern →
        ChecksList language rules context hypotheses children patterns →
        ChecksList language rules context hypotheses (child :: children) (pattern :: patterns)
end

mutual
  def proof? (language : LanguageDef) (rules : List Rule)
      (context : List TypeExpr) (hypotheses : List Pattern) : RawOpenProof → Option Pattern
    | .premise index => hypotheses[index]?
    | .node invocation children => do
        let rule ← lookupRule? rules invocation.ruleId.value
        if invocation.arguments.length = rule.row.vars.length ∧
            checkArgumentTypes language context invocation.arguments rule.variableTypes = true then
          let premises ← children? language rules context hypotheses children
          if premises = rule.row.instPremises invocation.arguments then
            some (rule.row.instConclusion invocation.arguments)
          else none
        else none
  termination_by proof => sizeOf proof

  def children? (language : LanguageDef) (rules : List Rule)
      (context : List TypeExpr) (hypotheses : List Pattern) : List RawOpenProof → Option (List Pattern)
    | [] => some []
    | child :: children => do
        let first ← proof? language rules context hypotheses child
        let rest ← children? language rules context hypotheses children
        pure (first :: rest)
  termination_by children => sizeOf children
end

mutual
  theorem Checks.eval {language : LanguageDef} {rules : List Rule} {context : List TypeExpr}
      {hypotheses : List Pattern} {proof : RawOpenProof} {pattern : Pattern}
      (checked : Checks language rules context hypotheses proof pattern) :
      proof? language rules context hypotheses proof = some pattern := by
    cases checked with
    | premise lookup => simpa only [proof?] using lookup
    | rule lookup arity typed fragments children =>
        simp [proof?, lookup, arity, (checkArgumentTypes_iff _ _ _ _).mpr ⟨typed, fragments⟩,
          children.eval]
  termination_by sizeOf proof

  theorem ChecksList.eval {language : LanguageDef} {rules : List Rule} {context : List TypeExpr}
      {hypotheses : List Pattern} {proofs : List RawOpenProof} {patterns : List Pattern}
      (checked : ChecksList language rules context hypotheses proofs patterns) :
      children? language rules context hypotheses proofs = some patterns := by
    cases checked with
    | nil => simp [children?]
    | cons first rest => simp [children?, first.eval, rest.eval]
  termination_by sizeOf proofs
end

mutual
  theorem proof?_sound {language : LanguageDef} {rules : List Rule} {context : List TypeExpr}
      {hypotheses : List Pattern} {proof : RawOpenProof} {pattern : Pattern}
      (accepted : proof? language rules context hypotheses proof = some pattern) :
      Checks language rules context hypotheses proof pattern := by
    cases proof with
    | premise index => exact .premise (by simpa only [proof?] using accepted)
    | node invocation children =>
        cases found : lookupRule? rules invocation.ruleId.value with
        | none => simp [proof?, found] at accepted
        | some rule =>
            by_cases valid : invocation.arguments.length = rule.row.vars.length ∧
                checkArgumentTypes language context invocation.arguments rule.variableTypes = true
            · cases returned : children? language rules context hypotheses children with
              | none => simp [proof?, found, valid, returned] at accepted
              | some premises =>
                  have data : premises = rule.row.instPremises invocation.arguments ∧
                      rule.row.instConclusion invocation.arguments = pattern := by
                    simpa [proof?, found, valid, returned] using accepted
                  obtain ⟨typed, fragment⟩ := (checkArgumentTypes_iff _ _ _ _).mp valid.2
                  rw [← data.2]
                  exact .rule found valid.1 typed fragment
                    (data.1 ▸ children?_sound returned)
            · simp [proof?, found, valid] at accepted
    termination_by sizeOf proof

  theorem children?_sound {language : LanguageDef} {rules : List Rule} {context : List TypeExpr}
      {hypotheses : List Pattern} {proofs : List RawOpenProof} {patterns : List Pattern}
      (accepted : children? language rules context hypotheses proofs = some patterns) :
      ChecksList language rules context hypotheses proofs patterns := by
    cases proofs with
    | nil =>
        simp only [children?, Option.some.injEq] at accepted
        subst patterns
        exact .nil
    | cons proof proofs =>
        cases first : proof? language rules context hypotheses proof with
        | none => simp [children?, first] at accepted
        | some pattern =>
            cases rest : children? language rules context hypotheses proofs with
            | none => simp [children?, first, rest] at accepted
            | some tail =>
                have same : pattern :: tail = patterns := by simpa [children?, first, rest] using accepted
                subst patterns
                exact .cons (proof?_sound first) (children?_sound rest)
  termination_by sizeOf proofs
end

theorem proof?_eq_some_iff (language : LanguageDef) (rules : List Rule) (context : List TypeExpr)
    (hypotheses : List Pattern) (proof : RawOpenProof) (pattern : Pattern) :
    proof? language rules context hypotheses proof = some pattern ↔
      Checks language rules context hypotheses proof pattern := ⟨proof?_sound, Checks.eval⟩

theorem Checks.derives {language : LanguageDef} {rules : List Rule} {context : List TypeExpr}
    {hypotheses : List Pattern} {proof : RawOpenProof} {pattern : Pattern}
    (checked : Checks language rules context hypotheses proof pattern) :
    Derives language rules context hypotheses pattern := by
  induction checked using Checks.rec
      (motive_2 := fun _ patterns _ => ∀ pattern ∈ patterns,
        Derives language rules context hypotheses pattern) with
  | premise lookup => exact .hypothesis (List.mem_of_getElem? lookup)
  | rule lookup arity typed fragments _ ih =>
      exact .rule (lookupRule?_member lookup).1 _ arity typed fragments ih
  | nil => rename_i pattern member; cases member
  | cons _ _ first rest =>
      rename_i pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact rest pattern member

private theorem certificates_for_children {language : LanguageDef} {rules : List Rule}
    {context : List TypeExpr} {hypotheses : List Pattern} (patterns : List Pattern)
    (children : ∀ pattern ∈ patterns, ∃ proof,
      Checks language rules context hypotheses proof pattern) :
    ∃ proofs, ChecksList language rules context hypotheses proofs patterns := by
  induction patterns with
  | nil => exact ⟨[], .nil⟩
  | cons pattern patterns ih =>
      obtain ⟨proof, checked⟩ := children pattern (by simp)
      obtain ⟨proofs, checks⟩ := ih (fun pattern member => children pattern (List.mem_cons_of_mem _ member))
      exact ⟨proof :: proofs, .cons checked checks⟩

theorem Derives.certificate_exists {language : LanguageDef} {rules : List Rule}
    (distinct : (rules.map (fun rule => rule.row.id)).Nodup)
    {context : List TypeExpr} {hypotheses : List Pattern} {pattern : Pattern}
    (derived : Derives language rules context hypotheses pattern) :
    ∃ proof, Checks language rules context hypotheses proof pattern := by
  induction derived with
  | hypothesis member =>
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
      exact ⟨.premise index, .premise lookup⟩
  | @rule rule member arguments arity typed fragments _ ih =>
      obtain ⟨children, checked⟩ := certificates_for_children _ ih
      exact ⟨.node ⟨⟨rule.row.id⟩, arguments⟩ children,
        .rule (lookupRule?_of_member distinct member) arity typed fragments checked⟩

end Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
