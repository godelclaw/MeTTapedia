import Mettapedia.Languages.MM0.Translation.CalculusSimulation

/-!
# The weight of a certificate, from the weights of its judgments

A rule whose formals have distinct names, each occurring in a premise or in the conclusion,
cannot be given an argument heavier than the judgments it relates: each argument is a
subpattern of an instantiated premise or of the instantiated conclusion. Every node of a
derivation then weighs at most its own judgment and its premises, and summing over the
derivation gives `proofWeight_erase_le`: the certificate of a derivation weighs at most
`2A + 1` times the summed weights of its judgments, `A` bounding the formals of every rule.

So the size of a certificate is governed by the judgments it proves, and a bound on those
judgments is a bound on the certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.CalculusSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Occurrences of a name -/

/-- A metavariable occurs in a schema, outside binders. -/
inductive Occurs (name : String) : Pattern → Prop where
  | here : Occurs name (.fvar name)
  | inside {constructor : String} {schemas : List Pattern} {schema : Pattern} :
      schema ∈ schemas → Occurs name schema → Occurs name (.apply constructor schemas)

mutual
  /-- Executable occurrence. -/
  def occursB (name : String) : Pattern → Bool
    | .fvar other => other == name
    | .apply _ schemas => occursListB name schemas
    | _ => false

  def occursListB (name : String) : List Pattern → Bool
    | [] => false
    | schema :: schemas => occursB name schema || occursListB name schemas
end

mutual
  theorem occursB_iff (name : String) : ∀ schema, occursB name schema = true ↔ Occurs name schema
    | .fvar other => by
        simp only [occursB, beq_iff_eq]
        constructor
        · rintro rfl
          exact .here
        · intro occurs
          cases occurs
          rfl
    | .apply constructor schemas => by
        rw [occursB, occursListB_iff name schemas]
        constructor
        · rintro ⟨schema, member, occurs⟩
          exact .inside member occurs
        · intro occurs
          cases occurs with
          | inside member occurs => exact ⟨_, member, occurs⟩
    | .bvar _ => by simp only [occursB, Bool.false_eq_true, false_iff]; intro occurs; cases occurs
    | .lambda _ _ => by simp only [occursB, Bool.false_eq_true, false_iff]; intro occurs; cases occurs
    | .multiLambda _ _ _ => by simp only [occursB, Bool.false_eq_true, false_iff]; intro occurs; cases occurs
    | .subst _ _ => by simp only [occursB, Bool.false_eq_true, false_iff]; intro occurs; cases occurs
    | .collection _ _ _ => by simp only [occursB, Bool.false_eq_true, false_iff]; intro occurs; cases occurs

  theorem occursListB_iff (name : String) : ∀ schemas,
      occursListB name schemas = true ↔ ∃ schema ∈ schemas, Occurs name schema
    | [] => by simp [occursListB]
    | schema :: schemas => by
        rw [occursListB, Bool.or_eq_true, occursB_iff name schema, occursListB_iff name schemas]
        constructor
        · rintro (occurs | ⟨other, member, occurs⟩)
          · exact ⟨schema, List.mem_cons.mpr (Or.inl rfl), occurs⟩
          · exact ⟨other, List.mem_cons_of_mem _ member, occurs⟩
        · rintro ⟨other, member, occurs⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl occurs
          · exact Or.inr ⟨other, member, occurs⟩
end

/-! ## Covering rules -/

/-- Every formal of the rule has its own name, depth zero, and occurs in the conclusion or in a
premise. -/
def RuleCovers (rule : RuleSchema) : Prop :=
  (rule.metavariables.map Prod.fst).Nodup ∧
    ∀ formal ∈ rule.metavariables, formal.2 = 0 ∧
      (Occurs formal.1 rule.conclusion ∨ ∃ premise ∈ rule.premises, Occurs formal.1 premise)

/-- Executable covering. -/
def ruleCoversB (rule : RuleSchema) : Bool :=
  decide (rule.metavariables.map Prod.fst).Nodup &&
    rule.metavariables.all fun formal =>
      formal.2 == 0 && (occursB formal.1 rule.conclusion || occursListB formal.1 rule.premises)

theorem ruleCoversB_iff (rule : RuleSchema) : ruleCoversB rule = true ↔ RuleCovers rule := by
  simp only [ruleCoversB, RuleCovers, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, Bool.or_eq_true, occursB_iff, occursListB_iff]

/-! ## An argument weighs at most the judgments around it -/

theorem weight_le_weights {pattern : Pattern} {patterns : List Pattern} (member : pattern ∈ patterns) :
    weight pattern ≤ weights patterns := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
      rw [weights]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have := ih member
        omega

mutual
  theorem weight_le_of_occurs {formals : List (String × Nat)} {arguments : List Pattern} {name : String}
      {argument : Pattern} (found : lookupArgumentAt? formals arguments name 0 = some argument) :
      ∀ {schema result : Pattern}, InstantiatesAt formals arguments 0 schema result → Occurs name schema →
        weight argument ≤ weight result
    | _, _, .fvar lookup, .here => by
        rw [found] at lookup
        cases lookup
        exact le_refl _
    | _, _, .apply items, .inside member occurs => by
        have inner := weight_le_of_occursList found items member occurs
        rw [weight]
        omega

  theorem weight_le_of_occursList {formals : List (String × Nat)} {arguments : List Pattern} {name : String}
      {argument : Pattern} (found : lookupArgumentAt? formals arguments name 0 = some argument) :
      ∀ {schemas results : List Pattern}, InstantiatesListAt formals arguments 0 schemas results →
        ∀ {schema : Pattern}, schema ∈ schemas → Occurs name schema → weight argument ≤ weights results
    | _, _, .nil _, _, member, _ => absurd member List.not_mem_nil
    | _, _, .cons head tail, _, member, occurs => by
        rw [weights]
        rcases List.mem_cons.mp member with rfl | member
        · have := weight_le_of_occurs found head occurs
          omega
        · have := weight_le_of_occursList found tail member occurs
          omega
end

theorem weight_le_of_occurs_premise {formals : List (String × Nat)} {arguments : List Pattern} {name : String}
    {argument : Pattern} (found : lookupArgumentAt? formals arguments name 0 = some argument)
    {schemas results : List Pattern} (items : InstantiatesListAt formals arguments 0 schemas results)
    {schema : Pattern} (member : schema ∈ schemas) (occurs : Occurs name schema) :
    weight argument ≤ weights results :=
  weight_le_of_occursList found items member occurs

/-- With distinct names, the formal at a position finds the argument at that position. -/
theorem lookupArgumentAt?_of_mem : ∀ {formals : List (String × Nat)} {arguments : List Pattern},
    (formals.map Prod.fst).Nodup → formals.length = arguments.length → (∀ formal ∈ formals, formal.2 = 0) →
      ∀ {argument : Pattern}, argument ∈ arguments →
        ∃ formal ∈ formals, lookupArgumentAt? formals arguments formal.1 0 = some argument
  | [], [], _, _, _, _, member => by cases member
  | formal :: formals, argument :: arguments, distinct, lengths, depths, other, member => by
      have depth := depths formal (List.mem_cons.mpr (Or.inl rfl))
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨formal, List.mem_cons.mpr (Or.inl rfl), ?_⟩
        simp only [lookupArgumentAt?, if_pos (Prod.ext rfl depth : formal = (formal.1, 0))]
      · simp only [List.map_cons, List.nodup_cons] at distinct
        obtain ⟨later, laterMember, found⟩ := lookupArgumentAt?_of_mem (formals := formals) (arguments := arguments)
          distinct.2 (by simpa using lengths) (fun other member => depths other (List.mem_cons_of_mem _ member)) member
        refine ⟨later, List.mem_cons_of_mem _ laterMember, ?_⟩
        have different : formal ≠ (later.1, 0) := by
          intro same
          apply distinct.1
          rw [same]
          exact List.mem_map.mpr ⟨later, laterMember, rfl⟩
        simp only [lookupArgumentAt?, if_neg different]
        exact found
  | [], _ :: _, _, lengths, _, _, _ => by simp at lengths
  | _ :: _, [], _, lengths, _, _, _ => by simp at lengths

/-- **Every argument of a covering rule weighs at most its instantiated judgments.** -/
theorem argument_weight_le {rule : RuleSchema} (covers : RuleCovers rule) {arguments premises : List Pattern}
    {conclusion : Pattern} (lengths : rule.metavariables.length = arguments.length)
    (premisesInstantiate : InstantiatesList rule.metavariables arguments rule.premises premises)
    (conclusionInstantiates : Instantiates rule.metavariables arguments rule.conclusion conclusion) :
    ∀ argument ∈ arguments, weight argument ≤ weight conclusion + weights premises := by
  intro argument member
  obtain ⟨formal, formalMember, found⟩ := lookupArgumentAt?_of_mem covers.1 lengths
    (fun formal member => (covers.2 formal member).1) member
  rcases (covers.2 formal formalMember).2 with occurs | ⟨premise, premiseMember, occurs⟩
  · have := weight_le_of_occurs found conclusionInstantiates occurs
    omega
  · have := weight_le_of_occurs_premise found premisesInstantiate premiseMember occurs
    omega

theorem weights_le_of_forall {patterns : List Pattern} {bound : ℕ} (each : ∀ pattern ∈ patterns, weight pattern ≤ bound) :
    weights patterns ≤ patterns.length * (bound + 1) := by
  induction patterns with
  | nil => simp [weights]
  | cons first rest ih =>
      have firstBound := each first (List.mem_cons.mpr (Or.inl rfl))
      have restBound := ih fun other member => each other (List.mem_cons_of_mem _ member)
      rw [weights, List.length_cons, Nat.succ_mul]
      omega

/-! ## The weight of a derivation's judgments -/

mutual
  /-- The summed weights of the judgments of a derivation, one more for each. -/
  def judgmentWeight {definition : ValidatedCalculusLanguageDef} {goal : Pattern} :
      Derivation definition goal → ℕ
    | .byRule _ _ children => weight goal + 1 + judgmentWeights children

  def judgmentWeights {definition : ValidatedCalculusLanguageDef} {premises : List Pattern} :
      DerivationList definition premises → ℕ
    | .nil => 0
    | .cons head tail => judgmentWeight head + judgmentWeights tail
end

theorem judgmentWeight_byRule {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (ruleInstance : RuleInstance) {premises : List Pattern}
    (application : RuleApplication definition ruleInstance premises goal) (children : DerivationList definition premises) :
    judgmentWeight (Derivation.byRule ruleInstance application children) = weight goal + 1 + judgmentWeights children := by
  rw [judgmentWeight]

theorem judgmentWeights_nil {definition : ValidatedCalculusLanguageDef} :
    judgmentWeights (DerivationList.nil : DerivationList definition []) = 0 := by
  rw [judgmentWeights]

theorem judgmentWeights_cons {definition : ValidatedCalculusLanguageDef} {premise : Pattern}
    {premises : List Pattern} (head : Derivation definition premise) (tail : DerivationList definition premises) :
    judgmentWeights (DerivationList.cons head tail) = judgmentWeight head + judgmentWeights tail := by
  rw [judgmentWeights]

/-- Every rule of the calculus covers its formals, and has at most `bound` of them. -/
def CoveringCalculus (definition : ValidatedCalculusLanguageDef) (bound : ℕ) : Prop :=
  ∀ rule ∈ definition.1.rules, RuleCovers rule ∧ rule.metavariables.length ≤ bound

theorem rule_member_of_lookup {definition : ValidatedCalculusLanguageDef} {id : RuleId} {rule : RuleSchema}
    (lookup : definition.1.lookupRule? id = some rule) : rule ∈ definition.1.rules :=
  List.mem_of_find?_eq_some lookup

mutual
  /-- **The certificate of a derivation weighs at most `2A + 1` times its judgments.** -/
  theorem proofWeight_erase_le {definition : ValidatedCalculusLanguageDef} {bound : ℕ}
      (covering : CoveringCalculus definition bound) :
      ∀ {goal : Pattern} (derivation : Derivation definition goal),
        proofWeight derivation.erase + bound * (weight goal + 1) ≤ (2 * bound + 1) * judgmentWeight derivation
    | goal, @Derivation.byRule _ ruleInstance premises _
        (.intro rule lookup valid _ premisesInstantiate conclusionInstantiates) children => by
        obtain ⟨covers, small⟩ := covering rule (rule_member_of_lookup lookup)
        have lengths := argumentsValidAt_length valid
        have each := argument_weight_le covers lengths premisesInstantiate conclusionInstantiates
        have argumentsBound := weights_le_of_forall each
        have childrenBound := proofWeights_erase_le covering children
        have count : ruleInstance.arguments.length ≤ bound := by omega
        rw [Derivation.erase, proofWeight, judgmentWeight]
        have product : ruleInstance.arguments.length * (weight goal + weights premises + 1) ≤
            bound * (weight goal + weights premises + 1) := Nat.mul_le_mul_right _ count
        nlinarith [product, argumentsBound, childrenBound]

  theorem proofWeights_erase_le {definition : ValidatedCalculusLanguageDef} {bound : ℕ}
      (covering : CoveringCalculus definition bound) :
      ∀ {premises : List Pattern} (derivations : DerivationList definition premises),
        proofWeights (DerivationList.erase derivations) + bound * weights premises ≤
          (2 * bound + 1) * judgmentWeights derivations
    | _, .nil => by simp [DerivationList.erase, proofWeights, weights, judgmentWeights]
    | _, .cons head tail => by
        have headBound := proofWeight_erase_le covering head
        have tailBound := proofWeights_erase_le covering tail
        rw [DerivationList.erase, proofWeights, weights, judgmentWeights]
        nlinarith [headBound, tailBound]
end

end Mettapedia.Languages.MM0.Translation.CalculusSimulation
