import Mettapedia.Languages.HOLLight.FirstOrder.Calculus
import Std.Data.String.ToNat
import Mathlib.Data.List.Sigma

/-!
# Admission of HOL Light's first-order calculus with finite axioms

The axiom sequents are ground encoded data. Their declarations satisfy the
existing schema checks for every finite list, including repeated sequents.
Declaration identifiers use list positions, so repetitions do not collide.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

mutual
  private theorem closedSchema_checks {pattern : Pattern} (schema : Schema [] pattern)
      (depth : Nat) :
      patternMetavariableOccurrencesAt depth pattern = [] ∧
        pattern.isWellScopedAt depth = true ∧
        patternHasNoCollectionRest pattern = true ∧
        pattern.hasCanonicalBinderMetadata = true := by
    cases schema with
    | metavariable impossible => cases impossible
    | constructor arguments =>
        simpa only [patternMetavariableOccurrencesAt, Pattern.isWellScopedAt,
          patternHasNoCollectionRest, Pattern.hasCanonicalBinderMetadata] using
          closedSchemas_checks arguments depth

  private theorem closedSchemas_checks {patterns : List Pattern} (schemas : Schemas [] patterns)
      (depth : Nat) :
      patternsMetavariableOccurrencesAt depth patterns = [] ∧
        Pattern.isWellScopedListAt depth patterns = true ∧
        patternsHaveNoCollectionRest patterns = true ∧
        Pattern.hasCanonicalBinderMetadataList patterns = true := by
    cases schemas with
    | nil => simp [patternsMetavariableOccurrencesAt, Pattern.isWellScopedListAt,
        patternsHaveNoCollectionRest, Pattern.hasCanonicalBinderMetadataList]
    | cons first rest =>
        obtain ⟨firstOccurrences, firstScope, firstRest, firstMetadata⟩ :=
          closedSchema_checks first depth
        obtain ⟨restOccurrences, restScope, restRest, restMetadata⟩ :=
          closedSchemas_checks rest depth
        simp only [patternsMetavariableOccurrencesAt, Pattern.isWellScopedListAt,
          patternsHaveNoCollectionRest, Pattern.hasCanonicalBinderMetadataList,
          firstOccurrences, firstScope, firstRest, firstMetadata, restOccurrences,
          restScope, restRest, restMetadata, List.nil_append, Bool.and_self,
          and_self]
end

private theorem numeral_schema (count : Nat) : Schema [] (numeralP count) := by
  induction count with
  | zero => exact .constructor .nil
  | succ count ih => exact .constructor (.cons ih .nil)

private theorem list_schema {patterns : List Pattern} (schemas : Schemas [] patterns) :
    Schema [] (listP patterns) := by
  induction patterns with
  | nil => exact .constructor .nil
  | cons first rest ih =>
      cases schemas with
      | cons firstSchema restSchemas =>
          exact .constructor (.cons firstSchema (.cons (ih restSchemas) .nil))

mutual
  private theorem tree_schema : ∀ tree : LabeledTree, Schema [] tree.toPattern
    | .node label children =>
        .constructor (.cons (numeral_schema label) (.cons (treeList_schema children) .nil))

  private theorem treeList_schema : ∀ trees : List LabeledTree,
      Schema [] (LabeledTree.toPatternList trees)
    | [] => .constructor .nil
    | tree :: trees => .constructor (.cons (tree_schema tree) (.cons (treeList_schema trees) .nil))
end

private abbrev dataLanguage := (holCalculus []).toLanguageDef

private theorem constructor_fixed {name : String} {arguments : List Pattern}
    (arity : languageHasConstructorArity dataLanguage name arguments.length = true)
    (valid : ∀ pattern ∈ arguments, fixedConstructorsValid dataLanguage pattern = true) :
    fixedConstructorsValid dataLanguage (.apply name arguments) = true := by
  rw [fixedConstructorsValid, arity, Bool.true_and]
  clear arity
  induction arguments with
  | nil => simp [fixedConstructorListsValid]
  | cons first rest ih =>
      rw [fixedConstructorListsValid, valid first (by simp), Bool.true_and]
      exact ih (fun pattern member => valid pattern (by simp [member]))

private theorem numeral_fixed (count : Nat) :
    fixedConstructorsValid dataLanguage (numeralP count) = true := by
  induction count with
  | zero => decide +kernel
  | succ count ih =>
      apply constructor_fixed (by change languageHasConstructorArity dataLanguage "tree.succ" 1 = true; decide +kernel)
      simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] using ih

private theorem list_fixed {patterns : List Pattern}
    (valid : ∀ pattern ∈ patterns, fixedConstructorsValid dataLanguage pattern = true) :
    fixedConstructorsValid dataLanguage (listP patterns) = true := by
  induction patterns with
  | nil => decide +kernel
  | cons first rest ih =>
      apply constructor_fixed (by change languageHasConstructorArity dataLanguage "tree.cons" 2 = true; decide +kernel)
      intro pattern member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact valid pattern (by simp)
      · exact ih (fun pattern member => valid pattern (by simp [member]))

mutual
  private theorem tree_fixed : ∀ tree : LabeledTree,
      fixedConstructorsValid dataLanguage tree.toPattern = true
    | .node label children => by
        apply constructor_fixed (by change languageHasConstructorArity dataLanguage "tree.node" 2 = true; decide +kernel)
        intro pattern member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact numeral_fixed _
        · exact treeList_fixed _

  private theorem treeList_fixed : ∀ trees : List LabeledTree,
      fixedConstructorsValid dataLanguage (LabeledTree.toPatternList trees) = true
    | [] => by decide +kernel
    | tree :: trees => by
        apply constructor_fixed (by change languageHasConstructorArity dataLanguage "tree.cons" 2 = true; decide +kernel)
        intro pattern member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact tree_fixed _
        · exact treeList_fixed _
end

private theorem sequent_schema (sequent : Sequent) : Schema [] (sequentJ sequent) := by
  apply Schema.constructor
  apply Schemas.cons
  · apply list_schema
    generalize (sortedHypotheses sequent.hyp) = hypotheses
    induction hypotheses with
    | nil => exact .nil
    | cons hypothesis hypotheses ih => exact .cons (tree_schema _) ih
  · exact .cons (tree_schema _) .nil

private theorem sequent_signature (sequent : Sequent) :
    (holCalculus []).judgmentSchemaValid (sequentJ sequent) = true := by
  have hypotheses := list_fixed (patterns :=
    (sortedHypotheses sequent.hyp).map fun term => groundP (encodeCanonical term))
    (by
      intro pattern member
      obtain ⟨term, _, rfl⟩ := List.mem_map.mp member
      exact tree_fixed _)
  simp only [sequentJ, thmJ, CalculusLanguageDef.judgmentSchemaValid,
    fixedConstructorListsValid]
  change fixedConstructorsValid dataLanguage (sequentHypothesesP sequent) = true at hypotheses
  have conclusion : fixedConstructorsValid dataLanguage (sequentConclusionP sequent) = true :=
    tree_fixed _
  rw [hypotheses, conclusion]
  simp only [List.length_cons, List.length_nil]
  decide +kernel

/-- Numbered axiom identifiers are injective, independently of the sequents. -/
theorem axiomIdentifier_injective :
    Function.Injective (fun index : Nat => "hol.axiom-" ++ toString index) := by
  intro first second equal
  exact Nat.repr_injective (String.append_right_inj "hol.axiom-" |>.mp equal)

private theorem axiomIdentifier_nonempty (index : Nat) :
    "hol.axiom-" ++ toString index ≠ "" := by
  intro equal
  have lists := congrArg String.toList equal
  rw [String.toList_append] at lists
  have prefixEmpty := (List.append_eq_nil_iff.mp lists).1
  exact (by decide +kernel : "hol.axiom-".toList ≠ []) prefixEmpty

private theorem axiomRule_local (sequent : Sequent) (index : Nat) :
    RuleSchema.isLocallyValid (rule ("hol.axiom-" ++ toString index) [] [] (sequentJ sequent)) =
      true := by
  obtain ⟨occurrences, scopeCheck, rest, metadata⟩ := closedSchema_checks (sequent_schema sequent) 0
  simp only [rule, RuleSchema.isLocallyValid, RuleSchema.occurrences, RuleSchema.patterns,
    RuleSchema.metavariableNames, List.map_nil, List.all_nil, List.eraseDups_nil,
    List.length_nil, beq_self_eq_true, Bool.and_true, List.nil_append,
    patternsMetavariableOccurrencesAt, occurrences, List.all_cons,
    Pattern.isWellScoped, scopeCheck, rest, metadata]
  simpa only [bne_iff_ne] using axiomIdentifier_nonempty index

private theorem axiomRule_valid (axioms : List Sequent) (sequent : Sequent) (index : Nat) :
    RuleSchema.isValidIn (holCalculus axioms)
      (rule ("hol.axiom-" ++ toString index) [] [] (sequentJ sequent)) = true := by
  have signature : (holCalculus axioms).judgmentSchemaValid (sequentJ sequent) = true :=
    sequent_signature sequent
  rw [RuleSchema.isValidIn, axiomRule_local, Bool.true_and]
  simp only [rule,
    RuleSchema.patterns, List.nil_append, List.all_cons, List.all_nil, signature, Bool.and_self]

private theorem holRules_split (axioms : List Sequent) :
    holRules axioms = holRules [] ++ axiomRules axioms := by
  simp only [holRules, axiomRules, List.zipIdx_nil, List.map_nil, List.append_nil,
    List.append_assoc]

private theorem base_rule_names_fresh :
    ((holRules []).map fun candidate => candidate.id.value).all
      (fun name => name.toList.take 10 != "hol.axiom-".toList) = true := by
  decide +kernel

private theorem axiomIdentifier_prefix (index : Nat) :
    ("hol.axiom-" ++ toString index).toList.take 10 = "hol.axiom-".toList := by
  rw [String.toList_append]
  have length : "hol.axiom-".toList.length = 10 := by decide +kernel
  rw [← length, List.take_left]

/-- Every authored rule and every numbered axiom retain distinct identifiers. -/
theorem holRules_distinct (axioms : List Sequent) :
    ((holRules axioms).map fun candidate => candidate.id.value).Nodup := by
  rw [holRules_split, List.map_append]
  apply List.nodup_append.mpr
  have firstOrder := firstOrderCheck_sound holCalculus_firstOrder
  have base : ((holRules []).map fun candidate => candidate.id.value).Nodup :=
    firstOrder.distinctRules
  have axiomsDistinct : ((axiomRules axioms).map fun candidate => candidate.id.value).Nodup := by
    have numbered := List.nodup_zipIdx_map_snd axioms
    simpa only [axiomRules, List.map_map, rule, Function.comp_def] using
      numbered.map axiomIdentifier_injective
  refine ⟨base, axiomsDistinct, ?_⟩
  intro baseName baseMember axiomName axiomMember equal
  have fresh := List.all_eq_true.mp base_rule_names_fresh baseName baseMember
  obtain ⟨candidate, candidateMember, candidateEqual⟩ := List.mem_map.mp axiomMember
  obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp candidateMember
  change "hol.axiom-" ++ toString index = axiomName at candidateEqual
  have prefixEqual : baseName.toList.take 10 = "hol.axiom-".toList := by
    rw [equal, ← candidateEqual, axiomIdentifier_prefix]
  exact (bne_iff_ne.mp fresh) prefixEqual

/-- The original first-order rendering is admitted for every finite axiom list. -/
theorem holCalculus_valid_axioms (axioms : List Sequent) :
    (holCalculus axioms).isValid = true := by
  have base := holCalculus_valid
  simp only [CalculusLanguageDef.isValid, Bool.and_eq_true,
    CalculusLanguageDef.hasValidLocalRules] at base ⊢
  have localRules : (holCalculus axioms).rules.all RuleSchema.isLocallyValid = true := by
    change (holRules axioms).all RuleSchema.isLocallyValid = true
    rw [holRules_split, List.all_append]
    rw [Bool.and_eq_true]
    refine ⟨base.1.1.1.1.2, ?_⟩
    rw [List.all_eq_true]
    intro candidate member
    obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp member
    exact axiomRule_local sequent index
  have distinct : (holCalculus axioms).ruleIds.Nodup := by
    have ids := holRules_distinct axioms
    apply List.Nodup.of_map (f := RuleId.value)
    simpa only [CalculusLanguageDef.ruleIds, List.map_map, Function.comp_def,
      holCalculus, cacheDefinition, CalculusLanguageDef.extend] using ids
  have validRules : (holCalculus axioms).rules.all (RuleSchema.isValidIn (holCalculus axioms)) = true := by
    change (holRules axioms).all (RuleSchema.isValidIn (holCalculus axioms)) = true
    rw [holRules_split, List.all_append]
    rw [Bool.and_eq_true]
    refine ⟨base.1.2, ?_⟩
    rw [List.all_eq_true]
    intro candidate member
    obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp member
    exact axiomRule_valid axioms sequent index
  refine ⟨⟨⟨⟨⟨base.1.1.1.1.1, localRules⟩, ?_⟩, base.1.1.2⟩, validRules⟩, base.2⟩
  exact (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr distinct

/-- Every finite axiom extension remains in the first-order calculus class. -/
theorem holCalculus_firstOrder_axioms (axioms : List Sequent) :
    FirstOrderCalculus (holCalculus axioms) := by
  have base := firstOrderCheck_sound holCalculus_firstOrder
  have split {candidate : RuleSchema} (member : candidate ∈ (holCalculus axioms).rules) :
      candidate ∈ (holCalculus []).rules ∨ candidate ∈ axiomRules axioms := by
    change candidate ∈ holRules axioms at member
    rwa [holRules_split, List.mem_append] at member
  constructor
  · intro candidate member entry formal
    rcases split member with member | member
    · exact base.arities candidate member entry formal
    · obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp member
      cases formal
  · intro candidate member
    rcases split member with member | member
    · exact base.distinctNames candidate member
    · obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp member
      exact List.nodup_nil
  · intro candidate member
    rcases split member with member | member
    · exact base.premiseSchemas candidate member
    · obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp member
      exact .nil
  · intro candidate member
    rcases split member with member | member
    · exact base.conclusionSchema candidate member
    · obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp member
      exact sequent_schema sequent
  · intro candidate member
    rcases split member with member | member
    · exact base.noSideConditions candidate member
    · obtain ⟨⟨sequent, index⟩, _, rfl⟩ := List.mem_map.mp member
      rfl
  · exact holRules_distinct axioms

/-- The executable first-order boundary accepts every finite axiom extension. -/
theorem holCalculus_firstOrderCheck_axioms (axioms : List Sequent) :
    firstOrderCheck (holCalculus axioms) = true := by
  have firstOrder := holCalculus_firstOrder_axioms axioms
  simp only [firstOrderCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq, checkSchema_iff, checkSchemas_iff, List.isEmpty_iff]
  refine ⟨?_, firstOrder.distinctRules⟩
  intro candidate member
  exact ⟨⟨⟨⟨firstOrder.arities candidate member, firstOrder.distinctNames candidate member⟩,
    firstOrder.premiseSchemas candidate member⟩, firstOrder.conclusionSchema candidate member⟩,
    firstOrder.noSideConditions candidate member⟩

/-- The checker-ready rendering calculus, with its original finite axiom list. -/
def validatedHolCalculus (axioms : List Sequent) : ValidatedCalculusLanguageDef :=
  ⟨holCalculus axioms, holCalculus_valid_axioms axioms⟩

namespace ValidationControls

/-- Repetition of the same axiom does not repeat its declaration identifier. -/
theorem duplicate_axiom_identifiers (sequent : Sequent) :
    ((axiomRules [sequent, sequent]).map fun candidate => candidate.id.value) =
      ["hol.axiom-0", "hol.axiom-1"] := by
  rfl

theorem duplicate_axioms_valid (sequent : Sequent) :
    (holCalculus [sequent, sequent]).isValid = true :=
  holCalculus_valid_axioms _

/-- An external rule referring to an undeclared judgment is refused. -/
theorem undeclared_judgment_refused :
    RuleSchema.isValidIn (holCalculus [])
      (rule "hol.external" [] [] (.apply "hol.Undeclared" [])) = false := by
  decide +kernel

end ValidationControls

end Mettapedia.Languages.HOLLight.FirstOrder
