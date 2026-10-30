import Mettapedia.Languages.MeTTa.HE.TypeRulePrograms
import Mettapedia.GSLT.LanguageDef.GroundFactExtension

/-! # Structural admission of every finite HE rule inventory -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypeRulePrograms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open InferenceChecker CertificateGSLT
open Spec.Type Spec.Type.RulePresentation

variable {space : Space} {lookup : TypeLookupRel} {matching : Matching}

private theorem name_safe (judgments : List Judgment) (goal : Judgment) :
    judgmentName judgments goal ≠ "" ∧
      judgmentName judgments goal ≠ Pattern.zipHead ∧
      judgmentName judgments goal ≠ Pattern.mapHead ∧
      judgmentName judgments goal ≠ Pattern.evalHead := by
  have lower (suffix : String) : 22 ≤ ("HE-reference-judgment/" ++ suffix).length := by
    rw [String.length_append]
    change 22 ≤ 22 + suffix.length
    omega
  have size : 22 ≤ (judgmentName judgments goal).length := lower _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro same <;>
    have lengths := congrArg String.length same <;>
    first | (change (judgmentName judgments goal).length = 0 at lengths; omega)
          | (change (judgmentName judgments goal).length = 4 at lengths; omega)
          | (change (judgmentName judgments goal).length = 5 at lengths; omega)

private theorem id_nonempty (position : Nat) : (ruleId position).value ≠ "" := by
  intro same
  have lengths := congrArg String.length same
  change ("HE-reference-rule/" ++ _).length = 0 at lengths
  rw [String.length_append] at lengths
  change 18 + _ = 0 at lengths
  omega

private theorem ground_patterns (judgments : List Judgment)
    (position : Nat) (entry : Instance space lookup matching) :
    Pattern.isGroundListAt 0 (RuleSchema.patterns (schema judgments position entry)) = true := by
  have ground := schema_premises_ground judgments (entry.1 ++ [entry.2.1])
  simpa only [RuleSchema.patterns, schema, List.map_append, List.map_cons, List.map_nil] using ground

theorem schema_locally_valid (judgments : List Judgment)
    (position : Nat) (entry : Instance space lookup matching) :
    RuleSchema.isLocallyValid (schema judgments position entry) = true := by
  have occurrences := GroundFactExtension.occurrencesList_eq_nil_of_groundAt
    0 (RuleSchema.patterns (schema judgments position entry)) (ground_patterns _ _ _)
  simp only [RuleSchema.isLocallyValid, RuleSchema.occurrences, occurrences]
  simp [RuleSchema.metavariableNames, RuleSchema.patterns, schema, encode,
    id_nonempty, List.all_append, List.all_map, List.all_eq_true,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

private theorem lookup_judgment (inventory : List (Instance space lookup matching))
    {goal : Judgment} (member : goal ∈ dictionary inventory) :
    (compile inventory).lookupJudgment? (judgmentName (dictionary inventory) goal) 0 =
      some ⟨judgmentName (dictionary inventory) goal, 0⟩ := by
  let names := ((dictionary inventory).map (judgmentName (dictionary inventory))).eraseDups
  have present : judgmentName (dictionary inventory) goal ∈ names := by
    simp only [names, List.mem_eraseDups, List.mem_map]
    exact ⟨goal, member, rfl⟩
  have nodup := Mettapedia.Util.LinearHash.eraseDups_nodup
    ((dictionary inventory).map (judgmentName (dictionary inventory)))
  have count := List.count_eq_one_of_mem nodup present
  have filtered : names.filter (fun name => name == judgmentName (dictionary inventory) goal) =
      [judgmentName (dictionary inventory) goal] := by
    rw [List.filter_beq, count]
    rfl
  unfold CalculusLanguageDef.lookupJudgment?
  change (match (names.map fun name => (⟨name, 0⟩ : JudgmentDecl)).filter
    (fun declaration => declaration.head == judgmentName (dictionary inventory) goal &&
      declaration.arity == 0) with
    | [declaration] => some declaration
    | _ => none) = _
  simp only [List.filter_map, Function.comp_def, beq_self_eq_true, Bool.and_true, filtered, List.map_cons, List.map_nil]

theorem compile_valid (inventory : List (Instance space lookup matching)) :
    (compile inventory).isValid = true := by
  have base : (LanguageDef.empty "HE-reference-instances").validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [LanguageDef.empty, LanguageDef.typeNames]
  have locals : (compile inventory).rules.all RuleSchema.isLocallyValid = true := by
    apply List.all_eq_true.mpr
    intro rule member
    obtain ⟨⟨entry, position⟩, _, rfl⟩ := List.mem_map.mp member
    exact schema_locally_valid _ _ _
  have ids : (compile inventory).ruleIds.Nodup := by
    have mapped := (List.nodup_range' (s := 0) (n := inventory.length)).map ruleId_injective
    have equal : (compile inventory).ruleIds = (inventory.zipIdx.map Prod.snd).map ruleId := by
      simp only [compile, CalculusLanguageDef.extend, CalculusLanguageDef.ruleIds, List.map_map, schema, Function.comp_def]
    rw [equal, List.zipIdx_map_snd]
    exact mapped
  have localValid : (compile inventory).hasValidLocalRules = true := by
    change ((LanguageDef.empty "HE-reference-instances").validate.isEmpty &&
      (compile inventory).rules.all RuleSchema.isLocallyValid &&
      ((compile inventory).ruleIds.eraseDups.length == (compile inventory).ruleIds.length)) = true
    rw [base, locals]
    simpa using (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr ids
  have signature : (compile inventory).judgmentSignatureValid = true := by
    simp only [CalculusLanguageDef.judgmentSignatureValid, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [compile, CalculusLanguageDef.extend, List.all_map, List.all_eq_true]
      intro name member
      obtain ⟨goal, _, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp member)
      simpa using (name_safe (dictionary inventory) goal).1
    · apply (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr
      simpa [compile, CalculusLanguageDef.extend, CalculusLanguageDef.judgmentHeads,
        Function.comp_def] using Mettapedia.Util.LinearHash.eraseDups_nodup
          ((dictionary inventory).map (judgmentName (dictionary inventory)))
    · simp only [compile, CalculusLanguageDef.extend, CalculusLanguageDef.judgmentHeads,
        List.map_map, List.all_map, List.all_eq_true]
      intro name member
      obtain ⟨goal, _, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp member)
      simp [LanguageDef.empty, (name_safe (dictionary inventory) goal).2]
  have rulesValid : (compile inventory).rules.all (RuleSchema.isValidIn (compile inventory)) = true := by
    apply List.all_eq_true.mpr
    intro rule member
    obtain ⟨⟨entry, position⟩, present, rfl⟩ := List.mem_map.mp member
    have entryMember := List.fst_mem_of_mem_zipIdx present
    simp only [RuleSchema.isValidIn, schema_locally_valid, Bool.true_and]
    change ((entry.1.map (encode (dictionary inventory)) ++ [encode (dictionary inventory) entry.2.1]).all
      (compile inventory).judgmentSchemaValid && true) = true
    simp only [Bool.and_true, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true]
    have good (goal : Judgment) (included : goal ∈ dictionary inventory) :
        (compile inventory).judgmentSchemaValid (encode (dictionary inventory) goal) = true := by
      simp [encode, CalculusLanguageDef.judgmentSchemaValid, lookup_judgment inventory included,
        fixedConstructorListsValid]
    refine ⟨?_, good _ (entry_judgments entryMember).1⟩
    apply List.all_eq_true.mpr
    intro pattern included
    obtain ⟨premise, present, rfl⟩ := List.mem_map.mp included
    exact good _ ((entry_judgments entryMember).2 _ present)
  rw [CalculusLanguageDef.isValid, localValid, signature, rulesValid]
  rfl

def definition (inventory : List (Instance space lookup matching)) : ValidatedCalculusLanguageDef :=
  ⟨compile inventory, compile_valid inventory⟩

def call (position : Nat) : RuleInstance := ⟨ruleId position, []⟩

theorem instance_application (inventory : List (Instance space lookup matching))
    (position : Fin inventory.length) :
    RuleApplication (definition inventory) (call position.val)
      (inventory[position].1.map (encode (dictionary inventory)))
      (encode (dictionary inventory) inventory[position].2.1) := by
  let row := schema (dictionary inventory) position.val inventory[position]
  have member : row ∈ (compile inventory).rules := by
    apply List.mem_map.mpr
    exact ⟨(inventory[position], position.val),
      List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem position.isLt), rfl⟩
  refine .intro row (lookupRule?_eq_some_of_mem (definition inventory) member) (by rfl) (by rfl) ?_ ?_
  · exact instantiateSchemasAt?_sound (instantiateSchemasAt?_eq_self_of_ground [] [] 0 _
      (schema_premises_ground _ _))
  · exact .apply (.nil 0)

/-- Abstraction leaves precisely the source instance's ordered premises as
holes. Application is the already-defined open-derivation substitution. -/
def abstractInstance (inventory : List (Instance space lookup matching))
    (position : Fin inventory.length) :
    OpenDerivation (definition inventory)
      (inventory[position].1.map (encode (dictionary inventory)))
      (encode (dictionary inventory) inventory[position].2.1) :=
  .byRule (call position.val) (instance_application inventory position)
    (assumptionEnvironment (definition inventory) _)

theorem abstractInstance_checks (inventory : List (Instance space lookup matching))
    (position : Fin inventory.length) :
    checkOpenRaw (definition inventory)
      (inventory[position].1.map (encode (dictionary inventory)))
      (encode (dictionary inventory) inventory[position].2.1)
      (abstractInstance inventory position).eraseOpen = true :=
  checkOpenRaw_erase _

/-- Extract every local source instance, including repeated rule occurrences.
No derived conclusion is substituted for a rule's recursive premises. -/
def instances {goal : Judgment} : Tree space lookup matching goal → List (Instance space lookup matching)
  | .node rule children => ⟨rule.1, goal, rule.2⟩ ::
      (List.ofFn fun position => instances (children position)).flatten

theorem tree_compiles {goal : Judgment} (tree : Tree space lookup matching goal)
    (inventory : List (Instance space lookup matching))
    (covered : ∀ entry ∈ instances tree, entry ∈ inventory) :
    Nonempty (OpenDerivation (definition inventory) [] (encode (dictionary inventory) goal)) := by
  classical
  refine Mettapedia.TypeTheory.JudgmentDerivation.Derivation.rec
    (motive := fun goal tree => ∀ (inventory : List (Instance space lookup matching)),
      (∀ entry ∈ instances tree, entry ∈ inventory) →
      Nonempty (OpenDerivation (definition inventory) [] (encode (dictionary inventory) goal)))
    ?_ tree inventory covered
  intro goal rule children ih inventory covered
  have root := covered ⟨rule.1, goal, rule.2⟩ (by simp [instances])
  obtain ⟨position, bound, selected⟩ := List.mem_iff_getElem.mp root
  have application := instance_application inventory ⟨position, bound⟩
  change RuleApplication (definition inventory) (call position)
    (inventory[position].1.map (encode (dictionary inventory)))
    (encode (dictionary inventory) inventory[position].2.1) at application
  rw [selected] at application
  have child (index : Fin rule.1.length) :
      Nonempty (OpenDerivation (definition inventory) []
        (encode (dictionary inventory) rule.1[index])) := by
    apply ih index
    intro entry member
    apply covered entry
    simp only [instances, List.mem_cons, List.mem_flatten, List.mem_ofFn]
    exact Or.inr ⟨instances (children index), ⟨index, rfl⟩, member⟩
  refine ⟨.byRule (call position) application (OpenDerivationList.ofFn _ (fun index => ?_))⟩
  simpa using Classical.choice (child ⟨index.val, by simpa using index.isLt⟩)
/-- Every finite source derivation has a finite qualified rule inventory and
a certificate accepted by the existing generic checker. -/
theorem source_tree_has_certificate {goal : Judgment} (tree : Tree space lookup matching goal) :
    ∃ proof : RawOpenProof,
      checkOpenRaw (definition (instances tree)) []
        (encode (dictionary (instances tree)) goal) proof = true := by
  obtain ⟨compiled⟩ := tree_compiles tree (instances tree) (fun _ member => member)
  exact ⟨compiled.eraseOpen, checkOpenRaw_erase compiled⟩

theorem tree_goal_member {goal : Judgment} (tree : Tree space lookup matching goal) :
    goal ∈ dictionary (instances tree) := by
  match tree with
  | .node rule children =>
      exact (entry_judgments (inventory := instances (.node rule children))
        (entry := ⟨rule.1, _, rule.2⟩) (by simp [instances])).1

/-- The inventory restriction is local source-rule qualification. All fifteen
source judgment families and all forty-one rule forms share this equivalence. -/
theorem source_iff_checked_inventory (goal : Judgment) :
    Source space lookup matching goal ↔
      ∃ inventory : List (Instance space lookup matching), goal ∈ dictionary inventory ∧
        ∃ proof, checkOpenRaw (definition inventory) []
          (encode (dictionary inventory) goal) proof = true := by
  constructor
  · intro source
    obtain ⟨tree⟩ := RulePresentation.complete source
    exact ⟨instances tree, tree_goal_member tree, source_tree_has_certificate tree⟩
  · rintro ⟨inventory, member, proof, checked⟩
    exact accepted_source (compile_valid inventory) member checked

#print axioms compile_valid
#print axioms abstractInstance_checks
#print axioms source_iff_checked_inventory

end Mettapedia.Languages.MeTTa.HE.TypeRulePrograms
