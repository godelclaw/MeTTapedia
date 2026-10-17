import Mettapedia.GSLT.LanguageDef.PartialRecursivePresentation
import Mettapedia.Languages.HOLLight.InferenceCompiler
import Mettapedia.Computability.UniversalEffectiveEvidence

/-!
# Finite-code evaluation hosted by the original HOL Light kernel

The existing twenty-three arithmetic and evaluation rules form one finite
calculus. Codes and inputs are data in its judgments. Rule admission and the
semantic interpretation are earned for this concrete family; no semantic
checker callback is supplied by the caller.

The target authority is the original HOL Light kernel under exactly the
finite generated axiom policy. Reflection covers arbitrary target proofs of
canonical evaluation judgments. Witness existence is distinct from an
executable uniform machine descriptor, reverse extraction, and a time bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.EffectiveEvidenceHosting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.PartialRecursive
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Nat.Partrec
open Mettapedia.Languages.OpenTheory

/-- The original ordered universal rule rows, without sorting annotations. -/
def universalRules : List FORule := rules.map Rule.row

/-- The original ten numeral/code formers, with judgment heads declared separately. -/
def termLanguage : LanguageDef := { language with terms := language.terms.take 10 }

/-- A finite admitted source calculus with the original data constructors. -/
def calculus : CalculusLanguageDef where
  toLanguageDef := termLanguage
  judgments := [⟨"add", 3⟩, ⟨"mul", 3⟩, ⟨"lt", 2⟩, ⟨"le", 2⟩, ⟨"pair", 3⟩,
    ⟨"eval", 3⟩, ⟨"prec", 5⟩, ⟨"search", 4⟩, ⟨"halts", 2⟩]
  rules := universalRules.map FORule.toSchema

theorem language_validate : termLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;> decide +kernel

theorem calculus_admitted : calculus.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [show calculus.toLanguageDef = termLanguage from rfl, language_validate]
  decide +kernel

def validatedCalculus : ValidatedCalculusLanguageDef := ⟨calculus, calculus_admitted⟩

theorem calculus_firstOrder : FirstOrderCalculus calculus :=
  firstOrderCheck_sound (by decide +kernel)

theorem inferenceRules_universal : inferenceRules calculus = universalRules := by
  simp only [inferenceRules, calculus, List.map_map]
  rw [← List.map_id universalRules]
  apply List.map_congr_left
  intro rule _
  cases rule
  simp [inferenceRule, FORule.toSchema, FORule.formals, ruleNames, List.map_map,
    Function.comp_def]

/-- Schema admission is derived from the checked concrete rule family. -/
theorem universalPackage : Mettapedia.Logic.HOL.Embedding.InferenceRules.SchemaPackage
    universalRules :=
  inferenceRules_universal ▸ inferenceRules_schemaPackage calculus_firstOrder

mutual
  theorem matchCorrect_object_canonical (pattern : Pattern)
      (correct : isMatchCorrectAux pattern = true) :
      isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true := by
    cases pattern with
    | bvar _ => exact ⟨rfl, rfl⟩
    | fvar _ => exact ⟨rfl, rfl⟩
    | apply _ arguments => exact matchCorrectList_object_canonical arguments correct
    | _ => simp [isMatchCorrectAux] at correct
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem matchCorrectList_object_canonical (patterns : List Pattern)
      (correct : isMatchCorrectListAux patterns = true) :
      isObjectPatternList patterns = true ∧
        Pattern.hasCanonicalBinderMetadataList patterns = true := by
    cases patterns with
    | nil => exact ⟨rfl, rfl⟩
    | cons pattern patterns =>
      obtain ⟨head, rest⟩ := (Bool.and_eq_true _ _).mp correct
      obtain ⟨headObject, headCanonical⟩ := matchCorrect_object_canonical pattern head
      obtain ⟨restObject, restCanonical⟩ := matchCorrectList_object_canonical patterns rest
      exact ⟨(Bool.and_eq_true _ _).mpr ⟨headObject, restObject⟩,
        (Bool.and_eq_true _ _).mpr ⟨headCanonical, restCanonical⟩⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- Typed, match-correct closed source arguments earn the exact HOL bridge admission. -/
theorem sorted_argument_valid {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty [] pattern type)
    (correct : isMatchCorrectAux pattern = true) : argumentValidAt 0 pattern = true := by
  obtain ⟨object, canonical⟩ := matchCorrect_object_canonical pattern correct
  exact (Bool.and_eq_true _ _).mpr ⟨typed.empty_isGroundAt object typed.isWellScopedAt, canonical⟩

theorem typed_arguments {patterns : List Pattern} {types : List TypeExpr}
    (typed : List.Forall₂ (fun argument type =>
      HasType language FreeTypeContext.empty [] argument type) patterns types) :
    ∀ a ∈ patterns, ∃ type, HasType language FreeTypeContext.empty [] a type := by
  induction typed with
  | nil => simp
  | cons head _ ih =>
    intro a member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, head⟩
    · exact ih a member

/-- Sorting is forgotten only after every original argument earns ground admission. -/
theorem sorted_to_firstOrder {pattern : Pattern}
    (derived : SortedFirstOrderRules.Derives language rules [] [] pattern) :
    FODerivable universalRules pattern := by
  induction derived with
  | hypothesis member => simp at member
  | @rule rule member arguments arity typed correct _ ih =>
    apply FODerivable.rule rule.row (List.mem_map.mpr ⟨rule, member, rfl⟩)
      arguments arity
    · intro argument inArguments
      obtain ⟨type, argumentTyped⟩ := typed_arguments typed argument inArguments
      exact sorted_argument_valid argumentTyped (correct argument inArguments)
    · exact ih

/-- Every untyped universal rule instance preserves the original code interpretation. -/
theorem firstOrder_valid {pattern : Pattern}
    (derived : FODerivable universalRules pattern) : Valid pattern := by
  induction derived with
  | rule rule member arguments arity _ _ ih =>
      change rule ∈ PartialRecursive.rules.map Rule.row at member
      obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
      subst rule
      simp only [PartialRecursive.rules, List.mem_cons, List.not_mem_nil, or_false] at originalMember
      rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨a, rfl⟩ := list_one arity
        simp [addZero_conclusion]
      · obtain ⟨a, b, c, rfl⟩ := list_three arity
        have sum := ih (addP a b c) (by simp [addSucc_premises])
        simp only [addSucc_conclusion, valid_add, natValue_succ] at sum ⊢
        omega
      · obtain ⟨a, rfl⟩ := list_one arity
        simp [mulZero_conclusion]
      · obtain ⟨a, b, c, d, rfl⟩ := list_four arity
        have product := ih (mulP a b c) (by simp [mulSucc_premises])
        have sum := ih (addP c a d) (by simp [mulSucc_premises])
        simp only [mulSucc_conclusion, valid_mul, valid_add, natValue_succ] at product sum ⊢
        rw [Nat.mul_succ, product, sum]
      · obtain ⟨a, rfl⟩ := list_one arity
        simp [ltZero_conclusion]
      · obtain ⟨a, b, rfl⟩ := list_two arity
        have below := ih (ltP a b) (by simp [ltSucc_premises])
        simp only [ltSucc_conclusion, valid_lt, natValue_succ] at below ⊢
        omega
      · obtain ⟨a, rfl⟩ := list_one arity
        simp [leZero_conclusion]
      · obtain ⟨a, b, rfl⟩ := list_two arity
        have below := ih (leP a b) (by simp [leSucc_premises])
        simp only [leSucc_conclusion, valid_le, natValue_succ] at below ⊢
        omega
      · obtain ⟨a, b, s, c, rfl⟩ := list_four arity
        have below := ih (ltP a b) (by simp [pairBelow_premises])
        have square := ih (mulP b b s) (by simp [pairBelow_premises])
        have sum := ih (addP s a c) (by simp [pairBelow_premises])
        simp only [pairBelow_conclusion, valid_lt, valid_mul, valid_add,
          valid_pair] at below square sum ⊢
        rw [Nat.pair, if_pos below, square, sum]
      · obtain ⟨a, b, s, t, c, rfl⟩ := list_five arity
        have below := ih (leP b a) (by simp [pairAbove_premises])
        have square := ih (mulP a a s) (by simp [pairAbove_premises])
        have lower := ih (addP s a t) (by simp [pairAbove_premises])
        have upper := ih (addP t b c) (by simp [pairAbove_premises])
        simp only [pairAbove_conclusion, valid_le, valid_mul, valid_add,
          valid_pair] at below square lower upper ⊢
        rw [Nat.pair, if_neg (Nat.not_lt.mpr below), square, lower, upper]
      · obtain ⟨n, rfl⟩ := list_one arity
        simp only [evalZero_conclusion, valid_eval, codeValue_czero, natValue_zero]
        exact mem_eval_zero.mpr rfl
      · obtain ⟨n, rfl⟩ := list_one arity
        simp only [evalSucc_conclusion, valid_eval, codeValue_csucc, natValue_succ]
        exact mem_eval_succ.mpr rfl
      · obtain ⟨n, a, b, rfl⟩ := list_three arity
        have paired := ih (pairP a b n) (by simp [evalLeft_premises])
        simp only [evalLeft_conclusion, valid_pair, valid_eval, codeValue_cleft] at paired ⊢
        rw [mem_eval_left, ← paired, Nat.unpair_pair]
      · obtain ⟨n, a, b, rfl⟩ := list_three arity
        have paired := ih (pairP a b n) (by simp [evalRight_premises])
        simp only [evalRight_conclusion, valid_pair, valid_eval, codeValue_cright] at paired ⊢
        rw [mem_eval_right, ← paired, Nat.unpair_pair]
      · obtain ⟨f, g, n, a, b, m, rfl⟩ := list_six arity
        have left := ih (evalP f n a) (by simp [evalPair_premises])
        have right := ih (evalP g n b) (by simp [evalPair_premises])
        have paired := ih (pairP a b m) (by simp [evalPair_premises])
        simp only [evalPair_conclusion, valid_eval, valid_pair,
          codeValue_cpair] at left right paired ⊢
        exact mem_eval_pair.mpr ⟨_, left, _, right, paired⟩
      · obtain ⟨f, g, n, k, m, rfl⟩ := list_five arity
        have inner := ih (evalP g n k) (by simp [evalComp_premises])
        have outer := ih (evalP f k m) (by simp [evalComp_premises])
        simp only [evalComp_conclusion, valid_eval, codeValue_ccomp] at inner outer ⊢
        exact mem_eval_comp.mpr ⟨_, inner, outer⟩
      · obtain ⟨f, g, a, m, rfl⟩ := list_four arity
        have base := ih (evalP f a m) (by simp [precZero_premises])
        simp only [precZero_conclusion, valid_eval, valid_prec, natValue_zero] at base ⊢
        exact base
      · obtain ⟨f, g, a, k, i, p, q, m, rfl⟩ := list_eight arity
        have previous := ih (precP f g a k i) (by simp [precSucc_premises])
        have inner := ih (pairP k i p) (by simp [precSucc_premises])
        have outer := ih (pairP a p q) (by simp [precSucc_premises])
        have step := ih (evalP g q m) (by simp [precSucc_premises])
        simp only [precSucc_conclusion, valid_prec, valid_pair, valid_eval,
          natValue_succ] at previous inner outer step ⊢
        rw [mem_precValue_succ]
        exact ⟨_, previous, by rw [inner, outer]; exact step⟩
      · obtain ⟨f, g, a, k, n, m, rfl⟩ := list_six arity
        have paired := ih (pairP a k n) (by simp [evalPrec_premises])
        have value := ih (precP f g a k m) (by simp [evalPrec_premises])
        simp only [evalPrec_conclusion, valid_pair, valid_prec, valid_eval,
          codeValue_cprec] at paired value ⊢
        rw [← paired, prec_eval]
        exact value
      · obtain ⟨f, a, s, rfl⟩ := list_three arity
        simp [searchZero_conclusion]
      · obtain ⟨f, a, s, j, t, q, w, rfl⟩ := list_seven arity
        have earlier := ih (searchP f a s j) (by simp [searchSucc_premises])
        have sum := ih (addP j s t) (by simp [searchSucc_premises])
        have paired := ih (pairP a t q) (by simp [searchSucc_premises])
        have step := ih (evalP f q (succP w)) (by simp [searchSucc_premises])
        simp only [searchSucc_conclusion, valid_search, valid_add, valid_pair, valid_eval,
          natValue_succ] at earlier sum paired step ⊢
        intro i below
        rcases Nat.lt_succ_iff_lt_or_eq.mp below with below | rfl
        · exact earlier i below
        · exact ⟨natValue w, by rw [sum, paired]; exact step⟩
      · obtain ⟨f, a, s, j, t, q, n, rfl⟩ := list_seven arity
        have earlier := ih (searchP f a s j) (by simp [evalSearch_premises])
        have sum := ih (addP j s t) (by simp [evalSearch_premises])
        have paired := ih (pairP a t q) (by simp [evalSearch_premises])
        have found := ih (evalP f q zeroP) (by simp [evalSearch_premises])
        have input := ih (pairP a s n) (by simp [evalSearch_premises])
        simp only [evalSearch_conclusion, valid_search, valid_add, valid_pair, valid_eval,
          natValue_zero, codeValue_crfind] at earlier sum paired found input ⊢
        rw [← input, mem_eval_rfind]
        simp only [Nat.unpair_pair]
        exact ⟨natValue j, sum, by rw [sum, paired]; exact found, earlier⟩
      · obtain ⟨c, n, m, rfl⟩ := list_three arity
        have value := ih (evalP c n m) (by simp [halting_premises])
        simp only [halting_conclusion, valid_eval, valid_halts] at value ⊢
        exact Part.dom_iff_mem.mpr ⟨_, value⟩


/-- The finite first-order calculus presents exactly the graph of the original code evaluator. -/
theorem firstOrder_iff (judgment : Judgment) :
    FODerivable universalRules judgment.pattern ↔ judgment.Holds := by
  constructor
  · intro derived
    exact (valid_iff_holds judgment).mp (firstOrder_valid derived)
  · intro holds
    exact sorted_to_firstOrder ((derives_iff judgment).mpr holds)

@[simp] theorem numeral_valid (n : Nat) : argumentValidAt 0 (num n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [argumentValidAt, num, succP, Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList] using ih

@[simp] theorem code_valid (code : Code) : argumentValidAt 0 (codePattern code) = true := by
  induction code <;>
    simp_all [argumentValidAt, codePattern, czeroP, csuccP, cleftP, crightP,
      cpairP, ccompP, cprecP, crfindP, Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

/-- Every closed universal judgment has the original checker's canonical admission. -/
theorem judgment_valid (judgment : Judgment) : argumentValidAt 0 judgment.pattern = true := by
  have numeral (n : Nat) := numeral_valid n
  have code (c : Code) := code_valid c
  cases judgment <;>
    simp_all [argumentValidAt, Judgment.pattern, addP, mulP, ltP, leP, pairP,
      evalP, precP, searchP, haltsP, Pattern.isGroundAt, Pattern.isGroundListAt,
      Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

/-- The admitted source checker accepts exactly true universal judgments. -/
theorem source_checked_iff (judgment : Judgment) :
    (∃ proof, checkRaw validatedCalculus judgment.pattern proof = true) ↔ judgment.Holds := by
  have bridge := checker_iff validatedCalculus calculus_firstOrder judgment.pattern
  change (∃ proof, checkRaw validatedCalculus judgment.pattern proof = true) ↔
    FODerivable (inferenceRules calculus) judgment.pattern at bridge
  rw [inferenceRules_universal] at bridge
  exact bridge.trans (firstOrder_iff judgment)

/-- The actual original target graph checker, under the generated finite policy. -/
def TargetChecked (judgment : Judgment) : Prop :=
  ∃ (out : Theorem) (certificate : ProofSystem.Certificate),
    (ProofSystem.checker (InferenceHosting.policy universalRules)).check out certificate = true ∧
    out.sequent.hyp = ∅ ∧ out.sequent.concl = InferenceCompiler.compileClaim judgment.pattern

/-- The source interpreter and the actual HOL graph authority agree on every code judgment. -/
theorem target_checked_iff (judgment : Judgment) : TargetChecked judgment ↔ judgment.Holds := by
  have bridge := InferenceCompiler.graph_checked_iff validatedCalculus calculus_firstOrder
    (judgment_valid judgment)
  change (∃ proof, checkRaw validatedCalculus judgment.pattern proof = true) ↔
    ∃ (out : Theorem) (certificate : ProofSystem.Certificate),
      (ProofSystem.checker (InferenceHosting.policy (inferenceRules calculus))).check
        out certificate = true ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = InferenceCompiler.compileClaim judgment.pattern at bridge
  rw [inferenceRules_universal] at bridge
  exact bridge.symm.trans (source_checked_iff judgment)

/-- Reflection is about arbitrary original kernel proofs, not only emitted certificates. -/
theorem arbitrary_proof_reflects (judgment : Judgment) {out : Theorem}
    (proof : Mettapedia.Logic.Derives (Rule (InferenceHosting.policy universalRules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim judgment.pattern) :
    judgment.Holds :=
  (firstOrder_iff judgment).mp
    (InferenceHosting.reflects universalPackage (judgment_valid judgment)
      proof hypotheses conclusion)

/-- Supplied finite evaluation evidence produces a certificate accepted by the original kernel. -/
theorem evidence_hosted (code : Code) (input output bound : Nat)
    (accepted : Mettapedia.Computability.UniversalEffectiveEvidence.check
      code input output bound = true) : TargetChecked (.eval code input output) :=
  (target_checked_iff (.eval code input output)).mpr
    (Mettapedia.Computability.UniversalEffectiveEvidence.check_sound
      code input output bound accepted)

/-- Arbitrary HOL proofs of an evaluation judgment reflect finite evidence for that exact code. -/
theorem arbitrary_proof_evidence (code : Code) (input output : Nat) {out : Theorem}
    (proof : Mettapedia.Logic.Derives (Rule (InferenceHosting.policy universalRules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim
      (Judgment.eval code input output).pattern) :
    ∃ bound, Mettapedia.Computability.UniversalEffectiveEvidence.check
      code input output bound = true :=
  (Mettapedia.Computability.UniversalEffectiveEvidence.graph_iff_evidence
    code input output).mp (arbitrary_proof_reflects (.eval code input output)
      proof hypotheses conclusion)

/-- Finite-code checking and the original HOL graph checker present exactly the same graph. -/
theorem evidence_iff_target (code : Code) (input output : Nat) :
    (∃ bound, Mettapedia.Computability.UniversalEffectiveEvidence.check
      code input output bound = true) ↔ TargetChecked (.eval code input output) :=
  (Mettapedia.Computability.UniversalEffectiveEvidence.graph_iff_evidence
    code input output).symm.trans (target_checked_iff (.eval code input output)).symm

/-- Every partial-recursive graph has a finite-code presentation in this same finite HOL theory.
Code existence supplies no executable synthesis from arbitrary Lean functions. -/
theorem every_partial_recursive_graph {function : Nat →. Nat}
    (effective : Nat.Partrec function) :
    ∃ code : Code, ∀ input output,
      output ∈ function input ↔ TargetChecked (.eval code input output) := by
  obtain ⟨code, implementation⟩ := Nat.Partrec.Code.exists_code.mp effective
  refine ⟨code, ?_⟩
  intro input output
  rw [← implementation]
  exact (target_checked_iff (.eval code input output)).symm

/-- Countable declarations can be represented by accepted evaluations of their enumerator.
This result does not admit the decoded declaration into any separate source history. -/
theorem declaration_evidence_iff (enumerator : Code) (declaration : Nat) :
    (∃ witness, Mettapedia.Computability.UniversalEffectiveEvidence.declarationMember
      enumerator declaration witness = true) ↔
      ∃ index, TargetChecked (.eval enumerator index declaration) := by
  rw [Mettapedia.Computability.UniversalEffectiveEvidence.declaration_member_iff]
  exact exists_congr fun index => (target_checked_iff (.eval enumerator index declaration)).symm

namespace Controls

theorem finite_rule_count : universalRules.length = 23 ∧
    (InferenceCompiler.compileAxioms calculus).length = 23 := by
  rw [InferenceCompiler.compileAxioms_length]
  decide +kernel

/-- Ordinary evaluation has an actual accepted target certificate. -/
theorem two_successors_hosted : TargetChecked (.eval (.comp .succ .succ) 3 5) := by
  apply (target_checked_iff _).mpr
  exact mem_eval_comp.mpr ⟨4, mem_eval_succ.mpr rfl, mem_eval_succ.mpr rfl⟩

/-- Arbitrary target proofs cannot certify the wrong successor value. -/
theorem wrong_successor_refused : ¬ TargetChecked (.eval .succ 3 3) := by
  rw [target_checked_iff]
  change ¬ 3 ∈ Code.succ.eval 3
  rw [mem_eval_succ]
  omega

/-- No finite accepting search evidence or arbitrary target proof exists for this divergent code. -/
theorem divergent_search_refused : ¬ TargetChecked (.halts (.rfind' .succ) 0) := by
  rw [target_checked_iff]
  change ¬ ((Code.rfind' .succ).eval 0).Dom
  rw [Part.dom_iff_mem]
  rintro ⟨m, value⟩
  obtain ⟨j, _, zero, _⟩ := mem_eval_rfind.mp value
  rw [mem_eval_succ] at zero
  omega

end Controls

end Mettapedia.Languages.HOLLight.EffectiveEvidenceHosting
