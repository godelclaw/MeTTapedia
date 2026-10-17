import Mettapedia.Languages.HOLLight.EffectiveEvidenceHosting

/-!
# Executable finite evaluation evidence compiled to source proofs

The evaluator records the successful branches of the original bounded code
interpreter. Its witnesses are compiled into explicit applications of the
existing twenty-three source rules, including arithmetic and search stages.
Source checking, concrete HOL graph emission and independent original replay
are separate executable operations. No proof enumeration is used.

The supplied bound limits this evaluation scheme's encountered values. The
unary arithmetic proofs and explicit evaluation trees have their own sizes;
no polynomial claim in the bit size of that bound is made.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.EffectiveEvidenceCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.PartialRecursive
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.HOLLight.EffectiveEvidenceHosting
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Nat.Partrec (Code)

abbrev Proof (judgment : Judgment) :=
  OpenDerivation validatedCalculus [] judgment.pattern

private theorem presentsUniversal : Presents validatedCalculus universalRules where
  package := inferenceRules_universal ▸ inferenceRules_package calculus_firstOrder
  rules_eq := rfl

private theorem value_valid (value : Value) : argumentValidAt 0 value.pattern = true := by
  cases value with
  | nat n => exact numeral_valid n
  | code c => exact code_valid c

/-- Build one original source application at its exact ordered value arguments. -/
def ruleProof (rule : SortedFirstOrderRules.Rule) (member : rule ∈ PartialRecursive.rules)
    (values : List Value) (arity : values.length = rule.row.vars.length)
    (children : OpenDerivationList validatedCalculus []
      (rule.row.instPremises (values.map Value.pattern))) :
    OpenDerivation validatedCalculus [] (rule.row.instConclusion (values.map Value.pattern)) := by
  have rowMember : rule.row ∈ universalRules := List.mem_map.mpr ⟨rule, member, rfl⟩
  apply OpenDerivation.byRule ⟨⟨rule.row.id⟩, values.map Value.pattern⟩ _ children
  apply (FirstOrderRules.ruleApplication_iff validatedCalculus universalRules
    presentsUniversal.package rule.row rowMember (presentsUniversal.lookup rowMember)
    _ _ _).mpr
  refine ⟨by simpa using arity, ?_, rfl, rfl⟩
  intro argument member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  exact value_valid value

/-- A concrete unary addition proof. -/
def addProof (a : Nat) : (b : Nat) → Proof (.add a b (a + b))
  | 0 => by
      have built := ruleProof addZero (by simp [rules]) [.nat a] rfl
        (by simp [addZero, inference, FORule.instPremises]; exact .nil)
      simpa [Proof, addZero_conclusion, Value.pattern, Judgment.pattern, num] using built
  | b + 1 => by
      have built := ruleProof addSucc (by simp [rules]) [.nat a, .nat b, .nat (a + b)] rfl
        (by simpa [Proof, addSucc_premises, Value.pattern, Judgment.pattern] using
          (OpenDerivationList.cons (addProof a b) .nil))
      simpa [Proof, addSucc_conclusion, Value.pattern, Judgment.pattern, num, Nat.add_succ] using built

/-- A concrete multiplication proof, including every required addition. -/
def mulProof (a : Nat) : (b : Nat) → Proof (.mul a b (a * b))
  | 0 => by
      have built := ruleProof mulZero (by simp [rules]) [.nat a] rfl
        (by simp [mulZero, inference, FORule.instPremises]; exact .nil)
      simpa [Proof, mulZero_conclusion, Value.pattern, Judgment.pattern, num] using built
  | b + 1 => by
      have built := ruleProof mulSucc (by simp [rules])
        [.nat a, .nat b, .nat (a * b), .nat (a * b + a)] rfl
        (by simpa [Proof, mulSucc_premises, Value.pattern, Judgment.pattern] using
          (OpenDerivationList.cons (mulProof a b) (.cons (addProof (a * b) a) .nil)))
      simpa [Proof, mulSucc_conclusion, Value.pattern, Judgment.pattern, num, Nat.mul_succ] using built

def ltProof : (a b : Nat) → a < b → Proof (.lt a b)
  | 0, b + 1, _ => by
      have built := ruleProof ltZero (by simp [rules]) [.nat b] rfl
        (by simp [ltZero, inference, FORule.instPremises]; exact .nil)
      simpa [Proof, ltZero_conclusion, Value.pattern, Judgment.pattern, num] using built
  | a + 1, b + 1, below => by
      have built := ruleProof ltSucc (by simp [rules]) [.nat a, .nat b] rfl
        (by simpa [Proof, ltSucc_premises, Value.pattern, Judgment.pattern] using
          (OpenDerivationList.cons (ltProof a b (Nat.lt_of_succ_lt_succ below)) .nil))
      simpa [Proof, ltSucc_conclusion, Value.pattern, Judgment.pattern, num] using built
  | _, 0, below => False.elim (Nat.not_lt_zero _ below)

def leProof : (a b : Nat) → a ≤ b → Proof (.le a b)
  | 0, b, _ => by
      have built := ruleProof leZero (by simp [rules]) [.nat b] rfl
        (by simp [leZero, inference, FORule.instPremises]; exact .nil)
      simpa [Proof, leZero_conclusion, Value.pattern, Judgment.pattern, num] using built
  | a + 1, b + 1, below => by
      have built := ruleProof leSucc (by simp [rules]) [.nat a, .nat b] rfl
        (by simpa [Proof, leSucc_premises, Value.pattern, Judgment.pattern] using
          (OpenDerivationList.cons (leProof a b (Nat.le_of_succ_le_succ below)) .nil))
      simpa [Proof, leSucc_conclusion, Value.pattern, Judgment.pattern, num] using built
  | _ + 1, 0, below => False.elim (Nat.not_succ_le_zero _ below)

/-- The original pairing rules, with all arithmetic premises produced. -/
def pairProof (a b : Nat) : Proof (.pair a b (Nat.pair a b)) := by
  by_cases below : a < b
  · have built := ruleProof pairBelow (by simp [rules])
      [.nat a, .nat b, .nat (b * b), .nat (b * b + a)] rfl
      (by simpa [Proof, pairBelow_premises, Value.pattern, Judgment.pattern] using
        (OpenDerivationList.cons (ltProof a b below)
          (.cons (mulProof b b) (.cons (addProof (b * b) a) .nil))))
    simpa [Proof, pairBelow_conclusion, Value.pattern, Judgment.pattern, Nat.pair, below] using built
  · have built := ruleProof pairAbove (by simp [rules])
      [.nat a, .nat b, .nat (a * a), .nat (a * a + a), .nat (a * a + a + b)] rfl
      (by simpa [Proof, pairAbove_premises, Value.pattern, Judgment.pattern] using
        (OpenDerivationList.cons (leProof b a (Nat.not_lt.mp below))
          (.cons (mulProof a a) (.cons (addProof (a * a) a)
            (.cons (addProof (a * a + a) b) .nil)))))
    simpa [Proof, pairAbove_conclusion, Value.pattern, Judgment.pattern, Nat.pair, below] using built

/-- Evaluation evidence records all actual subevaluations, including successive search starts. -/
inductive EvalWitness : Code → Nat → Nat → Type where
  | zero (n : Nat) : EvalWitness .zero n 0
  | succ (n : Nat) : EvalWitness .succ n (n + 1)
  | left (n : Nat) : EvalWitness .left n n.unpair.1
  | right (n : Nat) : EvalWitness .right n n.unpair.2
  | pair {f g : Code} {n a b : Nat} : EvalWitness f n a → EvalWitness g n b →
      EvalWitness (.pair f g) n (Nat.pair a b)
  | comp {f g : Code} {n k m : Nat} : EvalWitness g n k → EvalWitness f k m →
      EvalWitness (.comp f g) n m
  | precZero {f g : Code} {a m : Nat} : EvalWitness f a m →
      EvalWitness (.prec f g) (Nat.pair a 0) m
  | precSucc {f g : Code} {a k i m : Nat} :
      EvalWitness (.prec f g) (Nat.pair a k) i →
      EvalWitness g (Nat.pair a (Nat.pair k i)) m →
      EvalWitness (.prec f g) (Nat.pair a (k + 1)) m
  | searchZero {f : Code} {a s : Nat} : EvalWitness f (Nat.pair a s) 0 →
      EvalWitness (.rfind' f) (Nat.pair a s) s
  | searchSucc {f : Code} {a s w m : Nat} : EvalWitness f (Nat.pair a s) (w + 1) →
      EvalWitness (.rfind' f) (Nat.pair a (s + 1)) m →
      EvalWitness (.rfind' f) (Nat.pair a s) m

private def reindexInput {code : Code} {input other output : Nat} (same : input = other)
    (witness : EvalWitness code input output) : EvalWitness code other output := same ▸ witness

/-- Compute exactly the bounded evaluator while recording its successful evaluation tree. -/
def evaluate : (bound : Nat) → (code : Code) → (input : Nat) →
    Option (Sigma (EvalWitness code input))
  | 0, _, _ => none
  | k + 1, .zero, n => do
      guard (n ≤ k)
      return ⟨0, .zero n⟩
  | k + 1, .succ, n => do
      guard (n ≤ k)
      return ⟨n + 1, .succ n⟩
  | k + 1, .left, n => do
      guard (n ≤ k)
      return ⟨n.unpair.1, .left n⟩
  | k + 1, .right, n => do
      guard (n ≤ k)
      return ⟨n.unpair.2, .right n⟩
  | k + 1, .pair f g, n => do
      guard (n ≤ k)
      let ⟨a, left⟩ ← evaluate (k + 1) f n
      let ⟨b, right⟩ ← evaluate (k + 1) g n
      return ⟨Nat.pair a b, .pair left right⟩
  | k + 1, .comp f g, n => do
      guard (n ≤ k)
      let ⟨middle, inner⟩ ← evaluate (k + 1) g n
      let ⟨output, outer⟩ ← evaluate (k + 1) f middle
      return ⟨output, .comp inner outer⟩
  | k + 1, .prec f g, n => do
      guard (n ≤ k)
      match count : n.unpair.2 with
      | 0 =>
          let ⟨output, base⟩ ← evaluate (k + 1) f n.unpair.1
          return ⟨output, reindexInput (by simpa only [count] using Nat.pair_unpair n)
            (.precZero base)⟩
      | j + 1 =>
          let ⟨previous, earlier⟩ ← evaluate k (.prec f g) (Nat.pair n.unpair.1 j)
          let ⟨output, step⟩ ← evaluate (k + 1) g
            (Nat.pair n.unpair.1 (Nat.pair j previous))
          return ⟨output, reindexInput (by simpa only [count] using Nat.pair_unpair n)
            (.precSucc earlier step)⟩
  | k + 1, .rfind' f, n => do
      guard (n ≤ k)
      let ⟨value, tested⟩ ← evaluate (k + 1) f (Nat.pair n.unpair.1 n.unpair.2)
      match value, tested with
      | 0, tested => return ⟨n.unpair.2, reindexInput (Nat.pair_unpair n) (.searchZero tested)⟩
      | w + 1, tested =>
          let ⟨output, later⟩ ← evaluate k (.rfind' f) (Nat.pair n.unpair.1 (n.unpair.2 + 1))
          return ⟨output, reindexInput (Nat.pair_unpair n) (.searchSucc tested later)⟩
termination_by bound code => (bound, sizeOf code)
decreasing_by
  all_goals simp_wf
  all_goals first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega


mutual
  /-- Compile the recorded evaluation branches to original source rule applications. -/
  def compileWitness {code : Code} {input output : Nat}
      (witness : EvalWitness code input output) : Proof (.eval code input output) :=
    match witness with
    | .zero n => by
      have built := ruleProof evalZero (by simp [rules]) [.nat n] rfl
        (by simp [evalZero, inference, FORule.instPremises]; exact .nil)
      simpa [Proof, evalZero_conclusion, Value.pattern, Judgment.pattern, codePattern, num] using built
    | .succ n => by
      have built := ruleProof evalSucc (by simp [rules]) [.nat n] rfl
        (by simp [evalSucc, inference, FORule.instPremises]; exact .nil)
      simpa [Proof, evalSucc_conclusion, Value.pattern, Judgment.pattern, codePattern, num] using built
    | .left n => by
      have built := ruleProof evalLeft (by simp [rules])
        [.nat n, .nat n.unpair.1, .nat n.unpair.2] rfl
        (by simpa [Proof, evalLeft_premises, Value.pattern, Judgment.pattern, Nat.pair_unpair] using
          (OpenDerivationList.cons (pairProof n.unpair.1 n.unpair.2) .nil))
      simpa [Proof, evalLeft_conclusion, Value.pattern, Judgment.pattern, codePattern] using built
    | .right n => by
      have built := ruleProof evalRight (by simp [rules])
        [.nat n, .nat n.unpair.1, .nat n.unpair.2] rfl
        (by simpa [Proof, evalRight_premises, Value.pattern, Judgment.pattern, Nat.pair_unpair] using
          (OpenDerivationList.cons (pairProof n.unpair.1 n.unpair.2) .nil))
      simpa [Proof, evalRight_conclusion, Value.pattern, Judgment.pattern, codePattern] using built
    | @EvalWitness.pair f g n a b left right => by
      have built := ruleProof evalPair (by simp [rules])
        [.code f, .code g, .nat n, .nat a, .nat b, .nat (Nat.pair a b)] rfl
        (by simpa [Proof, evalPair_premises, Value.pattern, Judgment.pattern] using
          (OpenDerivationList.cons (compileWitness left)
            (.cons (compileWitness right) (.cons (pairProof a b) .nil))))
      simpa [Proof, evalPair_conclusion, Value.pattern, Judgment.pattern, codePattern] using built
    | @EvalWitness.comp f g n k m inner outer => by
      have built := ruleProof evalComp (by simp [rules])
        [.code f, .code g, .nat n, .nat k, .nat m] rfl
        (by simpa [Proof, evalComp_premises, Value.pattern, Judgment.pattern] using
          (OpenDerivationList.cons (compileWitness inner) (.cons (compileWitness outer) .nil)))
      simpa [Proof, evalComp_conclusion, Value.pattern, Judgment.pattern, codePattern] using built
    | @EvalWitness.precZero f g a m base => by
      have stage := compilePrecWitness (.precZero (g := g) base)
      have built := ruleProof evalPrec (by simp [rules])
        [.code f, .code g, .nat a, .nat 0, .nat (Nat.pair a 0), .nat m] rfl
        (by simpa [Proof, evalPrec_premises, Value.pattern, Judgment.pattern, Nat.unpair_pair] using
          (OpenDerivationList.cons (pairProof a 0) (.cons stage .nil)))
      simpa [Proof, evalPrec_conclusion, Value.pattern, Judgment.pattern, codePattern] using built
    | @EvalWitness.precSucc f g a k i m earlier step => by
      have stage := compilePrecWitness (.precSucc earlier step)
      have built := ruleProof evalPrec (by simp [rules])
        [.code f, .code g, .nat a, .nat (k + 1), .nat (Nat.pair a (k + 1)), .nat m] rfl
        (by simpa [Proof, evalPrec_premises, Value.pattern, Judgment.pattern, Nat.unpair_pair] using
          (OpenDerivationList.cons (pairProof a (k + 1)) (.cons stage .nil)))
      simpa [Proof, evalPrec_conclusion, Value.pattern, Judgment.pattern, codePattern] using built
    | @EvalWitness.searchZero f a s tested => by
      have initial := ruleProof searchZero (by simp [rules]) [.code f, .nat a, .nat s] rfl
        (by simp [searchZero, inference, FORule.instPremises]; exact .nil)
      have initialProof : Proof (.search f a s 0) := by
        simpa [Proof, searchZero_conclusion, Value.pattern, Judgment.pattern, num] using initial
      simpa [Nat.unpair_pair] using compileSearchWitness (.searchZero tested) s 0
        (by simp [Nat.unpair_pair]) (by simpa [Nat.unpair_pair] using initialProof)
    | @EvalWitness.searchSucc f a s w m tested later => by
      have initial := ruleProof searchZero (by simp [rules]) [.code f, .nat a, .nat s] rfl
        (by simp [searchZero, inference, FORule.instPremises]; exact .nil)
      have initialProof : Proof (.search f a s 0) := by
        simpa [Proof, searchZero_conclusion, Value.pattern, Judgment.pattern, num] using initial
      simpa [Nat.unpair_pair] using compileSearchWitness (.searchSucc tested later) s 0
        (by simp [Nat.unpair_pair]) (by simpa [Nat.unpair_pair] using initialProof)
  termination_by (sizeOf witness, 1)
  decreasing_by
    all_goals simp_wf
    all_goals first | apply Prod.Lex.left; omega | apply Prod.Lex.right; omega

  /-- Retain the primitive-recursion stage carried by its recorded branches. -/
  def compilePrecWitness {f g : Code} {input output : Nat}
      (witness : EvalWitness (.prec f g) input output) :
      Proof (.prec f g input.unpair.1 input.unpair.2 output) :=
    match witness with
    | @EvalWitness.precZero _ _ a m base => by
      have built := ruleProof precZero (by simp [rules]) [.code f, .code g, .nat a, .nat m] rfl
        (by simpa [Proof, precZero_premises, Value.pattern, Judgment.pattern] using
          (OpenDerivationList.cons (compileWitness base) .nil))
      simpa [Proof, precZero_conclusion, Value.pattern, Judgment.pattern, Nat.unpair_pair, num] using built
    | @EvalWitness.precSucc _ _ a k i m earlier step => by
      have built := ruleProof precSucc (by simp [rules])
        [.code f, .code g, .nat a, .nat k, .nat i, .nat (Nat.pair k i),
          .nat (Nat.pair a (Nat.pair k i)), .nat m] rfl
        (by simpa [Proof, precSucc_premises, Value.pattern, Judgment.pattern, Nat.unpair_pair] using
          (OpenDerivationList.cons (compilePrecWitness earlier)
            (.cons (pairProof k i) (.cons (pairProof a (Nat.pair k i))
              (.cons (compileWitness step) .nil)))))
      simpa [Proof, precSucc_conclusion, Value.pattern, Judgment.pattern, Nat.unpair_pair, num] using built
  termination_by (sizeOf witness, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (apply Prod.Lex.left; omega)

  /-- Search extends the earned prefix in original occurrence order, at its original start. -/
  def compileSearchWitness {f : Code} {input output : Nat}
      (witness : EvalWitness (.rfind' f) input output) : (start offset : Nat) →
      (position : input.unpair.2 = offset + start) →
      Proof (.search f input.unpair.1 start offset) →
      Proof (.eval (.rfind' f) (Nat.pair input.unpair.1 start) output) :=
    match witness with
    | @EvalWitness.searchZero _ a current tested => fun start offset position earlier => by
      simp only [Nat.unpair_pair] at position earlier ⊢
      have built := ruleProof evalSearch (by simp [rules])
        [.code f, .nat a, .nat start, .nat offset, .nat (offset + start),
          .nat (Nat.pair a (offset + start)), .nat (Nat.pair a start)] rfl
        (by
          have zeroProof := compileWitness tested
          rw [position] at zeroProof
          simpa [Proof, evalSearch_premises, Value.pattern, Judgment.pattern, num] using
            (OpenDerivationList.cons earlier (.cons (addProof offset start)
              (.cons (pairProof a (offset + start)) (.cons zeroProof
                (.cons (pairProof a start) .nil))))))
      simpa [Proof, evalSearch_conclusion, Value.pattern, Judgment.pattern, codePattern, position] using built
    | @EvalWitness.searchSucc _ a current w m tested later => fun start offset position earlier => by
      simp only [Nat.unpair_pair] at position earlier ⊢
      have built := ruleProof searchSucc (by simp [rules])
        [.code f, .nat a, .nat start, .nat offset, .nat (offset + start),
          .nat (Nat.pair a (offset + start)), .nat w] rfl
        (by
          have positive := compileWitness tested
          rw [position] at positive
          simpa [Proof, searchSucc_premises, Value.pattern, Judgment.pattern, num] using
            (OpenDerivationList.cons earlier (.cons (addProof offset start)
              (.cons (pairProof a (offset + start)) (.cons positive .nil)))))
      have nextStage : Proof (.search f a start (offset + 1)) := by
        simpa [Proof, searchSucc_conclusion, Value.pattern, Judgment.pattern, num] using built
      simpa [Nat.unpair_pair] using compileSearchWitness later start (offset + 1)
        (by simp only [Nat.unpair_pair]; omega) (by simpa [Nat.unpair_pair] using nextStage)
  termination_by (sizeOf witness, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (apply Prod.Lex.left; omega)
end


/-- Recording evaluation branches preserves the result of the original bounded interpreter. -/
theorem evaluate_result : ∀ (bound : Nat) (code : Code) (input : Nat),
    (evaluate bound code input).map Sigma.fst = Code.evaln bound code input := by
  intro bound
  induction bound with
  | zero => intro code input; simp [evaluate, Code.evaln]
  | succ k lower =>
    intro code
    induction code with
    | zero => intro n; simp [evaluate, Code.evaln, guard]
    | succ => intro n; simp [evaluate, Code.evaln, guard]
    | left => intro n; simp [evaluate, Code.evaln, guard]
    | right => intro n; simp [evaluate, Code.evaln, guard]
    | pair f g first second =>
      intro n
      by_cases small : n ≤ k
      · cases firstRun : evaluate (k + 1) f n <;>
          cases secondRun : evaluate (k + 1) g n <;>
          simp [evaluate, Code.evaln, guard, small, ← first n, ← second n,
            firstRun, secondRun, Seq.seq]
      · simp [evaluate, Code.evaln, guard, small]
    | comp f g outer inner =>
      intro n
      by_cases small : n ≤ k
      · cases innerRun : evaluate (k + 1) g n with
        | none => simp [evaluate, Code.evaln, guard, small, ← inner n, innerRun]
        | some value =>
          rcases value with ⟨middle, witness⟩
          cases outerRun : evaluate (k + 1) f middle <;>
            simp [evaluate, Code.evaln, guard, small, ← inner n, ← outer middle,
              innerRun, outerRun]
      · simp [evaluate, Code.evaln, guard, small]
    | prec f g base step =>
      intro n
      by_cases small : n ≤ k
      · cases count : n.unpair.2 with
        | zero =>
          cases baseRun : evaluate (k + 1) f n.unpair.1 <;>
            simp [evaluate, Code.evaln, guard, small, Nat.unpaired, count,
              ← base n.unpair.1, baseRun]
          all_goals split <;> simp_all
        | succ j =>
          cases previousRun : evaluate k (.prec f g) (Nat.pair n.unpair.1 j) with
          | none =>
            simp [evaluate, Code.evaln, guard, small, Nat.unpaired, count,
              ← lower (.prec f g) (Nat.pair n.unpair.1 j), previousRun]
            split <;> simp_all
            all_goals subst_vars
            all_goals simp_all
          | some value =>
            rcases value with ⟨previous, earlier⟩
            cases stepRun : evaluate (k + 1) g (Nat.pair n.unpair.1 (Nat.pair j previous)) <;>
              simp [evaluate, Code.evaln, guard, small, Nat.unpaired, count,
                ← lower (.prec f g) (Nat.pair n.unpair.1 j), previousRun,
                ← step (Nat.pair n.unpair.1 (Nat.pair j previous)), stepRun]
            all_goals split <;> simp_all
            all_goals subst_vars
            all_goals simp_all
      · simp [evaluate, Code.evaln, guard, small]
    | rfind' f tested =>
      intro n
      by_cases small : n ≤ k
      · cases testedRun : evaluate (k + 1) f (Nat.pair n.unpair.1 n.unpair.2) with
        | none =>
          have testedValue := (tested (Nat.pair n.unpair.1 n.unpair.2)).symm
          rw [testedRun] at testedValue
          simp only [Option.map_none, Nat.pair_unpair] at testedValue
          simp [evaluate, Code.evaln, guard, small, Nat.unpaired, testedRun, testedValue]
        | some value =>
          rcases value with ⟨value, witness⟩
          have testedValue := (tested (Nat.pair n.unpair.1 n.unpair.2)).symm
          rw [testedRun] at testedValue
          simp only [Option.map_some, Nat.pair_unpair] at testedValue
          cases value with
          | zero =>
            simp [evaluate, Code.evaln, guard, small, Nat.unpaired, testedRun, testedValue]
          | succ w =>
            cases laterRun : evaluate k (.rfind' f) (Nat.pair n.unpair.1 (n.unpair.2 + 1)) <;>
              simp [evaluate, Code.evaln, guard, small, Nat.unpaired, testedRun, testedValue,
                ← lower (.rfind' f) (Nat.pair n.unpair.1 (n.unpair.2 + 1)), laterRun]
      · simp [evaluate, Code.evaln, guard, small]


/-- Refuse insufficient bounds and wrong claimed outputs before source compilation. -/
def extractProof (bound : Nat) (code : Code) (input output : Nat) :
    Option (Proof (.eval code input output)) := do
  let ⟨actual, witness⟩ ← evaluate bound code input
  if same : actual = output then
    some (same ▸ compileWitness witness)
  else none

/-- A computed receipt agrees with the exact output of the original bounded evaluator. -/
theorem extractProof_matches (bound : Nat) (code : Code) (input output : Nat)
    {proof : Proof (.eval code input output)}
    (extracted : extractProof bound code input output = some proof) :
    Code.evaln bound code input = some output := by
  have projected := evaluate_result bound code input
  cases computed : evaluate bound code input with
  | none => simp [extractProof, computed] at extracted
  | some value =>
    rcases value with ⟨actual, witness⟩
    by_cases same : actual = output
    · rw [computed] at projected
      simpa [same] using projected.symm
    · simp [extractProof, computed, same] at extracted

/-- Every accepted original finite evidence computes a source derivation without proof search. -/
theorem extractProof_complete (bound : Nat) (code : Code) (input output : Nat)
    (accepted : Mettapedia.Computability.UniversalEffectiveEvidence.check
      code input output bound = true) :
    ∃ proof, extractProof bound code input output = some proof := by
  have value : Code.evaln bound code input = some output := of_decide_eq_true accepted
  have projected := evaluate_result bound code input
  rw [value] at projected
  cases computed : evaluate bound code input with
  | none => simp [computed] at projected
  | some result =>
    rcases result with ⟨actual, witness⟩
    simp only [computed, Option.map_some, Option.some.injEq] at projected
    subst actual
    exact ⟨compileWitness witness, by simp [extractProof, computed]⟩

/-- The original closed tree checker receives the actual computed source proof. -/
def extractRaw (bound : Nat) (code : Code) (input output : Nat) : Option RawProof :=
  (extractProof bound code input output).map fun proof => proof.close.erase

theorem extractRaw_checked (bound : Nat) (code : Code) (input output : Nat)
    {raw : RawProof} (extracted : extractRaw bound code input output = some raw) :
    checkRaw validatedCalculus (Judgment.eval code input output).pattern raw = true := by
  obtain ⟨proof, _, rfl⟩ := Option.map_eq_some_iff.mp extracted
  exact checkRaw_erase proof.close

/-- The same original applications in the chronological compiler's empty lemma context. -/
def sourceCertificate (bound : Nat) (code : Code) (input output : Nat) :
    Option LemmaCertificate :=
  (extractProof bound code input output).map fun proof => ([], proof.eraseOpen)

theorem sourceCertificate_checked (bound : Nat) (code : Code) (input output : Nat)
    {source : LemmaCertificate}
    (extracted : sourceCertificate bound code input output = some source) :
    InferenceCompiler.sharedSourceCheck validatedCalculus
      (Judgment.eval code input output).pattern source = true := by
  obtain ⟨proof, _, rfl⟩ := Option.map_eq_some_iff.mp extracted
  simp only [InferenceCompiler.sharedSourceCheck, checkLemmas, Bool.true_and, List.map_nil]
  exact checkOpenRaw_erase proof

/-- Produce the actual graph through the existing concrete HOL compiler. -/
def compile (bound : Nat) (code : Code) (input output : Nat) :
    Option ProofSystem.Certificate :=
  (sourceCertificate bound code input output).bind fun source =>
    InferenceCompiler.compileShared validatedCalculus (Judgment.eval code input output).pattern source

theorem compile_complete (bound : Nat) (code : Code) (input output : Nat)
    (accepted : Mettapedia.Computability.UniversalEffectiveEvidence.check
      code input output bound = true) :
    ∃ certificate, compile bound code input output = some certificate := by
  obtain ⟨proof, extracted⟩ := extractProof_complete bound code input output accepted
  have source : sourceCertificate bound code input output = some ([], proof.eraseOpen) := by
    simp [sourceCertificate, extracted]
  obtain ⟨certificate, compiled⟩ := InferenceCompiler.compileShared_preserves
    validatedCalculus calculus_firstOrder (Judgment.eval code input output).pattern
      ([], proof.eraseOpen) (sourceCertificate_checked bound code input output source)
  exact ⟨certificate, by simp [compile, source, compiled]⟩

/-- The independent original HOL graph checker verifies the computed output and exact claim. -/
theorem compile_checked (bound : Nat) (code : Code) (input output : Nat)
    {certificate : ProofSystem.Certificate}
    (compiled : compile bound code input output = some certificate) :
    (InferenceCompiler.compiledChecker calculus).check
      (Judgment.eval code input output).pattern certificate = true := by
  obtain ⟨source, _, emitted⟩ := Option.bind_eq_some_iff.mp compiled
  exact InferenceCompiler.compileShared_claim_checked validatedCalculus _
    source (judgment_valid (.eval code input output)) emitted

/-- Source extraction refuses exactly when that finite evidence is absent. -/
theorem extractProof_isSome_iff (bound : Nat) (code : Code) (input output : Nat) :
    (extractProof bound code input output).isSome = true ↔
      Mettapedia.Computability.UniversalEffectiveEvidence.check code input output bound = true := by
  constructor
  · intro extracted
    obtain ⟨proof, returned⟩ := Option.isSome_iff_exists.mp extracted
    exact decide_eq_true (extractProof_matches bound code input output returned)
  · intro accepted
    obtain ⟨proof, returned⟩ := extractProof_complete bound code input output accepted
    simp [returned]

/-- Absent bounded evidence returns no source certificate and emits no target graph. -/
theorem compile_refused (bound : Nat) (code : Code) (input output : Nat)
    (refused : Mettapedia.Computability.UniversalEffectiveEvidence.check
      code input output bound = false) : compile bound code input output = none := by
  have missing : extractProof bound code input output = none := by
    cases computed : extractProof bound code input output with
    | none => rfl
    | some proof =>
      have accepted := (extractProof_isSome_iff bound code input output).mp (by simp [computed])
      rw [refused] at accepted
      cases accepted
  simp [compile, sourceCertificate, missing]

/-- Successful actual emission retains the original supplied-bound evidence. -/
theorem compile_sound (bound : Nat) (code : Code) (input output : Nat)
    {certificate : ProofSystem.Certificate}
    (compiled : compile bound code input output = some certificate) :
    Mettapedia.Computability.UniversalEffectiveEvidence.check code input output bound = true := by
  obtain ⟨source, extracted, _⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨proof, returned, _⟩ := Option.map_eq_some_iff.mp extracted
  exact decide_eq_true (extractProof_matches bound code input output returned)

theorem compile_iff_evidence (bound : Nat) (code : Code) (input output : Nat) :
    (∃ certificate, compile bound code input output = some certificate) ↔
      Mettapedia.Computability.UniversalEffectiveEvidence.check code input output bound = true :=
  ⟨fun ⟨_, emitted⟩ => compile_sound bound code input output emitted,
    compile_complete bound code input output⟩

/-- Independent original graph authority verifies the complete computed target theorem. -/
theorem compile_kernel_checked (bound : Nat) (code : Code) (input output : Nat)
    {certificate : ProofSystem.Certificate}
    (compiled : compile bound code input output = some certificate) :
    ∃ out, (ProofSystem.checker (InferenceHosting.policy universalRules)).check out certificate = true ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl =
        InferenceCompiler.compileClaim (Judgment.eval code input output).pattern := by
  obtain ⟨source, _, emitted⟩ := Option.bind_eq_some_iff.mp compiled
  have checked := InferenceCompiler.compileShared_checked validatedCalculus _ source emitted
  change ∃ out, (ProofSystem.checker (InferenceHosting.policy (inferenceRules calculus))).check
    out certificate = true ∧ out.sequent.hyp = ∅ ∧ out.sequent.concl =
      InferenceCompiler.compileClaim (Judgment.eval code input output).pattern at checked
  rw [inferenceRules_universal] at checked
  exact checked

/-- The emitted-node account charges this extractor's complete actual source payload. -/
theorem compiled_nodes_bound (bound : Nat) (code : Code) (input output : Nat)
    {certificate : ProofSystem.Certificate}
    (compiled : compile bound code input output = some certificate) :
    ∃ source, sourceCertificate bound code input output = some source ∧
      certificate.1.length ≤ calculus.rules.length +
        8 * InferenceCompiler.localNodeFactor calculus *
          Mettapedia.GSLT.LanguageDef.ProofSystems.encodedSize
            Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.inputEncoding
              ((Judgment.eval code input output).pattern, source) := by
  obtain ⟨source, extracted, emitted⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨source, extracted,
    InferenceCompiler.compileShared_encoded_node_bound validatedCalculus _ source emitted⟩

/-- Count the actual recorded evaluation occurrences, including arithmetic-producing branches. -/
def EvalWitness.nodes {code : Code} {input output : Nat} (witness : EvalWitness code input output) : Nat :=
  match witness with
  | .zero _ | .succ _ | .left _ | .right _ => 1
  | .pair first second | .comp first second | .precSucc first second |
      .searchSucc first second => 1 + first.nodes + second.nodes
  | .precZero child | .searchZero child => 1 + child.nodes

/-- Sizes of actual evidence and source artifacts; these are not a machine-time budget. -/
structure PayloadAccount where
  boundSymbols : Nat
  evidenceNodes : Nat
  sourceNodes : Nat
  sourceSymbols : Nat
  deriving Repr

/-- Charge the encoded bound separately from the constructed proof tree and its full encoding. -/
def payloadAccount (bound : Nat) (code : Code) (input output : Nat) : Option PayloadAccount := do
  let ⟨actual, witness⟩ ← evaluate bound code input
  if same : actual = output then
    let proof := same ▸ compileWitness witness
    return {
      boundSymbols := (Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith
        Mettapedia.OSLF.Binding.WireCodec.Codec.nat bound).length
      evidenceNodes := witness.nodes
      sourceNodes := proof.eraseOpen.ruleCount
      sourceSymbols := (Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.encodeInput
        (Judgment.eval code input output).pattern ([], proof.eraseOpen)).length }
  else none

end Mettapedia.Languages.HOLLight.EffectiveEvidenceCompilation
