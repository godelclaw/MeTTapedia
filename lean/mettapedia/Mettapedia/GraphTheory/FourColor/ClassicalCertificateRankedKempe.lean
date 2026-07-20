import Mathlib.Data.Fintype.Vector
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateKempeClosure

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateRankedKempe

open ClassicalCertificateKempeClosure
open ClassicalCertificateTraceTree

abbrev TraceWord (length : Nat) := List.Vector TraceSymbol length
abbrev GramWord (length : Nat) := List.Vector ChromogramStep length

/-- The six permutations of the three nonzero colors. -/
inductive PermutationCode where
  | identity
  | swapRedBlue
  | swapRedPurple
  | swapBluePurple
  | cycleRedBluePurple
  | cycleRedPurpleBlue
  deriving DecidableEq, Fintype, Repr

namespace PermutationCode

def apply : PermutationCode → TraceSymbol → TraceSymbol
  | .identity, symbol => symbol
  | .swapRedBlue, .red => .blue
  | .swapRedBlue, .blue => .red
  | .swapRedBlue, .purple => .purple
  | .swapRedPurple, .red => .purple
  | .swapRedPurple, .blue => .blue
  | .swapRedPurple, .purple => .red
  | .swapBluePurple, .red => .red
  | .swapBluePurple, .blue => .purple
  | .swapBluePurple, .purple => .blue
  | .cycleRedBluePurple, .red => .blue
  | .cycleRedBluePurple, .blue => .purple
  | .cycleRedBluePurple, .purple => .red
  | .cycleRedPurpleBlue, .red => .purple
  | .cycleRedPurpleBlue, .blue => .red
  | .cycleRedPurpleBlue, .purple => .blue

def inverse : PermutationCode → PermutationCode
  | .identity => .identity
  | .swapRedBlue => .swapRedBlue
  | .swapRedPurple => .swapRedPurple
  | .swapBluePurple => .swapBluePurple
  | .cycleRedBluePurple => .cycleRedPurpleBlue
  | .cycleRedPurpleBlue => .cycleRedBluePurple

def toEquiv (code : PermutationCode) : SymbolPermutation where
  toFun := code.apply
  invFun := code.inverse.apply
  left_inv := by
    intro symbol
    cases code <;> cases symbol <;> rfl
  right_inv := by
    intro symbol
    cases code <;> cases symbol <;> rfl

end PermutationCode

def permute {length : Nat} (code : PermutationCode)
    (word : TraceWord length) : TraceWord length :=
  word.map code.apply

@[simp] theorem toList_permute {length : Nat} (code : PermutationCode)
    (word : TraceWord length) :
    (permute code word).toList =
      permuteWord code.toEquiv word.toList := by
  simp [permute, permuteWord, PermutationCode.toEquiv]

/-- The small executable list of matching chromograms for a fixed word. -/
def matchingGramWords {length : Nat} (word : TraceWord length) :
    List (GramWord length) :=
  (matchingChromograms word.toList).attach.map fun gram =>
    ⟨gram.val,
      ((mem_matchingChromograms_iff word.toList gram.val).1
        gram.property).length_eq.symm.trans word.2⟩

theorem mem_matchingGramWords {length : Nat} (word : TraceWord length)
    (gram : GramWord length) (hmatch : Matches word.toList gram.toList) :
    gram ∈ matchingGramWords word := by
  apply List.mem_map.2
  refine ⟨⟨gram.toList,
    (mem_matchingChromograms_iff word.toList gram.toList).2 hmatch⟩, ?_, ?_⟩
  · simp
  · apply Subtype.ext
    rfl

/-- Finite rule data attached to one fixed-length trace word. -/
inductive RuleCode (length : Nat) where
  | member
  | permutation (permutation : PermutationCode)
  | chromograms (response : GramWord length → TraceWord length)

/-- A ranked finite Kempe certificate.  Only `covered` words require rules;
all recursive successors must remain covered and have lower rank. -/
structure Certificate (length : Nat) where
  covered : Finset (TraceWord length)
  extendable : Finset (TraceWord length)
  rank : TraceWord length → Nat
  rule : TraceWord length → RuleCode length

namespace Certificate

variable {length : Nat}

def RuleValid (certificate : Certificate length)
    (word : TraceWord length) : Prop :=
  match certificate.rule word with
  | .member => word ∈ certificate.extendable
  | .permutation permutation =>
      let nextWord := permute permutation word
      nextWord ∈ certificate.covered ∧
        certificate.rank nextWord < certificate.rank word
  | .chromograms response =>
      ∀ gram, Matches word.toList gram.toList →
        let nextWord := response gram
        Matches nextWord.toList gram.toList ∧
          nextWord ∈ certificate.covered ∧
          certificate.rank nextWord < certificate.rank word

instance (certificate : Certificate length) (word : TraceWord length) :
    Decidable (certificate.RuleValid word) := by
  unfold RuleValid
  split
  · infer_instance
  · infer_instance
  · infer_instance

def Valid (certificate : Certificate length) : Prop :=
  ∀ word ∈ certificate.covered, certificate.RuleValid word

instance (certificate : Certificate length) : Decidable certificate.Valid := by
  unfold Valid
  infer_instance

def checker (certificate : Certificate length) : Bool :=
  decide certificate.Valid

/-- Optimized local rule semantics: quantify only over chromograms that the
proved-complete stack enumerator says can match the current word. -/
def FastRuleValid (certificate : Certificate length)
    (word : TraceWord length) : Prop :=
  match certificate.rule word with
  | .member => word ∈ certificate.extendable
  | .permutation permutation =>
      let nextWord := permute permutation word
      nextWord ∈ certificate.covered ∧
        certificate.rank nextWord < certificate.rank word
  | .chromograms response =>
      ∀ gram ∈ matchingGramWords word,
        let nextWord := response gram
        Matches nextWord.toList gram.toList ∧
          nextWord ∈ certificate.covered ∧
          certificate.rank nextWord < certificate.rank word

instance (certificate : Certificate length) (word : TraceWord length) :
    Decidable (certificate.FastRuleValid word) := by
  unfold FastRuleValid
  split <;> infer_instance

def FastValid (certificate : Certificate length) : Prop :=
  ∀ word ∈ certificate.covered, certificate.FastRuleValid word

instance (certificate : Certificate length) :
    Decidable certificate.FastValid := by
  unfold FastValid
  infer_instance

def fastChecker (certificate : Certificate length) : Bool :=
  decide certificate.FastValid

/-- Proof-erased local Boolean checker for one ranked rule. -/
def fastRuleBoolean (certificate : Certificate length)
    (word : TraceWord length) : Bool :=
  match certificate.rule word with
  | .member => decide (word ∈ certificate.extendable)
  | .permutation permutation =>
      let nextWord := permute permutation word
      decide (nextWord ∈ certificate.covered) &&
        decide (certificate.rank nextWord < certificate.rank word)
  | .chromograms response =>
      (matchingGramWords word).all fun gram =>
        let nextWord := response gram
        decide (Matches nextWord.toList gram.toList) &&
          decide (nextWord ∈ certificate.covered) &&
          decide (certificate.rank nextWord < certificate.rank word)

theorem fastRuleValid_of_fastRuleBoolean_eq_true
    (certificate : Certificate length) (word : TraceWord length)
    (haccepted : certificate.fastRuleBoolean word = true) :
    certificate.FastRuleValid word := by
  cases hrule : certificate.rule word with
  | member =>
      simp only [fastRuleBoolean, hrule] at haccepted
      simpa [FastRuleValid, hrule] using Bool.of_decide_true haccepted
  | permutation permutation =>
      simp only [fastRuleBoolean, hrule, Bool.and_eq_true] at haccepted
      simp only [FastRuleValid, hrule]
      exact ⟨Bool.of_decide_true haccepted.1,
        Bool.of_decide_true haccepted.2⟩
  | chromograms response =>
      simp only [fastRuleBoolean, hrule] at haccepted
      simp only [FastRuleValid, hrule]
      intro gram hgram
      have hlocal := (List.all_eq_true.mp haccepted) gram hgram
      simp only [Bool.and_eq_true] at hlocal
      exact ⟨Bool.of_decide_true hlocal.1.1,
        Bool.of_decide_true hlocal.1.2,
        Bool.of_decide_true hlocal.2⟩

theorem ruleValid_of_fastRuleValid (certificate : Certificate length)
    (word : TraceWord length)
    (hfast : certificate.FastRuleValid word) :
    certificate.RuleValid word := by
  cases hrule : certificate.rule word with
  | member =>
      simpa [FastRuleValid, RuleValid, hrule] using hfast
  | permutation permutation =>
      simpa [FastRuleValid, RuleValid, hrule] using hfast
  | chromograms response =>
      simp only [FastRuleValid, hrule] at hfast
      simp only [RuleValid, hrule]
      intro gram hmatch
      exact hfast gram (mem_matchingGramWords word gram hmatch)

theorem valid_of_fastValid (certificate : Certificate length)
    (hfast : certificate.FastValid) : certificate.Valid := by
  intro word hword
  exact certificate.ruleValid_of_fastRuleValid word (hfast word hword)

theorem valid_of_fastChecker_true (certificate : Certificate length)
    (haccepted : certificate.fastChecker = true) : certificate.Valid := by
  apply certificate.valid_of_fastValid
  exact Bool.of_decide_true (by simpa [fastChecker] using haccepted)

theorem valid_of_checker_true (certificate : Certificate length)
    (haccepted : certificate.checker = true) :
    certificate.Valid := by
  exact Bool.of_decide_true (by simpa [checker] using haccepted)

def CoveredFamily (certificate : Certificate length)
    (word : List TraceSymbol) : Prop :=
  ∃ fixedWord ∈ certificate.covered, fixedWord.toList = word

def ExtendableFamily (certificate : Certificate length)
    (word : List TraceSymbol) : Prop :=
  ∃ fixedWord ∈ certificate.extendable, fixedWord.toList = word

private def gramWordOfMatch (word : TraceWord length) (gram : Chromogram)
    (hmatch : Matches word.toList gram) : GramWord length :=
  ⟨gram, by simpa using hmatch.length_eq.symm⟩

/-- Soundness of the executable fixed-length ranked certificate. -/
theorem derivation_of_valid (certificate : Certificate length)
    (hvalid : certificate.Valid) (word : TraceWord length)
    (hcovered : word ∈ certificate.covered) :
    CoclosureDerivation certificate.ExtendableFamily word.toList := by
  have hrule := hvalid word hcovered
  cases hruleCode : certificate.rule word with
  | member =>
      simp only [RuleValid, hruleCode] at hrule
      exact .member ⟨word, hrule, rfl⟩
  | permutation permutation =>
      simp only [RuleValid, hruleCode] at hrule
      exact .permutation permutation.toEquiv (by
        simpa using derivation_of_valid certificate hvalid
          (permute permutation word) hrule.1)
  | chromograms response =>
      simp only [RuleValid, hruleCode] at hrule
      refine .chromograms
        (fun gram hmatch =>
          (response (gramWordOfMatch word gram hmatch)).toList) ?_ ?_
      · intro gram hmatch
        exact (hrule (gramWordOfMatch word gram hmatch) (by
          simpa [gramWordOfMatch] using hmatch)).1
      · intro gram hmatch
        have hresponse := hrule (gramWordOfMatch word gram hmatch) (by
          simpa [gramWordOfMatch] using hmatch)
        exact derivation_of_valid certificate hvalid
          (response (gramWordOfMatch word gram hmatch)) hresponse.2.1
termination_by certificate.rank word
decreasing_by
  all_goals simp_all [RuleValid]

theorem kempeCoclosure_of_checker_true
    (certificate : Certificate length)
    (haccepted : certificate.checker = true)
    (word : TraceWord length) (hcovered : word ∈ certificate.covered) :
    KempeCoclosure certificate.ExtendableFamily word.toList :=
  (certificate.derivation_of_valid
    (certificate.valid_of_checker_true haccepted) word hcovered).sound

theorem kempeCoclosure_of_fastChecker_true
    (certificate : Certificate length)
    (haccepted : certificate.fastChecker = true)
    (word : TraceWord length) (hcovered : word ∈ certificate.covered) :
    KempeCoclosure certificate.ExtendableFamily word.toList :=
  (certificate.derivation_of_valid
    (certificate.valid_of_fastChecker_true haccepted) word hcovered).sound

end Certificate

namespace Examples

def redWord : TraceWord 1 := ⟨[.red], rfl⟩
def blueWord : TraceWord 1 := ⟨[.blue], rfl⟩

/-- A one-step executable certificate: swap red and blue, then use the
extendable blue trace. -/
def oneStepPermutationCertificate : Certificate 1 where
  covered := {redWord, blueWord}
  extendable := {blueWord}
  rank := fun word => if word = redWord then 1 else 0
  rule := fun word =>
    if word = redWord then .permutation .swapRedBlue else .member

theorem oneStepPermutationCertificate_checker :
    oneStepPermutationCertificate.checker = true := by
  decide

theorem redWord_kempeCoclosure :
    KempeCoclosure oneStepPermutationCertificate.ExtendableFamily
      redWord.toList := by
  exact oneStepPermutationCertificate.kempeCoclosure_of_checker_true
    oneStepPermutationCertificate_checker redWord
      (by simp [oneStepPermutationCertificate])

end Examples

end ClassicalCertificateRankedKempe

end Mettapedia.GraphTheory.FourColor
