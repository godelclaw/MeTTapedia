import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankedKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTreeRankedKempe

open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree

/-- Add a symbol at the front of a fixed-length trace word. -/
def prependSymbol {length : Nat} (symbol : TraceSymbol)
    (word : TraceWord length) : TraceWord (length + 1) :=
  List.Vector.cons symbol word

@[simp] theorem traceWord_eq_iff {length : Nat}
    (left right : TraceWord length) :
    left = right ↔ left.toList = right.toList :=
  List.Vector.toList_injective.eq_iff.symm

@[simp] theorem exists_accepts_toList_eq {length : Nat}
    (tree : TraceTree) (target : TraceWord length) :
    (∃ word : TraceWord length,
      tree.accepts word.toList = true ∧
        word.toList = target.toList) ↔
      tree.accepts target.toList = true := by
  constructor
  · rintro ⟨word, hword, heq⟩
    rw [heq] at hword
    exact hword
  · intro htarget
    exact ⟨target, htarget, rfl⟩

/-- Enumerate exactly the fixed-length words accepted by a ternary trace
tree. Empty branches are skipped, so the enumeration follows the represented
set rather than the ambient `3^length` word space. -/
def acceptedWords : (length : Nat) → TraceTree → List (TraceWord length)
  | 0, .leaf => [⟨[], rfl⟩]
  | 0, _ => []
  | length + 1, .node red blue purple =>
      (acceptedWords length red).map (prependSymbol .red) ++
        (acceptedWords length blue).map (prependSymbol .blue) ++
        (acceptedWords length purple).map (prependSymbol .purple)
  | _ + 1, _ => []

theorem mem_acceptedWords_iff {length : Nat} (tree : TraceTree)
    (word : TraceWord length) :
    word ∈ acceptedWords length tree ↔
      tree.accepts word.toList = true := by
  induction length generalizing tree with
  | zero =>
      have hword : word = List.Vector.nil := Subsingleton.elim _ _
      subst word
      cases tree <;>
        simp [acceptedWords, TraceTree.accepts, traceWord_eq_iff]
  | succ length ih =>
      rw [← List.Vector.cons_head_tail word]
      cases hsymbol : word.head <;> cases tree <;>
        simp [acceptedWords, TraceTree.accepts, TraceTree.child,
          prependSymbol, traceWord_eq_iff, ih]

/-- Insert one word into a ternary trace tree. The intended use keeps all
inserted words at one fixed length. -/
def insertWord : List TraceSymbol → TraceTree → TraceTree
  | [], _ => .leaf
  | .red :: word, .node red blue purple =>
      .node (insertWord word red) blue purple
  | .blue :: word, .node red blue purple =>
      .node red (insertWord word blue) purple
  | .purple :: word, .node red blue purple =>
      .node red blue (insertWord word purple)
  | .red :: word, _ =>
      .node (insertWord word .empty) .empty .empty
  | .blue :: word, _ =>
      .node .empty (insertWord word .empty) .empty
  | .purple :: word, _ =>
      .node .empty .empty (insertWord word .empty)

theorem accepts_insertWord_iff (inserted target : List TraceSymbol)
    (tree : TraceTree) (hlength : target.length = inserted.length) :
    (insertWord inserted tree).accepts target = true ↔
      target = inserted ∨ tree.accepts target = true := by
  induction inserted generalizing target tree with
  | nil =>
      cases target with
      | nil => cases tree <;> simp [insertWord, TraceTree.accepts]
      | cons symbol target => simp at hlength
  | cons symbol inserted ih =>
      cases target with
      | nil => simp at hlength
      | cons targetSymbol target =>
          have htail : target.length = inserted.length :=
            Nat.succ.inj hlength
          cases symbol <;> cases targetSymbol <;> cases tree <;>
            simp [insertWord, TraceTree.accepts, TraceTree.child,
              ih target _ htail]

/-- Build a trace tree from a list of fixed-length words. -/
def fixedWordTree {length : Nat} (words : List (TraceWord length)) :
    TraceTree :=
  words.foldr (fun word tree => insertWord word.toList tree) .empty

@[simp] theorem fixedWordTree_accepts_iff {length : Nat}
    (words : List (TraceWord length)) (word : TraceWord length) :
    (fixedWordTree words).accepts word.toList = true ↔ word ∈ words := by
  induction words with
  | nil => simp [fixedWordTree, TraceTree.accepts]
  | cons head words ih =>
      rw [fixedWordTree, List.foldr_cons,
        accepts_insertWord_iff head.toList word.toList _ (by simp)]
      change (word.toList = head.toList ∨
        (fixedWordTree words).accepts word.toList = true) ↔ _
      rw [ih]
      simp [traceWord_eq_iff]

/-- A ranked Kempe DAG whose finite word sets are stored as ternary tries.
Only words represented by `covered` carry local rules. -/
structure Certificate (length : Nat) where
  covered : TraceTree
  extendable : TraceTree
  rank : TraceWord length → Nat
  rule : TraceWord length → RuleCode length

namespace Certificate

variable {length : Nat}

def RuleValid (certificate : Certificate length)
    (word : TraceWord length) : Prop :=
  match certificate.rule word with
  | .member => certificate.extendable.accepts word.toList = true
  | .permutation permutation =>
      let nextWord := permute permutation word
      certificate.covered.accepts nextWord.toList = true ∧
        certificate.rank nextWord < certificate.rank word
  | .chromograms response =>
      ∀ gram ∈ matchingGramWords word,
        let nextWord := response gram
        Matches nextWord.toList gram.toList ∧
          certificate.covered.accepts nextWord.toList = true ∧
          certificate.rank nextWord < certificate.rank word

instance (certificate : Certificate length) (word : TraceWord length) :
    Decidable (certificate.RuleValid word) := by
  unfold RuleValid
  split <;> infer_instance

def Valid (certificate : Certificate length) : Prop :=
  ∀ word, certificate.covered.accepts word.toList = true →
    certificate.RuleValid word

def ruleBoolean (certificate : Certificate length)
    (word : TraceWord length) : Bool :=
  match certificate.rule word with
  | .member => certificate.extendable.accepts word.toList
  | .permutation permutation =>
      let nextWord := permute permutation word
      certificate.covered.accepts nextWord.toList &&
        decide (certificate.rank nextWord < certificate.rank word)
  | .chromograms response =>
      (matchingGramWords word).all fun gram =>
        let nextWord := response gram
        decide (Matches nextWord.toList gram.toList) &&
          certificate.covered.accepts nextWord.toList &&
          decide (certificate.rank nextWord < certificate.rank word)

theorem ruleValid_of_ruleBoolean_eq_true
    (certificate : Certificate length) (word : TraceWord length)
    (haccepted : certificate.ruleBoolean word = true) :
    certificate.RuleValid word := by
  cases hrule : certificate.rule word with
  | member =>
      simpa [ruleBoolean, RuleValid, hrule] using haccepted
  | permutation permutation =>
      simp only [ruleBoolean, RuleValid, hrule, Bool.and_eq_true] at *
      exact ⟨haccepted.1, Bool.of_decide_true haccepted.2⟩
  | chromograms response =>
      simp only [ruleBoolean, RuleValid, hrule] at *
      intro gram hgram
      have hlocal := (List.all_eq_true.mp haccepted) gram hgram
      simp only [Bool.and_eq_true] at hlocal
      exact ⟨Bool.of_decide_true hlocal.1.1,
        hlocal.1.2, Bool.of_decide_true hlocal.2⟩

theorem ruleBoolean_eq_true_of_ruleValid
    (certificate : Certificate length) (word : TraceWord length)
    (hvalid : certificate.RuleValid word) :
    certificate.ruleBoolean word = true := by
  cases hrule : certificate.rule word with
  | member =>
      simpa [ruleBoolean, RuleValid, hrule] using hvalid
  | permutation permutation =>
      simp only [ruleBoolean, RuleValid, hrule, Bool.and_eq_true] at *
      exact ⟨hvalid.1, decide_eq_true hvalid.2⟩
  | chromograms response =>
      simp only [RuleValid, hrule] at hvalid
      simp only [ruleBoolean, hrule]
      apply List.all_eq_true.2
      intro gram hgram
      have hlocal := hvalid gram hgram
      simp only [Bool.and_eq_true]
      exact ⟨⟨decide_eq_true hlocal.1, hlocal.2.1⟩,
        decide_eq_true hlocal.2.2⟩

/-- The structural checker visits only accepted leaves of the covered trie. -/
def checker (certificate : Certificate length) : Bool :=
  (acceptedWords length certificate.covered).all certificate.ruleBoolean

theorem valid_of_checker_true (certificate : Certificate length)
    (haccepted : certificate.checker = true) : certificate.Valid := by
  intro word hcovered
  apply certificate.ruleValid_of_ruleBoolean_eq_true word
  exact (List.all_eq_true.mp haccepted) word
    ((mem_acceptedWords_iff certificate.covered word).2 hcovered)

theorem checker_eq_true_of_valid (certificate : Certificate length)
    (hvalid : certificate.Valid) : certificate.checker = true := by
  apply List.all_eq_true.2
  intro word hword
  apply certificate.ruleBoolean_eq_true_of_ruleValid word
  exact hvalid word
    ((mem_acceptedWords_iff certificate.covered word).1 hword)

def CoveredFamily (certificate : Certificate length)
    (word : List TraceSymbol) : Prop :=
  ∃ fixedWord : TraceWord length,
    fixedWord.toList = word ∧
      certificate.covered.accepts fixedWord.toList = true

def ExtendableFamily (certificate : Certificate length)
    (word : List TraceSymbol) : Prop :=
  ∃ fixedWord : TraceWord length,
    fixedWord.toList = word ∧
      certificate.extendable.accepts fixedWord.toList = true

private def gramWordOfMatch (word : TraceWord length) (gram : Chromogram)
    (hmatch : Matches word.toList gram) : GramWord length :=
  ⟨gram, by simpa using hmatch.length_eq.symm⟩

/-- Soundness of a tree-indexed ranked Kempe certificate. -/
theorem derivation_of_valid (certificate : Certificate length)
    (hvalid : certificate.Valid) (word : TraceWord length)
    (hcovered : certificate.covered.accepts word.toList = true) :
    CoclosureDerivation certificate.ExtendableFamily word.toList := by
  have hrule := hvalid word hcovered
  cases hruleCode : certificate.rule word with
  | member =>
      simp only [RuleValid, hruleCode] at hrule
      exact .member ⟨word, rfl, hrule⟩
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
        exact (hrule (gramWordOfMatch word gram hmatch)
          (mem_matchingGramWords word _ hmatch)).1
      · intro gram hmatch
        have hresponse := hrule (gramWordOfMatch word gram hmatch)
          (mem_matchingGramWords word _ hmatch)
        exact derivation_of_valid certificate hvalid
          (response (gramWordOfMatch word gram hmatch)) hresponse.2.1
termination_by certificate.rank word
decreasing_by
  all_goals simp_all [RuleValid]

theorem kempeCoclosure_of_checker_true
    (certificate : Certificate length)
    (haccepted : certificate.checker = true)
    (word : TraceWord length)
    (hcovered : certificate.covered.accepts word.toList = true) :
    KempeCoclosure certificate.ExtendableFamily word.toList :=
  (certificate.derivation_of_valid
    (certificate.valid_of_checker_true haccepted) word hcovered).sound

/-- Replace the two finite word sets of a ranked certificate by exact ternary
tries while retaining its ranks and local rules. -/
noncomputable def ofFinite
    (certificate : ClassicalCertificateRankedKempe.Certificate length) :
    Certificate length where
  covered := fixedWordTree certificate.covered.toList
  extendable := fixedWordTree certificate.extendable.toList
  rank := certificate.rank
  rule := certificate.rule

theorem valid_ofFinite
    (certificate : ClassicalCertificateRankedKempe.Certificate length)
    (hvalid : certificate.FastValid) : (ofFinite certificate).Valid := by
  intro word hcovered
  have hcoveredFinite : word ∈ certificate.covered := by
    simpa [ofFinite] using
      ((fixedWordTree_accepts_iff certificate.covered.toList word).1
        hcovered)
  have hlocal := hvalid word hcoveredFinite
  cases hrule : certificate.rule word with
  | member =>
      simp only [ofFinite, RuleValid, hrule]
      apply (fixedWordTree_accepts_iff certificate.extendable.toList word).2
      simpa using (by
        simpa [ClassicalCertificateRankedKempe.Certificate.FastRuleValid,
          hrule] using hlocal)
  | permutation permutation =>
      simp only [ofFinite, RuleValid, hrule]
      have hlocal' := (by
        simpa [ClassicalCertificateRankedKempe.Certificate.FastRuleValid,
          hrule] using hlocal)
      exact ⟨(fixedWordTree_accepts_iff certificate.covered.toList _).2
          (by simpa using hlocal'.1),
        hlocal'.2⟩
  | chromograms response =>
      simp only [ofFinite, RuleValid, hrule]
      intro gram hgram
      simp only [ClassicalCertificateRankedKempe.Certificate.FastRuleValid,
        hrule] at hlocal
      have hlocal' := hlocal gram hgram
      exact ⟨hlocal'.1,
        (fixedWordTree_accepts_iff certificate.covered.toList _).2
          (by simpa using hlocal'.2.1),
        hlocal'.2.2⟩

end Certificate

end ClassicalCertificateTreeRankedKempe

end Mettapedia.GraphTheory.FourColor
