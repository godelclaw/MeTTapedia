import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceWitness

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateEvenTraceKempe

open ClassicalCertificateColorTrace
open ClassicalCertificateConfiguration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness

/-- A fixed-length trace word satisfies the universal cyclic sum equation. -/
def IsEvenTraceWord {length : Nat} (word : TraceWord length) : Prop :=
  (word.toList.map TraceSymbol.toColor).sum = 0

instance {length : Nat} (word : TraceWord length) :
    Decidable (IsEvenTraceWord word) := by
  unfold IsEvenTraceWord
  infer_instance

/-- All nonzero trace words of a fixed length satisfying the cyclic sum
equation. -/
def evenTraceWords (length : Nat) : Finset (TraceWord length) :=
  Finset.univ.filter IsEvenTraceWord

@[simp] theorem mem_evenTraceWords {length : Nat} (word : TraceWord length) :
    word ∈ evenTraceWords length ↔ IsEvenTraceWord word := by
  simp [evenTraceWords]

def symbolDigit : TraceSymbol → Nat
  | .red => 0
  | .blue => 1
  | .purple => 2

/-- Base-three index of a trace word. -/
def wordIndex {length : Nat} (word : TraceWord length) : Nat :=
  word.toList.foldl (fun index symbol => index * 3 + symbolDigit symbol) 0

/-- Discovery ranks for all `3^6` words.  Entries outside the even-trace
universe are ignored by the certificate checker. -/
def firstCatalogueRankTable : Array Nat :=
  #[3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 3, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0,
    0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0,
    4, 0, 0, 0, 3,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0,
    8, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0,
    0, 5, 0, 0,
    0, 0, 0, 0, 0, 10, 0, 9, 0, 0, 0, 8, 0, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 8, 0, 3, 0, 0, 0, 7,
    0, 0, 0, 1,
    0, 0, 0, 0, 0, 9, 0, 10, 0, 0, 0, 7, 0, 0, 0, 1, 0, 0, 0, 8, 0, 6, 0,
    0, 0, 0, 0,
    1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 7, 0, 5, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0,
    0, 1, 0, 0,
    0, 1, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    6, 0, 5, 0,
    1, 0, 0, 0, 3, 0, 0, 0, 7, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0,
    0, 1, 0, 0,
    0, 0, 0, 0, 0, 8, 0, 7, 0, 0, 0, 10, 0, 0, 0, 8, 0, 0, 0, 1, 0, 7, 0,
    0, 0, 0, 0,
    3, 0, 0, 0, 1, 0, 0, 0, 5, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 1, 0, 0,
    0, 3, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    1, 0, 2, 0,
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 5, 0, 0, 0, 1,
    0, 0, 0, 2,
    0, 0, 0, 0, 0, 6, 0, 1, 0, 0, 0, 8, 0, 0, 0, 10, 0, 0, 0, 7, 0, 9, 0,
    0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 6, 0, 0, 0, 2,
    0, 0, 0, 1,
    0, 4, 0, 7, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    2, 0, 1, 0,
    0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 5, 0, 6, 0, 1, 0, 0, 0, 1,
    0, 0, 0, 1,
    0, 0, 0, 0, 0, 7, 0, 8, 0, 0, 0, 1, 0, 0, 0, 7, 0, 0, 0, 10, 0, 8, 0,
    0, 0, 0, 0,
    1, 0, 0, 0, 7, 0, 0, 0, 3, 0, 9, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 1, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 6, 0, 0, 0, 7, 0, 0, 0, 9, 0, 0, 0, 8, 0, 10, 0,
    0, 0, 0, 0,
    0, 0, 4, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 1,
    0, 0, 0, 1,
    0, 1, 0, 8, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0,
    1, 0, 1, 0,
    3, 0, 0, 0, 5, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 1, 0, 0,
    0, 1, 0, 1, 0, 0, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    1, 0, 1, 0,
    0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 1,
    0, 0, 0, 2]

def firstCatalogueRank (word : TraceWord 6) : Nat :=
  firstCatalogueRankTable[wordIndex word]?.getD 0

def defaultEvenWord : TraceWord 6 :=
  ⟨[.red, .red, .red, .red, .red, .red], rfl⟩

def permutationCodes : List PermutationCode :=
  [.identity, .swapRedBlue, .swapRedPurple, .swapBluePurple,
    .cycleRedBluePurple, .cycleRedPurpleBlue]

def prependSymbol {length : Nat} (symbol : TraceSymbol)
    (word : TraceWord length) : TraceWord (length + 1) :=
  ⟨symbol :: word.toList, by simp⟩

/-- Executable lexicographic enumeration of all ternary words. -/
def allTraceWords : (length : Nat) → List (TraceWord length)
  | 0 => [⟨[], rfl⟩]
  | length + 1 =>
      (allTraceWords length).flatMap fun word =>
        [prependSymbol .red word, prependSymbol .blue word,
          prependSymbol .purple word]

theorem mem_allTraceWords {length : Nat} (word : TraceWord length) :
    word ∈ allTraceWords length := by
  rcases word with ⟨symbols, hlength⟩
  induction length generalizing symbols with
  | zero =>
      cases symbols with
      | nil => simp [allTraceWords]
      | cons symbol symbols => simp at hlength
  | succ length ih =>
      cases symbols with
      | nil => simp at hlength
      | cons symbol symbols =>
          have htail : symbols.length = length := by
            exact Nat.succ.inj hlength
          have hmem := ih symbols htail
          simp only [allTraceWords, List.mem_flatMap]
          refine ⟨⟨symbols, htail⟩, hmem, ?_⟩
          cases symbol <;> simp [prependSymbol]

def firstLowerPermutation (word : TraceWord 6) : Option PermutationCode :=
  (permutationCodes.find? fun permutation =>
    decide (firstCatalogueRank (permute permutation word) <
      firstCatalogueRank word))

def gramStepDigit : ChromogramStep → Nat
  | .push => 0
  | .skip => 1
  | .popSame => 2
  | .popOpposite => 3

def gramIndex (gram : GramWord 6) : Nat :=
  gram.toList.foldl (fun index step => index * 4 + gramStepDigit step) 0

def symbolOfDigit (digit : Nat) : TraceSymbol :=
  match digit % 3 with
  | 0 => .red
  | 1 => .blue
  | _ => .purple

def wordOfIndex (index : Nat) : TraceWord 6 :=
  ⟨[symbolOfDigit (index / 243), symbolOfDigit (index / 81),
    symbolOfDigit (index / 27), symbolOfDigit (index / 9),
    symbolOfDigit (index / 3), symbolOfDigit index], rfl⟩

abbrev ResponseEntry := Nat × Nat × Nat

/-- Sparse responses for the 110 matching `(word, chromogram)` pairs whose
ranked rule is not already discharged by a global permutation. -/
def firstCatalogueResponseEntries : List ResponseEntry :=
  [(44, 1295, 50), (44, 1314, 40), (76, 1295, 50), (76, 1314, 40),
    (104, 1103, 98), (104, 1139, 106), (140, 1055, 116), (140, 1235, 142),
    (146, 1079, 128), (146, 1223, 154), (150, 1085, 132),
    (150, 1229, 156), (178, 1103, 98), (178, 1139, 106),
    (196, 1055, 116), (196, 1235, 142), (208, 1079, 128),
    (208, 1223, 154), (210, 1085, 132), (210, 1229, 156),
    (266, 335, 260), (266, 371, 268), (302, 287, 278), (302, 467, 304),
    (308, 311, 290), (308, 455, 316), (312, 317, 294), (312, 461, 318),
    (364, 42, 400), (364, 138, 472), (364, 162, 368), (364, 522, 392),
    (364, 546, 368), (376, 62, 394), (376, 138, 472), (376, 179, 374),
    (376, 522, 392), (376, 563, 374), (404, 47, 368), (404, 203, 392),
    (404, 242, 400), (404, 522, 392), (404, 546, 368), (410, 95, 332),
    (410, 851, 412), (416, 119, 344), (416, 839, 424), (420, 125, 348),
    (420, 845, 426), (438, 221, 384), (438, 797, 462), (450, 245, 396),
    (450, 821, 468), (454, 62, 394), (454, 206, 394), (454, 242, 400),
    (454, 782, 448), (454, 818, 458), (460, 150, 352), (460, 791, 434),
    (482, 47, 368), (482, 143, 368), (482, 179, 374), (482, 782, 448),
    (482, 803, 446), (502, 335, 260), (502, 371, 268), (520, 287, 278),
    (520, 467, 304), (532, 311, 290), (532, 455, 316), (534, 317, 294),
    (534, 461, 318), (574, 95, 332), (574, 851, 412), (586, 119, 344),
    (586, 839, 424), (588, 125, 348), (588, 845, 426), (596, 150, 352),
    (596, 791, 434), (610, 47, 368), (610, 143, 368), (610, 179, 374),
    (610, 782, 448), (610, 803, 446), (624, 221, 384), (624, 797, 462),
    (630, 245, 396), (630, 821, 468), (638, 62, 394), (638, 206, 394),
    (638, 242, 400), (638, 782, 448), (638, 818, 458), (688, 47, 368),
    (688, 203, 392), (688, 242, 400), (688, 522, 392), (688, 546, 368),
    (716, 62, 394), (716, 138, 472), (716, 179, 374), (716, 522, 392),
    (716, 563, 374), (728, 42, 400), (728, 138, 472), (728, 162, 368),
    (728, 522, 392), (728, 546, 368)]

def responseTarget (source gram : Nat) : Nat :=
  match firstCatalogueResponseEntries.find? fun entry =>
      entry.1 == source && entry.2.1 == gram with
  | some entry => entry.2.2
  | none => 0

def firstLowerResponse (word : TraceWord 6) (gram : GramWord 6) :
    TraceWord 6 :=
  wordOfIndex (responseTarget (wordIndex word) (gramIndex gram))

def firstCatalogueRule (word : TraceWord 6) : RuleCode 6 :=
  if word ∈ firstCatalogueWitnessCertificate.words then .member
  else
    match firstLowerPermutation word with
    | some permutation => .permutation permutation
    | none => .chromograms (firstLowerResponse word)

/-- A compact ranked certificate for every even six-symbol trace. -/
def firstCatalogueKempeCertificate :
    ClassicalCertificateRankedKempe.Certificate 6 where
  covered := evenTraceWords 6
  extendable := firstCatalogueWitnessCertificate.words
  rank := firstCatalogueRank
  rule := firstCatalogueRule

set_option maxRecDepth 10000 in
theorem evenTraceWords_six_card : (evenTraceWords 6).card = 183 := by
  decide

/-- Proof-erased validation of one word in the ranked universe. -/
def firstCatalogueRuleCheck (word : TraceWord 6) : Bool :=
  if word ∈ firstCatalogueKempeCertificate.covered then
    firstCatalogueKempeCertificate.fastRuleBoolean word
  else true

/-- Nine bounded blocks cover the `3^6 = 729` ternary words. -/
def firstCatalogueWordChunk (index : Nat) : List (TraceWord 6) :=
  (allTraceWords 6).drop (index * 81) |>.take 81

def firstCatalogueChunkedWords : List (TraceWord 6) :=
  firstCatalogueWordChunk 0 ++ firstCatalogueWordChunk 1 ++
    firstCatalogueWordChunk 2 ++ firstCatalogueWordChunk 3 ++
    firstCatalogueWordChunk 4 ++ firstCatalogueWordChunk 5 ++
    firstCatalogueWordChunk 6 ++ firstCatalogueWordChunk 7 ++
    firstCatalogueWordChunk 8

set_option maxRecDepth 10000 in
theorem firstCatalogueChunkedWords_eq :
    firstCatalogueChunkedWords = allTraceWords 6 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_zero_checker :
    (firstCatalogueWordChunk 0).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_one_checker :
    (firstCatalogueWordChunk 1).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_two_checker :
    (firstCatalogueWordChunk 2).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_three_checker :
    (firstCatalogueWordChunk 3).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_four_checker :
    (firstCatalogueWordChunk 4).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_five_checker :
    (firstCatalogueWordChunk 5).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_six_checker :
    (firstCatalogueWordChunk 6).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_seven_checker :
    (firstCatalogueWordChunk 7).all firstCatalogueRuleCheck = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstCatalogueWordChunk_eight_checker :
    (firstCatalogueWordChunk 8).all firstCatalogueRuleCheck = true := by
  rfl

/-- Boolean-only validation avoids constructing one enormous dependent
`Decidable` proof while retaining the same local rule propositions. -/
def firstCatalogueKempeRuleChecker : Bool :=
  (allTraceWords 6).all firstCatalogueRuleCheck

theorem firstCatalogueKempeCertificate_checker :
    firstCatalogueKempeRuleChecker = true := by
  unfold firstCatalogueKempeRuleChecker
  rw [← firstCatalogueChunkedWords_eq]
  simp only [firstCatalogueChunkedWords, List.all_append,
    firstCatalogueWordChunk_zero_checker,
    firstCatalogueWordChunk_one_checker,
    firstCatalogueWordChunk_two_checker,
    firstCatalogueWordChunk_three_checker,
    firstCatalogueWordChunk_four_checker,
    firstCatalogueWordChunk_five_checker,
    firstCatalogueWordChunk_six_checker,
    firstCatalogueWordChunk_seven_checker,
    firstCatalogueWordChunk_eight_checker, Bool.and_self]

theorem firstCatalogueKempeCertificate_fastValid :
    firstCatalogueKempeCertificate.FastValid := by
  intro word hcovered
  have hall := (List.all_eq_true.mp firstCatalogueKempeCertificate_checker)
    word (mem_allTraceWords word)
  have hlocal :
      firstCatalogueKempeCertificate.fastRuleBoolean word = true := by
    simpa [firstCatalogueKempeRuleChecker, firstCatalogueRuleCheck,
      hcovered] using hall
  exact firstCatalogueKempeCertificate.fastRuleValid_of_fastRuleBoolean_eq_true
    word hlocal

theorem firstCatalogueKempeCertificate_valid :
    firstCatalogueKempeCertificate.Valid :=
  firstCatalogueKempeCertificate.valid_of_fastValid
    firstCatalogueKempeCertificate_fastValid

theorem firstCatalogue_evenTrace_kempeCoclosure
    (word : TraceWord 6) (heven : IsEvenTraceWord word) :
    KempeCoclosure firstCatalogueKempeCertificate.ExtendableFamily
      word.toList := by
  exact (firstCatalogueKempeCertificate.derivation_of_valid
    firstCatalogueKempeCertificate_valid word
      ((mem_evenTraceWords word).2 heven)).sound

/-- Standard semantic family of boundary traces induced by ordinary
colorings of `cf001`. -/
def FirstCatalogueExtendableTrace (word : List TraceSymbol) : Prop :=
  FiniteHypermap.RingTrace
    (checkedHypermap firstCataloguePartitionValid) firstCatalogueRing
      (word.map TraceSymbol.toColor)

/-- Standard semantic family induced by colorings of the contracted
configuration. -/
def FirstCatalogueContractTrace (word : List TraceSymbol) : Prop :=
  FiniteHypermap.ContractRingTrace
    (checkedHypermap firstCataloguePartitionValid) firstCatalogueContract
      firstCatalogueRing (word.map TraceSymbol.toColor)

theorem firstCatalogue_extendableFamily_sound
    (word : List TraceSymbol)
    (hextendable : firstCatalogueKempeCertificate.ExtendableFamily word) :
    FirstCatalogueExtendableTrace word := by
  rcases hextendable with ⟨fixedWord, hword, rfl⟩
  obtain ⟨assignment, hproper, htrace⟩ :=
    firstCatalogue_witnessWord_is_ringTrace fixedWord hword
  exact (ringTrace_iff_exists_assignment firstCataloguePartitionValid
    firstCatalogueRing _).2 ⟨assignment, hproper, htrace⟩

/-- Every contracted boundary trace lies in the Kempe co-closure of a genuine
ordinary boundary trace. -/
theorem firstCatalogue_contractTrace_kempeCoclosure
    (word : List TraceSymbol) (hcontract : FirstCatalogueContractTrace word) :
    KempeCoclosure FirstCatalogueExtendableTrace word := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment firstCataloguePartitionValid
      firstCatalogueContract firstCatalogueRing _).1 hcontract
  have hlength : word.length = 6 := by
    calc
      word.length = (word.map TraceSymbol.toColor).length := by simp
      _ = (ringTraceOfAssignment firstCataloguePartitionValid
          firstCatalogueRing assignment).length :=
        congrArg List.length htrace
      _ = 6 := by
        simp [ringTraceOfAssignment, FiniteHypermap.ringColorWord,
          length_trace, firstCatalogueRing]
  let fixedWord : TraceWord 6 := ⟨word, hlength⟩
  have heven : IsEvenTraceWord fixedWord := by
    unfold IsEvenTraceWord
    change (word.map TraceSymbol.toColor).sum = 0
    rw [htrace]
    exact sum_trace _
  have hcoclosure := firstCatalogue_evenTrace_kempeCoclosure fixedWord heven
  exact (hcoclosure.mono firstCatalogue_extendableFamily_sound :
    KempeCoclosure FirstCatalogueExtendableTrace fixedWord.toList)

/-- Color-valued form: every genuine contract trace has a unique nonzero
symbol spelling whose Kempe co-closure reaches an ordinary coloring. -/
theorem firstCatalogue_contractRingTrace_reduces
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap firstCataloguePartitionValid) firstCatalogueContract
        firstCatalogueRing boundaryTrace) :
    ∃ symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure FirstCatalogueExtendableTrace symbols := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment firstCataloguePartitionValid
      firstCatalogueContract firstCatalogueRing boundaryTrace).1 hcontract
  obtain ⟨symbols, hsymbols, _⟩ :=
    firstCatalogue_contractAssignment_trace_symbols assignment hassignment
  have hsymbolsBoundary :
      symbols.map TraceSymbol.toColor = boundaryTrace :=
    hsymbols.trans htrace.symm
  refine ⟨symbols, hsymbolsBoundary, ?_⟩
  apply firstCatalogue_contractTrace_kempeCoclosure
  unfold FirstCatalogueContractTrace
  simpa [hsymbolsBoundary] using hcontract

end ClassicalCertificateEvenTraceKempe

end Mettapedia.GraphTheory.FourColor
