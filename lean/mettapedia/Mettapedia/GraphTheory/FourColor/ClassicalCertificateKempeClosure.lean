import Mettapedia.GraphTheory.FourColor.ClassicalCertificateHypermapColoring

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateKempeClosure

open ClassicalCertificateTraceTree

/-- A noncrossing two-color matching is encoded by stack operations.  The two
pop constructors record which side of the oriented matching is closed. -/
inductive ChromogramStep where
  | push
  | skip
  | popSame
  | popOpposite
  deriving DecidableEq, Repr

instance : Fintype ChromogramStep where
  elems := {.push, .skip, .popSame, .popOpposite}
  complete := by
    intro step
    cases step <;> simp

abbrev Chromogram := List ChromogramStep

/-- One stack transition of the chromogram matcher. -/
def chromogramAdvance (stack : List Bool) (symbol : TraceSymbol)
    (step : ChromogramStep) : Option (List Bool) :=
  match symbol, step, stack with
  | .red, .skip, _ => some stack
  | .blue, .push, _ => some (false :: stack)
  | .blue, .popSame, false :: rest => some rest
  | .blue, .popOpposite, true :: rest => some rest
  | .purple, .push, _ => some (true :: stack)
  | .purple, .popSame, true :: rest => some rest
  | .purple, .popOpposite, false :: rest => some rest
  | _, _, _ => none

/-- Exact matching relation between a normalized trace word and an oriented
noncrossing chromogram. -/
def chromogramMatches : List Bool → List TraceSymbol → Chromogram → Bool
  | [], [], [] => true
  | stack, symbol :: word, step :: gram =>
      match chromogramAdvance stack symbol step with
      | some nextStack => chromogramMatches nextStack word gram
      | none => false
  | _, _, _ => false

def Matches (word : List TraceSymbol) (gram : Chromogram) : Prop :=
  chromogramMatches [] word gram = true

instance (word : List TraceSymbol) (gram : Chromogram) :
    Decidable (Matches word gram) := by
  unfold Matches
  infer_instance

theorem length_eq_of_chromogramMatches
    {stack : List Bool} {word : List TraceSymbol} {gram : Chromogram}
    (hmatch : chromogramMatches stack word gram = true) :
    word.length = gram.length := by
  induction gram generalizing stack word with
  | nil =>
      cases word <;> simp_all [chromogramMatches]
  | cons step gram ih =>
      cases word with
      | nil => simp [chromogramMatches] at hmatch
      | cons symbol word =>
          cases hadvance : chromogramAdvance stack symbol step with
          | none => simp [chromogramMatches, hadvance] at hmatch
          | some nextStack =>
              have htail : word.length = gram.length :=
                ih (by simpa [chromogramMatches, hadvance] using hmatch)
              simp [htail]

theorem Matches.length_eq {word : List TraceSymbol} {gram : Chromogram}
    (hmatch : Matches word gram) :
    word.length = gram.length :=
  length_eq_of_chromogramMatches hmatch

abbrev SymbolPermutation := Equiv.Perm TraceSymbol

def permuteWord (permutation : SymbolPermutation)
    (word : List TraceSymbol) : List TraceSymbol :=
  word.map permutation

/-- A trace family is Kempe-closed when it is closed under global color
permutations and under every noncrossing two-color reconnection represented by
a matching chromogram. -/
def KempeClosed (family : List TraceSymbol → Prop) : Prop :=
  ∀ word, family word →
    (∀ permutation, family (permuteWord permutation word)) ∧
    ∃ gram, Matches word gram ∧
      ∀ otherWord, Matches otherWord gram → family otherWord

/-- A word is in the Kempe co-closure of `family` when every Kempe-closed set
containing the word intersects `family`. -/
def KempeCoclosure (family : List TraceSymbol → Prop)
    (word : List TraceSymbol) : Prop :=
  ∀ closedFamily, KempeClosed closedFamily → closedFamily word →
    ∃ otherWord, family otherWord ∧ closedFamily otherWord

theorem kempeCoclosure_of_mem
    {family : List TraceSymbol → Prop} {word : List TraceSymbol}
    (hmem : family word) :
    KempeCoclosure family word := by
  intro closedFamily _ hclosed
  exact ⟨word, hmem, hclosed⟩

theorem KempeCoclosure.mono
    {smaller larger : List TraceSymbol → Prop}
    (hsubset : ∀ word, smaller word → larger word)
    {word : List TraceSymbol}
    (hcoclosure : KempeCoclosure smaller word) :
    KempeCoclosure larger word := by
  intro closedFamily hclosed hword
  obtain ⟨otherWord, hsmall, hother⟩ :=
    hcoclosure closedFamily hclosed hword
  exact ⟨otherWord, hsubset otherWord hsmall, hother⟩

/-- A human-readable inductive proof language for Kempe co-closure.  Its third
rule is the adversarial planar case: whichever chromogram a surrounding planar
coloring realizes, some coloring with the same chromogram has already been
discharged. -/
inductive CoclosureDerivation
    (extendable : List TraceSymbol → Prop) :
    List TraceSymbol → Prop where
  | member {word} :
      extendable word → CoclosureDerivation extendable word
  | permutation {word} (permutation : SymbolPermutation) :
      CoclosureDerivation extendable
        (permuteWord permutation word) →
      CoclosureDerivation extendable word
  | chromograms {word}
      (nextWord : ∀ gram, Matches word gram → List TraceSymbol)
      (next_matches : ∀ gram (hmatch : Matches word gram),
        Matches (nextWord gram hmatch) gram)
      (next_derivation : ∀ gram (hmatch : Matches word gram),
        CoclosureDerivation extendable (nextWord gram hmatch)) :
      CoclosureDerivation extendable word

/-- Every finite derivation in the three-rule language proves the semantic
second-order Kempe co-closure property. -/
theorem CoclosureDerivation.sound
    {extendable : List TraceSymbol → Prop} {word : List TraceSymbol}
    (derivation : CoclosureDerivation extendable word) :
    KempeCoclosure extendable word := by
  induction derivation with
  | member hextendable =>
      exact kempeCoclosure_of_mem hextendable
  | @permutation word permutation _ ih =>
      intro closedFamily hclosed hword
      have hpermuted := (hclosed word hword).1 permutation
      exact ih closedFamily hclosed hpermuted
  | @chromograms word nextWord nextMatches nextDerivation ih =>
      intro closedFamily hclosed hword
      obtain ⟨gram, hwordGram, hfiber⟩ := (hclosed word hword).2
      exact ih gram hwordGram closedFamily hclosed
        (hfiber (nextWord gram hwordGram)
          (nextMatches gram hwordGram))

/-- One locally checkable rule in a ranked co-closure DAG. -/
inductive RankedRule
    (covered extendable : List TraceSymbol → Prop)
    (rank : List TraceSymbol → Nat) (word : List TraceSymbol) : Prop where
  | member : extendable word → RankedRule covered extendable rank word
  | permutation (permutation : SymbolPermutation)
      (next_covered : covered (permuteWord permutation word))
      (decreases : rank (permuteWord permutation word) < rank word) :
      RankedRule covered extendable rank word
  | chromograms
      (nextWord : ∀ gram, Matches word gram → List TraceSymbol)
      (next_matches : ∀ gram (hmatch : Matches word gram),
        Matches (nextWord gram hmatch) gram)
      (next_covered : ∀ gram (hmatch : Matches word gram),
        covered (nextWord gram hmatch))
      (decreases : ∀ gram (hmatch : Matches word gram),
        rank (nextWord gram hmatch) < rank word) :
      RankedRule covered extendable rank word

/-- Local ranked rules assemble by well-founded recursion into the inductive
co-closure proof language. -/
theorem derivation_of_rankedRules
    {covered extendable : List TraceSymbol → Prop}
    (rank : List TraceSymbol → Nat)
    (rules : ∀ word, covered word →
      RankedRule covered extendable rank word)
    (word : List TraceSymbol) (hcovered : covered word) :
    CoclosureDerivation extendable word := by
  rcases rules word hcovered with
    hmember | ⟨permutation, hnextCovered, hdecreases⟩ |
      ⟨nextWord, hnextMatches, hnextCovered, hdecreases⟩
  · exact .member hmember
  · exact .permutation permutation
      (derivation_of_rankedRules rank rules
        (permuteWord permutation word) hnextCovered)
  · exact .chromograms nextWord hnextMatches fun gram hmatch =>
      derivation_of_rankedRules rank rules
        (nextWord gram hmatch) (hnextCovered gram hmatch)
termination_by rank word
decreasing_by
  · exact hdecreases
  · exact hdecreases gram hmatch

theorem kempeCoclosure_of_rankedRules
    {covered extendable : List TraceSymbol → Prop}
    (rank : List TraceSymbol → Nat)
    (rules : ∀ word, covered word →
      RankedRule covered extendable rank word)
    {word : List TraceSymbol} (hcovered : covered word) :
    KempeCoclosure extendable word :=
  (derivation_of_rankedRules rank rules word hcovered).sound

/-- Semantic obligations carried by the two compact trees in a reducibility
certificate.  The contract tree covers every coloring of the contracted map;
absence from the second tree certifies Kempe reachability of an extendable
boundary trace. -/
structure ReducibilityTreeSemantics
    (contractTree unreachableTree : TraceTree)
    (contractTrace extendableTrace : List TraceSymbol → Prop) : Prop where
  contractTree_complete :
    ∀ word, contractTrace word → contractTree.accepts word = true
  unreachableTree_escape :
    ∀ word, unreachableTree.accepts word = false →
      KempeCoclosure extendableTrace word

/-- The central compositional reducibility implication: exact tree
disjointness plus the two local semantic certificates sends every contracted
boundary coloring into the Kempe co-closure of an extendable coloring. -/
theorem contractTrace_kempeCoclosure_of_disjoint
    {contractTree unreachableTree : TraceTree}
    {contractTrace extendableTrace : List TraceSymbol → Prop}
    (hsemantics : ReducibilityTreeSemantics contractTree unreachableTree
      contractTrace extendableTrace)
    (hdisjoint : contractTree.disjoint unreachableTree = true) :
    ∀ word, contractTrace word → KempeCoclosure extendableTrace word := by
  intro word hcontract
  have hcontractTree := hsemantics.contractTree_complete word hcontract
  have hunreachable : unreachableTree.accepts word = false := by
    cases hvalue : unreachableTree.accepts word with
    | false => rfl
    | true =>
        exact (TraceTree.disjoint_sound contractTree unreachableTree
          hdisjoint word ⟨hcontractTree, hvalue⟩).elim
  exact hsemantics.unreachableTree_escape word hunreachable

/-- A fully assembled trace-level reducibility certificate. -/
structure ReducibilityCertificate
    (contractTrace extendableTrace : List TraceSymbol → Prop) where
  data : DisjointTraceCertificate
  semantics : ReducibilityTreeSemantics data.contractTree data.kempeTree
    contractTrace extendableTrace
  accepted : data.checker = true

theorem ReducibilityCertificate.reduces
    {contractTrace extendableTrace : List TraceSymbol → Prop}
    (certificate : ReducibilityCertificate contractTrace extendableTrace) :
    ∀ word, contractTrace word → KempeCoclosure extendableTrace word :=
  contractTrace_kempeCoclosure_of_disjoint certificate.semantics
    certificate.accepted

end ClassicalCertificateKempeClosure

end Mettapedia.GraphTheory.FourColor
