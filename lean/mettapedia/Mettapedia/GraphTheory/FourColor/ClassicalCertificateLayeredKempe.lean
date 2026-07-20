import Mettapedia.GraphTheory.FourColor.ClassicalCertificateEvenTraceKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateLayeredKempe

open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree
open ClassicalCertificateTreeRankedKempe

private def prependResult (symbol : TraceSymbol) :
    Option (List TraceSymbol) → Option (List TraceSymbol) :=
  Option.map (symbol :: ·)

/-- Search an accepted trace trie directly for a word matching the supplied
chromogram and initial stack.  Only matcher-compatible branches are visited. -/
def findMatchingWord : TraceTree → List Bool → Chromogram →
    Option (List TraceSymbol)
  | tree, stack, [] =>
      if stack = [] ∧ tree.accepts [] = true then some [] else none
  | tree, stack, step :: gram =>
      let redResult :=
        match chromogramAdvance stack .red step with
        | none => none
        | some nextStack =>
            prependResult .red
              (findMatchingWord (tree.child .red) nextStack gram)
      let blueResult :=
        match chromogramAdvance stack .blue step with
        | none => none
        | some nextStack =>
            prependResult .blue
              (findMatchingWord (tree.child .blue) nextStack gram)
      let purpleResult :=
        match chromogramAdvance stack .purple step with
        | none => none
        | some nextStack =>
            prependResult .purple
              (findMatchingWord (tree.child .purple) nextStack gram)
      redResult.orElse fun _ =>
        blueResult.orElse fun _ => purpleResult

private theorem orElse_eq_some_iff {option : Option α}
    {fallback : Unit → Option α} {value : α} :
    option.orElse fallback = some value ↔
      option = some value ∨ option = none ∧ fallback () = some value := by
  cases option <;> simp [Option.orElse]

private theorem accepts_cons (tree : TraceTree) (symbol : TraceSymbol)
    (word : List TraceSymbol) :
    tree.accepts (symbol :: word) = (tree.child symbol).accepts word := by
  cases tree <;> cases symbol <;>
    simp [TraceTree.accepts, TraceTree.child]

/-- A successful trie search is a kernel-checked accepted word in the stated
chromogram fiber. -/
theorem findMatchingWord_sound
    (tree : TraceTree) (stack : List Bool) (gram : Chromogram)
    (word : List TraceSymbol)
    (hfound : findMatchingWord tree stack gram = some word) :
    tree.accepts word = true ∧
      chromogramMatches stack word gram = true := by
  induction gram generalizing tree stack word with
  | nil =>
      simp only [findMatchingWord] at hfound
      split at hfound
      · rename_i hbase
        have hword : word = [] := by simpa using hfound.symm
        subst word
        exact ⟨hbase.2, by simp [chromogramMatches, hbase.1]⟩
      · simp at hfound
  | cons step gram ih =>
      let redResult :=
        match chromogramAdvance stack .red step with
        | none => none
        | some nextStack =>
            prependResult .red
              (findMatchingWord (tree.child .red) nextStack gram)
      let blueResult :=
        match chromogramAdvance stack .blue step with
        | none => none
        | some nextStack =>
            prependResult .blue
              (findMatchingWord (tree.child .blue) nextStack gram)
      let purpleResult :=
        match chromogramAdvance stack .purple step with
        | none => none
        | some nextStack =>
            prependResult .purple
              (findMatchingWord (tree.child .purple) nextStack gram)
      have hchoice : redResult = some word ∨
          redResult = none ∧
            (blueResult = some word ∨
              blueResult = none ∧ purpleResult = some word) := by
        rw [findMatchingWord, orElse_eq_some_iff,
          orElse_eq_some_iff] at hfound
        simpa [redResult, blueResult, purpleResult] using hfound
      rcases hchoice with hred | ⟨_, hblue | ⟨_, hpurple⟩⟩
      · unfold redResult at hred
        cases hadvance : chromogramAdvance stack .red step with
        | none => simp [hadvance] at hred
        | some nextStack =>
            cases htail : findMatchingWord (tree.child .red) nextStack gram with
            | none => simp [hadvance, htail, prependResult] at hred
            | some tail =>
                have hword : word = .red :: tail := by
                  simpa [hadvance, htail, prependResult] using hred.symm
                subst word
                have hsound := ih (tree.child .red) nextStack tail htail
                exact ⟨by simpa [accepts_cons] using hsound.1,
                  by simpa [chromogramMatches, hadvance] using hsound.2⟩
      · unfold blueResult at hblue
        cases hadvance : chromogramAdvance stack .blue step with
        | none => simp [hadvance] at hblue
        | some nextStack =>
            cases htail : findMatchingWord (tree.child .blue) nextStack gram with
            | none => simp [hadvance, htail, prependResult] at hblue
            | some tail =>
                have hword : word = .blue :: tail := by
                  simpa [hadvance, htail, prependResult] using hblue.symm
                subst word
                have hsound := ih (tree.child .blue) nextStack tail htail
                exact ⟨by simpa [accepts_cons] using hsound.1,
                  by simpa [chromogramMatches, hadvance] using hsound.2⟩
      · unfold purpleResult at hpurple
        cases hadvance : chromogramAdvance stack .purple step with
        | none => simp [hadvance] at hpurple
        | some nextStack =>
            cases htail : findMatchingWord (tree.child .purple) nextStack gram with
            | none => simp [hadvance, htail, prependResult] at hpurple
            | some tail =>
                have hword : word = .purple :: tail := by
                  simpa [hadvance, htail, prependResult] using hpurple.symm
                subst word
                have hsound := ih (tree.child .purple) nextStack tail htail
                exact ⟨by simpa [accepts_cons] using hsound.1,
                  by simpa [chromogramMatches, hadvance] using hsound.2⟩

/-- A total response extracted from the trie search.  Its fallback is used
only outside accepted certificates. -/
def matchingResponse (tree : TraceTree) (gram : Chromogram) :
    List TraceSymbol :=
  (findMatchingWord tree [] gram).getD []

theorem matchingResponse_sound (tree : TraceTree) (gram : Chromogram)
    (hfound : (findMatchingWord tree [] gram).isSome = true) :
    tree.accepts (matchingResponse tree gram) = true ∧
      Matches (matchingResponse tree gram) gram := by
  obtain ⟨word, hword⟩ := Option.isSome_iff_exists.1 hfound
  have hsound := findMatchingWord_sound tree [] gram word hword
  simpa [matchingResponse, hword, Matches] using hsound

/-- Pointwise union for fixed-height trace tries.  Catalogue certificates use
it only on tries of one declared word length. -/
def union : TraceTree → TraceTree → TraceTree
  | .empty, right => right
  | left, .empty => left
  | .leaf, .leaf => .leaf
  | .node leftRed leftBlue leftPurple,
      .node rightRed rightBlue rightPurple =>
      .node (union leftRed rightRed) (union leftBlue rightBlue)
        (union leftPurple rightPurple)
  | left, _ => left

/-- Every word retained by the fixed-height union came from one of its input
tries.  This one-way statement is valid even for malformed mixed-height data. -/
theorem accepts_union (left right : TraceTree) (word : List TraceSymbol)
    (haccepted : (union left right).accepts word = true) :
    left.accepts word = true ∨ right.accepts word = true := by
  induction left generalizing right word with
  | empty => exact Or.inr (by simpa [union] using haccepted)
  | leaf =>
      cases right <;> cases word <;>
        simp [union, TraceTree.accepts] at haccepted ⊢
  | node leftRed leftBlue leftPurple ihRed ihBlue ihPurple =>
      cases right with
      | empty => exact Or.inl (by simpa [union] using haccepted)
      | leaf => exact Or.inl (by simpa [union] using haccepted)
      | node rightRed rightBlue rightPurple =>
          cases word with
          | nil => simp [union, TraceTree.accepts] at haccepted
          | cons symbol word =>
              cases symbol with
              | red =>
                  have hchild := ihRed rightRed word (by
                    simpa [union, TraceTree.accepts, TraceTree.child] using
                      haccepted)
                  simpa [TraceTree.accepts, TraceTree.child] using hchild
              | blue =>
                  have hchild := ihBlue rightBlue word (by
                    simpa [union, TraceTree.accepts, TraceTree.child] using
                      haccepted)
                  simpa [TraceTree.accepts, TraceTree.child] using hchild
              | purple =>
                  have hchild := ihPurple rightPurple word (by
                    simpa [union, TraceTree.accepts, TraceTree.child] using
                      haccepted)
                  simpa [TraceTree.accepts, TraceTree.child] using hchild

def AcceptedFamily (length : Nat) (tree : TraceTree)
    (word : List TraceSymbol) : Prop :=
  ∃ fixedWord : TraceWord length,
    fixedWord.toList = word ∧ tree.accepts fixedWord.toList = true

def previousPermutation? {length : Nat} (previous : TraceTree)
    (word : TraceWord length) : Option PermutationCode :=
  permutationCodes.find? fun permutation =>
    previous.accepts (permute permutation word).toList

/-- One layer rule: an extendable member, a word already in the previous
layer, a global permutation into it, or compatible responses for every
matching chromogram. -/
def ruleBoolean {length : Nat} (previous extendable : TraceTree)
    (word : TraceWord length) : Bool :=
  if extendable.accepts word.toList then true
  else if previous.accepts word.toList then true
  else
    match previousPermutation? previous word with
    | some _ => true
    | none =>
        (matchingGramWords word).all fun gram =>
          (findMatchingWord previous [] gram.toList).isSome

private def gramWordOfMatch {length : Nat} (word : TraceWord length)
    (gram : Chromogram) (hmatch : Matches word.toList gram) :
    GramWord length :=
  ⟨gram, hmatch.length_eq.symm.trans word.2⟩

/-- A locally accepted layer rule composes with derivations already proved
for the preceding layer. -/
theorem derivation_of_ruleBoolean {length : Nat}
    (previous extendable : TraceTree)
    (previousSound : ∀ word : TraceWord length,
      previous.accepts word.toList = true →
        CoclosureDerivation (AcceptedFamily length extendable) word.toList)
    (word : TraceWord length)
    (hrule : ruleBoolean previous extendable word = true) :
    CoclosureDerivation (AcceptedFamily length extendable) word.toList := by
  unfold ruleBoolean at hrule
  split at hrule
  · rename_i hextendable
    exact .member ⟨word, rfl, hextendable⟩
  · rename_i hnotExtendable
    split at hrule
    · rename_i hprevious
      exact previousSound word hprevious
    · rename_i hnotPrevious
      cases hpermutation : previousPermutation? previous word with
      | some permutation =>
          have haccepted :
              previous.accepts (permute permutation word).toList = true := by
            have hselected := List.find?_some hpermutation
            simpa [previousPermutation?] using hselected
          exact .permutation permutation.toEquiv (by
            simpa using previousSound (permute permutation word) haccepted)
      | none =>
          refine .chromograms
            (fun gram _ => matchingResponse previous gram) ?_ ?_
          · intro gram hmatch
            let fixedGram := gramWordOfMatch word gram hmatch
            have hmem : fixedGram ∈ matchingGramWords word :=
              mem_matchingGramWords word fixedGram hmatch
            have hsome := (List.all_eq_true.1 (by
              simpa [hpermutation] using hrule)) fixedGram hmem
            exact (matchingResponse_sound previous gram (by
              simpa [fixedGram, gramWordOfMatch] using hsome)).2
          · intro gram hmatch
            let fixedGram := gramWordOfMatch word gram hmatch
            have hmem : fixedGram ∈ matchingGramWords word :=
              mem_matchingGramWords word fixedGram hmatch
            have hsome := (List.all_eq_true.1 (by
              simpa [hpermutation] using hrule)) fixedGram hmem
            have hresponse := matchingResponse_sound previous gram (by
              simpa [fixedGram, gramWordOfMatch] using hsome)
            have hlength : (matchingResponse previous gram).length = length :=
              hresponse.2.length_eq.trans fixedGram.2
            exact previousSound ⟨matchingResponse previous gram, hlength⟩
              hresponse.1

/-- Verify every accepted word of one cumulative layer. -/
def layerBoolean (length : Nat) (current previous extendable : TraceTree) :
    Bool :=
  (acceptedWords length current).all (ruleBoolean previous extendable)

theorem derivation_of_layerBoolean {length : Nat}
    (current previous extendable : TraceTree)
    (previousSound : ∀ word : TraceWord length,
      previous.accepts word.toList = true →
        CoclosureDerivation (AcceptedFamily length extendable) word.toList)
    (hcheck : layerBoolean length current previous extendable = true)
    (word : TraceWord length)
    (hcurrent : current.accepts word.toList = true) :
    CoclosureDerivation (AcceptedFamily length extendable) word.toList := by
  apply derivation_of_ruleBoolean previous extendable previousSound word
  exact (List.all_eq_true.1 hcheck) word
    ((mem_acceptedWords_iff current word).2 hcurrent)

def foldLayers (previous : TraceTree) (deltas : List TraceTree) : TraceTree :=
  deltas.foldl union previous

/-- Check successive cumulative closures generated by unioning delta tries. -/
def checkLayers (length : Nat) (extendable : TraceTree) :
    TraceTree → List TraceTree → Bool
  | _, [] => true
  | previous, delta :: deltas =>
      let current := union previous delta
      layerBoolean length delta previous extendable &&
        checkLayers length extendable current deltas

theorem derivation_of_checkLayers {length : Nat}
    (extendable previous : TraceTree) (deltas : List TraceTree)
    (previousSound : ∀ word : TraceWord length,
      previous.accepts word.toList = true →
        CoclosureDerivation (AcceptedFamily length extendable) word.toList)
    (hcheck : checkLayers length extendable previous deltas = true) :
    ∀ word : TraceWord length,
      (foldLayers previous deltas).accepts word.toList = true →
        CoclosureDerivation (AcceptedFamily length extendable) word.toList := by
  induction deltas generalizing previous with
  | nil =>
      simpa [foldLayers] using previousSound
  | cons delta deltas ih =>
      let current := union previous delta
      have hcheck' :
          layerBoolean length delta previous extendable = true ∧
            checkLayers length extendable current deltas = true := by
        simpa [checkLayers, current] using hcheck
      have deltaSound : ∀ word : TraceWord length,
          delta.accepts word.toList = true →
            CoclosureDerivation (AcceptedFamily length extendable) word.toList :=
        derivation_of_layerBoolean delta previous extendable previousSound
          hcheck'.1
      have currentSound : ∀ word : TraceWord length,
          current.accepts word.toList = true →
            CoclosureDerivation (AcceptedFamily length extendable) word.toList :=
        fun word hcurrent =>
          (accepts_union previous delta word.toList hcurrent).elim
            (previousSound word) (deltaSound word)
      simpa [foldLayers, current] using
        ih current currentSound hcheck'.2

/-- A response-free Kempe certificate: each delta trie adds one verified
closure layer, and matching responses are reconstructed from the preceding
trie. -/
structure Certificate (length : Nat) where
  extendable : TraceTree
  deltas : List TraceTree
  deriving DecidableEq, Repr

namespace Certificate

variable {length : Nat}

def closureTree (certificate : Certificate length) : TraceTree :=
  foldLayers .empty certificate.deltas

def checker (certificate : Certificate length) : Bool :=
  checkLayers length certificate.extendable .empty certificate.deltas

def ExtendableFamily (certificate : Certificate length)
    (word : List TraceSymbol) : Prop :=
  AcceptedFamily length certificate.extendable word

theorem derivation_of_checker_true (certificate : Certificate length)
    (hchecker : certificate.checker = true) (word : TraceWord length)
    (hclosure : certificate.closureTree.accepts word.toList = true) :
    CoclosureDerivation certificate.ExtendableFamily word.toList := by
  apply derivation_of_checkLayers certificate.extendable .empty
    certificate.deltas (previousSound := ?_) hchecker word hclosure
  intro previousWord himpossible
  simp [TraceTree.accepts] at himpossible

theorem kempeCoclosure_of_checker_true (certificate : Certificate length)
    (hchecker : certificate.checker = true) (word : TraceWord length)
    (hclosure : certificate.closureTree.accepts word.toList = true) :
    KempeCoclosure certificate.ExtendableFamily word.toList :=
  (certificate.derivation_of_checker_true hchecker word hclosure).sound

end Certificate

end ClassicalCertificateLayeredKempe

end Mettapedia.GraphTheory.FourColor
