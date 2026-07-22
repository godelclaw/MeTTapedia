import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankResponseSearch

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankTransferClosure

open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitRankResponseSearch
open ClassicalCertificatePackedRankVector
open ClassicalCertificateRankedKempe
open ClassicalCertificateRankVectorDag
open ClassicalCertificateRankVectorProduct
open ClassicalCertificateTraceTree

variable {length : Nat}

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

def prependSymbol {length : Nat} (symbol : TraceSymbol)
    (word : TraceWord length) : TraceWord (length + 1) :=
  List.Vector.cons symbol word

/-- Enumerate the rank-vector leaves of one fixed-height trace DAG. -/
def traceEntries : (length : Nat) → TraceCode → Nat →
    List (TraceWord length × Nat)
  | 0, code, root =>
      match code.nodeAt root with
      | .leaf rankVector => [(List.Vector.nil, rankVector)]
      | _ => []
  | length + 1, code, root =>
      match code.nodeAt root with
      | .node red blue purple =>
          (traceEntries length code red).map (fun entry =>
              (prependSymbol .red entry.1, entry.2)) ++
            (traceEntries length code blue).map (fun entry =>
              (prependSymbol .blue entry.1, entry.2)) ++
            (traceEntries length code purple).map (fun entry =>
              (prependSymbol .purple entry.1, entry.2))
      | _ => []

@[simp] theorem exists_trace_lookup_toList_eq_iff
    (code : TraceCode) (root rankVector : Nat)
    (word : TraceWord length) :
    (∃ candidate : TraceWord length,
        code.lookup length root candidate.toList = some rankVector ∧
          candidate.toList = word.toList) ↔
      code.lookup length root word.toList = some rankVector := by
  constructor
  · rintro ⟨candidate, hlookup, heq⟩
    simpa [heq] using hlookup
  · intro hlookup
    exact ⟨word, hlookup, rfl⟩

theorem mem_traceEntries_iff_lookup
    (code : TraceCode) (root : Nat)
    (word : TraceWord length) (rankVector : Nat) :
    (word, rankVector) ∈ traceEntries length code root ↔
      code.lookup length root word.toList = some rankVector := by
  induction length generalizing root with
  | zero =>
      have hword : word = List.Vector.nil := Subsingleton.elim _ _
      subst word
      cases hnode : code.nodeAt root <;>
        simp [traceEntries, TraceCode.lookup, hnode, eq_comm]
  | succ length ih =>
      rw [← List.Vector.cons_head_tail word]
      cases hsymbol : word.head <;>
        cases hnode : code.nodeAt root <;>
          simp [traceEntries, TraceCode.lookup, hnode, prependSymbol,
            ih]

/-- Test one global color permutation as a launch spelling for a specified
configuration rank. -/
def launchCandidate?
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (table : Table length) (config rank : Nat) (word : TraceWord length)
    (permutation : PermutationCode) : Option (PermutationCode × Nat) :=
  match certificate.traceCode.lookup length certificate.sourceRoot
      (permute permutation word).toList with
  | none => none
  | some sourceVector =>
      if table.ranks.rankAt? sourceVector config = some rank then
        some (permutation, sourceVector)
      else none

/-- Search the six global color permutations for a product-certified launch
spelling carrying the requested configuration rank. -/
def findLaunch?
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (table : Table length)
    (config rank : Nat) (word : TraceWord length) :
    Option (PermutationCode × Nat) :=
  permutationCodes.findSome? fun permutation =>
    launchCandidate? certificate table config rank word permutation

theorem findLaunch?_sound
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (table : Table length) (config rank : Nat) (word : TraceWord length)
    (permutation : PermutationCode) (sourceVector : Nat)
    (hfound : findLaunch? certificate table config rank word =
      some (permutation, sourceVector)) :
    certificate.traceCode.lookup length certificate.sourceRoot
        (permute permutation word).toList = some sourceVector ∧
      table.ranks.rankAt? sourceVector config = some rank := by
  rw [findLaunch?, List.findSome?_eq_some_iff] at hfound
  obtain ⟨_prefix, selected, _suffix, _hcodes, hselected, _hprior⟩ :=
    hfound
  unfold launchCandidate? at hselected
  split at hselected
  · contradiction
  · rename_i storedSourceVector hlookup
    split at hselected
    · rename_i hrank
      cases hselected
      exact ⟨hlookup, hrank⟩
    · contradiction

/-- Every positive rank stored at an orbit representative has a launch
spelling in the product source trie. -/
def launchCoverageChecker (table : Table length)
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (config : Nat) : Bool :=
  (traceEntries length table.orbitCode table.orbitRoot).all fun entry =>
    match table.ranks.rankAt? entry.2 config with
    | some (rank + 1) =>
        (findLaunch? certificate table config (rank + 1) entry.1).isSome
    | _ => true

theorem launchCoverageChecker_sound (table : Table length)
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (config : Nat)
    (hchecker : launchCoverageChecker table certificate config = true)
    (word : TraceWord length) (orbitVector rank : Nat)
    (hlookup : table.vectorAt? word = some orbitVector)
    (hrank : table.ranks.rankAt? orbitVector config = some (rank + 1)) :
    ∃ permutation sourceVector,
      certificate.traceCode.lookup length certificate.sourceRoot
          (permute permutation word).toList = some sourceVector ∧
        table.ranks.rankAt? sourceVector config = some (rank + 1) := by
  have hentry : (word, orbitVector) ∈
      traceEntries length table.orbitCode table.orbitRoot :=
    (mem_traceEntries_iff_lookup table.orbitCode table.orbitRoot word
      orbitVector).2 (by simpa [Table.vectorAt?] using hlookup)
  have hlocal := (List.all_eq_true.1 hchecker) (word, orbitVector) hentry
  simp [hrank] at hlocal
  obtain ⟨launch, hlaunch⟩ := Option.isSome_iff_exists.1 hlocal
  rcases launch with ⟨permutation, sourceVector⟩
  exact ⟨permutation, sourceVector,
    findLaunch?_sound certificate table config (rank + 1) word permutation
      sourceVector hlaunch⟩

/-- Check the rank-zero orbit leaves against an independently meaningful base
predicate. -/
def baseCoverageChecker (table : Table length) (config : Nat)
    (base : TraceWord length → Bool) : Bool :=
  (traceEntries length table.orbitCode table.orbitRoot).all fun entry =>
    match table.ranks.rankAt? entry.2 config with
    | some 0 => base entry.1
    | _ => true

theorem baseCoverageChecker_sound (table : Table length) (config : Nat)
    (base : TraceWord length → Bool)
    (hchecker : baseCoverageChecker table config base = true)
    (word : TraceWord length) (orbitVector : Nat)
    (hlookup : table.vectorAt? word = some orbitVector)
    (hrank : table.ranks.rankAt? orbitVector config = some 0) :
    base word = true := by
  have hentry : (word, orbitVector) ∈
      traceEntries length table.orbitCode table.orbitRoot :=
    (mem_traceEntries_iff_lookup table.orbitCode table.orbitRoot word
      orbitVector).2 (by simpa [Table.vectorAt?] using hlookup)
  have hlocal := (List.all_eq_true.1 hchecker) (word, orbitVector) hentry
  simpa [baseCoverageChecker, hrank] using hlocal

private def gramWordOfMatch (word : TraceWord length)
    (gram : Chromogram) (hmatch : Matches word.toList gram) :
    GramWord length :=
  ⟨gram, hmatch.length_eq.symm.trans word.2⟩

/-- Orbit representatives, launch spellings, and pointer-free lower-rank
responses assemble into one finite Kempe co-closure derivation.  The two
global permutations are nonrecursive; only the orbit rank decreases. -/
theorem derivation
    (table : Table length)
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (config : Nat) (hconfig : config < table.ranks.configCount)
    (hranks : certificate.ranks = table.ranks)
    (hproduct : certificate.checker = true)
    (hwitness : responseWitnessChecker table certificate.responseCode
      certificate.responseRoot = true)
    (hlaunch : launchCoverageChecker table certificate config = true)
    (base : TraceWord length → Bool)
    (hbase : baseCoverageChecker table config base = true)
    (ordinary : List TraceSymbol → Prop)
    (baseSound : ∀ word, base word = true → ordinary word.toList)
    (word : TraceWord length) (rank : Nat)
    (hrank : table.rankAt? config word = some rank) :
    CoclosureDerivation ordinary word.toList := by
  obtain ⟨orbitPermutation, orbitVector, horbitLookup, horbitRank⟩ :=
    table.rankAt?_sound config rank word hrank
  let orbitWord := permute orbitPermutation word
  apply CoclosureDerivation.permutation orbitPermutation.toEquiv
  change CoclosureDerivation ordinary orbitWord.toList
  cases rank with
  | zero =>
      apply CoclosureDerivation.member
      apply baseSound orbitWord
      exact baseCoverageChecker_sound table config base hbase orbitWord
        orbitVector horbitLookup horbitRank
  | succ rank =>
      obtain ⟨launchPermutation, sourceVector, hsourceLookup,
          hsourceRank⟩ :=
        launchCoverageChecker_sound table certificate config hlaunch orbitWord
          orbitVector rank horbitLookup horbitRank
      let launchWord := permute launchPermutation orbitWord
      apply CoclosureDerivation.permutation launchPermutation.toEquiv
      change CoclosureDerivation ordinary launchWord.toList
      refine CoclosureDerivation.chromograms
        (fun gram hmatch =>
          let fixedGram := gramWordOfMatch launchWord gram hmatch
          (Classical.choose
            (exists_lower_response_of_checkers certificate table hranks
              hproduct hwitness launchWord sourceVector config (rank + 1)
                hsourceLookup hconfig hsourceRank fixedGram hmatch).2).toList)
        ?_ ?_
      · intro gram hmatch
        let fixedGram := gramWordOfMatch launchWord gram hmatch
        have hresponses :=
          (exists_lower_response_of_checkers certificate table hranks
            hproduct hwitness launchWord sourceVector config (rank + 1)
              hsourceLookup hconfig hsourceRank fixedGram hmatch).2
        obtain ⟨responseRank, hmatches, _hrank, _hlower⟩ :=
          Classical.choose_spec hresponses
        simpa [fixedGram, gramWordOfMatch] using hmatches
      · intro gram hmatch
        let fixedGram := gramWordOfMatch launchWord gram hmatch
        have hresponses :=
          (exists_lower_response_of_checkers certificate table hranks
            hproduct hwitness launchWord sourceVector config (rank + 1)
              hsourceLookup hconfig hsourceRank fixedGram hmatch).2
        obtain ⟨responseRank, _hmatches, hresponseRank, hlower⟩ :=
          Classical.choose_spec hresponses
        exact derivation table certificate config hconfig hranks hproduct
          hwitness hlaunch base hbase ordinary baseSound
            (Classical.choose hresponses) responseRank hresponseRank
termination_by rank
decreasing_by omega

theorem kempeCoclosure
    (table : Table length)
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (config : Nat) (hconfig : config < table.ranks.configCount)
    (hranks : certificate.ranks = table.ranks)
    (hproduct : certificate.checker = true)
    (hwitness : responseWitnessChecker table certificate.responseCode
      certificate.responseRoot = true)
    (hlaunch : launchCoverageChecker table certificate config = true)
    (base : TraceWord length → Bool)
    (hbase : baseCoverageChecker table config base = true)
    (ordinary : List TraceSymbol → Prop)
    (baseSound : ∀ word, base word = true → ordinary word.toList)
    (word : TraceWord length) (rank : Nat)
    (hrank : table.rankAt? config word = some rank) :
    KempeCoclosure ordinary word.toList :=
  (derivation table certificate config hconfig hranks hproduct hwitness
    hlaunch base hbase ordinary baseSound word rank hrank).sound

end ClassicalCertificateOrbitRankTransferClosure

end Mettapedia.GraphTheory.FourColor
