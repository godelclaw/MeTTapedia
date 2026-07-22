import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitProofDagReduction
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankVectorDag
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankVectorProductSound

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankResponseSearch

open ClassicalCertificateKempeClosure
open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateOrbitProofDagReduction
open ClassicalCertificatePackedRankVector
open ClassicalCertificateRankedKempe
open ClassicalCertificateRankVectorDag
open ClassicalCertificateRankVectorProduct
open ClassicalCertificateRankVectorProductSound
open ClassicalCertificateTraceTree

variable {length : Nat}

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

def traceSymbols : List TraceSymbol := [.red, .blue, .purple]

/-- Enumerate the trace words realizing one oriented noncrossing chromogram.
At length fourteen a fiber has at most one binary choice per push, so this is
a small structural search rather than a scan of the ambient word space. -/
def matchingWordsFrom : List Bool → Chromogram → List (List TraceSymbol)
  | stack, [] => if stack = [] then [[]] else []
  | stack, step :: gram =>
      traceSymbols.flatMap fun symbol =>
        match chromogramAdvance stack symbol step with
        | none => []
        | some nextStack =>
            (matchingWordsFrom nextStack gram).map (symbol :: ·)

theorem mem_matchingWordsFrom_iff
    (stack : List Bool) (word : List TraceSymbol) (gram : Chromogram) :
    word ∈ matchingWordsFrom stack gram ↔
      chromogramMatches stack word gram = true := by
  induction gram generalizing stack word with
  | nil =>
      cases word <;> cases stack <;>
        simp [matchingWordsFrom, chromogramMatches]
  | cons step gram ih =>
      cases word with
      | nil =>
          cases step <;> cases stack with
          | nil =>
              simp [matchingWordsFrom, traceSymbols, chromogramMatches,
                chromogramAdvance]
          | cons head tail =>
              cases head <;>
                simp [matchingWordsFrom, traceSymbols, chromogramMatches,
                  chromogramAdvance]
      | cons symbol word =>
          cases symbol <;> cases step <;> cases stack with
          | nil =>
              simp [matchingWordsFrom, traceSymbols, chromogramMatches,
                chromogramAdvance, ih]
          | cons head tail =>
              cases head <;>
                simp [matchingWordsFrom, traceSymbols, chromogramMatches,
                  chromogramAdvance, ih]

/-- Fixed-length form of the exact chromogram fiber enumeration. -/
def matchingTraceWords (gram : GramWord length) :
    List (TraceWord length) :=
  (matchingWordsFrom [] gram.toList).attach.map fun word =>
    ⟨word.val,
      (ClassicalCertificateKempeClosure.length_eq_of_chromogramMatches
        ((mem_matchingWordsFrom_iff [] word.val gram.toList).1
          word.property)).trans gram.2⟩

theorem mem_matchingTraceWords_iff
    (gram : GramWord length) (word : TraceWord length) :
    word ∈ matchingTraceWords gram ↔ Matches word.toList gram.toList := by
  constructor
  · intro hword
    obtain ⟨attached, _hattached, heq⟩ := List.mem_map.1 hword
    have hlist : attached.val = word.toList := by
      simpa using congrArg List.Vector.toList heq
    rw [← hlist]
    exact (mem_matchingWordsFrom_iff [] attached.val gram.toList).1
      attached.property
  · intro hmatch
    apply List.mem_map.2
    refine ⟨⟨word.toList,
      (mem_matchingWordsFrom_iff [] word.toList gram.toList).2 hmatch⟩,
      by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem canonicalWord_length (word : List TraceSymbol) :
    (canonicalWord word).length = word.length := by
  unfold canonicalWord
  let step := fun best (permutation : PermutationCode) =>
    let candidate := word.map permutation.apply
    if wordIndexList candidate < wordIndexList best then candidate else best
  have hfold : ∀ (permutations : List PermutationCode)
      (best : List TraceSymbol),
      best.length = word.length →
        (permutations.foldl step best).length = word.length := by
    intro permutations
    induction permutations with
    | nil => simpa
    | cons permutation permutations ih =>
        intro best hbest
        apply ih
        simp only [step]
        split
        · simp
        · exact hbest
  change (List.foldl step word permutationCodes).length = word.length
  exact hfold permutationCodes word rfl

def canonicalTraceWord (word : TraceWord length) : TraceWord length :=
  ⟨canonicalWord word.toList, canonicalWord_length word.toList |>.trans word.2⟩

/-- Canonical orbit words point to configuration-rank vectors. -/
structure Table (length : Nat) where
  ranks : ClassicalCertificatePackedRankVector.Code
  orbitCode : TraceCode
  orbitRoot : Nat

def Table.vectorAt? (table : Table length)
    (word : TraceWord length) : Option Nat :=
  table.orbitCode.lookup length table.orbitRoot
    (canonicalTraceWord word).toList

def Table.rankAt? (table : Table length)
    (config : Nat) (word : TraceWord length) : Option Nat :=
  match table.vectorAt? word with
  | none => none
  | some vector => table.ranks.rankAt? vector config

/-- Search one exact chromogram fiber for a word carrying the requested orbit
rank in one configuration. -/
def findResponse? (table : Table length) (config rank : Nat)
    (gram : GramWord length) : Option (TraceWord length) :=
  (matchingTraceWords gram).find? fun word =>
    decide (table.rankAt? config word = some rank)

theorem findResponse?_sound (table : Table length)
    (config rank : Nat) (gram : GramWord length)
    (response : TraceWord length)
    (hfound : findResponse? table config rank gram = some response) :
    Matches response.toList gram.toList ∧
      table.rankAt? config response = some rank := by
  have hselected := List.find?_some hfound
  have hmember := List.mem_of_find?_eq_some hfound
  exact ⟨(mem_matchingTraceWords_iff gram response).1 hmember,
    of_decide_eq_true hselected⟩

/-- Check that every active rank in one response vector is realized by an
actual word in the stated chromogram fiber. -/
def responseVectorWitnessBoolean (table : Table length)
    (responseVector : Nat) (gram : GramWord length) : Bool :=
  decide (responseVector < table.ranks.vectorCount) &&
    (List.range table.ranks.configCount).all fun config =>
      match table.ranks.rankAt? responseVector config with
      | none => true
      | some rank => (findResponse? table config rank gram).isSome

theorem responseVectorWitnessBoolean_sound (table : Table length)
    (responseVector : Nat) (gram : GramWord length)
    (hcheck : responseVectorWitnessBoolean table responseVector gram = true)
    (config rank : Nat) (hconfig : config < table.ranks.configCount)
    (hrank : table.ranks.rankAt? responseVector config = some rank) :
    ∃ response : TraceWord length,
      Matches response.toList gram.toList ∧
        table.rankAt? config response = some rank := by
  simp only [responseVectorWitnessBoolean, Bool.and_eq_true] at hcheck
  have hlocal := (List.all_eq_true.1 hcheck.2) config
    (List.mem_range.2 hconfig)
  simp [hrank] at hlocal
  obtain ⟨response, hresponse⟩ := Option.isSome_iff_exists.1 hlocal
  exact ⟨response,
    findResponse?_sound table config rank gram response hresponse⟩

def prependStep {length : Nat} (step : ChromogramStep)
    (gram : GramWord length) : GramWord (length + 1) :=
  List.Vector.cons step gram

@[simp] theorem gramWord_eq_iff {length : Nat}
    (left right : GramWord length) :
    left = right ↔ left.toList = right.toList :=
  List.Vector.toList_injective.eq_iff.symm

@[simp] theorem exists_lookup_toList_eq_iff
    (code : ResponseCode) (root rankVector : Nat)
    (gram : GramWord length) :
    (∃ candidate : GramWord length,
        code.lookup root candidate.toList = some rankVector ∧
          candidate.toList = gram.toList) ↔
      code.lookup root gram.toList = some rankVector := by
  constructor
  · rintro ⟨candidate, hlookup, heq⟩
    simpa [heq] using hlookup
  · intro hlookup
    exact ⟨gram, hlookup, rfl⟩

/-- Enumerate the rank-vector leaves of one fixed-height chromogram DAG. -/
def responseEntries : (length : Nat) → ResponseCode → Nat →
    List (GramWord length × Nat)
  | 0, code, root =>
      match code.nodeAt root with
      | .leaf rankVector => [(List.Vector.nil, rankVector)]
      | _ => []
  | length + 1, code, root =>
      match code.nodeAt root with
      | .node push skip popSame popOpposite =>
          (responseEntries length code push).map (fun entry =>
              (prependStep .push entry.1, entry.2)) ++
            (responseEntries length code skip).map (fun entry =>
              (prependStep .skip entry.1, entry.2)) ++
            (responseEntries length code popSame).map (fun entry =>
              (prependStep .popSame entry.1, entry.2)) ++
            (responseEntries length code popOpposite).map (fun entry =>
              (prependStep .popOpposite entry.1, entry.2))
      | _ => []

theorem mem_responseEntries_iff_lookup
    (code : ResponseCode) (root : Nat)
    (gram : GramWord length) (rankVector : Nat) :
    (gram, rankVector) ∈ responseEntries length code root ↔
      code.lookup root gram.toList = some rankVector := by
  induction length generalizing root with
  | zero =>
      have hgram : gram = List.Vector.nil := Subsingleton.elim _ _
      subst gram
      cases hnode : code.nodeAt root <;>
        simp [responseEntries, ResponseCode.lookup, hnode, eq_comm]
  | succ length ih =>
      rw [← List.Vector.cons_head_tail gram]
      cases hstep : gram.head <;>
        cases hnode : code.nodeAt root <;>
          simp [responseEntries, ResponseCode.lookup, hnode,
            ResponseNodeCode.child, prependStep, gramWord_eq_iff, ih]

/-- Validate response-rank witnesses at every occupied chromogram leaf. -/
def responseWitnessChecker (table : Table length)
    (code : ResponseCode) (root : Nat) : Bool :=
  (responseEntries length code root).all fun entry =>
    responseVectorWitnessBoolean table entry.2 entry.1

theorem responseWitnessChecker_sound (table : Table length)
    (code : ResponseCode) (root : Nat)
    (hchecker : responseWitnessChecker table code root = true)
    (gram : GramWord length) (responseVector : Nat)
    (hlookup : code.lookup root gram.toList = some responseVector)
    (config rank : Nat) (hconfig : config < table.ranks.configCount)
    (hrank : table.ranks.rankAt? responseVector config = some rank) :
    ∃ response : TraceWord length,
      Matches response.toList gram.toList ∧
        table.rankAt? config response = some rank := by
  apply responseVectorWitnessBoolean_sound table responseVector gram
  · exact (List.all_eq_true.1 hchecker) (gram, responseVector)
      ((mem_responseEntries_iff_lookup code root gram responseVector).2 hlookup)
  · exact hconfig
  · exact hrank

/-- The product check and witness check compose to an actual matching word of
strictly lower orbit rank, without storing a response pointer. -/
theorem exists_lower_response_of_checkers
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (table : Table length)
    (hranks : certificate.ranks = table.ranks)
    (hproduct : certificate.checker = true)
    (hwitness : responseWitnessChecker table certificate.responseCode
      certificate.responseRoot = true)
    (word : TraceWord length) (sourceVector config sourceRank : Nat)
    (haccepted : certificate.traceCode.lookup length certificate.sourceRoot
      word.toList = some sourceVector)
    (hconfig : config < table.ranks.configCount)
    (hsourceRank : table.ranks.rankAt? sourceVector config = some sourceRank)
    (gram : GramWord length)
    (hmatch : Matches word.toList gram.toList) :
    0 < sourceRank ∧
      ∃ response : TraceWord length, ∃ responseRank,
        Matches response.toList gram.toList ∧
          table.rankAt? config response = some responseRank ∧
            responseRank < sourceRank := by
  have hsourceRank' : certificate.ranks.rankAt? sourceVector config =
      some sourceRank := by simpa [hranks] using hsourceRank
  have hconfig' : config < certificate.ranks.configCount := by
    simpa [hranks] using hconfig
  obtain ⟨hpositive, responseVector, responseRank, hlookup,
      hresponseRank, hlower⟩ :=
    certificate_response_rank_lt_of_checker_true certificate hproduct word
      sourceVector config sourceRank haccepted hconfig' hsourceRank' gram hmatch
  have hresponseRank' : table.ranks.rankAt? responseVector config =
      some responseRank := by simpa [hranks] using hresponseRank
  obtain ⟨response, hmatches, hrank⟩ :=
    responseWitnessChecker_sound table certificate.responseCode
      certificate.responseRoot hwitness gram responseVector hlookup config
        responseRank hconfig hresponseRank'
  exact ⟨hpositive, response, responseRank, hmatches, hrank, hlower⟩

end ClassicalCertificateOrbitRankResponseSearch

end Mettapedia.GraphTheory.FourColor
