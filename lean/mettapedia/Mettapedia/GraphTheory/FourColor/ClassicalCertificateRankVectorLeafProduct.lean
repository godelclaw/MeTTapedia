import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankTransferClosure

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateRankVectorLeafProduct

open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitRankResponseSearch
open ClassicalCertificateOrbitRankTransferClosure
open ClassicalCertificatePackedRankVector
open ClassicalCertificateRankedKempe
open ClassicalCertificateRankVectorDag
open ClassicalCertificateRankVectorProduct
open ClassicalCertificateTraceTree

variable {length : Nat}

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-- Count the accepted leaves of a fixed-height trace DAG without
materializing their words. -/
def traceEntryCount : (height : Nat) → TraceCode → Nat → Nat
  | 0, code, root =>
      match code.nodeAt root with
      | .leaf _ => 1
      | _ => 0
  | height + 1, code, root =>
      match code.nodeAt root with
      | .node red blue purple =>
          traceEntryCount height code red +
            traceEntryCount height code blue +
              traceEntryCount height code purple
      | _ => 0

/-- The structural leaf count agrees with the extensional trace-entry
enumerator. -/
theorem traceEntries_length_eq_traceEntryCount
    (height : Nat) (code : TraceCode) (root : Nat) :
    (traceEntries height code root).length =
      traceEntryCount height code root := by
  induction height generalizing root with
  | zero =>
      cases hnode : code.nodeAt root <;>
        simp [traceEntries, traceEntryCount, hnode]
  | succ height ih =>
      cases hnode : code.nodeAt root <;>
        simp [traceEntries, traceEntryCount, hnode, ih, Nat.add_assoc]

/-- Compare one source rank vector with the response vector stored at a
matching chromogram leaf. -/
def leafResponseBoolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (sourceVector : Nat) (gram : Chromogram) : Bool :=
  match certificate.responseCode.lookup certificate.responseRoot gram with
  | none => false
  | some responseVector =>
      respondsBoolean certificate.ranks sourceVector responseVector

/-- Check every matching chromogram of one accepted source word. -/
def sourceEntryBoolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (entry : TraceWord length × Nat) : Bool :=
  (matchingChromograms entry.1.toList).all
    (leafResponseBoolean certificate entry.2)

/-- Extensional rank-product checker.  It enumerates only accepted source
leaves and their noncrossing chromograms; internal trie-product states are
not part of the certificate. -/
def checker
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length) :
    Bool :=
  (traceEntries length certificate.traceCode certificate.sourceRoot).all
    (sourceEntryBoolean certificate)

/-- Concatenate the first `blockCount` consecutive blocks of a list. -/
def consecutiveBlocks (entries : List α)
    (blockSize blockCount : Nat) : List α :=
  (List.range blockCount).flatMap fun block =>
    (entries.drop (block * blockSize)).take blockSize

/-- Consecutive blocks followed by the unconsumed suffix reconstruct the
original list. -/
theorem consecutiveBlocks_append_drop (entries : List α)
    (blockSize blockCount : Nat) :
    consecutiveBlocks entries blockSize blockCount ++
        entries.drop (blockCount * blockSize) = entries := by
  induction blockCount with
  | zero => simp [consecutiveBlocks]
  | succ blockCount ih =>
      rw [consecutiveBlocks, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      rw [List.append_assoc]
      have hdrop : entries.drop ((blockCount + 1) * blockSize) =
          (entries.drop (blockCount * blockSize)).drop blockSize := by
        rw [Nat.add_mul, one_mul, ← List.drop_drop]
      rw [hdrop, List.take_append_drop]
      exact ih

/-- Enough consecutive blocks cover a list exactly. -/
theorem consecutiveBlocks_eq_of_length_le (entries : List α)
    (blockSize blockCount : Nat)
    (hlength : entries.length ≤ blockCount * blockSize) :
    consecutiveBlocks entries blockSize blockCount = entries := by
  have hreconstruct :=
    consecutiveBlocks_append_drop entries blockSize blockCount
  rw [List.drop_eq_nil_of_le hlength, List.append_nil] at hreconstruct
  exact hreconstruct

/-- A bounded consecutive block of accepted source leaves. -/
def sourceEntryBlock
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (blockSize block : Nat) : List (TraceWord length × Nat) :=
  (traceEntries length certificate.traceCode certificate.sourceRoot).drop
      (block * blockSize) |>.take blockSize

/-- Check one bounded block of accepted source leaves. -/
def sourceEntryBlockBoolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (blockSize block : Nat) : Bool :=
  (sourceEntryBlock certificate blockSize block).all
    (sourceEntryBoolean certificate)

/-- The concatenation of a finite family of consecutive source blocks. -/
def blockedSourceEntries
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (blockSize blockCount : Nat) : List (TraceWord length × Nat) :=
  consecutiveBlocks
    (traceEntries length certificate.traceCode certificate.sourceRoot)
    blockSize blockCount

theorem blockedSourceEntries_eq_of_length_le
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (blockSize blockCount : Nat)
    (hlength :
      (traceEntries length certificate.traceCode
        certificate.sourceRoot).length ≤ blockCount * blockSize) :
    blockedSourceEntries certificate blockSize blockCount =
      traceEntries length certificate.traceCode certificate.sourceRoot :=
  consecutiveBlocks_eq_of_length_le _ _ _ hlength

theorem leafResponseBoolean_sound
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (sourceVector : Nat) (gram : Chromogram)
    (hcheck : leafResponseBoolean certificate sourceVector gram = true) :
    ∃ responseVector,
      certificate.responseCode.lookup certificate.responseRoot gram =
          some responseVector ∧
        respondsBoolean certificate.ranks sourceVector responseVector = true := by
  unfold leafResponseBoolean at hcheck
  split at hcheck
  · contradiction
  · rename_i responseVector hlookup
    exact ⟨responseVector, hlookup, hcheck⟩

/-- Recursive source-trie traversal carrying the already-read word in
reverse order.  Rank comparisons occur only at accepted source leaves. -/
def sourceTreeBoolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length) :
    Nat → Nat → List TraceSymbol → Bool
  | 0, sourceRoot, reversedPrefix =>
      match certificate.traceCode.nodeAt sourceRoot with
      | .leaf sourceVector =>
          (matchingChromograms reversedPrefix.reverse).all
            (leafResponseBoolean certificate sourceVector)
      | _ => true
  | remaining + 1, sourceRoot, reversedPrefix =>
      match certificate.traceCode.nodeAt sourceRoot with
      | .node red blue purple =>
          sourceTreeBoolean certificate remaining red
              (.red :: reversedPrefix) &&
            sourceTreeBoolean certificate remaining blue
              (.blue :: reversedPrefix) &&
            sourceTreeBoolean certificate remaining purple
              (.purple :: reversedPrefix)
      | _ => true

/-- One residual source-trie traversal state. -/
structure SourceState where
  remaining : Nat
  sourceRoot : Nat
  reversedPrefix : List TraceSymbol
  deriving DecidableEq, Repr

namespace SourceState

def boolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (state : SourceState) : Bool :=
  sourceTreeBoolean certificate state.remaining state.sourceRoot
    state.reversedPrefix

def child (state : SourceState) (sourceRoot : Nat)
    (symbol : TraceSymbol) : SourceState where
  remaining := state.remaining - 1
  sourceRoot := sourceRoot
  reversedPrefix := symbol :: state.reversedPrefix

end SourceState

/-- Expose the three exact children of a nonterminal source-trie state.
Terminal states retain themselves, while vacuous states have no obligations. -/
def expandSource
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (state : SourceState) : List SourceState :=
  match state.remaining with
  | 0 => [state]
  | _ + 1 =>
      match certificate.traceCode.nodeAt state.sourceRoot with
      | .node red blue purple =>
          [state.child red .red, state.child blue .blue,
            state.child purple .purple]
      | _ => []

theorem SourceState.boolean_eq_all_expandSource
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (state : SourceState) :
    state.boolean certificate =
      (expandSource certificate state).all (SourceState.boolean certificate) := by
  rcases state with ⟨remaining, sourceRoot, reversedPrefix⟩
  cases remaining with
  | zero => simp [SourceState.boolean, expandSource]
  | succ remaining =>
      cases hnode : certificate.traceCode.nodeAt sourceRoot <;>
        simp [SourceState.boolean, SourceState.child, expandSource,
          sourceTreeBoolean, hnode, Bool.and_assoc]

/-- Expand a source-trie state to a fixed prefix depth. -/
def sourceFrontier
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length) :
    Nat → SourceState → List SourceState
  | 0, state => [state]
  | depth + 1, state =>
      (expandSource certificate state).flatMap
        (sourceFrontier certificate depth)

theorem all_sourceFrontier_eq_boolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth : Nat) (state : SourceState) :
    (sourceFrontier certificate depth state).all
        (SourceState.boolean certificate) =
      state.boolean certificate := by
  induction depth generalizing state with
  | zero => simp [sourceFrontier]
  | succ depth ih =>
      rw [sourceFrontier, List.all_flatMap]
      simp only [ih]
      exact (state.boolean_eq_all_expandSource certificate).symm

def rootSourceState
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length) :
    SourceState where
  remaining := length
  sourceRoot := certificate.sourceRoot
  reversedPrefix := []

/-- A finite source prefix frontier has the same Boolean value as the full
source-trie traversal. -/
theorem rootSourceBoolean_eq_all_frontier
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth : Nat) :
    sourceTreeBoolean certificate length certificate.sourceRoot [] =
      (sourceFrontier certificate depth
        (rootSourceState certificate)).all
          (SourceState.boolean certificate) := by
  exact (all_sourceFrontier_eq_boolean certificate depth
    (rootSourceState certificate)).symm

/-- A successful recursive source traversal supplies an exact lower response
vector for every accepted suffix and every matching chromogram. -/
theorem sourceTreeBoolean_response
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (remaining sourceRoot sourceVector : Nat)
    (reversedPrefix : List TraceSymbol)
    (word : List TraceSymbol) (gram : Chromogram)
    (hwordLength : word.length = remaining)
    (hcheck : sourceTreeBoolean certificate remaining sourceRoot
      reversedPrefix = true)
    (haccepted : certificate.traceCode.lookup remaining sourceRoot word =
      some sourceVector)
    (hmatch : Matches (reversedPrefix.reverse ++ word) gram) :
    ∃ responseVector,
      certificate.responseCode.lookup certificate.responseRoot gram =
          some responseVector ∧
        respondsBoolean certificate.ranks sourceVector responseVector = true := by
  induction remaining generalizing sourceRoot reversedPrefix word with
  | zero =>
      cases word with
      | cons symbol word => simp at hwordLength
      | nil =>
          cases hnode : certificate.traceCode.nodeAt sourceRoot with
          | empty => simp [TraceCode.lookup, hnode] at haccepted
          | node red blue purple =>
              simp [TraceCode.lookup, hnode] at haccepted
          | leaf storedSourceVector =>
              have hsourceVector : storedSourceVector = sourceVector := by
                simpa [TraceCode.lookup, hnode] using haccepted
              subst storedSourceVector
              have hgramMem : gram ∈
                  matchingChromograms reversedPrefix.reverse :=
                (mem_matchingChromograms_iff reversedPrefix.reverse gram).2
                  (by simpa using hmatch)
              have hgramCheck :=
                (List.all_eq_true.1 (by
                  simpa [sourceTreeBoolean, hnode] using hcheck)) gram hgramMem
              exact leafResponseBoolean_sound certificate sourceVector gram
                hgramCheck
  | succ remaining ih =>
      cases word with
      | nil => simp at hwordLength
      | cons symbol word =>
          have htailLength : word.length = remaining :=
            Nat.succ.inj hwordLength
          cases hnode : certificate.traceCode.nodeAt sourceRoot with
          | empty => simp [TraceCode.lookup, hnode] at haccepted
          | leaf storedSourceVector =>
              simp [TraceCode.lookup, hnode] at haccepted
          | node red blue purple =>
              have hchecks :
                  (sourceTreeBoolean certificate remaining red
                      (.red :: reversedPrefix) = true ∧
                    sourceTreeBoolean certificate remaining blue
                      (.blue :: reversedPrefix) = true) ∧
                    sourceTreeBoolean certificate remaining purple
                      (.purple :: reversedPrefix) = true := by
                simpa [sourceTreeBoolean, hnode, Bool.and_eq_true] using hcheck
              cases symbol with
              | red =>
                  apply ih red (.red :: reversedPrefix) word htailLength
                    hchecks.1.1
                  · simpa [TraceCode.lookup, hnode] using haccepted
                  · simpa [List.reverse_cons, List.append_assoc] using hmatch
              | blue =>
                  apply ih blue (.blue :: reversedPrefix) word htailLength
                    hchecks.1.2
                  · simpa [TraceCode.lookup, hnode] using haccepted
                  · simpa [List.reverse_cons, List.append_assoc] using hmatch
              | purple =>
                  apply ih purple (.purple :: reversedPrefix) word htailLength
                    hchecks.2
                  · simpa [TraceCode.lookup, hnode] using haccepted
                  · simpa [List.reverse_cons, List.append_assoc] using hmatch

/-- Recursive source-trie validation proves the semantic rank-product
interface without retaining internal source/response product states. -/
theorem productValid_of_sourceTreeBoolean_true
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (hchecker : sourceTreeBoolean certificate length
      certificate.sourceRoot [] = true) :
    ProductValid certificate := by
  intro word sourceVector config sourceRank haccepted hconfig hsourceRank
    gram hmatch
  obtain ⟨responseVector, hresponseLookup, hresponds⟩ :=
    sourceTreeBoolean_response certificate length certificate.sourceRoot
      sourceVector [] word.toList gram.toList word.2 hchecker haccepted
        (by simpa using hmatch)
  have hlocal := respondsBoolean_sound certificate.ranks sourceVector
    responseVector hresponds
  obtain ⟨hpositive, responseRank, hresponseRank, hlower⟩ :=
    hlocal.2.2 config sourceRank hconfig hsourceRank
  exact ⟨hpositive, responseVector, responseRank, hresponseLookup,
    hresponseRank, hlower⟩

/-- Pointwise checks on a finite source prefix frontier prove semantic
rank-product validity. -/
theorem productValid_of_sourceFrontier
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth : Nat)
    (hfrontier : ∀ state,
      state ∈ sourceFrontier certificate depth
          (rootSourceState certificate) →
        state.boolean certificate = true) :
    ProductValid certificate := by
  apply productValid_of_sourceTreeBoolean_true certificate
  rw [rootSourceBoolean_eq_all_frontier certificate depth]
  exact List.all_eq_true.2 hfrontier

/-- A bounded consecutive block of a source prefix frontier. -/
def sourceFrontierBlock
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth blockSize block : Nat) : List SourceState :=
  (sourceFrontier certificate depth (rootSourceState certificate)).drop
      (block * blockSize) |>.take blockSize

def sourceFrontierBlockBoolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth blockSize block : Nat) : Bool :=
  (sourceFrontierBlock certificate depth blockSize block).all
    (SourceState.boolean certificate)

/-- Refine every state in one coarse source-frontier block by an additional
exact prefix depth. -/
def refinedSourceFrontierBlock
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth blockSize block refinementDepth : Nat) : List SourceState :=
  (sourceFrontierBlock certificate depth blockSize block).flatMap
    (sourceFrontier certificate refinementDepth)

/-- A bounded consecutive subblock of a refined source-frontier block. -/
def refinedSourceFrontierSubblock
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth blockSize block refinementDepth subblockSize subblock : Nat) :
    List SourceState :=
  (refinedSourceFrontierBlock certificate depth blockSize block
      refinementDepth).drop (subblock * subblockSize) |>.take subblockSize

def refinedSourceFrontierSubblockBoolean
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth blockSize block refinementDepth subblockSize subblock : Nat) :
    Bool :=
  (refinedSourceFrontierSubblock certificate depth blockSize block
      refinementDepth subblockSize subblock).all
    (SourceState.boolean certificate)

/-- Bounded checks of an exact refinement prove the original coarse block.
This permits large trie prefixes to be subdivided without changing the
semantic frontier or its coverage theorem. -/
theorem sourceFrontierBlockBoolean_of_refined_block_checkers
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth blockSize block refinementDepth subblockSize subblockCount : Nat)
    (hlength :
      (refinedSourceFrontierBlock certificate depth blockSize block
        refinementDepth).length ≤ subblockCount * subblockSize)
    (hblocks : ∀ subblock, subblock < subblockCount →
      refinedSourceFrontierSubblockBoolean certificate depth blockSize block
        refinementDepth subblockSize subblock = true) :
    sourceFrontierBlockBoolean certificate depth blockSize block = true := by
  have hcoverage := consecutiveBlocks_eq_of_length_le
    (refinedSourceFrontierBlock certificate depth blockSize block
      refinementDepth) subblockSize subblockCount hlength
  have hall :
      (refinedSourceFrontierBlock certificate depth blockSize block
        refinementDepth).all (SourceState.boolean certificate) = true := by
    rw [← hcoverage, consecutiveBlocks, List.all_flatMap]
    apply List.all_eq_true.2
    intro subblock hsubblock
    exact hblocks subblock (List.mem_range.1 hsubblock)
  rw [refinedSourceFrontierBlock, List.all_flatMap] at hall
  simp only [all_sourceFrontier_eq_boolean] at hall
  exact hall

/-- Bounded checks covering a source prefix frontier prove semantic
rank-product validity. -/
theorem productValid_of_sourceFrontier_block_checkers
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (depth blockSize blockCount : Nat)
    (hlength :
      (sourceFrontier certificate depth
        (rootSourceState certificate)).length ≤ blockCount * blockSize)
    (hblocks : ∀ block, block < blockCount →
      sourceFrontierBlockBoolean certificate depth blockSize block = true) :
    ProductValid certificate := by
  apply productValid_of_sourceFrontier certificate depth
  intro state hstate
  have hcoverage := consecutiveBlocks_eq_of_length_le
    (sourceFrontier certificate depth (rootSourceState certificate))
    blockSize blockCount hlength
  have hall :
      (sourceFrontier certificate depth
        (rootSourceState certificate)).all
          (SourceState.boolean certificate) = true := by
    rw [← hcoverage, consecutiveBlocks, List.all_flatMap]
    apply List.all_eq_true.2
    intro block hblock
    exact hblocks block (List.mem_range.1 hblock)
  exact (List.all_eq_true.1 hall) state hstate

/-- Leaf enumeration proves the same semantic pointwise rank descent as the
recursive trie-product checker. -/
theorem productValid_of_checker_true
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (hchecker : checker certificate = true) :
    ProductValid certificate := by
  intro word sourceVector config sourceRank haccepted hconfig hsourceRank
    gram hmatch
  have hentry : (word, sourceVector) ∈
      traceEntries length certificate.traceCode certificate.sourceRoot :=
    (mem_traceEntries_iff_lookup certificate.traceCode
      certificate.sourceRoot word sourceVector).2 haccepted
  have hsourceCheck : sourceEntryBoolean certificate
      (word, sourceVector) = true :=
    (List.all_eq_true.1 hchecker) (word, sourceVector) hentry
  have hgramMem : gram.toList ∈ matchingChromograms word.toList :=
    (mem_matchingChromograms_iff word.toList gram.toList).2 hmatch
  have hgramCheck :
      leafResponseBoolean certificate sourceVector gram.toList = true :=
    (List.all_eq_true.1 hsourceCheck) gram.toList hgramMem
  obtain ⟨responseVector, hresponseLookup, hresponds⟩ :=
    leafResponseBoolean_sound certificate sourceVector gram.toList hgramCheck
  have hlocal := respondsBoolean_sound certificate.ranks sourceVector
    responseVector hresponds
  obtain ⟨hpositive, responseRank, hresponseRank, hlower⟩ :=
    hlocal.2.2 config sourceRank hconfig hsourceRank
  exact ⟨hpositive, responseVector, responseRank, hresponseLookup,
    hresponseRank, hlower⟩

/-- All bounded block checks imply semantic product validity once their
concatenation is certified to cover the accepted source leaves exactly. -/
theorem productValid_of_block_checkers
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (blockSize blockCount : Nat)
    (hcoverage : blockedSourceEntries certificate blockSize blockCount =
      traceEntries length certificate.traceCode certificate.sourceRoot)
    (hblocks : ∀ block, block < blockCount →
      sourceEntryBlockBoolean certificate blockSize block = true) :
    ProductValid certificate := by
  apply productValid_of_checker_true certificate
  unfold checker
  rw [← hcoverage, blockedSourceEntries, consecutiveBlocks,
    List.all_flatMap]
  apply List.all_eq_true.2
  intro block hblock
  exact hblocks block (List.mem_range.1 hblock)

end ClassicalCertificateRankVectorLeafProduct

end Mettapedia.GraphTheory.FourColor
