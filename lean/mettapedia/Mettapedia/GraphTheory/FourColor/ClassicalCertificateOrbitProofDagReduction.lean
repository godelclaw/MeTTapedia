import Mettapedia.GraphTheory.FourColor.ClassicalCertificateProofDagReduction

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitProofDagReduction

open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateExactTraceEnumeration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateProofDagReduction
open ClassicalCertificateRankedKempe
open ClassicalCertificateReductionMetadata
open ClassicalCertificateTraceTree

/-- A color-orbit proof node is either an ordinary trace witness or a Kempe
chromogram step.  Response entries pack an earlier representative together
with the global color permutation giving the required spelling. -/
inductive RuleCode where
  | member (assignmentCode : Nat)
  | chromograms (responses : Array Nat)
  deriving DecidableEq, Repr

structure NodeCode where
  wordCode : Nat
  rule : RuleCode
  deriving DecidableEq, Repr

/-- A complete proof DAG modulo the six global permutations of the nonzero
Tait colors.  Contract targets are indexed only by the canonical spelling of
each color orbit. -/
structure Code where
  nodeCount : Nat
  nodeChunks : Array (Array NodeCode)
  contractTargets : ClassicalCertificateProofDagReduction.TargetTreeCode
  deriving DecidableEq, Repr

namespace Code

def nodeChunkSize : Nat := 128
def nodeBlockSize : Nat := 16
def nodeBlocksPerChunk : Nat := nodeChunkSize / nodeBlockSize

def nodeValueBound (code : Code) : Nat :=
  code.nodeChunks.size * nodeChunkSize

def nodeBlockCount (code : Code) : Nat :=
  code.nodeChunks.size * nodeBlocksPerChunk

def nodeAt? (code : Code) (index : Nat) : Option NodeCode :=
  (code.nodeChunks[index / nodeChunkSize]?).bind fun chunk =>
    chunk[index % nodeChunkSize]?

def nodeWord (length : Nat) (node : NodeCode) : TraceWord length :=
  ClassicalCertificateResponseDag.decodedTraceWord length node.wordCode

end Code

def wordIndexList (word : List TraceSymbol) : Nat :=
  word.foldl (fun index symbol => index * 3 + symbolDigit symbol) 0

/-- Canonical spelling of a global color orbit: the least base-three word
among its six global color permutations. -/
def canonicalWord (word : List TraceSymbol) : List TraceSymbol :=
  permutationCodes.foldl (fun best permutation =>
    let candidate := word.map permutation.apply
    if wordIndexList candidate < wordIndexList best then candidate else best)
    word

variable {metadata : ClassicalCertificateReductionMetadata.Code}

abbrev OrdinaryTrace
    (valid : ClassicalCertificateReductionMetadata.Valid metadata) :=
  ClassicalCertificateProofDagReduction.OrdinaryTrace valid

def responseTarget (packed : Nat) : Nat := packed / 6

def responsePermutation (packed : Nat) : PermutationCode :=
  match packed % 6 with
  | 0 => .identity
  | 1 => .swapRedBlue
  | 2 => .swapRedPurple
  | 3 => .swapBluePurple
  | 4 => .cycleRedBluePurple
  | _ => .cycleRedPurpleBlue

def ResponseTargetValid
    (code : Code) (index : Nat)
    (gram : GramWord (ring metadata).length)
    (packed : Nat) : Prop :=
  responseTarget packed < index ∧
    match code.nodeAt? (responseTarget packed) with
    | none => False
    | some targetNode =>
        Matches
          (permute (responsePermutation packed)
            (Code.nodeWord (ring metadata).length targetNode)).toList
          gram.toList

instance
    (code : Code) (index : Nat)
    (gram : GramWord (ring metadata).length)
    (packed : Nat) :
    Decidable (ResponseTargetValid code index gram packed) := by
  unfold ResponseTargetValid
  cases hnode : code.nodeAt? (responseTarget packed) with
  | none => infer_instance
  | some targetNode => infer_instance

def ChromogramResponsesValid
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat) : Prop :=
  let grams := matchingGramWords word
  responses.size = grams.length ∧
    ∀ offset : Fin grams.length,
      match responses[offset.val]? with
      | none => False
      | some packed =>
          ResponseTargetValid code index (grams.get offset) packed

instance
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat) :
    Decidable (ChromogramResponsesValid code index word responses) := by
  unfold ChromogramResponsesValid
  let grams := matchingGramWords word
  letI (offset : Fin grams.length) : Decidable (
      match responses[offset.val]? with
      | none => False
      | some packed =>
          ResponseTargetValid code index (grams.get offset) packed) := by
    cases hresponse : responses[offset.val]? with
    | none => infer_instance
    | some packed => infer_instance
  infer_instance

def NodeConditions
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (index : Nat) (node : NodeCode) : Prop :=
  let word := Code.nodeWord (ring metadata).length node
  match node.rule with
  | .member assignmentCode =>
      ClassicalCertificateProofDagReduction.OrdinaryWitnessValid
        valid word assignmentCode
  | .chromograms responses =>
      ChromogramResponsesValid code index word responses

instance
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (index : Nat) (node : NodeCode) :
    Decidable (NodeConditions valid code index node) := by
  unfold NodeConditions
  cases node.rule <;> infer_instance

def nodeEntryBoolean
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (index : Nat) : Bool :=
  if index < code.nodeCount then
    match code.nodeAt? index with
    | none => false
    | some node => decide (NodeConditions valid code index node)
  else true

def nodeBlockBoolean
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (block : Nat) : Bool :=
  (List.range Code.nodeBlockSize).all fun offset =>
    nodeEntryBoolean valid code (block * Code.nodeBlockSize + offset)

def nodeChecker
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) : Bool :=
  decide (code.nodeCount ≤ code.nodeValueBound) &&
    (List.range code.nodeBlockCount).all (nodeBlockBoolean valid code)

theorem nodeConditions_of_checker_true
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (hchecker : nodeChecker valid code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    NodeConditions valid code index node := by
  have hparts :
      decide (code.nodeCount ≤ code.nodeValueBound) = true ∧
        (List.range code.nodeBlockCount).all
          (nodeBlockBoolean valid code) = true := by
    simpa [nodeChecker] using hchecker
  have hbound : index < code.nodeValueBound :=
    Nat.lt_of_lt_of_le hindex (of_decide_eq_true hparts.1)
  have hblock : index / Code.nodeBlockSize < code.nodeBlockCount := by
    simp only [Code.nodeBlockSize, Code.nodeBlockCount,
      Code.nodeBlocksPerChunk, Code.nodeChunkSize,
      Code.nodeValueBound] at hbound ⊢
    omega
  have hblockValid := (List.all_eq_true.1 hparts.2)
    (index / Code.nodeBlockSize) (List.mem_range.2 hblock)
  have hoffset : index % Code.nodeBlockSize < Code.nodeBlockSize :=
    Nat.mod_lt _ (by decide)
  have hentry := (List.all_eq_true.1 hblockValid)
    (index % Code.nodeBlockSize) (List.mem_range.2 hoffset)
  have hindexEq : index / Code.nodeBlockSize * Code.nodeBlockSize +
      index % Code.nodeBlockSize = index := by
    simpa [Nat.mul_comm] using Nat.div_add_mod index Code.nodeBlockSize
  have hentry' : nodeEntryBoolean valid code index = true := by
    simpa [nodeBlockBoolean, hindexEq] using hentry
  simpa [nodeEntryBoolean, hindex, hnode] using hentry'

def responseWord
    (code : Code) (word : TraceWord (ring metadata).length)
    (responses : Array Nat)
    (gram : GramWord (ring metadata).length) :
    TraceWord (ring metadata).length :=
  let offset := (matchingGramWords word).idxOf gram
  match responses[offset]? with
  | none => word
  | some packed =>
      match code.nodeAt? (responseTarget packed) with
      | none => word
      | some targetNode =>
          permute (responsePermutation packed)
            (Code.nodeWord (ring metadata).length targetNode)

@[simp] theorem inverse_permute (permutation : PermutationCode)
    {length : Nat} (word : TraceWord length) :
    permute permutation.inverse (permute permutation word) = word := by
  apply Subtype.ext
  change List.map permutation.inverse.apply
      (List.map permutation.apply word.toList) = word.toList
  rw [List.map_map]
  have hcomposition :
      permutation.inverse.apply ∘ permutation.apply = id := by
    funext symbol
    cases permutation <;> cases symbol <;> rfl
  simp [hcomposition]

theorem exists_response_of_valid
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat)
    (hvalid : ChromogramResponsesValid code index word responses)
    (gram : GramWord (ring metadata).length)
    (hmem : gram ∈ matchingGramWords word) :
    ∃ packed targetNode,
      responses[(matchingGramWords word).idxOf gram]? = some packed ∧
        code.nodeAt? (responseTarget packed) = some targetNode ∧
          responseTarget packed < index ∧
            Matches
              (permute (responsePermutation packed)
                (Code.nodeWord (ring metadata).length targetNode)).toList
              gram.toList := by
  let grams := matchingGramWords word
  have hvalid' : responses.size = grams.length ∧
      ∀ offset : Fin grams.length,
        match responses[offset.val]? with
        | none => False
        | some packed =>
            ResponseTargetValid code index (grams.get offset) packed := by
    simpa [ChromogramResponsesValid, grams] using hvalid
  have hoffset : grams.idxOf gram < grams.length :=
    List.idxOf_lt_length_of_mem (by simpa [grams] using hmem)
  let offset : Fin grams.length := ⟨grams.idxOf gram, hoffset⟩
  have hgram : grams.get offset = gram := by
    simp [offset]
  have hentry := hvalid'.2 offset
  cases hresponse : responses[offset.val]? with
  | none => simp [hresponse] at hentry
  | some packed =>
      cases hnode : code.nodeAt? (responseTarget packed) with
      | none =>
          simp [hresponse, ResponseTargetValid, hnode] at hentry
      | some targetNode =>
          rw [hgram] at hentry
          have hlocal : responseTarget packed < index ∧
              Matches
                (permute (responsePermutation packed)
                  (Code.nodeWord (ring metadata).length targetNode)).toList
                gram.toList := by
            simpa [hresponse, ResponseTargetValid, hnode] using hentry
          exact ⟨packed, targetNode, rfl, hnode, hlocal⟩

private def gramWordOfMatch
    (word : TraceWord (ring metadata).length)
    (gram : Chromogram) (hmatch : Matches word.toList gram) :
    GramWord (ring metadata).length :=
  ⟨gram, by simpa using hmatch.length_eq.symm⟩

/-- Every checked orbit node denotes a genuine finite Kempe co-closure
derivation.  Shared response permutations recover the exact spelling needed
by each chromogram. -/
theorem derivation_of_node
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (hchecker : nodeChecker valid code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    CoclosureDerivation (OrdinaryTrace valid)
      (Code.nodeWord (ring metadata).length node).toList := by
  induction index using Nat.strong_induction_on generalizing node with
  | h index ih =>
      have hconditions := nodeConditions_of_checker_true valid code hchecker
        index hindex node hnode
      let word := Code.nodeWord (ring metadata).length node
      cases hrule : node.rule with
      | member assignmentCode =>
          have hwitness :
              ClassicalCertificateProofDagReduction.OrdinaryWitnessValid
                valid word assignmentCode := by
            simpa [NodeConditions, word, hrule] using hconditions
          exact .member
            (ClassicalCertificateProofDagReduction.ordinaryTrace_of_witness
              valid word assignmentCode hwitness)
      | chromograms responses =>
          have hlocal :
              ChromogramResponsesValid code index word responses := by
            simpa [NodeConditions, word, hrule] using hconditions
          refine .chromograms
            (fun gram hmatch =>
              (responseWord code word responses
                (gramWordOfMatch word gram hmatch)).toList) ?_ ?_
          · intro gram hmatch
            let fixedGram := gramWordOfMatch word gram hmatch
            have hmem : fixedGram ∈ matchingGramWords word :=
              mem_matchingGramWords word fixedGram (by
                simpa [fixedGram, gramWordOfMatch] using hmatch)
            obtain ⟨packed, targetNode, hresponseCode,
                htargetNode, _htarget, hmatches⟩ :=
              exists_response_of_valid code index word responses hlocal
                fixedGram hmem
            have hresponse : responseWord code word responses fixedGram =
                permute (responsePermutation packed)
                  (Code.nodeWord (ring metadata).length targetNode) := by
              simp [responseWord, hresponseCode, htargetNode]
            rw [hresponse]
            simpa [fixedGram, gramWordOfMatch] using hmatches
          · intro gram hmatch
            let fixedGram := gramWordOfMatch word gram hmatch
            have hmem : fixedGram ∈ matchingGramWords word :=
              mem_matchingGramWords word fixedGram (by
                simpa [fixedGram, gramWordOfMatch] using hmatch)
            obtain ⟨packed, targetNode, hresponseCode,
                htargetNode, htarget, _hmatches⟩ :=
              exists_response_of_valid code index word responses hlocal
                fixedGram hmem
            have htargetCount : responseTarget packed < code.nodeCount :=
              Nat.lt_trans htarget hindex
            have hderivation :=
              ih (responseTarget packed) htarget htargetCount targetNode
                htargetNode
            have hpermuted : CoclosureDerivation (OrdinaryTrace valid)
                (permute (responsePermutation packed)
                  (Code.nodeWord (ring metadata).length targetNode)).toList := by
              apply CoclosureDerivation.permutation
                (responsePermutation packed).inverse.toEquiv
              simpa [← toList_permute, inverse_permute] using hderivation
            have hresponse : responseWord code word responses fixedGram =
                permute (responsePermutation packed)
                  (Code.nodeWord (ring metadata).length targetNode) := by
              simp [responseWord, hresponseCode, htargetNode]
            simpa [fixedGram, hresponse] using hpermuted

theorem kempeCoclosure_of_node
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (hchecker : nodeChecker valid code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    KempeCoclosure (OrdinaryTrace valid)
      (Code.nodeWord (ring metadata).length node).toList :=
  (derivation_of_node valid code hchecker index hindex node hnode).sound

def OrbitTargetValid (length : Nat) (code : Code)
    (word : List TraceSymbol) (target : Nat) : Prop :=
  target < code.nodeCount ∧
    match code.nodeAt? target with
    | none => False
    | some targetNode =>
        ∃ permutation : PermutationCode,
          (permute permutation (Code.nodeWord length targetNode)).toList = word

instance (length : Nat) (code : Code)
    (word : List TraceSymbol) (target : Nat) :
    Decidable (OrbitTargetValid length code word target) := by
  unfold OrbitTargetValid
  cases hnode : code.nodeAt? target with
  | none => infer_instance
  | some targetNode => infer_instance

/-- Check an exact contract word through the one stored leaf for its global
color orbit. -/
def targetBoolean (length : Nat) (code : Code)
    (word : List TraceSymbol) : Bool :=
  match code.contractTargets.lookup (canonicalWord word) with
  | none => false
  | some target => decide (OrbitTargetValid length code word target)

theorem orbitTargetValid_of_targetBoolean_true
    (length : Nat) (code : Code) (word : List TraceSymbol)
    (hcheck : targetBoolean length code word = true) :
    ∃ target, code.contractTargets.lookup (canonicalWord word) = some target ∧
      OrbitTargetValid length code word target := by
  unfold targetBoolean at hcheck
  cases hlookup : code.contractTargets.lookup (canonicalWord word) with
  | none => simp [hlookup] at hcheck
  | some target =>
      exact ⟨target, rfl,
        of_decide_eq_true (by simpa [hlookup] using hcheck)⟩

theorem contractWord_reduces
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (hnodeChecker : nodeChecker valid code = true)
    (word : List TraceSymbol)
    (htarget : targetBoolean (ring metadata).length code word = true) :
    KempeCoclosure (OrdinaryTrace valid) word := by
  obtain ⟨target, _hlookup, htargetValid⟩ :=
    orbitTargetValid_of_targetBoolean_true
      (ring metadata).length code word htarget
  obtain ⟨htarget, htargetLocal⟩ := htargetValid
  cases hnode : code.nodeAt? target with
  | none => simp [hnode] at htargetLocal
  | some node =>
      obtain ⟨permutation, hword⟩ := by
        simpa [hnode] using htargetLocal
      have hderivation := derivation_of_node valid code hnodeChecker
        target htarget node hnode
      have hwordDerivation : CoclosureDerivation (OrdinaryTrace valid) word := by
        rw [← hword]
        apply CoclosureDerivation.permutation permutation.inverse.toEquiv
        simpa [← toList_permute, inverse_permute] using hderivation
      exact hwordDerivation.sound

theorem contractTrace_reduces
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code)
    (search : ClassicalCertificateContractColorSearch.Certificate
      metadata.components.componentCount)
    (hnodeChecker : nodeChecker valid code = true)
    (hsearch : search.checkerBy valid.componentsValid (ring metadata)
      (targetBoolean (ring metadata).length code) = true)
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap valid.partitionValid) (contract metadata)
        (ring metadata) (word.map TraceSymbol.toColor)) :
    KempeCoclosure (OrdinaryTrace valid) word := by
  obtain ⟨assignment, hassignment, hword⟩ :=
    (contractRingTrace_iff_exists_assignment valid.partitionValid
      (contract metadata) (ring metadata)
        (word.map TraceSymbol.toColor)).1 hcontract
  have htarget := search.acceptsBy_of_contractWord valid.componentsValid
    (ring metadata) (targetBoolean (ring metadata).length code) hsearch
      valid.reverseBoundaryCycle valid.contractAvoidsBoundary
        assignment hassignment word hword
  exact contractWord_reduces valid code hnodeChecker word htarget

theorem contractRingTrace_reduces
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code)
    (search : ClassicalCertificateContractColorSearch.Certificate
      metadata.components.componentCount)
    (hnodeChecker : nodeChecker valid code = true)
    (hsearch : search.checkerBy valid.componentsValid (ring metadata)
      (targetBoolean (ring metadata).length code) = true)
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap valid.partitionValid) (contract metadata)
        (ring metadata) boundaryTrace) :
    ∃ word : List TraceSymbol,
      word.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure (OrdinaryTrace valid) word := by
  obtain ⟨assignment, hassignment, hboundary⟩ :=
    (contractRingTrace_iff_exists_assignment valid.partitionValid
      (contract metadata) (ring metadata) boundaryTrace).1 hcontract
  let word :=
    ClassicalCertificateContractColorSearch.symbolTraceOfAssignment
      valid.partitionValid (ring metadata) assignment
  have hword : word.map TraceSymbol.toColor = boundaryTrace := by
    rw [ClassicalCertificateContractColorSearch.symbolTraceOfAssignment_toColor
      valid.partitionValid (contract metadata) (ring metadata) assignment
        hassignment valid.reverseBoundaryCycle valid.contractAvoidsBoundary]
    exact hboundary.symm
  refine ⟨word, hword,
    contractTrace_reduces valid code search hnodeChecker hsearch word ?_⟩
  simpa only [hword] using hcontract

end ClassicalCertificateOrbitProofDagReduction

end Mettapedia.GraphTheory.FourColor
