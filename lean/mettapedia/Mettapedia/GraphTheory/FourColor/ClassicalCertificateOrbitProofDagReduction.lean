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
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat)
    (gram : Chromogram)
    (packed : Nat) : Prop :=
  responseTarget packed < index ∧
    match code.nodeAt? (responseTarget packed) with
    | none => False
    | some targetNode =>
        Matches
          (permute (responsePermutation packed)
            (Code.nodeWord (ring metadata).length targetNode)).toList
          gram

instance
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat)
    (gram : Chromogram)
    (packed : Nat) :
    Decidable (ResponseTargetValid metadata code index gram packed) := by
  unfold ResponseTargetValid
  cases hnode : code.nodeAt? (responseTarget packed) with
  | none => infer_instance
  | some targetNode => infer_instance

/-- Pointwise semantic validity for a list of chromograms and its aligned
packed responses. -/
def ResponseListValid
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat) :
    List Chromogram → List Nat → Prop
  | [], [] => True
  | gram :: grams, packed :: responses =>
      ResponseTargetValid metadata code index gram packed ∧
        ResponseListValid metadata code index grams responses
  | _, _ => False

instance
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat)
    (grams : List Chromogram) (responses : List Nat) :
    Decidable (ResponseListValid metadata code index grams responses) := by
  induction grams generalizing responses with
  | nil => cases responses <;> simp only [ResponseListValid] <;> infer_instance
  | cons gram grams ih =>
      cases responses with
      | nil => simp only [ResponseListValid]; infer_instance
      | cons packed responses =>
          simp only [ResponseListValid]
          letI := ih responses
          infer_instance

def ChromogramResponsesValid
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat) : Prop :=
  ResponseListValid metadata code index (matchingChromograms word.toList)
    responses.toList

instance
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat) :
    Decidable (ChromogramResponsesValid code index word responses) := by
  unfold ChromogramResponsesValid
  infer_instance

/-- Direct Boolean response check.  It traverses the raw chromogram list,
avoiding proof-bearing vectors in reflected computations. -/
def responseTargetBoolean
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat) (gram : Chromogram)
    (packed : Nat) : Bool :=
  decide (responseTarget packed < index) &&
    match code.nodeAt? (responseTarget packed) with
    | none => false
    | some targetNode =>
        chromogramMatches []
          (permute (responsePermutation packed)
            (Code.nodeWord (ring metadata).length targetNode)).toList
          gram

def responseListBoolean
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat) :
    List Chromogram → List Nat → Bool
  | [], [] => true
  | gram :: grams, packed :: responses =>
      responseTargetBoolean metadata code index gram packed &&
        responseListBoolean metadata code index grams responses
  | _, _ => false

def chromogramResponsesBoolean
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat) : Bool :=
  responseListBoolean metadata code index (matchingChromograms word.toList)
    responses.toList

theorem responseTargetValid_of_boolean_true
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat) (gram : Chromogram)
    (packed : Nat)
    (hcheck : responseTargetBoolean metadata code index gram packed = true) :
    ResponseTargetValid metadata code index gram packed := by
  unfold responseTargetBoolean at hcheck
  simp only [Bool.and_eq_true] at hcheck
  refine ⟨of_decide_eq_true hcheck.1, ?_⟩
  cases hnode : code.nodeAt? (responseTarget packed) with
  | none => simp [hnode] at hcheck
  | some targetNode =>
      simpa [hnode, Matches] using hcheck.2

theorem responseListValid_of_boolean_true
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat)
    (grams : List Chromogram) (responses : List Nat)
    (hcheck : responseListBoolean metadata code index grams responses = true) :
    ResponseListValid metadata code index grams responses := by
  induction grams generalizing responses with
  | nil =>
      cases responses with
      | nil => trivial
      | cons packed responses => simp [responseListBoolean] at hcheck
  | cons gram grams ih =>
      cases responses with
      | nil => simp [responseListBoolean] at hcheck
      | cons packed responses =>
          simp only [responseListBoolean, Bool.and_eq_true] at hcheck
          exact ⟨responseTargetValid_of_boolean_true metadata code index gram
              packed hcheck.1,
            ih responses hcheck.2⟩

theorem chromogramResponsesValid_of_boolean_true
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat)
    (hcheck : chromogramResponsesBoolean code index word responses = true) :
    ChromogramResponsesValid code index word responses := by
  exact responseListValid_of_boolean_true metadata code index
    (matchingChromograms word.toList) responses.toList hcheck

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
    | some node =>
        let word := Code.nodeWord (ring metadata).length node
        match node.rule with
        | .member assignmentCode =>
            decide
              (ClassicalCertificateProofDagReduction.OrdinaryWitnessValid
                valid word assignmentCode)
        | .chromograms responses =>
            chromogramResponsesBoolean code index word responses
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
  let word := Code.nodeWord (ring metadata).length node
  cases hrule : node.rule with
  | member assignmentCode =>
      have hwitness :
          ClassicalCertificateProofDagReduction.OrdinaryWitnessValid
            valid word assignmentCode :=
        of_decide_eq_true (by
          simpa [nodeEntryBoolean, hindex, hnode, word, hrule] using hentry')
      simpa [NodeConditions, word, hrule] using hwitness
  | chromograms responses =>
      have hresponses :
          chromogramResponsesBoolean code index word responses = true := by
        simpa [nodeEntryBoolean, hindex, hnode, word, hrule] using hentry'
      have hvalid := chromogramResponsesValid_of_boolean_true
        code index word responses hresponses
      simpa [NodeConditions, word, hrule] using hvalid

def responseWord
    (code : Code) (word : TraceWord (ring metadata).length)
    (responses : Array Nat)
    (gram : Chromogram) :
    TraceWord (ring metadata).length :=
  let offset := (matchingChromograms word.toList).idxOf gram
  match responses.toList[offset]? with
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

theorem exists_response_of_list_valid
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (code : Code) (index : Nat)
    (grams : List Chromogram) (responses : List Nat)
    (hvalid : ResponseListValid metadata code index grams responses)
    (gram : Chromogram) (hmem : gram ∈ grams) :
    ∃ packed targetNode,
      responses[grams.idxOf gram]? = some packed ∧
        code.nodeAt? (responseTarget packed) = some targetNode ∧
          responseTarget packed < index ∧
            Matches
              (permute (responsePermutation packed)
                (Code.nodeWord (ring metadata).length targetNode)).toList
              gram := by
  induction grams generalizing responses with
  | nil => simp at hmem
  | cons head grams ih =>
      cases responses with
      | nil => simp [ResponseListValid] at hvalid
      | cons packed responses =>
          have hparts :
              ResponseTargetValid metadata code index head packed ∧
                ResponseListValid metadata code index grams responses := by
            simpa [ResponseListValid] using hvalid
          by_cases heq : gram = head
          · subst gram
            cases hnode : code.nodeAt? (responseTarget packed) with
            | none => simp [ResponseTargetValid, hnode] at hparts
            | some targetNode =>
                have hlocal : responseTarget packed < index ∧
                    Matches
                      (permute (responsePermutation packed)
                        (Code.nodeWord (ring metadata).length
                          targetNode)).toList
                      head := by
                  simpa [ResponseTargetValid, hnode] using hparts.1
                exact ⟨packed, targetNode, by simp, hnode, hlocal⟩
          · have htail : gram ∈ grams := by
              simpa [heq] using hmem
            obtain ⟨targetPacked, targetNode, hresponse,
                htargetNode, htarget, hmatches⟩ :=
              ih responses hparts.2 htail
            refine ⟨targetPacked, targetNode, ?_, htargetNode,
              htarget, hmatches⟩
            simpa [List.idxOf_cons_ne grams (Ne.symm heq)] using hresponse

theorem exists_response_of_valid
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length)
    (responses : Array Nat)
    (hvalid : ChromogramResponsesValid code index word responses)
    (gram : Chromogram)
    (hmem : gram ∈ matchingChromograms word.toList) :
    ∃ packed targetNode,
      responses.toList[(matchingChromograms word.toList).idxOf gram]? =
          some packed ∧
        code.nodeAt? (responseTarget packed) = some targetNode ∧
          responseTarget packed < index ∧
            Matches
              (permute (responsePermutation packed)
                (Code.nodeWord (ring metadata).length targetNode)).toList
              gram := by
  exact exists_response_of_list_valid metadata code index
    (matchingChromograms word.toList) responses.toList hvalid gram hmem

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
            (fun gram _hmatch =>
              (responseWord code word responses gram).toList) ?_ ?_
          · intro gram hmatch
            have hmem : gram ∈ matchingChromograms word.toList :=
              (mem_matchingChromograms_iff word.toList gram).2 hmatch
            obtain ⟨packed, targetNode, hresponseCode,
                htargetNode, _htarget, hmatches⟩ :=
              exists_response_of_valid code index word responses hlocal
                gram hmem
            have hresponse : responseWord code word responses gram =
                permute (responsePermutation packed)
                  (Code.nodeWord (ring metadata).length targetNode) := by
              simp [responseWord, hresponseCode, htargetNode]
            rw [hresponse]
            exact hmatches
          · intro gram hmatch
            have hmem : gram ∈ matchingChromograms word.toList :=
              (mem_matchingChromograms_iff word.toList gram).2 hmatch
            obtain ⟨packed, targetNode, hresponseCode,
                htargetNode, htarget, _hmatches⟩ :=
              exists_response_of_valid code index word responses hlocal
                gram hmem
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
            have hresponse : responseWord code word responses gram =
                permute (responsePermutation packed)
                  (Code.nodeWord (ring metadata).length targetNode) := by
              simp [responseWord, hresponseCode, htargetNode]
            simpa [hresponse] using hpermuted

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
