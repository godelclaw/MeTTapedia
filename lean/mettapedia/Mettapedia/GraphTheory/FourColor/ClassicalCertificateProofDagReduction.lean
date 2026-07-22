import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedLayeredKempe
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateLayeredReduction

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateProofDagReduction

open ClassicalCertificateExactTraceEnumeration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateLayeredReduction
open ClassicalCertificateRankedKempe
open ClassicalCertificateReductionMetadata
open ClassicalCertificateResponseDag
open ClassicalCertificateTraceTree
open ClassicalCertificateTreeRankedKempe

/-- One compositional proof step for a fixed boundary word.  Every recursive
step names an earlier proof node. -/
inductive RuleCode where
  | member (assignmentCode : Nat)
  | permutation (permutation : PermutationCode) (target : Nat)
  | chromograms (targets : Array Nat)
  deriving DecidableEq, Repr

/-- A boundary word and its local proof rule. -/
structure NodeCode where
  wordCode : Nat
  rule : RuleCode
  deriving DecidableEq, Repr

/-- A ternary boundary trie whose accepted leaves carry proof-node indices. -/
inductive TargetTreeCode where
  | empty
  | leaf (target : Nat)
  | node (red blue purple : TargetTreeCode)
  deriving DecidableEq, Repr

namespace TargetTreeCode

def lookup : TargetTreeCode → List TraceSymbol → Option Nat
  | .empty, _ => none
  | .leaf target, [] => some target
  | .leaf _, _ :: _ => none
  | .node _ _ _, [] => none
  | .node red _ _, .red :: word => red.lookup word
  | .node _ blue _, .blue :: word => blue.lookup word
  | .node _ _ purple, .purple :: word => purple.lookup word

end TargetTreeCode

/-- The complete proof DAG for one checked configuration. -/
structure Code where
  nodeCount : Nat
  nodeChunks : Array (Array NodeCode)
  contractTargets : TargetTreeCode
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
  decodedTraceWord length node.wordCode

end Code

namespace TargetTreeCode

def LeafValid (length : Nat) (code : Code)
    (path : List TraceSymbol) (target : Nat) : Prop :=
  target < code.nodeCount ∧
    match code.nodeAt? target with
    | none => False
    | some proofNode => (Code.nodeWord length proofNode).toList = path

instance (length : Nat) (code : Code)
    (path : List TraceSymbol) (target : Nat) :
    Decidable (LeafValid length code path target) := by
  unfold LeafValid
  cases hnode : code.nodeAt? target with
  | none => infer_instance
  | some proofNode => infer_instance

def targetBoolean (length : Nat) (code : Code)
    (word : List TraceSymbol) : Bool :=
  match code.contractTargets.lookup word with
  | none => false
  | some target => decide (LeafValid length code word target)

theorem leafValid_of_targetBoolean_true (length : Nat) (code : Code)
    (word : List TraceSymbol) (hcheck : targetBoolean length code word = true) :
    ∃ target, code.contractTargets.lookup word = some target ∧
      LeafValid length code word target := by
  unfold targetBoolean at hcheck
  cases hlookup : code.contractTargets.lookup word with
  | none => simp [hlookup] at hcheck
  | some target =>
      exact ⟨target, rfl,
        of_decide_eq_true (by simpa [hlookup] using hcheck)⟩

end TargetTreeCode

/-- Decode the big-endian base-four assignment stored in a member node. -/
def decodedAssignment (faceCount assignmentCode : Nat) :
    Fin faceCount → Color := fun face =>
  HypermapCode.decodeColor
    ((assignmentCode / 4 ^ (faceCount - 1 - face.val)) % 4)

variable {metadata : ClassicalCertificateReductionMetadata.Code}

def OrdinaryTrace
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (word : List TraceSymbol) : Prop :=
  FiniteHypermap.RingTrace
    (checkedHypermap valid.partitionValid) (ring metadata)
      (word.map TraceSymbol.toColor)

def OrdinaryWitnessValid
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (word : TraceWord (ring metadata).length)
    (assignmentCode : Nat) : Prop :=
  let assignment := decodedAssignment metadata.partition.faceCount assignmentCode
  IsProperAssignment valid.partitionValid assignment ∧
    word.toList.map TraceSymbol.toColor =
      ringTraceOfAssignment valid.partitionValid (ring metadata) assignment

instance
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (word : TraceWord (ring metadata).length) (assignmentCode : Nat) :
    Decidable (OrdinaryWitnessValid valid word assignmentCode) := by
  unfold OrdinaryWitnessValid
  infer_instance

def ChromogramTargetValid
    (code : Code) (index : Nat)
    (gram : GramWord (ring metadata).length) (target : Nat) : Prop :=
  target < index ∧
    match code.nodeAt? target with
    | none => False
    | some targetNode =>
        Matches
          (Code.nodeWord (ring metadata).length targetNode).toList
          gram.toList

instance
    (code : Code) (index : Nat)
    (gram : GramWord (ring metadata).length) (target : Nat) :
    Decidable (ChromogramTargetValid code index gram target) := by
  unfold ChromogramTargetValid
  cases hnode : code.nodeAt? target with
  | none => infer_instance
  | some targetNode => infer_instance

def ChromogramTargetsValid
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length) (targets : Array Nat) : Prop :=
  let grams := matchingGramWords word
  targets.size = grams.length ∧
    ∀ offset : Fin grams.length,
      match targets[offset.val]? with
      | none => False
      | some target =>
          ChromogramTargetValid code index (grams.get offset) target

instance
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length) (targets : Array Nat) :
    Decidable (ChromogramTargetsValid code index word targets) := by
  unfold ChromogramTargetsValid
  let grams := matchingGramWords word
  letI (offset : Fin grams.length) : Decidable (
      match targets[offset.val]? with
      | none => False
      | some target =>
          ChromogramTargetValid code index (grams.get offset) target) := by
    cases htarget : targets[offset.val]? with
    | none => infer_instance
    | some target => infer_instance
  infer_instance

def NodeConditions
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (index : Nat) (node : NodeCode) : Prop :=
  let word := Code.nodeWord (ring metadata).length node
  match node.rule with
  | .member assignmentCode =>
      OrdinaryWitnessValid valid word assignmentCode
  | .permutation permutation target =>
      target < index ∧
        match code.nodeAt? target with
        | none => False
        | some targetNode =>
            Code.nodeWord (ring metadata).length targetNode =
              permute permutation word
  | .chromograms targets =>
      ChromogramTargetsValid code index word targets

instance
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (index : Nat) (node : NodeCode) :
    Decidable (NodeConditions valid code index node) := by
  unfold NodeConditions
  cases node.rule with
  | member assignmentCode => infer_instance
  | permutation permutation target =>
      cases hnode : code.nodeAt? target with
      | none =>
          simp only [hnode]
          infer_instance
      | some targetNode =>
          simp only [hnode]
          infer_instance
  | chromograms targets => infer_instance

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

theorem ordinaryTrace_of_witness
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (word : TraceWord (ring metadata).length) (assignmentCode : Nat)
    (hwitness : OrdinaryWitnessValid valid word assignmentCode) :
    OrdinaryTrace valid word.toList := by
  exact (ringTrace_iff_exists_assignment valid.partitionValid
    (ring metadata) _).2
      ⟨decodedAssignment metadata.partition.faceCount assignmentCode,
        hwitness.1, hwitness.2⟩

def responseWord (code : Code) (length : Nat) (word : TraceWord length)
    (targets : Array Nat) (gram : GramWord length) : TraceWord length :=
  let offset := (matchingGramWords word).idxOf gram
  match targets[offset]? with
  | none => decodedTraceWord length 0
  | some target =>
      match code.nodeAt? target with
      | none => decodedTraceWord length 0
      | some node => Code.nodeWord length node

theorem exists_chromogramTarget_of_valid
    (code : Code) (index : Nat)
    (word : TraceWord (ring metadata).length) (targets : Array Nat)
    (hvalid : ChromogramTargetsValid code index word targets)
    (gram : GramWord (ring metadata).length)
    (hmem : gram ∈ matchingGramWords word) :
    ∃ target targetNode,
      targets[(matchingGramWords word).idxOf gram]? = some target ∧
        code.nodeAt? target = some targetNode ∧
          target < index ∧
            Matches
              (Code.nodeWord (ring metadata).length targetNode).toList
              gram.toList := by
  let grams := matchingGramWords word
  have hvalid' : targets.size = grams.length ∧
      ∀ offset : Fin grams.length,
        match targets[offset.val]? with
        | none => False
        | some target =>
            ChromogramTargetValid code index (grams.get offset) target := by
    simpa [ChromogramTargetsValid, grams] using hvalid
  have hoffset : grams.idxOf gram < grams.length :=
    List.idxOf_lt_length_of_mem (by simpa [grams] using hmem)
  let offset : Fin grams.length := ⟨grams.idxOf gram, hoffset⟩
  have hgram : grams.get offset = gram := by
    simp [offset]
  have hentry := hvalid'.2 offset
  cases htarget : targets[offset.val]? with
  | none => simp [htarget] at hentry
  | some target =>
      cases hnode : code.nodeAt? target with
      | none => simp [htarget, ChromogramTargetValid, hnode] at hentry
      | some targetNode =>
          rw [hgram] at hentry
          have hlocal : target < index ∧
              Matches
                (Code.nodeWord (ring metadata).length targetNode).toList
                gram.toList := by
            simpa [htarget, ChromogramTargetValid, hnode] using hentry
          exact ⟨target, targetNode, rfl, hnode, hlocal⟩

private def gramWordOfMatch (word : TraceWord (ring metadata).length)
    (gram : Chromogram) (hmatch : Matches word.toList gram) :
    GramWord (ring metadata).length :=
  ⟨gram, by simpa using hmatch.length_eq.symm⟩

/-- Every checked proof node denotes an actual finite Kempe co-closure
derivation.  The topological node order is the termination measure. -/
theorem derivation_of_node
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (hchecker : nodeChecker valid code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    CoclosureDerivation (OrdinaryTrace valid)
      (Code.nodeWord (ring metadata).length node).toList := by
  induction index using Nat.strong_induction_on generalizing node with
  | h index ih =>
      have hconditions :=
        nodeConditions_of_checker_true valid code hchecker index hindex
          node hnode
      let word := Code.nodeWord (ring metadata).length node
      cases hrule : node.rule with
      | member assignmentCode =>
          have hwitness : OrdinaryWitnessValid valid word assignmentCode := by
            simpa [NodeConditions, word, hrule] using hconditions
          exact .member (ordinaryTrace_of_witness valid word assignmentCode
            hwitness)
      | permutation permutation target =>
          have hlocal : target < index ∧
              match code.nodeAt? target with
              | none => False
              | some targetNode =>
                  Code.nodeWord (ring metadata).length targetNode =
                    permute permutation word := by
            simpa [NodeConditions, word, hrule] using hconditions
          obtain ⟨htarget, htargetLocal⟩ := hlocal
          cases htargetNode : code.nodeAt? target with
          | none => simp [htargetNode] at htargetLocal
          | some targetNode =>
              have htargetWord :
                  Code.nodeWord (ring metadata).length targetNode =
                    permute permutation word := by
                simpa [htargetNode] using htargetLocal
              have htargetCount : target < code.nodeCount :=
                Nat.lt_trans htarget hindex
              have hderivation :=
                ih target htarget htargetCount targetNode htargetNode
              apply CoclosureDerivation.permutation permutation.toEquiv
              rw [← toList_permute permutation word, ← htargetWord]
              exact hderivation
      | chromograms targets =>
          have hlocal :
              ChromogramTargetsValid code index word targets := by
            simpa [NodeConditions, word, hrule] using hconditions
          refine .chromograms
            (fun gram hmatch =>
              (responseWord code (ring metadata).length
                word targets
                (gramWordOfMatch word gram hmatch)).toList) ?_ ?_
          · intro gram hmatch
            let fixedGram := gramWordOfMatch word gram hmatch
            have hmem : fixedGram ∈ matchingGramWords word :=
              mem_matchingGramWords word fixedGram (by
                simpa [fixedGram, gramWordOfMatch] using hmatch)
            obtain ⟨target, targetNode, htargetCode, htargetNode,
                _htarget, hmatches⟩ :=
              exists_chromogramTarget_of_valid code index word targets
                hlocal fixedGram hmem
            have hresponseWord :
                responseWord code (ring metadata).length word targets
                    fixedGram =
                  Code.nodeWord (ring metadata).length targetNode := by
              simp [responseWord, htargetCode, htargetNode]
            rw [hresponseWord]
            simpa [fixedGram, gramWordOfMatch] using hmatches
          · intro gram hmatch
            let fixedGram := gramWordOfMatch word gram hmatch
            have hmem : fixedGram ∈ matchingGramWords word :=
              mem_matchingGramWords word fixedGram (by
                simpa [fixedGram, gramWordOfMatch] using hmatch)
            obtain ⟨target, targetNode, htargetCode, htargetNode,
                htarget, _hmatches⟩ :=
              exists_chromogramTarget_of_valid code index word targets
                hlocal fixedGram hmem
            have htargetCount : target < code.nodeCount :=
              Nat.lt_trans htarget hindex
            have hderivation :=
              ih target htarget htargetCount targetNode htargetNode
            have hresponseWord :
                responseWord code (ring metadata).length word targets
                    fixedGram =
                  Code.nodeWord (ring metadata).length targetNode := by
              simp [responseWord, htargetCode, htargetNode]
            simpa [fixedGram, hresponseWord] using hderivation

theorem kempeCoclosure_of_node
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (hchecker : nodeChecker valid code = true)
    (index : Nat) (hindex : index < code.nodeCount)
    (node : NodeCode) (hnode : code.nodeAt? index = some node) :
    KempeCoclosure (OrdinaryTrace valid)
      (Code.nodeWord (ring metadata).length node).toList :=
  (derivation_of_node valid code hchecker index hindex node hnode).sound

/-- Every word in the exact contracted language follows the target trie to a
checked proof node, hence reduces to an ordinary coloring trace. -/
theorem contractWord_reduces
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code) (hnodeChecker : nodeChecker valid code = true)
    (word : List TraceSymbol)
    (htarget : TargetTreeCode.targetBoolean (ring metadata).length
      code word = true) :
    KempeCoclosure (OrdinaryTrace valid) word := by
  obtain ⟨target, _hlookup, htargetValid⟩ :=
    TargetTreeCode.leafValid_of_targetBoolean_true
      (ring metadata).length code word htarget
  obtain ⟨htarget, htargetLocal⟩ := htargetValid
  cases hnode : code.nodeAt? target with
  | none => simp [hnode] at htargetLocal
  | some node =>
      have hnodeWord :
          (Code.nodeWord (ring metadata).length node).toList = word := by
        simpa [hnode] using htargetLocal
      have hclosure := kempeCoclosure_of_node valid code hnodeChecker
        target htarget node hnode
      simpa [hnodeWord] using hclosure

theorem contractTrace_reduces
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (code : Code)
    (search : ClassicalCertificateContractColorSearch.Certificate
      metadata.components.componentCount)
    (hnodeChecker : nodeChecker valid code = true)
    (hsearch : search.checkerBy valid.componentsValid (ring metadata)
      (TargetTreeCode.targetBoolean (ring metadata).length code) = true)
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
    (ring metadata)
      (TargetTreeCode.targetBoolean (ring metadata).length code) hsearch
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
      (TargetTreeCode.targetBoolean (ring metadata).length code) = true)
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

end ClassicalCertificateProofDagReduction

end Mettapedia.GraphTheory.FourColor
