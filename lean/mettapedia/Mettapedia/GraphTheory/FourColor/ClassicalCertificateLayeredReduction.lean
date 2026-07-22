import Mettapedia.GraphTheory.FourColor.ClassicalCertificateLayeredKempe
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrdinaryTraceEnumeration
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadata

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateLayeredReduction

open ClassicalCertificateExactTraceEnumeration
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateLayeredKempe
open ClassicalCertificateReductionMetadata
open ClassicalCertificateTraceTree

variable {code : ClassicalCertificateReductionMetadata.Code}

/-- The exact contracted boundary language determined by checked reduction
metadata. -/
def contractTree (valid : ClassicalCertificateReductionMetadata.Valid code) :
    TraceTree :=
  ClassicalCertificateExactTraceEnumeration.enumerate
    (ClassicalCertificateReductionMetadata.Valid.componentsValid valid)
      (ClassicalCertificateReductionMetadata.ring code)
        (ClassicalCertificateReductionMetadata.order code)

/-- The exact ordinary boundary language of the same checked hypermap. -/
def ordinaryTree (valid : ClassicalCertificateReductionMetadata.Valid code) :
    TraceTree :=
  ClassicalCertificateOrdinaryTraceEnumeration.enumerate
    (ClassicalCertificateReductionMetadata.Valid.partitionValid valid)
      (ClassicalCertificateReductionMetadata.ring code)

/-- Root-directed closure layers for one checked catalogue configuration.
Their extendable base is fixed to the exact ordinary coloring language. -/
structure Certificate
    (valid : ClassicalCertificateReductionMetadata.Valid code) where
  deltas : List TraceTree

namespace Certificate

def layered
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (certificate : Certificate valid) :
    ClassicalCertificateLayeredKempe.Certificate
      (ClassicalCertificateReductionMetadata.ring code).length where
  extendable := ordinaryTree valid
  deltas := certificate.deltas

def checker
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (certificate : Certificate valid) : Bool :=
  (certificate.layered valid).checker &&
    ClassicalCertificateExactTraceEnumeration.TraceTree.subset
      (contractTree valid) (certificate.layered valid).closureTree

def OrdinaryTrace
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (word : List TraceSymbol) : Prop :=
  FiniteHypermap.RingTrace
    (ClassicalCertificateFacePartition.checkedHypermap
      (ClassicalCertificateReductionMetadata.Valid.partitionValid valid))
    (ClassicalCertificateReductionMetadata.ring code)
    (word.map TraceSymbol.toColor)

/-- An accepted layered certificate sends every genuine contracted boundary
trace into the Kempe co-closure of a genuine ordinary face-coloring trace of
the same checked hypermap. -/
theorem contractTrace_reduces
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (certificate : Certificate valid)
    (hchecker : certificate.checker valid = true)
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (ClassicalCertificateFacePartition.checkedHypermap
        (ClassicalCertificateReductionMetadata.Valid.partitionValid valid))
      (ClassicalCertificateReductionMetadata.contract code)
      (ClassicalCertificateReductionMetadata.ring code)
      (word.map TraceSymbol.toColor)) :
    KempeCoclosure (OrdinaryTrace valid) word := by
  have hparts :
      (certificate.layered valid).checker = true ∧
        ClassicalCertificateExactTraceEnumeration.TraceTree.subset
          (contractTree valid)
            (certificate.layered valid).closureTree = true := by
    simpa [checker] using hchecker
  have hcontractAccepted : (contractTree valid).accepts word = true := by
    exact
      (ClassicalCertificateReductionMetadata.Valid.enumerate_accepts_iff_contractRingTrace
        valid word).2 hcontract
  have hlength :
      word.length =
        (ClassicalCertificateReductionMetadata.ring code).length := by
    apply ClassicalCertificateExactTraceEnumeration.TraceTree.length_eq_of_uniform_accepts
      (tree := contractTree valid)
    · exact ClassicalCertificateExactTraceEnumeration.enumerate_uniform
        (ClassicalCertificateReductionMetadata.Valid.componentsValid valid)
          (ClassicalCertificateReductionMetadata.ring code)
            (ClassicalCertificateReductionMetadata.order code)
    · exact hcontractAccepted
  let fixedWord :
      ClassicalCertificateRankedKempe.TraceWord
        (ClassicalCertificateReductionMetadata.ring code).length :=
    ⟨word, hlength⟩
  have hclosure :
      (certificate.layered valid).closureTree.accepts
        fixedWord.toList = true := by
    apply ClassicalCertificateExactTraceEnumeration.TraceTree.accepts_of_subset
      (contractTree valid) (certificate.layered valid).closureTree hparts.2
    simpa [fixedWord] using hcontractAccepted
  have hcoclosure :=
    (certificate.layered valid).kempeCoclosure_of_checker_true hparts.1
      fixedWord hclosure
  exact hcoclosure.mono fun otherWord hother => by
    rcases hother with ⟨otherFixedWord, hword, haccepted⟩
    subst otherWord
    apply
      (ClassicalCertificateOrdinaryTraceEnumeration.enumerate_accepts_iff_ringTrace
          (ClassicalCertificateReductionMetadata.Valid.partitionValid valid)
          (ClassicalCertificateReductionMetadata.ring code)
          (ClassicalCertificateReductionMetadata.Valid.reverseBoundaryCycle
            valid)
          otherFixedWord.toList).1
    simpa [layered, ordinaryTree] using haccepted

/-- Color-valued form of catalogue reducibility: every contracted boundary
trace has a canonical nonzero symbolic spelling, and that spelling reduces to
an ordinary face-coloring trace. -/
theorem contractRingTrace_reduces
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (certificate : Certificate valid)
    (hchecker : certificate.checker valid = true)
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (ClassicalCertificateFacePartition.checkedHypermap
        (ClassicalCertificateReductionMetadata.Valid.partitionValid valid))
      (ClassicalCertificateReductionMetadata.contract code)
      (ClassicalCertificateReductionMetadata.ring code)
      boundaryTrace) :
    ∃ word : List TraceSymbol,
      word.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure (OrdinaryTrace valid) word := by
  obtain ⟨assignment, hassignment, hboundary⟩ :=
    (ClassicalCertificateFacePartition.contractRingTrace_iff_exists_assignment
        (ClassicalCertificateReductionMetadata.Valid.partitionValid valid)
        (ClassicalCertificateReductionMetadata.contract code)
        (ClassicalCertificateReductionMetadata.ring code)
        boundaryTrace).1 hcontract
  let word :=
    ClassicalCertificateContractColorSearch.symbolTraceOfAssignment
      (ClassicalCertificateReductionMetadata.Valid.partitionValid valid)
      (ClassicalCertificateReductionMetadata.ring code) assignment
  have hword : word.map TraceSymbol.toColor = boundaryTrace := by
    rw [ClassicalCertificateContractColorSearch.symbolTraceOfAssignment_toColor
        (ClassicalCertificateReductionMetadata.Valid.partitionValid valid)
        (ClassicalCertificateReductionMetadata.contract code)
        (ClassicalCertificateReductionMetadata.ring code) assignment
        hassignment
        (ClassicalCertificateReductionMetadata.Valid.reverseBoundaryCycle
          valid)
        (ClassicalCertificateReductionMetadata.Valid.contractAvoidsBoundary
          valid)]
    exact hboundary.symm
  refine ⟨word, hword,
    contractTrace_reduces valid certificate hchecker word ?_⟩
  simpa [hword] using hcontract

end Certificate

end ClassicalCertificateLayeredReduction

end Mettapedia.GraphTheory.FourColor
