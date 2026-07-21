import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueFourExactTraceZero
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueFourExactTraceRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueFourExactTraceBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueFourExactTracePurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueFourExactTrace

open ClassicalCertificateCatalogueFour
open ClassicalCertificateCatalogueFourLayered
open ClassicalCertificateContractColorSearch
open ClassicalCertificateContractComponents
open ClassicalCertificateExactTraceEnumeration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Every genuine `cf004` contract trace reaches the layered Kempe root trie
through one of the four exact first-color branches. -/
theorem fourthCatalogue_exactTrace_covered
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap fourthCataloguePartitionValid)
        fourthCatalogueContract fourthCatalogueRing
          (word.map TraceSymbol.toColor)) :
    fourthCoveredTraceTree.accepts word = true := by
  obtain ⟨assignment, hassignment, hboundary⟩ :=
    (contractRingTrace_iff_exists_assignment fourthCataloguePartitionValid
      fourthCatalogueContract fourthCatalogueRing _).1 hcontract
  let componentAssignment :=
    restrictAssignment fourthCatalogueComponentsValid assignment
  have hfactor :
      liftAssignment fourthCatalogueComponentsValid componentAssignment =
        assignment :=
    lift_restrictAssignment_eq fourthCatalogueComponentsValid assignment
      hassignment
  have hcomponentContract :
      IsContractAssignment fourthCataloguePartitionValid
        fourthCatalogueContract
          (liftAssignment fourthCatalogueComponentsValid
            componentAssignment) := by
    rw [hfactor]
    exact hassignment
  let exactWord := symbolTraceOfAssignment fourthCataloguePartitionValid
    fourthCatalogueRing
      (liftAssignment fourthCatalogueComponentsValid componentAssignment)
  have hexactWord : exactWord = word := by
    apply TraceSymbol.map_toColor_injective
    rw [symbolTraceOfAssignment_toColor fourthCataloguePartitionValid
      fourthCatalogueContract fourthCatalogueRing
        (liftAssignment fourthCatalogueComponentsValid componentAssignment)
          hcomponentContract fourthCatalogueRing_reverseBoundaryCycle
            fourthCatalogueContract_avoidsBoundary]
    simpa [hfactor] using hboundary.symm
  have branchAccepts (code : FaceColorCode)
      (hcolor : componentAssignment fourthCatalogueExactTraceFirst =
        code.toColor) :
      (fourthCatalogueExactTraceBranch code).accepts exactWord = true := by
    apply enumerateAux_accepts_of_contract fourthCatalogueComponentsValid
      fourthCatalogueRing
        (fourthCatalogueExactTraceAssigned code)
          fourthCatalogueExactTraceRemaining componentAssignment
    · intro entry hentry
      simp only [fourthCatalogueExactTraceAssigned,
        List.mem_singleton] at hentry
      subst entry
      exact hcolor
    · exact hcomponentContract
    · exact fourthCatalogueExactTraceAllCovered code
  rcases color_four_cases
      (componentAssignment fourthCatalogueExactTraceFirst) with
    hzero | hred | hblue | hpurple
  · rw [← hexactWord]
    exact fourthCatalogueExactTraceBranch_subset .zero
      fourthCatalogueExactTraceBranchZero_checker exactWord
        (branchAccepts .zero (by
          simpa [FaceColorCode.toColor] using hzero))
  · rw [← hexactWord]
    exact fourthCatalogueExactTraceBranch_subset .red
      fourthCatalogueExactTraceBranchRed_checker exactWord
        (branchAccepts .red (by
          simpa [FaceColorCode.toColor] using hred))
  · rw [← hexactWord]
    exact fourthCatalogueExactTraceBranch_subset .blue
      fourthCatalogueExactTraceBranchBlue_checker exactWord
        (branchAccepts .blue (by
          simpa [FaceColorCode.toColor] using hblue))
  · rw [← hexactWord]
    exact fourthCatalogueExactTraceBranch_subset .purple
      fourthCatalogueExactTraceBranchPurple_checker exactWord
        (branchAccepts .purple (by
          simpa [FaceColorCode.toColor] using hpurple))

/-- The `cf004` reduction with its contract language generated internally,
without the separate 305-node pruned search certificate. -/
theorem fourthCatalogue_exact_contractTrace_kempeCoclosure
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap fourthCataloguePartitionValid)
        fourthCatalogueContract fourthCatalogueRing
          (word.map TraceSymbol.toColor)) :
    KempeCoclosure FourthCatalogueExtendableTrace word := by
  have hcovered := fourthCatalogue_exactTrace_covered word hcontract
  have hlength : word.length = 8 := by
    calc
      word.length = (word.map TraceSymbol.toColor).length := by simp
      _ = 8 := by
        obtain ⟨assignment, _, hboundary⟩ :=
          (contractRingTrace_iff_exists_assignment
            fourthCataloguePartitionValid fourthCatalogueContract
              fourthCatalogueRing _).1 hcontract
        rw [hboundary]
        simp [ringTraceOfAssignment,
          ClassicalCertificateHypermapColoring.FiniteHypermap.ringColorWord,
          ClassicalCertificateColorTrace.length_trace,
          fourthCatalogueRing]
  let fixedWord : TraceWord 8 := ⟨word, hlength⟩
  have hcoclosure :=
    fourthCatalogueLayered_root_kempeCoclosure fixedWord hcovered
  exact hcoclosure.mono fourthCatalogueLayered_extendableFamily_sound

end ClassicalCertificateCatalogueFourExactTrace

end Mettapedia.GraphTheory.FourColor
