import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchZero
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchPurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyLayerChecks

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateCatalogueTwentyLayerChecks
open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateColorTrace
open ClassicalCertificateContractColorSearch
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Every accepted leaf of the pruned component search lands in one of the
twenty-one checked Kempe layers. -/
theorem twentiethCatalogueContractSearch_checker :
    twentiethCatalogueContractSearch.checkerBy
      twentiethCatalogueComponentsValid twentiethCatalogueRing
        twentiethCatalogueHasContractTrace = true := by
  unfold ClassicalCertificateContractColorSearch.Certificate.checkerBy
  rw [Bool.and_eq_true]
  constructor
  · decide
  · change
      SearchTree.checkBy twentiethCatalogueComponentsValid
        twentiethCatalogueRing twentiethCatalogueHasContractTrace
          twentiethCatalogueContractSearch.tree []
            (twentiethCatalogueContractSearchFirstComponent ::
              twentiethCatalogueContractSearchRemaining) = true
    apply SearchTree.checkBy_of_isNode_and_children
    · exact twentiethCatalogueContractSearch_isNode
    · simpa [twentiethCatalogueContractSearchFirstBranch] using
        twentiethCatalogueContractSearchZero_checker
    · simpa [twentiethCatalogueContractSearchFirstBranch] using
        twentiethCatalogueContractSearchRed_checker
    · simpa [twentiethCatalogueContractSearchFirstBranch] using
        twentiethCatalogueContractSearchBlue_checker
    · simpa [twentiethCatalogueContractSearchFirstBranch] using
        twentiethCatalogueContractSearchPurple_checker

/-- Every genuine contracted boundary trace of `cf020` occurs in one of the
checked indexed Kempe layers. -/
theorem twentiethCatalogue_contractTrace_indexedLayer
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
        twentiethCatalogueContract twentiethCatalogueRing
          (word.map TraceSymbol.toColor)) :
    ∃ fixedWord : TraceWord 12,
      fixedWord.toList = word ∧
        ∃ layer,
          layer < twentiethCatalogueIndexedKempeCertificate.deltaRoots.length ∧
            twentiethCatalogueIndexedKempeCertificate.acceptsAt layer
              fixedWord = true := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment twentiethCataloguePartitionValid
      twentiethCatalogueContract twentiethCatalogueRing _).1 hcontract
  have hlength : word.length = 12 := by
    calc
      word.length = (word.map TraceSymbol.toColor).length := by simp
      _ = (ringTraceOfAssignment twentiethCataloguePartitionValid
          twentiethCatalogueRing assignment).length :=
        congrArg List.length htrace
      _ = 12 := by
        simp [ringTraceOfAssignment, FiniteHypermap.ringColorWord,
          length_trace, twentiethCatalogueRing]
  let fixedWord : TraceWord 12 := ⟨word, hlength⟩
  have hroot : twentiethCatalogueHasContractTrace fixedWord.toList = true := by
    apply twentiethCatalogueContractSearch.acceptsBy_of_contractWord
      twentiethCatalogueComponentsValid twentiethCatalogueRing
        twentiethCatalogueHasContractTrace
          twentiethCatalogueContractSearch_checker
            twentiethCatalogueRing_reverseBoundaryCycle
              twentiethCatalogueContract_avoidsBoundary assignment hassignment
    exact htrace
  obtain ⟨layer, hlookup⟩ :
      ∃ layer, twentiethCatalogueContractTraceMap.lookup fixedWord.toList =
        some layer :=
    Option.isSome_iff_exists.1 (by
      simpa [twentiethCatalogueHasContractTrace] using hroot)
  have htarget :=
    twentiethCatalogueContractTraceMap.lookup_sound_of_checker_true 12
      twentiethCatalogueContractTraceTarget
        twentiethCatalogueContractTraceMap_checker fixedWord.toList layer
          (by simp) hlookup
  have hparts :
      decide
          (layer <
            twentiethCatalogueIndexedKempeCertificate.deltaRoots.length) =
            true ∧
        ClassicalCertificateTraceDag.accepts 12
          twentiethCatalogueIndexedKempeCertificate.traceCode
            (twentiethCatalogueIndexedKempeCertificate.rootAt layer)
              fixedWord.toList = true := by
    simpa [twentiethCatalogueContractTraceTarget] using htarget
  have hlayer :
      layer < twentiethCatalogueIndexedKempeCertificate.deltaRoots.length :=
    of_decide_eq_true hparts.1
  have haccepted :
      twentiethCatalogueIndexedKempeCertificate.acceptsAt layer fixedWord =
        true := by
    simpa [ClassicalCertificateIndexedLayeredKempe.Certificate.acceptsAt]
      using hparts.2
  exact ⟨fixedWord, rfl, layer, hlayer, haccepted⟩

/-- Every contracted `cf020` boundary trace lies in the Kempe co-closure of
the certificate's explicitly indexed extendable traces. -/
theorem twentiethCatalogue_contractTrace_kempeCoclosure
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
        twentiethCatalogueContract twentiethCatalogueRing
          (word.map TraceSymbol.toColor)) :
    KempeCoclosure
      twentiethCatalogueIndexedKempeCertificate.ExtendableFamily word := by
  obtain ⟨fixedWord, hfixed, layer, hlayer, haccepted⟩ :=
    twentiethCatalogue_contractTrace_indexedLayer word hcontract
  subst word
  exact twentiethCatalogueIndexed_root_kempeCoclosure
    layer hlayer fixedWord haccepted

/-- Color-valued form of the indexed `cf020` contraction reduction. -/
theorem twentiethCatalogue_contractRingTrace_reducesToIndexedFamily
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
        twentiethCatalogueContract twentiethCatalogueRing boundaryTrace) :
    ∃ symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure
          twentiethCatalogueIndexedKempeCertificate.ExtendableFamily
            symbols := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment twentiethCataloguePartitionValid
      twentiethCatalogueContract twentiethCatalogueRing boundaryTrace).1
        hcontract
  obtain ⟨symbols, hsymbols, _⟩ :=
    twentiethCatalogue_contractAssignment_trace_symbols assignment hassignment
  have hsymbolsBoundary :
      symbols.map TraceSymbol.toColor = boundaryTrace :=
    hsymbols.trans htrace.symm
  refine ⟨symbols, hsymbolsBoundary, ?_⟩
  apply twentiethCatalogue_contractTrace_kempeCoclosure
  simpa [hsymbolsBoundary] using hcontract

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
