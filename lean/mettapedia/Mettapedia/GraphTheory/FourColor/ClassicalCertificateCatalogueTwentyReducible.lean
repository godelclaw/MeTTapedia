import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearch
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessTableCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateIndexedTraceWitness
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- A normalized trace is ordinarily extendable precisely when it is realized
by a genuine face coloring of the checked `cf020` hypermap. -/
def TwentiethCatalogueExtendableTrace (word : List TraceSymbol) : Prop :=
  FiniteHypermap.RingTrace
    (checkedHypermap twentiethCataloguePartitionValid)
      twentiethCatalogueRing (word.map TraceSymbol.toColor)

/-- Every trace accepted at the indexed extendable root is realized by one of
the checked ordinary face-color assignments. -/
theorem twentiethCatalogue_extendableFamily_sound
    (word : List TraceSymbol)
    (hextendable :
      twentiethCatalogueIndexedKempeCertificate.ExtendableFamily word) :
    TwentiethCatalogueExtendableTrace word := by
  rcases hextendable with ⟨fixedWord, hfixed, haccepted⟩
  subst word
  obtain ⟨assignment, hproper, htrace⟩ :=
    twentiethCatalogueWitnessCertificate.exists_properAssignment_of_dag_accepts
      twentiethCataloguePartitionValid twentiethCatalogueRingVector
        twentiethCatalogueTraceDag twentiethCatalogueExtendableRoot
          twentiethCatalogueWitnessTable_checker
            twentiethCatalogueWitnessMap_checker
              twentiethCatalogueWitnessMap_coversExtendableRoot fixedWord (by
                simpa [
                  ClassicalCertificateIndexedLayeredKempe.Certificate.acceptsExtendable,
                  twentiethCatalogueIndexedKempeCertificate]
                    using haccepted)
  exact (ringTrace_iff_exists_assignment twentiethCataloguePartitionValid
    twentiethCatalogueRing _).2 ⟨assignment, hproper, htrace⟩

/-- Every contracted symbolic boundary trace of `cf020` reaches a genuine
ordinary boundary coloring through the checked Kempe co-closure. -/
theorem twentiethCatalogue_contractTrace_reduces
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
        twentiethCatalogueContract twentiethCatalogueRing
          (word.map TraceSymbol.toColor)) :
    KempeCoclosure TwentiethCatalogueExtendableTrace word := by
  have hcoclosure :=
    twentiethCatalogue_contractTrace_kempeCoclosure word hcontract
  exact hcoclosure.mono twentiethCatalogue_extendableFamily_sound

/-- Color-valued reducibility theorem for the twentieth classical catalogue
configuration. -/
theorem twentiethCatalogue_contractRingTrace_reduces
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
        twentiethCatalogueContract twentiethCatalogueRing boundaryTrace) :
    ∃ symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure TwentiethCatalogueExtendableTrace symbols := by
  obtain ⟨symbols, hsymbols, hcoclosure⟩ :=
    twentiethCatalogue_contractRingTrace_reducesToIndexedFamily
      boundaryTrace hcontract
  exact ⟨symbols, hsymbols,
    hcoclosure.mono twentiethCatalogue_extendableFamily_sound⟩

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
