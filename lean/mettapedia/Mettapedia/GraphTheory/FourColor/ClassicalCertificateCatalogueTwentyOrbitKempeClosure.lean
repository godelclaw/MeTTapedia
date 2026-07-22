import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseValueCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessTableCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitBaseWitness
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitLayeredKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitKempeClosure

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheck
open ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck
open ClassicalCertificateCatalogueTwentyOrbitResponseValueCheck
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitBaseWitness
open ClassicalCertificateOrbitLayeredKempe
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-- Every word in every retained color-orbit layer of `cf020` has a finite
Kempe co-closure derivation to its extendable base. -/
theorem twentiethCatalogueOrbit_root_derivation
    (layer : Nat)
    (hlayer :
      layer < twentiethCatalogueOrbitProductCertificate.deltaRoots.length)
    (word : TraceWord 12)
    (haccepted : twentiethCatalogueOrbitProductCertificate.acceptsAt layer
      word = true) :
    CoclosureDerivation
      twentiethCatalogueOrbitProductCertificate.ExtendableFamily
        word.toList := by
  apply derivation_at_rank twentiethCatalogueOrbitProductCertificate
    (by rfl) twentiethCatalogueOrbitResponseMatching_checker
      twentiethCatalogueOrbitResponseValueTable_checker
        twentiethCatalogueOrbitProductLayers_checker layer hlayer word
          haccepted

theorem twentiethCatalogueOrbit_root_kempeCoclosure
    (layer : Nat)
    (hlayer :
      layer < twentiethCatalogueOrbitProductCertificate.deltaRoots.length)
    (word : TraceWord 12)
    (haccepted : twentiethCatalogueOrbitProductCertificate.acceptsAt layer
      word = true) :
    KempeCoclosure
      twentiethCatalogueOrbitProductCertificate.ExtendableFamily
        word.toList :=
  (twentiethCatalogueOrbit_root_derivation layer hlayer word haccepted).sound

/-- Every orbit-product base word occurs in the independently checked map of
ordinary `cf020` face-coloring witnesses. -/
theorem twentiethCatalogueOrbitProductBase_coversWitnessMap :
    twentiethCatalogueWitnessCertificate.coversDagBoolean
      twentiethCatalogueOrbitProductCertificate.traceCode
        twentiethCatalogueOrbitProductCertificate.extendableRoot = true := by
  rfl

/-- The orbit-product base language denotes genuine ordinary boundary
colorings of the checked `cf020` hypermap. -/
theorem twentiethCatalogueOrbitProduct_extendableFamily_sound
    (word : List TraceSymbol)
    (hextendable :
      twentiethCatalogueOrbitProductCertificate.ExtendableFamily word) :
    FiniteHypermap.RingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
        twentiethCatalogueRing (word.map TraceSymbol.toColor) := by
  simpa [twentiethCatalogueRingVector] using
    extendableFamily_subset_ringTrace twentiethCataloguePartitionValid
      twentiethCatalogueRingVector twentiethCatalogueOrbitProductCertificate
        twentiethCatalogueWitnessCertificate
          twentiethCatalogueWitnessTable_checker
            twentiethCatalogueWitnessMap_checker
              twentiethCatalogueOrbitProductBase_coversWitnessMap word
                hextendable

/-- Every retained orbit-layer word reaches a genuine ordinary boundary
coloring through finite Kempe co-closure. -/
theorem twentiethCatalogueOrbit_root_kempeCoclosure_ordinary
    (layer : Nat)
    (hlayer :
      layer < twentiethCatalogueOrbitProductCertificate.deltaRoots.length)
    (word : TraceWord 12)
    (haccepted : twentiethCatalogueOrbitProductCertificate.acceptsAt layer
      word = true) :
    KempeCoclosure
      (fun otherWord => FiniteHypermap.RingTrace
        (checkedHypermap twentiethCataloguePartitionValid)
          twentiethCatalogueRing (otherWord.map TraceSymbol.toColor))
      word.toList :=
  (twentiethCatalogueOrbit_root_kempeCoclosure layer hlayer word
    haccepted).mono twentiethCatalogueOrbitProduct_extendableFamily_sound

end ClassicalCertificateCatalogueTwentyOrbitKempeClosure

end Mettapedia.GraphTheory.FourColor
