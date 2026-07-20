import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayersTenTwenty

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyLayerChecks

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateCatalogueTwentyResponseSeal
open ClassicalCertificateCatalogueTwentySourceLayerZero
open ClassicalCertificateCatalogueTwentySourceLayerOne
open ClassicalCertificateCatalogueTwentySourceLayerTwo
open ClassicalCertificateCatalogueTwentySourceLayersThreeFour
open ClassicalCertificateCatalogueTwentySourceLayersFiveNine
open ClassicalCertificateCatalogueTwentySourceLayersTenTwenty
open ClassicalCertificateKempeClosure
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateRankedKempe
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem twentiethCatalogueSourceLayerCount :
    twentiethCatalogueIndexedKempeCertificate.deltaRoots.length = 21 := by rfl

theorem twentiethCatalogueSourceLayers_checker :
    ClassicalCertificateTreeIndexedLayeredKempe.sourceBoolean
      twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree =
        true := by
  unfold ClassicalCertificateTreeIndexedLayeredKempe.sourceBoolean
  rw [twentiethCatalogueSourceLayerCount]
  apply List.all_eq_true.2
  intro layer hlayer
  have hlt : layer < 21 := List.mem_range.1 hlayer
  interval_cases layer <;>
    simp only [twentiethCatalogueSourceLayer00,
      twentiethCatalogueSourceLayer01, twentiethCatalogueSourceLayer02,
      twentiethCatalogueSourceLayer03, twentiethCatalogueSourceLayer04,
      twentiethCatalogueSourceLayer05, twentiethCatalogueSourceLayer06,
      twentiethCatalogueSourceLayer07, twentiethCatalogueSourceLayer08,
      twentiethCatalogueSourceLayer09, twentiethCatalogueSourceLayer10,
      twentiethCatalogueSourceLayer11, twentiethCatalogueSourceLayer12,
      twentiethCatalogueSourceLayer13, twentiethCatalogueSourceLayer14,
      twentiethCatalogueSourceLayer15, twentiethCatalogueSourceLayer16,
      twentiethCatalogueSourceLayer17, twentiethCatalogueSourceLayer18,
      twentiethCatalogueSourceLayer19, twentiethCatalogueSourceLayer20]

theorem twentiethCatalogueTreeIndexedChecks :
    twentiethCatalogueIndexedKempeCertificate.responseTableBoolean = true ∧
      ClassicalCertificateTreeIndexedLayeredKempe.sourceBoolean
        twentiethCatalogueIndexedKempeCertificate
          twentiethCatalogueResponseTree = true :=
  ⟨twentiethCatalogueResponseTable_checker,
    twentiethCatalogueSourceLayers_checker⟩

theorem twentiethCatalogueIndexed_root_kempeCoclosure
    (layer : Nat)
    (hlayer :
      layer < twentiethCatalogueIndexedKempeCertificate.deltaRoots.length)
    (word : TraceWord 12)
    (hcovered : twentiethCatalogueIndexedKempeCertificate.acceptsAt layer word =
      true) :
    KempeCoclosure
      twentiethCatalogueIndexedKempeCertificate.ExtendableFamily
        word.toList :=
  ClassicalCertificateTreeIndexedLayeredKempe.kempeCoclosure_at_rank_of_checks
      twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
        twentiethCatalogueTreeIndexedChecks.1
          twentiethCatalogueTreeIndexedChecks.2 layer hlayer word hcovered

end ClassicalCertificateCatalogueTwentyLayerChecks

end Mettapedia.GraphTheory.FourColor
