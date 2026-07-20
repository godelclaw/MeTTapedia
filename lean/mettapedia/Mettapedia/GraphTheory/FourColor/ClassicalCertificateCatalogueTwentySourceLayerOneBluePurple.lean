import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerOneBlueBlue

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayerOneBluePurple

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTreeRankedKempe
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

def twentiethCatalogueLayerOneBluePurpleBoolean : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords 10
    twentiethCatalogueTraceDag 2871).all fun suffix =>
      ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
        twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
          1 (prependSymbol .blue (prependSymbol .purple suffix))

theorem twentiethCatalogueLayerOneBluePurple_checker :
    twentiethCatalogueLayerOneBluePurpleBoolean = true := by
  rfl

end ClassicalCertificateCatalogueTwentySourceLayerOneBluePurple

end Mettapedia.GraphTheory.FourColor
