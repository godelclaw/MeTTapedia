import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerOneBluePurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayerOnePurple

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTreeRankedKempe
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

def twentiethCatalogueLayerOnePurpleBoolean : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords 11
    twentiethCatalogueTraceDag 3010).all fun suffix =>
      ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
        twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
          1 (prependSymbol .purple suffix)

theorem twentiethCatalogueLayerOnePurple_checker :
    twentiethCatalogueLayerOnePurpleBoolean = true := by
  rfl

end ClassicalCertificateCatalogueTwentySourceLayerOnePurple

end Mettapedia.GraphTheory.FourColor
