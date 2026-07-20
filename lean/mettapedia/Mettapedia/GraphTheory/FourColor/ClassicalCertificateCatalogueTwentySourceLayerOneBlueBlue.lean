import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerOneBlueRed

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayerOneBlueBlue

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTreeRankedKempe
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

def twentiethCatalogueLayerOneBlueBlueBoolean : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords 10
    twentiethCatalogueTraceDag 2605).all fun suffix =>
      ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
        twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
          1 (prependSymbol .blue (prependSymbol .blue suffix))

theorem twentiethCatalogueLayerOneBlueBlue_checker :
    twentiethCatalogueLayerOneBlueBlueBoolean = true := by
  rfl

end ClassicalCertificateCatalogueTwentySourceLayerOneBlueBlue

end Mettapedia.GraphTheory.FourColor
