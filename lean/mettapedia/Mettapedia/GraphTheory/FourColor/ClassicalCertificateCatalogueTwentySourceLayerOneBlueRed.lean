import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerOneRed

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayerOneBlueRed

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTreeRankedKempe
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

def twentiethCatalogueLayerOneBlueRedBoolean : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords 10
    twentiethCatalogueTraceDag 2174).all fun suffix =>
      ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
        twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
          1 (prependSymbol .blue (prependSymbol .red suffix))

theorem twentiethCatalogueLayerOneBlueRed_checker :
    twentiethCatalogueLayerOneBlueRedBoolean = true := by
  rfl

end ClassicalCertificateCatalogueTwentySourceLayerOneBlueRed

end Mettapedia.GraphTheory.FourColor
