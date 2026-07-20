import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerZero
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyResponseTree
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTreeIndexedLayeredKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayerOneRed

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTreeRankedKempe
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

def twentiethCatalogueLayerOneRedBoolean : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords 11
    twentiethCatalogueTraceDag 1921).all fun suffix =>
      ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
        twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
          1 (prependSymbol .red suffix)

theorem twentiethCatalogueLayerOneRed_checker :
    twentiethCatalogueLayerOneRedBoolean = true := by
  rfl

end ClassicalCertificateCatalogueTwentySourceLayerOneRed

end Mettapedia.GraphTheory.FourColor
