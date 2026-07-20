import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerTwo

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayersThreeFour

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem twentiethCatalogueSourceLayer03 :
    ClassicalCertificateTreeIndexedLayeredKempe.layerBoolean
      twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
        3 = true := by rfl
theorem twentiethCatalogueSourceLayer04 :
    ClassicalCertificateTreeIndexedLayeredKempe.layerBoolean
      twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
        4 = true := by rfl

end ClassicalCertificateCatalogueTwentySourceLayersThreeFour

end Mettapedia.GraphTheory.FourColor
