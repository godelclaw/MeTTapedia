import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerOne

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayerTwo

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateTreeIndexedLayeredKempe

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem twentiethCatalogueSourceLayer02 :
    ClassicalCertificateTreeIndexedLayeredKempe.layerBoolean
      twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
        2 = true := by
  rfl

end ClassicalCertificateCatalogueTwentySourceLayerTwo

end Mettapedia.GraphTheory.FourColor
