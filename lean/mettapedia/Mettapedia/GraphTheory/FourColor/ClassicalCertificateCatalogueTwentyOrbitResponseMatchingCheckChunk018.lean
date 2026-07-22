import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProductData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitResponseMatching

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitResponsePrefix0576_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30050 [.skip, .skip, .push, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0577_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30062 [.popOpposite, .skip, .push, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0578_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30081 [.push, .popSame, .push, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0579_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30088 [.skip, .popSame, .push, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0580_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30207 [.push, .popOpposite, .push, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0581_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30270 [.skip, .popOpposite, .push, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0582_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30302 [.push, .push, .skip, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0583_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30326 [.skip, .push, .skip, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0584_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30327 [.popSame, .push, .skip, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0585_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30345 [.popOpposite, .push, .skip, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0586_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30445 [.push, .skip, .skip, .skip, .skip, .skip] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0587_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      30465 [.skip, .skip, .skip, .skip, .skip, .skip] = true := by
  rfl

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
