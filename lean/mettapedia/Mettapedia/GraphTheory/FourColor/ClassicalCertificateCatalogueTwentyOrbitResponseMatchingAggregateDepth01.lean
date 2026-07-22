import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingAggregateDepth02

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateOrbitResponseMatchingAggregate

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitResponseDepth01Prefix0000_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      11 22623 [.push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 10 22623
      [.push] 13563 17659
        19238 22622 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth02Prefix0000_checker
  · exact twentiethCatalogueOrbitResponseDepth02Prefix0001_checker
  · exact twentiethCatalogueOrbitResponseDepth02Prefix0002_checker
  · exact twentiethCatalogueOrbitResponseDepth02Prefix0003_checker

theorem twentiethCatalogueOrbitResponseDepth01Prefix0001_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      11 30470 [.skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 10 30470
      [.skip] 27710 30469
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth02Prefix0004_checker
  · exact twentiethCatalogueOrbitResponseDepth02Prefix0005_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 10 0 [.popSame, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 10 0 [.popOpposite, .skip] (by rfl)

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
