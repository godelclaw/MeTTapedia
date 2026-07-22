import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingAggregateDepth01

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateOrbitResponseMatchingAggregate

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-- Every shared response spelling lies in the chromogram fiber indexing it. -/
theorem twentiethCatalogueOrbitResponseMatching_checker :
    checker twentiethCatalogueOrbitProductCertificate = true := by
  change matchingBoolean twentiethCatalogueOrbitProductCertificate 12
    30471 [] = true
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 11 30471
      [] 22623 30470
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth01Prefix0000_checker
  · exact twentiethCatalogueOrbitResponseDepth01Prefix0001_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 11 0 [.popSame] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 11 0 [.popOpposite] (by rfl)

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
