import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingAggregateDepth03

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateOrbitResponseMatchingAggregate

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitResponseDepth02Prefix0000_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      10 13563 [.push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 9 13563
      [.push, .push] 6890 9367
        10933 13562 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0000_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0001_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0002_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0003_checker

theorem twentiethCatalogueOrbitResponseDepth02Prefix0001_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      10 17659 [.skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 9 17659
      [.skip, .push] 15734 17061
        17385 17658 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0004_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0005_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0006_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0007_checker

theorem twentiethCatalogueOrbitResponseDepth02Prefix0002_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      10 19238 [.popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 9 19238
      [.popSame, .push] 18982 19237
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0008_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0009_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 9 0 [.popSame, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 9 0 [.popOpposite, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth02Prefix0003_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      10 22622 [.popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 9 22622
      [.popOpposite, .push] 22076 22621
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0010_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0011_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 9 0 [.popSame, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 9 0 [.popOpposite, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth02Prefix0004_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      10 27710 [.push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 9 27710
      [.push, .skip] 24502 27062
        27256 27709 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0012_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0013_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0014_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0015_checker

theorem twentiethCatalogueOrbitResponseDepth02Prefix0005_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      10 30469 [.skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 9 30469
      [.skip, .skip] 29531 30468
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0016_checker
  · exact twentiethCatalogueOrbitResponseDepth03Prefix0017_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 9 0 [.popSame, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 9 0 [.popOpposite, .skip, .skip] (by rfl)

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
