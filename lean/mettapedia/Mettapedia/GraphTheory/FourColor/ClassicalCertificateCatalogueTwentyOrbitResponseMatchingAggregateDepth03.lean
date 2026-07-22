import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingAggregateDepth04

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateOrbitResponseMatchingAggregate

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitResponseDepth03Prefix0000_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 6890 [.push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 6890
      [.push, .push, .push] 2335 4138
        5387 6889 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0000_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0001_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0002_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0003_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0001_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 9367 [.skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 9367
      [.skip, .push, .push] 8077 8618
        8853 9366 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0004_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0005_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0006_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0007_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0002_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 10933 [.popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 10933
      [.popSame, .push, .push] 10148 10521
        10666 10932 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0008_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0009_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0010_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0011_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0003_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 13562 [.popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 13562
      [.popOpposite, .push, .push] 12112 12862
        13147 13561 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0012_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0013_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0014_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0015_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0004_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 15734 [.push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 15734
      [.push, .skip, .push] 14481 15024
        15333 15733 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0016_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0017_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0018_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0019_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0005_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 17061 [.skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 17061
      [.skip, .skip, .push] 16515 16667
        16768 17060 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0020_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0021_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0022_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0023_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0006_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 17385 [.popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 17385
      [.popSame, .skip, .push] 17327 17384
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0024_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0025_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popSame, .popSame, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popOpposite, .popSame, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth03Prefix0007_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 17658 [.popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 17658
      [.popOpposite, .skip, .push] 17625 17657
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0026_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0027_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popSame, .popOpposite, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popOpposite, .popOpposite, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth03Prefix0008_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 18982 [.push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 18982
      [.push, .popSame, .push] 18394 18719
        18847 18981 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0028_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0029_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0030_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0031_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0009_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 19237 [.skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 19237
      [.skip, .popSame, .push] 19206 19236
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0032_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0033_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popSame, .skip, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popOpposite, .skip, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth03Prefix0010_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 22076 [.push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 22076
      [.push, .popOpposite, .push] 20639 21456
        21812 22075 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0034_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0035_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0036_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0037_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0011_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 22621 [.skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 22621
      [.skip, .popOpposite, .push] 22518 22620
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0038_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0039_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popSame, .skip, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popOpposite, .skip, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth03Prefix0012_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 24502 [.push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 24502
      [.push, .push, .skip] 23302 24101
        24299 24501 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0040_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0041_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0042_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0043_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0013_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 27062 [.skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 27062
      [.skip, .push, .skip] 26049 26356
        26599 27061 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0044_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0045_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0046_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0047_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0014_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 27256 [.popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 27256
      [.popSame, .push, .skip] 27144 27255
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0048_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0049_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popSame, .popSame, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popOpposite, .popSame, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth03Prefix0015_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 27709 [.popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 27709
      [.popOpposite, .push, .skip] 27387 27708
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0050_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0051_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popSame, .popOpposite, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popOpposite, .popOpposite, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth03Prefix0016_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 29531 [.push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 29531
      [.push, .skip, .skip] 28757 29060
        29285 29530 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0052_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0053_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0054_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0055_checker

theorem twentiethCatalogueOrbitResponseDepth03Prefix0017_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      9 30468 [.skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 8 30468
      [.skip, .skip, .skip] 30272 30467
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0056_checker
  · exact twentiethCatalogueOrbitResponseDepth04Prefix0057_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popSame, .skip, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 8 0 [.popOpposite, .skip, .skip, .skip] (by rfl)

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
