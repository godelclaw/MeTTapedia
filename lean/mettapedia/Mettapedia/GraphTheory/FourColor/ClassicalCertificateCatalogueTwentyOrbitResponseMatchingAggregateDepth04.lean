import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingAggregateDepth05

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateOrbitResponseMatchingAggregate

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitResponseDepth04Prefix0000_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 2335 [.push, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 2335
      [.push, .push, .push, .push] 605 1050
        1550 2334 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0000_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0001_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0002_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0003_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0001_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 4138 [.skip, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 4138
      [.skip, .push, .push, .push] 2810 3468
        3747 4137 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0004_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0005_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0006_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0007_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0002_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 5387 [.popSame, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 5387
      [.popSame, .push, .push, .push] 4726 4953
        5221 5386 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0008_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0009_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0010_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0011_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0003_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 6889 [.popOpposite, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 6889
      [.popOpposite, .push, .push, .push] 5940 6282
        6594 6888 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0012_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0013_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0014_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0015_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0004_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 8077 [.push, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 8077
      [.push, .skip, .push, .push] 7323 7517
        7793 8076 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0016_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0017_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0018_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0019_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0005_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 8618 [.skip, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 8618
      [.skip, .skip, .push, .push] 8253 8512
        8617 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0020_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0021_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0022_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .skip, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0006_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 8853 [.popSame, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 8853
      [.popSame, .skip, .push, .push] 8724 8783
        8811 8852 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0023_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0024_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0025_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0026_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0007_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 9366 [.popOpposite, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 9366
      [.popOpposite, .skip, .push, .push] 9117 9201
        9298 9365 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0027_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0028_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0029_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0030_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0008_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 10148 [.push, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 10148
      [.push, .popSame, .push, .push] 9642 9896
        9997 10147 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0031_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0032_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0033_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0034_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0009_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 10521 [.skip, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 10521
      [.skip, .popSame, .push, .push] 10321 10439
        10466 10520 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0035_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0036_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0037_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0038_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0010_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 10666 [.popSame, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 10666
      [.popSame, .popSame, .push, .push] 10598 10665
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0039_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0040_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popSame, .popSame, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popSame, .popSame, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0011_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 10932 [.popOpposite, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 10932
      [.popOpposite, .popSame, .push, .push] 10850 10931
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0041_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0042_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popOpposite, .popSame, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popOpposite, .popSame, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0012_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 12112 [.push, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 12112
      [.push, .popOpposite, .push, .push] 11469 11673
        11793 12111 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0043_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0044_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0045_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0046_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0013_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 12862 [.skip, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 12862
      [.skip, .popOpposite, .push, .push] 12446 12766
        12825 12861 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0047_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0048_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0049_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0050_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0014_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 13147 [.popSame, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 13147
      [.popSame, .popOpposite, .push, .push] 13065 13146
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0051_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0052_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popSame, .popOpposite, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popSame, .popOpposite, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0015_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 13561 [.popOpposite, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 13561
      [.popOpposite, .popOpposite, .push, .push] 13516 13560
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0053_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0054_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popOpposite, .popOpposite, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popOpposite, .popOpposite, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0016_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 14481 [.push, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 14481
      [.push, .push, .skip, .push] 13828 14106
        14280 14480 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0055_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0056_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0057_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0058_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0017_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 15024 [.skip, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 15024
      [.skip, .push, .skip, .push] 14692 14860
        14939 15023 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0059_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0060_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0061_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0062_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0018_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 15333 [.popSame, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 15333
      [.popSame, .push, .skip, .push] 15138 15257
        15283 15332 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0063_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0064_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0065_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0066_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0019_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 15733 [.popOpposite, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 15733
      [.popOpposite, .push, .skip, .push] 15523 15629
        15689 15732 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0067_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0068_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0069_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0070_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0020_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 16515 [.push, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 16515
      [.push, .skip, .skip, .push] 16159 16210
        16282 16514 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0071_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0072_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0073_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0074_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0021_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 16667 [.skip, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 16667
      [.skip, .skip, .skip, .push] 16535 16656
        0 16666 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0075_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0076_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .skip, .skip, .push] (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0077_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0022_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 16768 [.popSame, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 16768
      [.popSame, .skip, .skip, .push] 16742 16767
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0078_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0079_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popSame, .skip, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popSame, .skip, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0023_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 17060 [.popOpposite, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 17060
      [.popOpposite, .skip, .skip, .push] 17047 17059
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0080_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0081_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popOpposite, .skip, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popOpposite, .skip, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0024_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 17327 [.push, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 17327
      [.push, .popSame, .skip, .push] 17179 17270
        17286 17326 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0082_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0083_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0084_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0085_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0025_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 17384 [.skip, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 17384
      [.skip, .popSame, .skip, .push] 17370 17383
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0086_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0087_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .popSame, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .popSame, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0026_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 17625 [.push, .popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 17625
      [.push, .popOpposite, .skip, .push] 17465 17584
        17597 17624 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0088_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0089_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0090_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0091_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0027_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 17657 [.skip, .popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 17657
      [.skip, .popOpposite, .skip, .push] 17656 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0092_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.skip, .skip, .popOpposite, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .popOpposite, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .popOpposite, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0028_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 18394 [.push, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 18394
      [.push, .push, .popSame, .push] 17956 18135
        18211 18393 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0093_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0094_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0095_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0096_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0029_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 18719 [.skip, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 18719
      [.skip, .push, .popSame, .push] 18563 18664
        18675 18718 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0097_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0098_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0099_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0100_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0030_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 18847 [.popSame, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 18847
      [.popSame, .push, .popSame, .push] 18820 18846
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0101_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0102_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popSame, .push, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popSame, .push, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0031_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 18981 [.popOpposite, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 18981
      [.popOpposite, .push, .popSame, .push] 18915 18980
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0103_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0104_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popOpposite, .push, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popOpposite, .push, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0032_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 19206 [.push, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 19206
      [.push, .skip, .popSame, .push] 19119 19167
        19187 19205 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0105_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0106_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0107_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0108_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0033_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 19236 [.skip, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 19236
      [.skip, .skip, .popSame, .push] 19211 19235
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0109_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0110_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .skip, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .skip, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0034_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 20639 [.push, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 20639
      [.push, .push, .popOpposite, .push] 19897 20080
        20311 20638 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0111_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0112_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0113_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0114_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0035_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 21456 [.skip, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 21456
      [.skip, .push, .popOpposite, .push] 20906 21334
        21417 21455 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0115_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0116_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0117_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0118_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0036_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 21812 [.popSame, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 21812
      [.popSame, .push, .popOpposite, .push] 21759 21811
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0119_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0120_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popSame, .push, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popSame, .push, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0037_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 22075 [.popOpposite, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 22075
      [.popOpposite, .push, .popOpposite, .push] 22050 22074
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0121_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0122_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popOpposite, .push, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popOpposite, .push, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0038_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 22518 [.push, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 22518
      [.push, .skip, .popOpposite, .push] 22351 22370
        22451 22517 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0123_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0124_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0125_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0126_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0039_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 22620 [.skip, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 22620
      [.skip, .skip, .popOpposite, .push] 22559 22619
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0127_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0128_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .skip, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .skip, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0040_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 23302 [.push, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 23302
      [.push, .push, .push, .skip] 22911 0
        23080 23301 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0129_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.skip, .push, .push, .push, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0130_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0131_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0041_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 24101 [.skip, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 24101
      [.skip, .push, .push, .skip] 23609 23954
        23999 24100 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0132_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0133_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0134_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0135_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0042_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 24299 [.popSame, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 24299
      [.popSame, .push, .push, .skip] 24220 0
        24251 24298 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0136_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.skip, .popSame, .push, .push, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0137_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0138_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0043_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 24501 [.popOpposite, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 24501
      [.popOpposite, .push, .push, .skip] 24441 0
        24463 24500 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0139_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.skip, .popOpposite, .push, .push, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0140_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0141_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0044_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 26049 [.push, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 26049
      [.push, .skip, .push, .skip] 25188 25544
        25694 26048 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0142_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0143_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0144_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0145_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0045_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 26356 [.skip, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 26356
      [.skip, .skip, .push, .skip] 26213 26285
        26319 26355 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0146_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0147_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0148_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0149_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0046_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 26599 [.popSame, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 26599
      [.popSame, .skip, .push, .skip] 26562 26598
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0150_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0151_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popSame, .skip, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popSame, .skip, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0047_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 27061 [.popOpposite, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 27061
      [.popOpposite, .skip, .push, .skip] 26931 27060
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0152_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0153_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popOpposite, .skip, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popOpposite, .skip, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0048_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 27144 [.push, .popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 27144
      [.push, .popSame, .push, .skip] 27114 0
        27119 27143 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0154_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.skip, .push, .popSame, .push, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0155_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0156_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0049_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 27255 [.skip, .popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 27255
      [.skip, .popSame, .push, .skip] 27214 27254
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0157_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0158_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .popSame, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .popSame, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0050_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 27387 [.push, .popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 27387
      [.push, .popOpposite, .push, .skip] 27339 0
        27363 27386 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0159_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.skip, .push, .popOpposite, .push, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0160_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0161_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0051_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 27708 [.skip, .popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 27708
      [.skip, .popOpposite, .push, .skip] 27602 27707
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0162_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0163_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .popOpposite, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .popOpposite, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0052_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 28757 [.push, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 28757
      [.push, .push, .skip, .skip] 28121 28468
        28577 28756 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0164_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0165_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0166_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0167_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0053_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 29060 [.skip, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 29060
      [.skip, .push, .skip, .skip] 28921 29050
        29059 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0168_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0169_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0170_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .push, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0054_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 29285 [.popSame, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 29285
      [.popSame, .push, .skip, .skip] 29253 29284
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0171_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0172_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popSame, .push, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popSame, .push, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0055_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 29530 [.popOpposite, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 29530
      [.popOpposite, .push, .skip, .skip] 29402 29529
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0173_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0174_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .popOpposite, .push, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .popOpposite, .push, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth04Prefix0056_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 30272 [.push, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 30272
      [.push, .skip, .skip, .skip] 29989 30063
        30089 30271 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0175_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0176_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0177_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0178_checker

theorem twentiethCatalogueOrbitResponseDepth04Prefix0057_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      8 30467 [.skip, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 7 30467
      [.skip, .skip, .skip, .skip] 30346 30466
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0179_checker
  · exact twentiethCatalogueOrbitResponseDepth05Prefix0180_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popSame, .skip, .skip, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 7 0 [.popOpposite, .skip, .skip, .skip, .skip] (by rfl)

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
