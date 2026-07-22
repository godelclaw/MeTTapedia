import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitResponseMatchingAggregate
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk008
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk009
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk010
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk011
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk012
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk013
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk014
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk015
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk016
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk017
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheckChunk018

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching
open ClassicalCertificateOrbitResponseMatchingAggregate

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitResponseDepth05Prefix0000_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 605 [.push, .push, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 605
      [.push, .push, .push, .push, .push] 57 148
        371 604 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0000_checker
  · exact twentiethCatalogueOrbitResponsePrefix0001_checker
  · exact twentiethCatalogueOrbitResponsePrefix0002_checker
  · exact twentiethCatalogueOrbitResponsePrefix0003_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0001_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 1050 [.skip, .push, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 1050
      [.skip, .push, .push, .push, .push] 690 776
        928 1049 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0004_checker
  · exact twentiethCatalogueOrbitResponsePrefix0005_checker
  · exact twentiethCatalogueOrbitResponsePrefix0006_checker
  · exact twentiethCatalogueOrbitResponsePrefix0007_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0002_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 1550 [.popSame, .push, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 1550
      [.popSame, .push, .push, .push, .push] 1132 1286
        1413 1549 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0008_checker
  · exact twentiethCatalogueOrbitResponsePrefix0009_checker
  · exact twentiethCatalogueOrbitResponsePrefix0010_checker
  · exact twentiethCatalogueOrbitResponsePrefix0011_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0003_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 2334 [.popOpposite, .push, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 2334
      [.popOpposite, .push, .push, .push, .push] 1740 1927
        2142 2333 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0012_checker
  · exact twentiethCatalogueOrbitResponsePrefix0013_checker
  · exact twentiethCatalogueOrbitResponsePrefix0014_checker
  · exact twentiethCatalogueOrbitResponsePrefix0015_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0004_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 2810 [.push, .skip, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 2810
      [.push, .skip, .push, .push, .push] 2413 2482
        2635 2809 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0016_checker
  · exact twentiethCatalogueOrbitResponsePrefix0017_checker
  · exact twentiethCatalogueOrbitResponsePrefix0018_checker
  · exact twentiethCatalogueOrbitResponsePrefix0019_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0005_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 3468 [.skip, .skip, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 3468
      [.skip, .skip, .push, .push, .push] 2982 3141
        3290 3467 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0020_checker
  · exact twentiethCatalogueOrbitResponsePrefix0021_checker
  · exact twentiethCatalogueOrbitResponsePrefix0022_checker
  · exact twentiethCatalogueOrbitResponsePrefix0023_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0006_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 3747 [.popSame, .skip, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 3747
      [.popSame, .skip, .push, .push, .push] 3556 3625
        3673 3746 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0024_checker
  · exact twentiethCatalogueOrbitResponsePrefix0025_checker
  · exact twentiethCatalogueOrbitResponsePrefix0026_checker
  · exact twentiethCatalogueOrbitResponsePrefix0027_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0007_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 4137 [.popOpposite, .skip, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 4137
      [.popOpposite, .skip, .push, .push, .push] 3874 3986
        4037 4136 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0028_checker
  · exact twentiethCatalogueOrbitResponsePrefix0029_checker
  · exact twentiethCatalogueOrbitResponsePrefix0030_checker
  · exact twentiethCatalogueOrbitResponsePrefix0031_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0008_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 4726 [.push, .popSame, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 4726
      [.push, .popSame, .push, .push, .push] 4279 4440
        4549 4725 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0032_checker
  · exact twentiethCatalogueOrbitResponsePrefix0033_checker
  · exact twentiethCatalogueOrbitResponsePrefix0034_checker
  · exact twentiethCatalogueOrbitResponsePrefix0035_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0009_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 4953 [.skip, .popSame, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 4953
      [.skip, .popSame, .push, .push, .push] 4793 4837
        4883 4952 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0036_checker
  · exact twentiethCatalogueOrbitResponsePrefix0037_checker
  · exact twentiethCatalogueOrbitResponsePrefix0038_checker
  · exact twentiethCatalogueOrbitResponsePrefix0039_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0010_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 5221 [.popSame, .popSame, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 5221
      [.popSame, .popSame, .push, .push, .push] 5037 5141
        5172 5220 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0040_checker
  · exact twentiethCatalogueOrbitResponsePrefix0041_checker
  · exact twentiethCatalogueOrbitResponsePrefix0042_checker
  · exact twentiethCatalogueOrbitResponsePrefix0043_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0011_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 5386 [.popOpposite, .popSame, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 5386
      [.popOpposite, .popSame, .push, .push, .push] 5278 5344
        5365 5385 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0044_checker
  · exact twentiethCatalogueOrbitResponsePrefix0045_checker
  · exact twentiethCatalogueOrbitResponsePrefix0046_checker
  · exact twentiethCatalogueOrbitResponsePrefix0047_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0012_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 5940 [.push, .popOpposite, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 5940
      [.push, .popOpposite, .push, .push, .push] 5485 5648
        5811 5939 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0048_checker
  · exact twentiethCatalogueOrbitResponsePrefix0049_checker
  · exact twentiethCatalogueOrbitResponsePrefix0050_checker
  · exact twentiethCatalogueOrbitResponsePrefix0051_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0013_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 6282 [.skip, .popOpposite, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 6282
      [.skip, .popOpposite, .push, .push, .push] 6035 6155
        6234 6281 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0052_checker
  · exact twentiethCatalogueOrbitResponsePrefix0053_checker
  · exact twentiethCatalogueOrbitResponsePrefix0054_checker
  · exact twentiethCatalogueOrbitResponsePrefix0055_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0014_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 6594 [.popSame, .popOpposite, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 6594
      [.popSame, .popOpposite, .push, .push, .push] 6400 6513
        6544 6593 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0056_checker
  · exact twentiethCatalogueOrbitResponsePrefix0057_checker
  · exact twentiethCatalogueOrbitResponsePrefix0058_checker
  · exact twentiethCatalogueOrbitResponsePrefix0059_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0015_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 6888 [.popOpposite, .popOpposite, .push, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 6888
      [.popOpposite, .popOpposite, .push, .push, .push] 6706 6796
        6822 6887 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0060_checker
  · exact twentiethCatalogueOrbitResponsePrefix0061_checker
  · exact twentiethCatalogueOrbitResponsePrefix0062_checker
  · exact twentiethCatalogueOrbitResponsePrefix0063_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0016_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 7323 [.push, .push, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 7323
      [.push, .push, .skip, .push, .push] 6982 7048
        7190 7322 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0064_checker
  · exact twentiethCatalogueOrbitResponsePrefix0065_checker
  · exact twentiethCatalogueOrbitResponsePrefix0066_checker
  · exact twentiethCatalogueOrbitResponsePrefix0067_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0017_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 7517 [.skip, .push, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 7517
      [.skip, .push, .skip, .push, .push] 7356 7425
        7449 7516 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0068_checker
  · exact twentiethCatalogueOrbitResponsePrefix0069_checker
  · exact twentiethCatalogueOrbitResponsePrefix0070_checker
  · exact twentiethCatalogueOrbitResponsePrefix0071_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0018_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 7793 [.popSame, .push, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 7793
      [.popSame, .push, .skip, .push, .push] 7593 7647
        7719 7792 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0072_checker
  · exact twentiethCatalogueOrbitResponsePrefix0073_checker
  · exact twentiethCatalogueOrbitResponsePrefix0074_checker
  · exact twentiethCatalogueOrbitResponsePrefix0075_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0019_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8076 [.popOpposite, .push, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8076
      [.popOpposite, .push, .skip, .push, .push] 7876 7957
        8004 8075 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0076_checker
  · exact twentiethCatalogueOrbitResponsePrefix0077_checker
  · exact twentiethCatalogueOrbitResponsePrefix0078_checker
  · exact twentiethCatalogueOrbitResponsePrefix0079_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0020_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8253 [.push, .skip, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8253
      [.push, .skip, .skip, .push, .push] 8134 8159
        8192 8252 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0080_checker
  · exact twentiethCatalogueOrbitResponsePrefix0081_checker
  · exact twentiethCatalogueOrbitResponsePrefix0082_checker
  · exact twentiethCatalogueOrbitResponsePrefix0083_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0021_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8512 [.skip, .skip, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8512
      [.skip, .skip, .skip, .push, .push] 8366 8415
        8466 8511 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0084_checker
  · exact twentiethCatalogueOrbitResponsePrefix0085_checker
  · exact twentiethCatalogueOrbitResponsePrefix0086_checker
  · exact twentiethCatalogueOrbitResponsePrefix0087_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0022_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8617 [.popSame, .skip, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8617
      [.popSame, .skip, .skip, .push, .push] 8558 8570
        8576 8616 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0088_checker
  · exact twentiethCatalogueOrbitResponsePrefix0089_checker
  · exact twentiethCatalogueOrbitResponsePrefix0090_checker
  · exact twentiethCatalogueOrbitResponsePrefix0091_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0023_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8724 [.push, .popSame, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8724
      [.push, .popSame, .skip, .push, .push] 8655 8665
        8700 8723 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0092_checker
  · exact twentiethCatalogueOrbitResponsePrefix0093_checker
  · exact twentiethCatalogueOrbitResponsePrefix0094_checker
  · exact twentiethCatalogueOrbitResponsePrefix0095_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0024_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8783 [.skip, .popSame, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8783
      [.skip, .popSame, .skip, .push, .push] 8739 8773
        8774 8782 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0096_checker
  · exact twentiethCatalogueOrbitResponsePrefix0097_checker
  · exact twentiethCatalogueOrbitResponsePrefix0098_checker
  · exact twentiethCatalogueOrbitResponsePrefix0099_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0025_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8811 [.popSame, .popSame, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8811
      [.popSame, .popSame, .skip, .push, .push] 8800 8810
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0100_checker
  · exact twentiethCatalogueOrbitResponsePrefix0101_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .popSame, .skip, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .popSame, .skip, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0026_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 8852 [.popOpposite, .popSame, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 8852
      [.popOpposite, .popSame, .skip, .push, .push] 8838 8851
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0102_checker
  · exact twentiethCatalogueOrbitResponsePrefix0103_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .popSame, .skip, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .popSame, .skip, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0027_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 9117 [.push, .popOpposite, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 9117
      [.push, .popOpposite, .skip, .push, .push] 8955 8995
        9063 9116 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0104_checker
  · exact twentiethCatalogueOrbitResponsePrefix0105_checker
  · exact twentiethCatalogueOrbitResponsePrefix0106_checker
  · exact twentiethCatalogueOrbitResponsePrefix0107_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0028_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 9201 [.skip, .popOpposite, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 9201
      [.skip, .popOpposite, .skip, .push, .push] 9145 9180
        9194 9200 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0108_checker
  · exact twentiethCatalogueOrbitResponsePrefix0109_checker
  · exact twentiethCatalogueOrbitResponsePrefix0110_checker
  · exact twentiethCatalogueOrbitResponsePrefix0111_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0029_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 9298 [.popSame, .popOpposite, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 9298
      [.popSame, .popOpposite, .skip, .push, .push] 9277 9297
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0112_checker
  · exact twentiethCatalogueOrbitResponsePrefix0113_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .popOpposite, .skip, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .popOpposite, .skip, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0030_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 9365 [.popOpposite, .popOpposite, .skip, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 9365
      [.popOpposite, .popOpposite, .skip, .push, .push] 9343 9364
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0114_checker
  · exact twentiethCatalogueOrbitResponsePrefix0115_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .popOpposite, .skip, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .popOpposite, .skip, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0031_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 9642 [.push, .push, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 9642
      [.push, .push, .popSame, .push, .push] 9445 9509
        9583 9641 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0116_checker
  · exact twentiethCatalogueOrbitResponsePrefix0117_checker
  · exact twentiethCatalogueOrbitResponsePrefix0118_checker
  · exact twentiethCatalogueOrbitResponsePrefix0119_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0032_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 9896 [.skip, .push, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 9896
      [.skip, .push, .popSame, .push, .push] 9738 9790
        9832 9895 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0120_checker
  · exact twentiethCatalogueOrbitResponsePrefix0121_checker
  · exact twentiethCatalogueOrbitResponsePrefix0122_checker
  · exact twentiethCatalogueOrbitResponsePrefix0123_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0033_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 9997 [.popSame, .push, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 9997
      [.popSame, .push, .popSame, .push, .push] 9921 9953
        9966 9996 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0124_checker
  · exact twentiethCatalogueOrbitResponsePrefix0125_checker
  · exact twentiethCatalogueOrbitResponsePrefix0126_checker
  · exact twentiethCatalogueOrbitResponsePrefix0127_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0034_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10147 [.popOpposite, .push, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10147
      [.popOpposite, .push, .popSame, .push, .push] 10044 10082
        10114 10146 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0128_checker
  · exact twentiethCatalogueOrbitResponsePrefix0129_checker
  · exact twentiethCatalogueOrbitResponsePrefix0130_checker
  · exact twentiethCatalogueOrbitResponsePrefix0131_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0035_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10321 [.push, .skip, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10321
      [.push, .skip, .popSame, .push, .push] 10194 10243
        10277 10320 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0132_checker
  · exact twentiethCatalogueOrbitResponsePrefix0133_checker
  · exact twentiethCatalogueOrbitResponsePrefix0134_checker
  · exact twentiethCatalogueOrbitResponsePrefix0135_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0036_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10439 [.skip, .skip, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10439
      [.skip, .skip, .popSame, .push, .push] 10360 10412
        10417 10438 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0136_checker
  · exact twentiethCatalogueOrbitResponsePrefix0137_checker
  · exact twentiethCatalogueOrbitResponsePrefix0138_checker
  · exact twentiethCatalogueOrbitResponsePrefix0139_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0037_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10466 [.popSame, .skip, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10466
      [.popSame, .skip, .popSame, .push, .push] 10465 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0140_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .popSame, .skip, .popSame, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .skip, .popSame, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .skip, .popSame, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0038_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10520 [.popOpposite, .skip, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10520
      [.popOpposite, .skip, .popSame, .push, .push] 10493 10519
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0141_checker
  · exact twentiethCatalogueOrbitResponsePrefix0142_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .skip, .popSame, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .skip, .popSame, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0039_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10598 [.push, .popSame, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10598
      [.push, .popSame, .popSame, .push, .push] 10558 10577
        10583 10597 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0143_checker
  · exact twentiethCatalogueOrbitResponsePrefix0144_checker
  · exact twentiethCatalogueOrbitResponsePrefix0145_checker
  · exact twentiethCatalogueOrbitResponsePrefix0146_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0040_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10665 [.skip, .popSame, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10665
      [.skip, .popSame, .popSame, .push, .push] 10638 10664
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0147_checker
  · exact twentiethCatalogueOrbitResponsePrefix0148_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popSame, .popSame, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popSame, .popSame, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0041_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10850 [.push, .popOpposite, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10850
      [.push, .popOpposite, .popSame, .push, .push] 10735 10804
        10834 10849 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0149_checker
  · exact twentiethCatalogueOrbitResponsePrefix0150_checker
  · exact twentiethCatalogueOrbitResponsePrefix0151_checker
  · exact twentiethCatalogueOrbitResponsePrefix0152_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0042_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 10931 [.skip, .popOpposite, .popSame, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 10931
      [.skip, .popOpposite, .popSame, .push, .push] 10912 10930
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0153_checker
  · exact twentiethCatalogueOrbitResponsePrefix0154_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popOpposite, .popSame, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popOpposite, .popSame, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0043_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 11469 [.push, .push, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 11469
      [.push, .push, .popOpposite, .push, .push] 11085 11201
        11311 11468 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0155_checker
  · exact twentiethCatalogueOrbitResponsePrefix0156_checker
  · exact twentiethCatalogueOrbitResponsePrefix0157_checker
  · exact twentiethCatalogueOrbitResponsePrefix0158_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0044_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 11673 [.skip, .push, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 11673
      [.skip, .push, .popOpposite, .push, .push] 11536 11596
        11642 11672 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0159_checker
  · exact twentiethCatalogueOrbitResponsePrefix0160_checker
  · exact twentiethCatalogueOrbitResponsePrefix0161_checker
  · exact twentiethCatalogueOrbitResponsePrefix0162_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0045_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 11793 [.popSame, .push, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 11793
      [.popSame, .push, .popOpposite, .push, .push] 11718 11759
        11775 11792 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0163_checker
  · exact twentiethCatalogueOrbitResponsePrefix0164_checker
  · exact twentiethCatalogueOrbitResponsePrefix0165_checker
  · exact twentiethCatalogueOrbitResponsePrefix0166_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0046_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 12111 [.popOpposite, .push, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 12111
      [.popOpposite, .push, .popOpposite, .push, .push] 11920 12013
        12053 12110 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0167_checker
  · exact twentiethCatalogueOrbitResponsePrefix0168_checker
  · exact twentiethCatalogueOrbitResponsePrefix0169_checker
  · exact twentiethCatalogueOrbitResponsePrefix0170_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0047_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 12446 [.push, .skip, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 12446
      [.push, .skip, .popOpposite, .push, .push] 12238 12294
        12354 12445 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0171_checker
  · exact twentiethCatalogueOrbitResponsePrefix0172_checker
  · exact twentiethCatalogueOrbitResponsePrefix0173_checker
  · exact twentiethCatalogueOrbitResponsePrefix0174_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0048_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 12766 [.skip, .skip, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 12766
      [.skip, .skip, .popOpposite, .push, .push] 12576 12667
        12699 12765 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0175_checker
  · exact twentiethCatalogueOrbitResponsePrefix0176_checker
  · exact twentiethCatalogueOrbitResponsePrefix0177_checker
  · exact twentiethCatalogueOrbitResponsePrefix0178_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0049_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 12825 [.popSame, .skip, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 12825
      [.popSame, .skip, .popOpposite, .push, .push] 12810 12824
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0179_checker
  · exact twentiethCatalogueOrbitResponsePrefix0180_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .skip, .popOpposite, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .skip, .popOpposite, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0050_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 12861 [.popOpposite, .skip, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 12861
      [.popOpposite, .skip, .popOpposite, .push, .push] 12855 12860
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0181_checker
  · exact twentiethCatalogueOrbitResponsePrefix0182_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .skip, .popOpposite, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .skip, .popOpposite, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0051_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 13065 [.push, .popSame, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 13065
      [.push, .popSame, .popOpposite, .push, .push] 12951 13002
        13020 13064 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0183_checker
  · exact twentiethCatalogueOrbitResponsePrefix0184_checker
  · exact twentiethCatalogueOrbitResponsePrefix0185_checker
  · exact twentiethCatalogueOrbitResponsePrefix0186_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0052_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 13146 [.skip, .popSame, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 13146
      [.skip, .popSame, .popOpposite, .push, .push] 13130 13145
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0187_checker
  · exact twentiethCatalogueOrbitResponsePrefix0188_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popSame, .popOpposite, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popSame, .popOpposite, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0053_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 13516 [.push, .popOpposite, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 13516
      [.push, .popOpposite, .popOpposite, .push, .push] 13318 13430
        13466 13515 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0189_checker
  · exact twentiethCatalogueOrbitResponsePrefix0190_checker
  · exact twentiethCatalogueOrbitResponsePrefix0191_checker
  · exact twentiethCatalogueOrbitResponsePrefix0192_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0054_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 13560 [.skip, .popOpposite, .popOpposite, .push, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 13560
      [.skip, .popOpposite, .popOpposite, .push, .push] 13536 13559
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0193_checker
  · exact twentiethCatalogueOrbitResponsePrefix0194_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popOpposite, .popOpposite, .push, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popOpposite, .popOpposite, .push, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0055_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 13828 [.push, .push, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 13828
      [.push, .push, .push, .skip, .push] 13607 13674
        13707 13827 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0195_checker
  · exact twentiethCatalogueOrbitResponsePrefix0196_checker
  · exact twentiethCatalogueOrbitResponsePrefix0197_checker
  · exact twentiethCatalogueOrbitResponsePrefix0198_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0056_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 14106 [.skip, .push, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 14106
      [.skip, .push, .push, .skip, .push] 13899 13967
        14034 14105 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0199_checker
  · exact twentiethCatalogueOrbitResponsePrefix0200_checker
  · exact twentiethCatalogueOrbitResponsePrefix0201_checker
  · exact twentiethCatalogueOrbitResponsePrefix0202_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0057_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 14280 [.popSame, .push, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 14280
      [.popSame, .push, .push, .skip, .push] 14150 14205
        14246 14279 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0203_checker
  · exact twentiethCatalogueOrbitResponsePrefix0204_checker
  · exact twentiethCatalogueOrbitResponsePrefix0205_checker
  · exact twentiethCatalogueOrbitResponsePrefix0206_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0058_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 14480 [.popOpposite, .push, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 14480
      [.popOpposite, .push, .push, .skip, .push] 14347 14406
        14452 14479 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0207_checker
  · exact twentiethCatalogueOrbitResponsePrefix0208_checker
  · exact twentiethCatalogueOrbitResponsePrefix0209_checker
  · exact twentiethCatalogueOrbitResponsePrefix0210_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0059_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 14692 [.push, .skip, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 14692
      [.push, .skip, .push, .skip, .push] 14537 14569
        14612 14691 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0211_checker
  · exact twentiethCatalogueOrbitResponsePrefix0212_checker
  · exact twentiethCatalogueOrbitResponsePrefix0213_checker
  · exact twentiethCatalogueOrbitResponsePrefix0214_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0060_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 14860 [.skip, .skip, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 14860
      [.skip, .skip, .push, .skip, .push] 14744 14810
        14844 14859 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0215_checker
  · exact twentiethCatalogueOrbitResponsePrefix0216_checker
  · exact twentiethCatalogueOrbitResponsePrefix0217_checker
  · exact twentiethCatalogueOrbitResponsePrefix0218_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0061_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 14939 [.popSame, .skip, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 14939
      [.popSame, .skip, .push, .skip, .push] 14900 14910
        14914 14938 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0219_checker
  · exact twentiethCatalogueOrbitResponsePrefix0220_checker
  · exact twentiethCatalogueOrbitResponsePrefix0221_checker
  · exact twentiethCatalogueOrbitResponsePrefix0222_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0062_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15023 [.popOpposite, .skip, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15023
      [.popOpposite, .skip, .push, .skip, .push] 14976 14996
        15012 15022 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0223_checker
  · exact twentiethCatalogueOrbitResponsePrefix0224_checker
  · exact twentiethCatalogueOrbitResponsePrefix0225_checker
  · exact twentiethCatalogueOrbitResponsePrefix0226_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0063_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15138 [.push, .popSame, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15138
      [.push, .popSame, .push, .skip, .push] 15057 15087
        15095 15137 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0227_checker
  · exact twentiethCatalogueOrbitResponsePrefix0228_checker
  · exact twentiethCatalogueOrbitResponsePrefix0229_checker
  · exact twentiethCatalogueOrbitResponsePrefix0230_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0064_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15257 [.skip, .popSame, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15257
      [.skip, .popSame, .push, .skip, .push] 15201 15218
        15224 15256 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0231_checker
  · exact twentiethCatalogueOrbitResponsePrefix0232_checker
  · exact twentiethCatalogueOrbitResponsePrefix0233_checker
  · exact twentiethCatalogueOrbitResponsePrefix0234_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0065_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15283 [.popSame, .popSame, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15283
      [.popSame, .popSame, .push, .skip, .push] 15276 15282
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0235_checker
  · exact twentiethCatalogueOrbitResponsePrefix0236_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .popSame, .push, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .popSame, .push, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0066_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15332 [.popOpposite, .popSame, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15332
      [.popOpposite, .popSame, .push, .skip, .push] 15312 15331
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0237_checker
  · exact twentiethCatalogueOrbitResponsePrefix0238_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .popSame, .push, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .popSame, .push, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0067_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15523 [.push, .popOpposite, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15523
      [.push, .popOpposite, .push, .skip, .push] 15379 15452
        15488 15522 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0239_checker
  · exact twentiethCatalogueOrbitResponsePrefix0240_checker
  · exact twentiethCatalogueOrbitResponsePrefix0241_checker
  · exact twentiethCatalogueOrbitResponsePrefix0242_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0068_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15629 [.skip, .popOpposite, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15629
      [.skip, .popOpposite, .push, .skip, .push] 15567 15602
        15618 15628 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0243_checker
  · exact twentiethCatalogueOrbitResponsePrefix0244_checker
  · exact twentiethCatalogueOrbitResponsePrefix0245_checker
  · exact twentiethCatalogueOrbitResponsePrefix0246_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0069_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15689 [.popSame, .popOpposite, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15689
      [.popSame, .popOpposite, .push, .skip, .push] 15657 15688
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0247_checker
  · exact twentiethCatalogueOrbitResponsePrefix0248_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .popOpposite, .push, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .popOpposite, .push, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0070_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 15732 [.popOpposite, .popOpposite, .push, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 15732
      [.popOpposite, .popOpposite, .push, .skip, .push] 15714 15731
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0249_checker
  · exact twentiethCatalogueOrbitResponsePrefix0250_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .popOpposite, .push, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .popOpposite, .push, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0071_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16159 [.push, .push, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16159
      [.push, .push, .skip, .skip, .push] 15850 15918
        16042 16158 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0251_checker
  · exact twentiethCatalogueOrbitResponsePrefix0252_checker
  · exact twentiethCatalogueOrbitResponsePrefix0253_checker
  · exact twentiethCatalogueOrbitResponsePrefix0254_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0072_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16210 [.skip, .push, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16210
      [.skip, .push, .skip, .skip, .push] 16171 16191
        0 16209 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0255_checker
  · exact twentiethCatalogueOrbitResponsePrefix0256_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .push, .skip, .skip, .push] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0257_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0073_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16282 [.popSame, .push, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16282
      [.popSame, .push, .skip, .skip, .push] 16239 16251
        16260 16281 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0258_checker
  · exact twentiethCatalogueOrbitResponsePrefix0259_checker
  · exact twentiethCatalogueOrbitResponsePrefix0260_checker
  · exact twentiethCatalogueOrbitResponsePrefix0261_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0074_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16514 [.popOpposite, .push, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16514
      [.popOpposite, .push, .skip, .skip, .push] 16384 16452
        16483 16513 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0262_checker
  · exact twentiethCatalogueOrbitResponsePrefix0263_checker
  · exact twentiethCatalogueOrbitResponsePrefix0264_checker
  · exact twentiethCatalogueOrbitResponsePrefix0265_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0075_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16535 [.push, .skip, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16535
      [.push, .skip, .skip, .skip, .push] 16522 0
        16534 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0266_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .push, .skip, .skip, .skip, .push] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0267_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .push, .skip, .skip, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0076_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16656 [.skip, .skip, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16656
      [.skip, .skip, .skip, .skip, .push] 16582 16628
        16629 16655 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0268_checker
  · exact twentiethCatalogueOrbitResponsePrefix0269_checker
  · exact twentiethCatalogueOrbitResponsePrefix0270_checker
  · exact twentiethCatalogueOrbitResponsePrefix0271_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0077_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16666 [.popOpposite, .skip, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16666
      [.popOpposite, .skip, .skip, .skip, .push] 16665 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0272_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .popOpposite, .skip, .skip, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .skip, .skip, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .skip, .skip, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0078_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16742 [.push, .popSame, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16742
      [.push, .popSame, .skip, .skip, .push] 16698 16730
        16260 16741 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0273_checker
  · exact twentiethCatalogueOrbitResponsePrefix0274_checker
  · exact twentiethCatalogueOrbitResponsePrefix0275_checker
  · exact twentiethCatalogueOrbitResponsePrefix0276_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0079_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 16767 [.skip, .popSame, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 16767
      [.skip, .popSame, .skip, .skip, .push] 16759 16766
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0277_checker
  · exact twentiethCatalogueOrbitResponsePrefix0278_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popSame, .skip, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popSame, .skip, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0080_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17047 [.push, .popOpposite, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17047
      [.push, .popOpposite, .skip, .skip, .push] 16892 16948
        17023 17046 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0279_checker
  · exact twentiethCatalogueOrbitResponsePrefix0280_checker
  · exact twentiethCatalogueOrbitResponsePrefix0281_checker
  · exact twentiethCatalogueOrbitResponsePrefix0282_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0081_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17059 [.skip, .popOpposite, .skip, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17059
      [.skip, .popOpposite, .skip, .skip, .push] 0 17058
        0 0 (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.push, .skip, .popOpposite, .skip, .skip, .push] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0283_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popOpposite, .skip, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popOpposite, .skip, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0082_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17179 [.push, .push, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17179
      [.push, .push, .popSame, .skip, .push] 17096 17137
        17156 17178 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0284_checker
  · exact twentiethCatalogueOrbitResponsePrefix0285_checker
  · exact twentiethCatalogueOrbitResponsePrefix0286_checker
  · exact twentiethCatalogueOrbitResponsePrefix0287_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0083_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17270 [.skip, .push, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17270
      [.skip, .push, .popSame, .skip, .push] 17230 17249
        17252 17269 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0288_checker
  · exact twentiethCatalogueOrbitResponsePrefix0289_checker
  · exact twentiethCatalogueOrbitResponsePrefix0290_checker
  · exact twentiethCatalogueOrbitResponsePrefix0291_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0084_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17286 [.popSame, .push, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17286
      [.popSame, .push, .popSame, .skip, .push] 17282 17285
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0292_checker
  · exact twentiethCatalogueOrbitResponsePrefix0293_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .push, .popSame, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .push, .popSame, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0085_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17326 [.popOpposite, .push, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17326
      [.popOpposite, .push, .popSame, .skip, .push] 17308 17325
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0294_checker
  · exact twentiethCatalogueOrbitResponsePrefix0295_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .push, .popSame, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .push, .popSame, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0086_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17370 [.push, .skip, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17370
      [.push, .skip, .popSame, .skip, .push] 17356 14910
        17359 17369 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0296_checker
  · exact twentiethCatalogueOrbitResponsePrefix0297_checker
  · exact twentiethCatalogueOrbitResponsePrefix0298_checker
  · exact twentiethCatalogueOrbitResponsePrefix0299_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0087_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17383 [.skip, .skip, .popSame, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17383
      [.skip, .skip, .popSame, .skip, .push] 17380 17382
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0300_checker
  · exact twentiethCatalogueOrbitResponsePrefix0301_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .skip, .popSame, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .skip, .popSame, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0088_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17465 [.push, .push, .popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17465
      [.push, .push, .popOpposite, .skip, .push] 17398 17447
        17461 17464 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0302_checker
  · exact twentiethCatalogueOrbitResponsePrefix0303_checker
  · exact twentiethCatalogueOrbitResponsePrefix0304_checker
  · exact twentiethCatalogueOrbitResponsePrefix0305_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0089_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17584 [.skip, .push, .popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17584
      [.skip, .push, .popOpposite, .skip, .push] 17514 17559
        17572 17583 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0306_checker
  · exact twentiethCatalogueOrbitResponsePrefix0307_checker
  · exact twentiethCatalogueOrbitResponsePrefix0308_checker
  · exact twentiethCatalogueOrbitResponsePrefix0309_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0090_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17597 [.popSame, .push, .popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17597
      [.popSame, .push, .popOpposite, .skip, .push] 17587 17596
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0310_checker
  · exact twentiethCatalogueOrbitResponsePrefix0311_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .push, .popOpposite, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .push, .popOpposite, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0091_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17624 [.popOpposite, .push, .popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17624
      [.popOpposite, .push, .popOpposite, .skip, .push] 17610 17623
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0312_checker
  · exact twentiethCatalogueOrbitResponsePrefix0313_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .push, .popOpposite, .skip, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .push, .popOpposite, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0092_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17656 [.push, .skip, .popOpposite, .skip, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17656
      [.push, .skip, .popOpposite, .skip, .push] 17648 0
        17655 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0314_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .push, .skip, .popOpposite, .skip, .push] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0315_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .push, .skip, .popOpposite, .skip, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0093_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 17956 [.push, .push, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 17956
      [.push, .push, .push, .popSame, .push] 17749 17821
        17891 17955 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0316_checker
  · exact twentiethCatalogueOrbitResponsePrefix0317_checker
  · exact twentiethCatalogueOrbitResponsePrefix0318_checker
  · exact twentiethCatalogueOrbitResponsePrefix0319_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0094_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18135 [.skip, .push, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18135
      [.skip, .push, .push, .popSame, .push] 18009 18065
        18115 18134 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0320_checker
  · exact twentiethCatalogueOrbitResponsePrefix0321_checker
  · exact twentiethCatalogueOrbitResponsePrefix0322_checker
  · exact twentiethCatalogueOrbitResponsePrefix0323_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0095_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18211 [.popSame, .push, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18211
      [.popSame, .push, .push, .popSame, .push] 18163 18187
        18192 18210 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0324_checker
  · exact twentiethCatalogueOrbitResponsePrefix0325_checker
  · exact twentiethCatalogueOrbitResponsePrefix0326_checker
  · exact twentiethCatalogueOrbitResponsePrefix0327_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0096_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18393 [.popOpposite, .push, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18393
      [.popOpposite, .push, .push, .popSame, .push] 18298 18346
        18371 18392 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0328_checker
  · exact twentiethCatalogueOrbitResponsePrefix0329_checker
  · exact twentiethCatalogueOrbitResponsePrefix0330_checker
  · exact twentiethCatalogueOrbitResponsePrefix0331_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0097_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18563 [.push, .skip, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18563
      [.push, .skip, .push, .popSame, .push] 18444 18487
        18527 18562 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0332_checker
  · exact twentiethCatalogueOrbitResponsePrefix0333_checker
  · exact twentiethCatalogueOrbitResponsePrefix0334_checker
  · exact twentiethCatalogueOrbitResponsePrefix0335_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0098_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18664 [.skip, .skip, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18664
      [.skip, .skip, .push, .popSame, .push] 18611 18646
        18653 18663 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0336_checker
  · exact twentiethCatalogueOrbitResponsePrefix0337_checker
  · exact twentiethCatalogueOrbitResponsePrefix0338_checker
  · exact twentiethCatalogueOrbitResponsePrefix0339_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0099_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18675 [.popSame, .skip, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18675
      [.popSame, .skip, .push, .popSame, .push] 18674 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0340_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .popSame, .skip, .push, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .skip, .push, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .skip, .push, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0100_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18718 [.popOpposite, .skip, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18718
      [.popOpposite, .skip, .push, .popSame, .push] 18704 18717
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0341_checker
  · exact twentiethCatalogueOrbitResponsePrefix0342_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .skip, .push, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .skip, .push, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0101_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18820 [.push, .popSame, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18820
      [.push, .popSame, .push, .popSame, .push] 18763 18790
        18805 18819 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0343_checker
  · exact twentiethCatalogueOrbitResponsePrefix0344_checker
  · exact twentiethCatalogueOrbitResponsePrefix0345_checker
  · exact twentiethCatalogueOrbitResponsePrefix0346_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0102_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18846 [.skip, .popSame, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18846
      [.skip, .popSame, .push, .popSame, .push] 18840 18845
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0347_checker
  · exact twentiethCatalogueOrbitResponsePrefix0348_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popSame, .push, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popSame, .push, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0103_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18915 [.push, .popOpposite, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18915
      [.push, .popOpposite, .push, .popSame, .push] 18872 18896
        18911 18914 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0349_checker
  · exact twentiethCatalogueOrbitResponsePrefix0350_checker
  · exact twentiethCatalogueOrbitResponsePrefix0351_checker
  · exact twentiethCatalogueOrbitResponsePrefix0352_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0104_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 18980 [.skip, .popOpposite, .push, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 18980
      [.skip, .popOpposite, .push, .popSame, .push] 18958 18979
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0353_checker
  · exact twentiethCatalogueOrbitResponsePrefix0354_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popOpposite, .push, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popOpposite, .push, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0105_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 19119 [.push, .push, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 19119
      [.push, .push, .skip, .popSame, .push] 19010 19057
        19079 19118 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0355_checker
  · exact twentiethCatalogueOrbitResponsePrefix0356_checker
  · exact twentiethCatalogueOrbitResponsePrefix0357_checker
  · exact twentiethCatalogueOrbitResponsePrefix0358_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0106_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 19167 [.skip, .push, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 19167
      [.skip, .push, .skip, .popSame, .push] 19138 19156
        8774 19166 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0359_checker
  · exact twentiethCatalogueOrbitResponsePrefix0360_checker
  · exact twentiethCatalogueOrbitResponsePrefix0361_checker
  · exact twentiethCatalogueOrbitResponsePrefix0362_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0107_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 19187 [.popSame, .push, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 19187
      [.popSame, .push, .skip, .popSame, .push] 19183 19186
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0363_checker
  · exact twentiethCatalogueOrbitResponsePrefix0364_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .push, .skip, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .push, .skip, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0108_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 19205 [.popOpposite, .push, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 19205
      [.popOpposite, .push, .skip, .popSame, .push] 19200 19204
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0365_checker
  · exact twentiethCatalogueOrbitResponsePrefix0366_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .push, .skip, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .push, .skip, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0109_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 19211 [.push, .skip, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 19211
      [.push, .skip, .skip, .popSame, .push] 8558 8570
        8576 19210 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0367_checker
  · exact twentiethCatalogueOrbitResponsePrefix0368_checker
  · exact twentiethCatalogueOrbitResponsePrefix0369_checker
  · exact twentiethCatalogueOrbitResponsePrefix0370_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0110_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 19235 [.skip, .skip, .skip, .popSame, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 19235
      [.skip, .skip, .skip, .popSame, .push] 19232 19234
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0371_checker
  · exact twentiethCatalogueOrbitResponsePrefix0372_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .skip, .skip, .popSame, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .skip, .skip, .popSame, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0111_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 19897 [.push, .push, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 19897
      [.push, .push, .push, .popOpposite, .push] 19415 19566
        19705 19896 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0373_checker
  · exact twentiethCatalogueOrbitResponsePrefix0374_checker
  · exact twentiethCatalogueOrbitResponsePrefix0375_checker
  · exact twentiethCatalogueOrbitResponsePrefix0376_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0112_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 20080 [.skip, .push, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 20080
      [.skip, .push, .push, .popOpposite, .push] 19971 20014
        20035 20079 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0377_checker
  · exact twentiethCatalogueOrbitResponsePrefix0378_checker
  · exact twentiethCatalogueOrbitResponsePrefix0379_checker
  · exact twentiethCatalogueOrbitResponsePrefix0380_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0113_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 20311 [.popSame, .push, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 20311
      [.popSame, .push, .push, .popOpposite, .push] 20167 20260
        20291 20310 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0381_checker
  · exact twentiethCatalogueOrbitResponsePrefix0382_checker
  · exact twentiethCatalogueOrbitResponsePrefix0383_checker
  · exact twentiethCatalogueOrbitResponsePrefix0384_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0114_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 20638 [.popOpposite, .push, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 20638
      [.popOpposite, .push, .push, .popOpposite, .push] 20460 20542
        20583 20637 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0385_checker
  · exact twentiethCatalogueOrbitResponsePrefix0386_checker
  · exact twentiethCatalogueOrbitResponsePrefix0387_checker
  · exact twentiethCatalogueOrbitResponsePrefix0388_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0115_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 20906 [.push, .skip, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 20906
      [.push, .skip, .push, .popOpposite, .push] 20729 20791
        20844 20905 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0389_checker
  · exact twentiethCatalogueOrbitResponsePrefix0390_checker
  · exact twentiethCatalogueOrbitResponsePrefix0391_checker
  · exact twentiethCatalogueOrbitResponsePrefix0392_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0116_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 21334 [.skip, .skip, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 21334
      [.skip, .skip, .push, .popOpposite, .push] 21112 21218
        21262 21333 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0393_checker
  · exact twentiethCatalogueOrbitResponsePrefix0394_checker
  · exact twentiethCatalogueOrbitResponsePrefix0395_checker
  · exact twentiethCatalogueOrbitResponsePrefix0396_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0117_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 21417 [.popSame, .skip, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 21417
      [.popSame, .skip, .push, .popOpposite, .push] 21392 21416
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0397_checker
  · exact twentiethCatalogueOrbitResponsePrefix0398_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .skip, .push, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .skip, .push, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0118_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 21455 [.popOpposite, .skip, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 21455
      [.popOpposite, .skip, .push, .popOpposite, .push] 21449 21454
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0399_checker
  · exact twentiethCatalogueOrbitResponsePrefix0400_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .skip, .push, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .skip, .push, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0119_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 21759 [.push, .popSame, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 21759
      [.push, .popSame, .push, .popOpposite, .push] 21601 21670
        21709 21758 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0401_checker
  · exact twentiethCatalogueOrbitResponsePrefix0402_checker
  · exact twentiethCatalogueOrbitResponsePrefix0403_checker
  · exact twentiethCatalogueOrbitResponsePrefix0404_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0120_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 21811 [.skip, .popSame, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 21811
      [.skip, .popSame, .push, .popOpposite, .push] 21799 21810
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0405_checker
  · exact twentiethCatalogueOrbitResponsePrefix0406_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popSame, .push, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popSame, .push, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0121_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22050 [.push, .popOpposite, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22050
      [.push, .popOpposite, .push, .popOpposite, .push] 21923 21993
        22012 22049 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0407_checker
  · exact twentiethCatalogueOrbitResponsePrefix0408_checker
  · exact twentiethCatalogueOrbitResponsePrefix0409_checker
  · exact twentiethCatalogueOrbitResponsePrefix0410_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0122_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22074 [.skip, .popOpposite, .push, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22074
      [.skip, .popOpposite, .push, .popOpposite, .push] 22063 22073
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0411_checker
  · exact twentiethCatalogueOrbitResponsePrefix0412_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popOpposite, .push, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popOpposite, .push, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0123_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22351 [.push, .push, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22351
      [.push, .push, .skip, .popOpposite, .push] 22179 22223
        22310 22350 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0413_checker
  · exact twentiethCatalogueOrbitResponsePrefix0414_checker
  · exact twentiethCatalogueOrbitResponsePrefix0415_checker
  · exact twentiethCatalogueOrbitResponsePrefix0416_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0124_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22370 [.skip, .push, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22370
      [.skip, .push, .skip, .popOpposite, .push] 0 22369
        0 0 (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.push, .skip, .push, .skip, .popOpposite, .push] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0417_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .push, .skip, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .push, .skip, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0125_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22451 [.popSame, .push, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22451
      [.popSame, .push, .skip, .popOpposite, .push] 22436 22450
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0418_checker
  · exact twentiethCatalogueOrbitResponsePrefix0419_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .push, .skip, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .push, .skip, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0126_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22517 [.popOpposite, .push, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22517
      [.popOpposite, .push, .skip, .popOpposite, .push] 22490 22516
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0420_checker
  · exact twentiethCatalogueOrbitResponsePrefix0421_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .push, .skip, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .push, .skip, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0127_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22559 [.push, .skip, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22559
      [.push, .skip, .skip, .popOpposite, .push] 22531 22546
        22558 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0422_checker
  · exact twentiethCatalogueOrbitResponsePrefix0423_checker
  · exact twentiethCatalogueOrbitResponsePrefix0424_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .push, .skip, .skip, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0128_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22619 [.skip, .skip, .skip, .popOpposite, .push] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22619
      [.skip, .skip, .skip, .popOpposite, .push] 22618 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0425_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .skip, .skip, .skip, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .skip, .skip, .popOpposite, .push] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .skip, .skip, .popOpposite, .push] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0129_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 22911 [.push, .push, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 22911
      [.push, .push, .push, .push, .skip] 22688 22747
        22819 22910 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0426_checker
  · exact twentiethCatalogueOrbitResponsePrefix0427_checker
  · exact twentiethCatalogueOrbitResponsePrefix0428_checker
  · exact twentiethCatalogueOrbitResponsePrefix0429_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0130_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 23080 [.popSame, .push, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 23080
      [.popSame, .push, .push, .push, .skip] 22964 22998
        23028 23079 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0430_checker
  · exact twentiethCatalogueOrbitResponsePrefix0431_checker
  · exact twentiethCatalogueOrbitResponsePrefix0432_checker
  · exact twentiethCatalogueOrbitResponsePrefix0433_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0131_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 23301 [.popOpposite, .push, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 23301
      [.popOpposite, .push, .push, .push, .skip] 23150 23225
        23268 23300 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0434_checker
  · exact twentiethCatalogueOrbitResponsePrefix0435_checker
  · exact twentiethCatalogueOrbitResponsePrefix0436_checker
  · exact twentiethCatalogueOrbitResponsePrefix0437_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0132_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 23609 [.push, .skip, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 23609
      [.push, .skip, .push, .push, .skip] 23378 23431
        23491 23608 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0438_checker
  · exact twentiethCatalogueOrbitResponsePrefix0439_checker
  · exact twentiethCatalogueOrbitResponsePrefix0440_checker
  · exact twentiethCatalogueOrbitResponsePrefix0441_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0133_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 23954 [.skip, .skip, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 23954
      [.skip, .skip, .push, .push, .skip] 23740 23821
        23871 23953 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0442_checker
  · exact twentiethCatalogueOrbitResponsePrefix0443_checker
  · exact twentiethCatalogueOrbitResponsePrefix0444_checker
  · exact twentiethCatalogueOrbitResponsePrefix0445_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0134_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 23999 [.popSame, .skip, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 23999
      [.popSame, .skip, .push, .push, .skip] 23971 23991
        23992 23998 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0446_checker
  · exact twentiethCatalogueOrbitResponsePrefix0447_checker
  · exact twentiethCatalogueOrbitResponsePrefix0448_checker
  · exact twentiethCatalogueOrbitResponsePrefix0449_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0135_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 24100 [.popOpposite, .skip, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 24100
      [.popOpposite, .skip, .push, .push, .skip] 24023 24043
        24075 24099 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0450_checker
  · exact twentiethCatalogueOrbitResponsePrefix0451_checker
  · exact twentiethCatalogueOrbitResponsePrefix0452_checker
  · exact twentiethCatalogueOrbitResponsePrefix0453_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0136_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 24220 [.push, .popSame, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 24220
      [.push, .popSame, .push, .push, .skip] 24138 24183
        24201 24219 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0454_checker
  · exact twentiethCatalogueOrbitResponsePrefix0455_checker
  · exact twentiethCatalogueOrbitResponsePrefix0456_checker
  · exact twentiethCatalogueOrbitResponsePrefix0457_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0137_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 24251 [.popSame, .popSame, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 24251
      [.popSame, .popSame, .push, .push, .skip] 24244 24250
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0458_checker
  · exact twentiethCatalogueOrbitResponsePrefix0459_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .popSame, .push, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .popSame, .push, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0138_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 24298 [.popOpposite, .popSame, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 24298
      [.popOpposite, .popSame, .push, .push, .skip] 24274 24297
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0460_checker
  · exact twentiethCatalogueOrbitResponsePrefix0461_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .popSame, .push, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .popSame, .push, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0139_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 24441 [.push, .popOpposite, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 24441
      [.push, .popOpposite, .push, .push, .skip] 24350 24373
        24408 24440 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0462_checker
  · exact twentiethCatalogueOrbitResponsePrefix0463_checker
  · exact twentiethCatalogueOrbitResponsePrefix0464_checker
  · exact twentiethCatalogueOrbitResponsePrefix0465_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0140_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 24463 [.popSame, .popOpposite, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 24463
      [.popSame, .popOpposite, .push, .push, .skip] 24462 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0466_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .popSame, .popOpposite, .push, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .popOpposite, .push, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .popOpposite, .push, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0141_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 24500 [.popOpposite, .popOpposite, .push, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 24500
      [.popOpposite, .popOpposite, .push, .push, .skip] 24489 24499
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0467_checker
  · exact twentiethCatalogueOrbitResponsePrefix0468_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .popOpposite, .push, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .popOpposite, .push, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0142_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 25188 [.push, .push, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 25188
      [.push, .push, .skip, .push, .skip] 24676 24827
        24985 25187 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0469_checker
  · exact twentiethCatalogueOrbitResponsePrefix0470_checker
  · exact twentiethCatalogueOrbitResponsePrefix0471_checker
  · exact twentiethCatalogueOrbitResponsePrefix0472_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0143_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 25544 [.skip, .push, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 25544
      [.skip, .push, .skip, .push, .skip] 25325 25432
        25498 25543 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0473_checker
  · exact twentiethCatalogueOrbitResponsePrefix0474_checker
  · exact twentiethCatalogueOrbitResponsePrefix0475_checker
  · exact twentiethCatalogueOrbitResponsePrefix0476_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0144_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 25694 [.popSame, .push, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 25694
      [.popSame, .push, .skip, .push, .skip] 25592 25639
        25652 25693 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0477_checker
  · exact twentiethCatalogueOrbitResponsePrefix0478_checker
  · exact twentiethCatalogueOrbitResponsePrefix0479_checker
  · exact twentiethCatalogueOrbitResponsePrefix0480_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0145_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26048 [.popOpposite, .push, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26048
      [.popOpposite, .push, .skip, .push, .skip] 25828 25959
        26000 26047 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0481_checker
  · exact twentiethCatalogueOrbitResponsePrefix0482_checker
  · exact twentiethCatalogueOrbitResponsePrefix0483_checker
  · exact twentiethCatalogueOrbitResponsePrefix0484_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0146_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26213 [.push, .skip, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26213
      [.push, .skip, .skip, .push, .skip] 26103 26145
        26153 26212 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0485_checker
  · exact twentiethCatalogueOrbitResponsePrefix0486_checker
  · exact twentiethCatalogueOrbitResponsePrefix0487_checker
  · exact twentiethCatalogueOrbitResponsePrefix0488_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0147_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26285 [.skip, .skip, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26285
      [.skip, .skip, .skip, .push, .skip] 26257 0
        26259 26284 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0489_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .skip, .skip, .skip, .push, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0490_checker
  · exact twentiethCatalogueOrbitResponsePrefix0491_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0148_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26319 [.popSame, .skip, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26319
      [.popSame, .skip, .skip, .push, .skip] 26318 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0492_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .popSame, .skip, .skip, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .skip, .skip, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .skip, .skip, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0149_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26355 [.popOpposite, .skip, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26355
      [.popOpposite, .skip, .skip, .push, .skip] 26329 26354
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0493_checker
  · exact twentiethCatalogueOrbitResponsePrefix0494_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .skip, .skip, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .skip, .skip, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0150_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26562 [.push, .popSame, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26562
      [.push, .popSame, .skip, .push, .skip] 26431 26511
        26522 26561 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0495_checker
  · exact twentiethCatalogueOrbitResponsePrefix0496_checker
  · exact twentiethCatalogueOrbitResponsePrefix0497_checker
  · exact twentiethCatalogueOrbitResponsePrefix0498_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0151_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26598 [.skip, .popSame, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26598
      [.skip, .popSame, .skip, .push, .skip] 26585 26597
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0499_checker
  · exact twentiethCatalogueOrbitResponsePrefix0500_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popSame, .skip, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popSame, .skip, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0152_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 26931 [.push, .popOpposite, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 26931
      [.push, .popOpposite, .skip, .push, .skip] 26758 26840
        26879 26930 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0501_checker
  · exact twentiethCatalogueOrbitResponsePrefix0502_checker
  · exact twentiethCatalogueOrbitResponsePrefix0503_checker
  · exact twentiethCatalogueOrbitResponsePrefix0504_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0153_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27060 [.skip, .popOpposite, .skip, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27060
      [.skip, .popOpposite, .skip, .push, .skip] 27014 27059
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0505_checker
  · exact twentiethCatalogueOrbitResponsePrefix0506_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popOpposite, .skip, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popOpposite, .skip, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0154_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27114 [.push, .push, .popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27114
      [.push, .push, .popSame, .push, .skip] 27083 27095
        27107 27113 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0507_checker
  · exact twentiethCatalogueOrbitResponsePrefix0508_checker
  · exact twentiethCatalogueOrbitResponsePrefix0509_checker
  · exact twentiethCatalogueOrbitResponsePrefix0510_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0155_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27119 [.popSame, .push, .popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27119
      [.popSame, .push, .popSame, .push, .skip] 24244 27118
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0511_checker
  · exact twentiethCatalogueOrbitResponsePrefix0512_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .push, .popSame, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .push, .popSame, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0156_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27143 [.popOpposite, .push, .popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27143
      [.popOpposite, .push, .popSame, .push, .skip] 27125 27142
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0513_checker
  · exact twentiethCatalogueOrbitResponsePrefix0514_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .push, .popSame, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .push, .popSame, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0157_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27214 [.push, .skip, .popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27214
      [.push, .skip, .popSame, .push, .skip] 27173 27187
        27190 27213 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0515_checker
  · exact twentiethCatalogueOrbitResponsePrefix0516_checker
  · exact twentiethCatalogueOrbitResponsePrefix0517_checker
  · exact twentiethCatalogueOrbitResponsePrefix0518_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0158_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27254 [.skip, .skip, .popSame, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27254
      [.skip, .skip, .popSame, .push, .skip] 27242 27253
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0519_checker
  · exact twentiethCatalogueOrbitResponsePrefix0520_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .skip, .popSame, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .skip, .popSame, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0159_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27339 [.push, .push, .popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27339
      [.push, .push, .popOpposite, .push, .skip] 27284 27301
        27323 27338 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0521_checker
  · exact twentiethCatalogueOrbitResponsePrefix0522_checker
  · exact twentiethCatalogueOrbitResponsePrefix0523_checker
  · exact twentiethCatalogueOrbitResponsePrefix0524_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0160_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27363 [.popSame, .push, .popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27363
      [.popSame, .push, .popOpposite, .push, .skip] 27353 27362
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0525_checker
  · exact twentiethCatalogueOrbitResponsePrefix0526_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .push, .popOpposite, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .push, .popOpposite, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0161_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27386 [.popOpposite, .push, .popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27386
      [.popOpposite, .push, .popOpposite, .push, .skip] 27378 27385
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0527_checker
  · exact twentiethCatalogueOrbitResponsePrefix0528_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .push, .popOpposite, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .push, .popOpposite, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0162_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27602 [.push, .skip, .popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27602
      [.push, .skip, .popOpposite, .push, .skip] 27470 27517
        27544 27601 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0529_checker
  · exact twentiethCatalogueOrbitResponsePrefix0530_checker
  · exact twentiethCatalogueOrbitResponsePrefix0531_checker
  · exact twentiethCatalogueOrbitResponsePrefix0532_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0163_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 27707 [.skip, .skip, .popOpposite, .push, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 27707
      [.skip, .skip, .popOpposite, .push, .skip] 27671 27706
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0533_checker
  · exact twentiethCatalogueOrbitResponsePrefix0534_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .skip, .popOpposite, .push, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .skip, .popOpposite, .push, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0164_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 28121 [.push, .push, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 28121
      [.push, .push, .push, .skip, .skip] 27809 27889
        28002 28120 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0535_checker
  · exact twentiethCatalogueOrbitResponsePrefix0536_checker
  · exact twentiethCatalogueOrbitResponsePrefix0537_checker
  · exact twentiethCatalogueOrbitResponsePrefix0538_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0165_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 28468 [.skip, .push, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 28468
      [.skip, .push, .push, .skip, .skip] 28253 28344
        28408 28467 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0539_checker
  · exact twentiethCatalogueOrbitResponsePrefix0540_checker
  · exact twentiethCatalogueOrbitResponsePrefix0541_checker
  · exact twentiethCatalogueOrbitResponsePrefix0542_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0166_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 28577 [.popSame, .push, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 28577
      [.popSame, .push, .push, .skip, .skip] 28492 28517
        28532 28576 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0543_checker
  · exact twentiethCatalogueOrbitResponsePrefix0544_checker
  · exact twentiethCatalogueOrbitResponsePrefix0545_checker
  · exact twentiethCatalogueOrbitResponsePrefix0546_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0167_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 28756 [.popOpposite, .push, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 28756
      [.popOpposite, .push, .push, .skip, .skip] 28652 28715
        28747 28755 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0547_checker
  · exact twentiethCatalogueOrbitResponsePrefix0548_checker
  · exact twentiethCatalogueOrbitResponsePrefix0549_checker
  · exact twentiethCatalogueOrbitResponsePrefix0550_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0168_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 28921 [.push, .skip, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 28921
      [.push, .skip, .push, .skip, .skip] 28841 0
        28878 28920 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0551_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .push, .skip, .push, .skip, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0552_checker
  · exact twentiethCatalogueOrbitResponsePrefix0553_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0169_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 29050 [.skip, .skip, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 29050
      [.skip, .skip, .push, .skip, .skip] 28974 29019
        29021 29049 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0554_checker
  · exact twentiethCatalogueOrbitResponsePrefix0555_checker
  · exact twentiethCatalogueOrbitResponsePrefix0556_checker
  · exact twentiethCatalogueOrbitResponsePrefix0557_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0170_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 29059 [.popSame, .skip, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 29059
      [.popSame, .skip, .push, .skip, .skip] 29058 0
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0558_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.skip, .popSame, .skip, .push, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .skip, .push, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .skip, .push, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0171_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 29253 [.push, .popSame, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 29253
      [.push, .popSame, .push, .skip, .skip] 29137 29187
        29197 29252 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0559_checker
  · exact twentiethCatalogueOrbitResponsePrefix0560_checker
  · exact twentiethCatalogueOrbitResponsePrefix0561_checker
  · exact twentiethCatalogueOrbitResponsePrefix0562_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0172_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 29284 [.skip, .popSame, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 29284
      [.skip, .popSame, .push, .skip, .skip] 29275 29283
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0563_checker
  · exact twentiethCatalogueOrbitResponsePrefix0564_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popSame, .push, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popSame, .push, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0173_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 29402 [.push, .popOpposite, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 29402
      [.push, .popOpposite, .push, .skip, .skip] 29342 29370
        29395 29401 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0565_checker
  · exact twentiethCatalogueOrbitResponsePrefix0566_checker
  · exact twentiethCatalogueOrbitResponsePrefix0567_checker
  · exact twentiethCatalogueOrbitResponsePrefix0568_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0174_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 29529 [.skip, .popOpposite, .push, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 29529
      [.skip, .popOpposite, .push, .skip, .skip] 29483 29528
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0569_checker
  · exact twentiethCatalogueOrbitResponsePrefix0570_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .popOpposite, .push, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .popOpposite, .push, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0175_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 29989 [.push, .push, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 29989
      [.push, .push, .skip, .skip, .skip] 29699 29814
        29888 29988 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0571_checker
  · exact twentiethCatalogueOrbitResponsePrefix0572_checker
  · exact twentiethCatalogueOrbitResponsePrefix0573_checker
  · exact twentiethCatalogueOrbitResponsePrefix0574_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0176_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 30063 [.skip, .push, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 30063
      [.skip, .push, .skip, .skip, .skip] 30003 30050
        0 30062 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0575_checker
  · exact twentiethCatalogueOrbitResponsePrefix0576_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .push, .skip, .skip, .skip] (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0577_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0177_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 30089 [.popSame, .push, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 30089
      [.popSame, .push, .skip, .skip, .skip] 30081 30088
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0578_checker
  · exact twentiethCatalogueOrbitResponsePrefix0579_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popSame, .push, .skip, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popSame, .push, .skip, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0178_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 30271 [.popOpposite, .push, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 30271
      [.popOpposite, .push, .skip, .skip, .skip] 30207 30270
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0580_checker
  · exact twentiethCatalogueOrbitResponsePrefix0581_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .popOpposite, .push, .skip, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .popOpposite, .push, .skip, .skip, .skip] (by rfl)

theorem twentiethCatalogueOrbitResponseDepth05Prefix0179_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 30346 [.push, .skip, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 30346
      [.push, .skip, .skip, .skip, .skip] 30302 30326
        30327 30345 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0582_checker
  · exact twentiethCatalogueOrbitResponsePrefix0583_checker
  · exact twentiethCatalogueOrbitResponsePrefix0584_checker
  · exact twentiethCatalogueOrbitResponsePrefix0585_checker

theorem twentiethCatalogueOrbitResponseDepth05Prefix0180_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate
      7 30466 [.skip, .skip, .skip, .skip, .skip] = true := by
  apply matchingBoolean_succ_of_node
    twentiethCatalogueOrbitProductCertificate 6 30466
      [.skip, .skip, .skip, .skip, .skip] 30445 30465
        0 0 (by rfl)
  · exact twentiethCatalogueOrbitResponsePrefix0586_checker
  · exact twentiethCatalogueOrbitResponsePrefix0587_checker
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popSame, .skip, .skip, .skip, .skip, .skip] (by rfl)
  · exact matchingBoolean_of_empty twentiethCatalogueOrbitProductCertificate 6 0 [.popOpposite, .skip, .skip, .skip, .skip, .skip] (by rfl)

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
