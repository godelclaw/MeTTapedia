import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProductData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitResponseMatching

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateOrbitResponseMatching

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitResponsePrefix0000_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      57 [.push, .push, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0001_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      148 [.skip, .push, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0002_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      371 [.popSame, .push, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0003_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      604 [.popOpposite, .push, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0004_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      690 [.push, .skip, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0005_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      776 [.skip, .skip, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0006_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      928 [.popSame, .skip, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0007_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      1049 [.popOpposite, .skip, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0008_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      1132 [.push, .popSame, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0009_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      1286 [.skip, .popSame, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0010_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      1413 [.popSame, .popSame, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0011_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      1549 [.popOpposite, .popSame, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0012_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      1740 [.push, .popOpposite, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0013_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      1927 [.skip, .popOpposite, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0014_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      2142 [.popSame, .popOpposite, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0015_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      2333 [.popOpposite, .popOpposite, .push, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0016_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      2413 [.push, .push, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0017_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      2482 [.skip, .push, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0018_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      2635 [.popSame, .push, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0019_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      2809 [.popOpposite, .push, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0020_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      2982 [.push, .skip, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0021_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3141 [.skip, .skip, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0022_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3290 [.popSame, .skip, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0023_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3467 [.popOpposite, .skip, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0024_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3556 [.push, .popSame, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0025_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3625 [.skip, .popSame, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0026_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3673 [.popSame, .popSame, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0027_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3746 [.popOpposite, .popSame, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0028_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3874 [.push, .popOpposite, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0029_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      3986 [.skip, .popOpposite, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0030_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      4037 [.popSame, .popOpposite, .skip, .push, .push, .push] = true := by
  rfl

theorem twentiethCatalogueOrbitResponsePrefix0031_checker :
    matchingBoolean twentiethCatalogueOrbitProductCertificate 6
      4136 [.popOpposite, .popOpposite, .skip, .push, .push, .push] = true := by
  rfl

end ClassicalCertificateCatalogueTwentyOrbitResponseMatchingCheck

end Mettapedia.GraphTheory.FourColor
