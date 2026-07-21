import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapRedRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapRedBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapRedPurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapBlueRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapBlueBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapBluePurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapPurpleRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapPurpleBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapPurplePurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The nine checked two-symbol branches reassemble the complete contract
trace map. -/
theorem twentiethCatalogueContractTraceMap_checker :
    twentiethCatalogueContractTraceMap.checker 12
      twentiethCatalogueContractTraceTarget = true := by
  change
    (((Tree.checkAt twentiethCatalogueContractTraceTarget 10
          (twentiethCatalogueContractTraceMapBranch .red .red)
            [.red, .red] &&
        Tree.checkAt twentiethCatalogueContractTraceTarget 10
          (twentiethCatalogueContractTraceMapBranch .red .blue)
            [.red, .blue]) &&
      Tree.checkAt twentiethCatalogueContractTraceTarget 10
        (twentiethCatalogueContractTraceMapBranch .red .purple)
          [.red, .purple]) &&
      ((Tree.checkAt twentiethCatalogueContractTraceTarget 10
          (twentiethCatalogueContractTraceMapBranch .blue .red)
            [.blue, .red] &&
        Tree.checkAt twentiethCatalogueContractTraceTarget 10
          (twentiethCatalogueContractTraceMapBranch .blue .blue)
            [.blue, .blue]) &&
      Tree.checkAt twentiethCatalogueContractTraceTarget 10
        (twentiethCatalogueContractTraceMapBranch .blue .purple)
          [.blue, .purple])) &&
    ((Tree.checkAt twentiethCatalogueContractTraceTarget 10
        (twentiethCatalogueContractTraceMapBranch .purple .red)
          [.purple, .red] &&
      Tree.checkAt twentiethCatalogueContractTraceTarget 10
        (twentiethCatalogueContractTraceMapBranch .purple .blue)
          [.purple, .blue]) &&
    Tree.checkAt twentiethCatalogueContractTraceTarget 10
      (twentiethCatalogueContractTraceMapBranch .purple .purple)
        [.purple, .purple]) = true
  simp only [twentiethCatalogueContractTraceMapRedRed_checker,
    twentiethCatalogueContractTraceMapRedBlue_checker,
    twentiethCatalogueContractTraceMapRedPurple_checker,
    twentiethCatalogueContractTraceMapBlueRed_checker,
    twentiethCatalogueContractTraceMapBlueBlue_checker,
    twentiethCatalogueContractTraceMapBluePurple_checker,
    twentiethCatalogueContractTraceMapPurpleRed_checker,
    twentiethCatalogueContractTraceMapPurpleBlue_checker,
    twentiethCatalogueContractTraceMapPurplePurple_checker,
    Bool.and_self]
  decide

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
