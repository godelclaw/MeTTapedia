import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMap

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueContractTraceMapRedPurple_checker :
    ClassicalCertificateIndexedTraceMap.Tree.checkAt
      twentiethCatalogueContractTraceTarget 10
        (twentiethCatalogueContractTraceMapBranch
          .red .purple)
            [.red, .purple] = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
