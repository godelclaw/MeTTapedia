import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapBase

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagContractTraceMapBluePurple_checker :
    Tree.checkAt twentiethCatalogueProofDagContractTraceTarget 10
      (twentiethCatalogueProofDagContractTraceMapBranch .blue .purple)
      [.blue, .purple] = true := by
  rfl

end ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

end Mettapedia.GraphTheory.FourColor
