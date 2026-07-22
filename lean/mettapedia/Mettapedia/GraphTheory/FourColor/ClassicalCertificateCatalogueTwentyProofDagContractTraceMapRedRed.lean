import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapBase

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagContractTraceMapRedRed_checker :
    Tree.checkAt twentiethCatalogueProofDagContractTraceTarget 10
      (twentiethCatalogueProofDagContractTraceMapBranch .red .red)
      [.red, .red] = true := by
  rfl

end ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

end Mettapedia.GraphTheory.FourColor
