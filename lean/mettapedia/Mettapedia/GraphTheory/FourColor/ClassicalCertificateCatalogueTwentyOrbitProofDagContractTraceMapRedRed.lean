import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapBase

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap

open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagContractTraceMapRedRed_checker :
    Tree.checkAt twentiethCatalogueOrbitProofDagContractTraceTarget 10
      (twentiethCatalogueOrbitProofDagContractTraceMapBranch .red .red)
      [.red, .red] = true := by
  rfl

end ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap

end Mettapedia.GraphTheory.FourColor
