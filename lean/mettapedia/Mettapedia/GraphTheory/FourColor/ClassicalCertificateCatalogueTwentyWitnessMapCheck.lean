import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyLayers

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateIndexedTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Every stored trace points to a witness carrying that exact trace. -/
theorem twentiethCatalogueWitnessMap_checker :
    twentiethCatalogueWitnessCertificate.mapBoolean = true := by
  rfl

/-- Every word accepted at the indexed extendable root occurs in the witness
map. -/
theorem twentiethCatalogueWitnessMap_coversExtendableRoot :
    twentiethCatalogueWitnessCertificate.coversDagBoolean
      twentiethCatalogueTraceDag twentiethCatalogueExtendableRoot = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
