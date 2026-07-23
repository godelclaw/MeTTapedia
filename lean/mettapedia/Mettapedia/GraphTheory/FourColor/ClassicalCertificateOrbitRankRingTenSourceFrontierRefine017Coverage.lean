import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankVectorLeafProduct

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem ringTenSourceFrontierRefine017Length :
    (refinedSourceFrontierBlock ringTenRankCertificate
      4 1 17 1).length = 3 := by
  rfl

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
