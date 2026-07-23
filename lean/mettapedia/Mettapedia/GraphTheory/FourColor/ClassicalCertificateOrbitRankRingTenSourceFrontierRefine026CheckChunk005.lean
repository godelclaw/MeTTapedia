import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankVectorLeafProduct

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem ringTenSourceFrontierRefine026Block005_checker :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 26 2 1 5 = true := by
  rfl

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
