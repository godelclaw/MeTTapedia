import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine037CheckChunk008

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine037Block_checker
    (block : Nat) (hblock : block < 9) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 37 2 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine037Block000_checker,
      ringTenSourceFrontierRefine037Block001_checker,
      ringTenSourceFrontierRefine037Block002_checker,
      ringTenSourceFrontierRefine037Block003_checker,
      ringTenSourceFrontierRefine037Block004_checker,
      ringTenSourceFrontierRefine037Block005_checker,
      ringTenSourceFrontierRefine037Block006_checker,
      ringTenSourceFrontierRefine037Block007_checker,
      ringTenSourceFrontierRefine037Block008_checker]

theorem ringTenSourceFrontierBlock037_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 37 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 37 2 1 9
  · rw [ringTenSourceFrontierRefine037Length]
  · exact ringTenSourceFrontierRefine037Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
