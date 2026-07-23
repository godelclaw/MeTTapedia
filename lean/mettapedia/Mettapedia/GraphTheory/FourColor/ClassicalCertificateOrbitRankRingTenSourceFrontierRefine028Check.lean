import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine028CheckChunk008

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine028Block_checker
    (block : Nat) (hblock : block < 9) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 28 2 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine028Block000_checker,
      ringTenSourceFrontierRefine028Block001_checker,
      ringTenSourceFrontierRefine028Block002_checker,
      ringTenSourceFrontierRefine028Block003_checker,
      ringTenSourceFrontierRefine028Block004_checker,
      ringTenSourceFrontierRefine028Block005_checker,
      ringTenSourceFrontierRefine028Block006_checker,
      ringTenSourceFrontierRefine028Block007_checker,
      ringTenSourceFrontierRefine028Block008_checker]

theorem ringTenSourceFrontierBlock028_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 28 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 28 2 1 9
  · rw [ringTenSourceFrontierRefine028Length]
  · exact ringTenSourceFrontierRefine028Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
