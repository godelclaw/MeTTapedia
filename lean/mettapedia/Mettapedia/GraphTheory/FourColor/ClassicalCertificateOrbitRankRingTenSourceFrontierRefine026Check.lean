import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine026CheckChunk008

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine026Block_checker
    (block : Nat) (hblock : block < 9) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 26 2 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine026Block000_checker,
      ringTenSourceFrontierRefine026Block001_checker,
      ringTenSourceFrontierRefine026Block002_checker,
      ringTenSourceFrontierRefine026Block003_checker,
      ringTenSourceFrontierRefine026Block004_checker,
      ringTenSourceFrontierRefine026Block005_checker,
      ringTenSourceFrontierRefine026Block006_checker,
      ringTenSourceFrontierRefine026Block007_checker,
      ringTenSourceFrontierRefine026Block008_checker]

theorem ringTenSourceFrontierBlock026_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 26 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 26 2 1 9
  · rw [ringTenSourceFrontierRefine026Length]
  · exact ringTenSourceFrontierRefine026Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
