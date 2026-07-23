import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine032CheckChunk008

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine032Block_checker
    (block : Nat) (hblock : block < 9) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 32 2 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine032Block000_checker,
      ringTenSourceFrontierRefine032Block001_checker,
      ringTenSourceFrontierRefine032Block002_checker,
      ringTenSourceFrontierRefine032Block003_checker,
      ringTenSourceFrontierRefine032Block004_checker,
      ringTenSourceFrontierRefine032Block005_checker,
      ringTenSourceFrontierRefine032Block006_checker,
      ringTenSourceFrontierRefine032Block007_checker,
      ringTenSourceFrontierRefine032Block008_checker]

theorem ringTenSourceFrontierBlock032_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 32 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 32 2 1 9
  · rw [ringTenSourceFrontierRefine032Length]
  · exact ringTenSourceFrontierRefine032Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
