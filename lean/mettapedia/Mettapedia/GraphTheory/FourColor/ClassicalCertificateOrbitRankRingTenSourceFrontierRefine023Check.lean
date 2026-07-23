import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine023Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine023CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine023CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine023CheckChunk002

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine023Block_checker
    (block : Nat) (hblock : block < 3) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 23 1 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine023Block000_checker,
      ringTenSourceFrontierRefine023Block001_checker,
      ringTenSourceFrontierRefine023Block002_checker]

theorem ringTenSourceFrontierBlock023_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 23 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 23 1 1 3
  · rw [ringTenSourceFrontierRefine023Length]
  · exact ringTenSourceFrontierRefine023Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
