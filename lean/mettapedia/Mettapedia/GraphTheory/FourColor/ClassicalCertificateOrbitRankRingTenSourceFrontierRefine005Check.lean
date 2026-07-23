import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine005Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine005CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine005CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine005CheckChunk002

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine005Block_checker
    (block : Nat) (hblock : block < 3) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 5 1 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine005Block000_checker,
      ringTenSourceFrontierRefine005Block001_checker,
      ringTenSourceFrontierRefine005Block002_checker]

theorem ringTenSourceFrontierBlock005_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 5 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 5 1 1 3
  · rw [ringTenSourceFrontierRefine005Length]
  · exact ringTenSourceFrontierRefine005Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
