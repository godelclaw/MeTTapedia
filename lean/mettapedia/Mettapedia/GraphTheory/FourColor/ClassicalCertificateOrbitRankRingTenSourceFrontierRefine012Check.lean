import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine012Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine012CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine012CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine012CheckChunk002

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine012Block_checker
    (block : Nat) (hblock : block < 3) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 12 1 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine012Block000_checker,
      ringTenSourceFrontierRefine012Block001_checker,
      ringTenSourceFrontierRefine012Block002_checker]

theorem ringTenSourceFrontierBlock012_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 12 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 12 1 1 3
  · rw [ringTenSourceFrontierRefine012Length]
  · exact ringTenSourceFrontierRefine012Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
