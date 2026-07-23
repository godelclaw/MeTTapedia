import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine014Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine014CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine014CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine014CheckChunk002

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine014Block_checker
    (block : Nat) (hblock : block < 3) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 14 1 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine014Block000_checker,
      ringTenSourceFrontierRefine014Block001_checker,
      ringTenSourceFrontierRefine014Block002_checker]

theorem ringTenSourceFrontierBlock014_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 14 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 14 1 1 3
  · rw [ringTenSourceFrontierRefine014Length]
  · exact ringTenSourceFrontierRefine014Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
