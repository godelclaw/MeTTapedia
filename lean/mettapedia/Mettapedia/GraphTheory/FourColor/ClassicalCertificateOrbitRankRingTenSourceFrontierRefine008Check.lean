import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine008Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine008CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine008CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine008CheckChunk002

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine008Block_checker
    (block : Nat) (hblock : block < 3) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 8 1 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine008Block000_checker,
      ringTenSourceFrontierRefine008Block001_checker,
      ringTenSourceFrontierRefine008Block002_checker]

theorem ringTenSourceFrontierBlock008_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 8 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 8 1 1 3
  · rw [ringTenSourceFrontierRefine008Length]
  · exact ringTenSourceFrontierRefine008Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
