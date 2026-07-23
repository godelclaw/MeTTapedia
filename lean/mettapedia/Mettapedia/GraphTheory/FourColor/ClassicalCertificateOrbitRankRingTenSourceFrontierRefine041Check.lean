import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041Coverage
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankRingTenSourceFrontierRefine041CheckChunk008

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

open ClassicalCertificateOrbitRankRingTenData
open ClassicalCertificateRankVectorLeafProduct

theorem ringTenSourceFrontierRefine041Block_checker
    (block : Nat) (hblock : block < 9) :
    refinedSourceFrontierSubblockBoolean ringTenRankCertificate
      4 1 41 2 1 block = true := by
  interval_cases block <;>
    simp_all only [ringTenSourceFrontierRefine041Block000_checker,
      ringTenSourceFrontierRefine041Block001_checker,
      ringTenSourceFrontierRefine041Block002_checker,
      ringTenSourceFrontierRefine041Block003_checker,
      ringTenSourceFrontierRefine041Block004_checker,
      ringTenSourceFrontierRefine041Block005_checker,
      ringTenSourceFrontierRefine041Block006_checker,
      ringTenSourceFrontierRefine041Block007_checker,
      ringTenSourceFrontierRefine041Block008_checker]

theorem ringTenSourceFrontierBlock041_refined_checker :
    sourceFrontierBlockBoolean ringTenRankCertificate 4 1 41 = true := by
  apply sourceFrontierBlockBoolean_of_refined_block_checkers
    ringTenRankCertificate 4 1 41 2 1 9
  · rw [ringTenSourceFrontierRefine041Length]
  · exact ringTenSourceFrontierRefine041Block_checker

end ClassicalCertificateOrbitRankRingTenSourceFrontierCheck

end Mettapedia.GraphTheory.FourColor
