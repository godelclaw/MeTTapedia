import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapRedRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapRedBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapRedPurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapBlueRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapBlueBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapBluePurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapPurpleRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapPurpleBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMapPurplePurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedTraceMapJoin

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateOrbitProofDagReduction
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Every word stored in the exact cf020 contract-trace map names a
semantically matching color-orbit target node. -/
theorem twentiethCatalogueOrbitProofDagContractTraceMap_isNode :
    twentiethCatalogueContractTraceMap.isNode = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagContractTraceMapRed_isNode :
    (twentiethCatalogueContractTraceMap.child .red).isNode = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagContractTraceMapBlue_isNode :
    (twentiethCatalogueContractTraceMap.child .blue).isNode = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagContractTraceMapPurple_isNode :
    (twentiethCatalogueContractTraceMap.child .purple).isNode = true := by
  rfl


theorem twentiethCatalogueOrbitProofDagContractTraceMapRed_checker :
    Tree.checkAt twentiethCatalogueOrbitProofDagContractTraceTarget 11
      (twentiethCatalogueContractTraceMap.child .red) [.red] = true := by
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueOrbitProofDagContractTraceMapRed_isNode
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapRedRed_checker
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapRedBlue_checker
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapRedPurple_checker

theorem twentiethCatalogueOrbitProofDagContractTraceMapBlue_checker :
    Tree.checkAt twentiethCatalogueOrbitProofDagContractTraceTarget 11
      (twentiethCatalogueContractTraceMap.child .blue) [.blue] = true := by
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueOrbitProofDagContractTraceMapBlue_isNode
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapBlueRed_checker
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapBlueBlue_checker
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapBluePurple_checker

theorem twentiethCatalogueOrbitProofDagContractTraceMapPurple_checker :
    Tree.checkAt twentiethCatalogueOrbitProofDagContractTraceTarget 11
      (twentiethCatalogueContractTraceMap.child .purple) [.purple] = true := by
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueOrbitProofDagContractTraceMapPurple_isNode
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapPurpleRed_checker
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapPurpleBlue_checker
  · simpa [twentiethCatalogueOrbitProofDagContractTraceMapBranch] using
      twentiethCatalogueOrbitProofDagContractTraceMapPurplePurple_checker

theorem twentiethCatalogueOrbitProofDagContractTraceMap_checker :
    twentiethCatalogueContractTraceMap.checker 12
      twentiethCatalogueOrbitProofDagContractTraceTarget = true := by
  unfold Tree.checker
  change Tree.checkAt twentiethCatalogueOrbitProofDagContractTraceTarget (11 + 1)
    twentiethCatalogueContractTraceMap [] = true
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueOrbitProofDagContractTraceMap_isNode
  · simpa using twentiethCatalogueOrbitProofDagContractTraceMapRed_checker
  · simpa using twentiethCatalogueOrbitProofDagContractTraceMapBlue_checker
  · simpa using twentiethCatalogueOrbitProofDagContractTraceMapPurple_checker

/-- Membership in the exact contracted language yields a checked color-orbit
proof-DAG target. -/
theorem twentiethCatalogueOrbitProofDagTarget_of_contractTraceMap
    (word : List TraceSymbol) (hlength : word.length = 12)
    (hmember : (twentiethCatalogueContractTraceMap.lookup word).isSome = true) :
    targetBoolean 12 twentiethCatalogueOrbitProofDagCode word = true := by
  obtain ⟨layer, hlookup⟩ := Option.isSome_iff_exists.1 hmember
  have htarget := twentiethCatalogueContractTraceMap.lookup_sound_of_checker_true
    12 twentiethCatalogueOrbitProofDagContractTraceTarget
      twentiethCatalogueOrbitProofDagContractTraceMap_checker word layer
        hlength hlookup
  simpa [twentiethCatalogueOrbitProofDagContractTraceTarget] using htarget

end ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap

end Mettapedia.GraphTheory.FourColor
