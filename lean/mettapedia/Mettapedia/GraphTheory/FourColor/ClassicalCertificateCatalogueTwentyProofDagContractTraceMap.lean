import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapRedRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapRedBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapRedPurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapBlueRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapBlueBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapBluePurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapPurpleRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapPurpleBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMapPurplePurple
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedTraceMapJoin

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateProofDagReduction
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Every word stored in the exact cf020 contract-trace map names a
semantically matching target node of the proof DAG. -/
theorem twentiethCatalogueProofDagContractTraceMap_isNode :
    twentiethCatalogueContractTraceMap.isNode = true := by
  rfl

theorem twentiethCatalogueProofDagContractTraceMapRed_isNode :
    (twentiethCatalogueContractTraceMap.child .red).isNode = true := by
  rfl

theorem twentiethCatalogueProofDagContractTraceMapBlue_isNode :
    (twentiethCatalogueContractTraceMap.child .blue).isNode = true := by
  rfl

theorem twentiethCatalogueProofDagContractTraceMapPurple_isNode :
    (twentiethCatalogueContractTraceMap.child .purple).isNode = true := by
  rfl

theorem twentiethCatalogueProofDagContractTraceMapRed_checker :
    Tree.checkAt twentiethCatalogueProofDagContractTraceTarget 11
      (twentiethCatalogueContractTraceMap.child .red) [.red] = true := by
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueProofDagContractTraceMapRed_isNode
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapRedRed_checker
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapRedBlue_checker
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapRedPurple_checker

theorem twentiethCatalogueProofDagContractTraceMapBlue_checker :
    Tree.checkAt twentiethCatalogueProofDagContractTraceTarget 11
      (twentiethCatalogueContractTraceMap.child .blue) [.blue] = true := by
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueProofDagContractTraceMapBlue_isNode
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapBlueRed_checker
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapBlueBlue_checker
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapBluePurple_checker

theorem twentiethCatalogueProofDagContractTraceMapPurple_checker :
    Tree.checkAt twentiethCatalogueProofDagContractTraceTarget 11
      (twentiethCatalogueContractTraceMap.child .purple) [.purple] = true := by
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueProofDagContractTraceMapPurple_isNode
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapPurpleRed_checker
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapPurpleBlue_checker
  · simpa [twentiethCatalogueProofDagContractTraceMapBranch] using
      twentiethCatalogueProofDagContractTraceMapPurplePurple_checker

theorem twentiethCatalogueProofDagContractTraceMap_checker :
    twentiethCatalogueContractTraceMap.checker 12
      twentiethCatalogueProofDagContractTraceTarget = true := by
  unfold Tree.checker
  change Tree.checkAt twentiethCatalogueProofDagContractTraceTarget (11 + 1)
    twentiethCatalogueContractTraceMap [] = true
  apply Tree.checkAt_of_isNode_and_children
  · exact twentiethCatalogueProofDagContractTraceMap_isNode
  · simpa using twentiethCatalogueProofDagContractTraceMapRed_checker
  · simpa using twentiethCatalogueProofDagContractTraceMapBlue_checker
  · simpa using twentiethCatalogueProofDagContractTraceMapPurple_checker

/-- Membership in the old indexed contract language therefore yields a
checked proof-DAG target. -/
theorem twentiethCatalogueProofDagTarget_of_contractTraceMap
    (word : List TraceSymbol) (hlength : word.length = 12)
    (hmember : (twentiethCatalogueContractTraceMap.lookup word).isSome = true) :
    TargetTreeCode.targetBoolean 12 twentiethCatalogueProofDagCode word = true := by
  obtain ⟨layer, hlookup⟩ := Option.isSome_iff_exists.1 hmember
  have htarget := twentiethCatalogueContractTraceMap.lookup_sound_of_checker_true
    12 twentiethCatalogueProofDagContractTraceTarget
      twentiethCatalogueProofDagContractTraceMap_checker word layer
        hlength hlookup
  simpa [twentiethCatalogueProofDagContractTraceTarget] using htarget

end ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

end Mettapedia.GraphTheory.FourColor
