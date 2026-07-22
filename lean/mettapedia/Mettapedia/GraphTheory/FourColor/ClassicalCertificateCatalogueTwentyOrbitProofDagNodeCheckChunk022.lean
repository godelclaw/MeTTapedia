import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock176_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 176 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock177_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 177 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock178_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 178 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock179_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 179 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock180_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 180 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock181_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 181 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock182_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 182 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock183_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 183 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 022. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk022_checker
    (block : Nat) (hlower : 176 ≤ block) (hupper : block < 184) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock176_checker,
      twentiethCatalogueOrbitProofDagNodeBlock177_checker,
      twentiethCatalogueOrbitProofDagNodeBlock178_checker,
      twentiethCatalogueOrbitProofDagNodeBlock179_checker,
      twentiethCatalogueOrbitProofDagNodeBlock180_checker,
      twentiethCatalogueOrbitProofDagNodeBlock181_checker,
      twentiethCatalogueOrbitProofDagNodeBlock182_checker,
      twentiethCatalogueOrbitProofDagNodeBlock183_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
