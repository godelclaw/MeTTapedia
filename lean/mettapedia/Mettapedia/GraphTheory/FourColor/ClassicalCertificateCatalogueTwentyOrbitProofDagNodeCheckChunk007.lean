import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock056_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 56 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock057_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 57 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock058_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 58 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock059_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 59 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock060_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 60 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock061_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 61 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock062_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 62 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock063_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 63 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 007. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk007_checker
    (block : Nat) (hlower : 56 ≤ block) (hupper : block < 64) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock056_checker,
      twentiethCatalogueOrbitProofDagNodeBlock057_checker,
      twentiethCatalogueOrbitProofDagNodeBlock058_checker,
      twentiethCatalogueOrbitProofDagNodeBlock059_checker,
      twentiethCatalogueOrbitProofDagNodeBlock060_checker,
      twentiethCatalogueOrbitProofDagNodeBlock061_checker,
      twentiethCatalogueOrbitProofDagNodeBlock062_checker,
      twentiethCatalogueOrbitProofDagNodeBlock063_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
