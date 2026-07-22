import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock112_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 112 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock113_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 113 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock114_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 114 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock115_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 115 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock116_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 116 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock117_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 117 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock118_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 118 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock119_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 119 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 014. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk014_checker
    (block : Nat) (hlower : 112 ≤ block) (hupper : block < 120) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock112_checker,
      twentiethCatalogueOrbitProofDagNodeBlock113_checker,
      twentiethCatalogueOrbitProofDagNodeBlock114_checker,
      twentiethCatalogueOrbitProofDagNodeBlock115_checker,
      twentiethCatalogueOrbitProofDagNodeBlock116_checker,
      twentiethCatalogueOrbitProofDagNodeBlock117_checker,
      twentiethCatalogueOrbitProofDagNodeBlock118_checker,
      twentiethCatalogueOrbitProofDagNodeBlock119_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
