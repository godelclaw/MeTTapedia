import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock120_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 120 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock121_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 121 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock122_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 122 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock123_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 123 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock124_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 124 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock125_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 125 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock126_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 126 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock127_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 127 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 015. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk015_checker
    (block : Nat) (hlower : 120 ≤ block) (hupper : block < 128) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock120_checker,
      twentiethCatalogueOrbitProofDagNodeBlock121_checker,
      twentiethCatalogueOrbitProofDagNodeBlock122_checker,
      twentiethCatalogueOrbitProofDagNodeBlock123_checker,
      twentiethCatalogueOrbitProofDagNodeBlock124_checker,
      twentiethCatalogueOrbitProofDagNodeBlock125_checker,
      twentiethCatalogueOrbitProofDagNodeBlock126_checker,
      twentiethCatalogueOrbitProofDagNodeBlock127_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
