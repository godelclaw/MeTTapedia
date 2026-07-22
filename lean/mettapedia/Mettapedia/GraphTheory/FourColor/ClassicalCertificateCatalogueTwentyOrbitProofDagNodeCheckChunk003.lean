import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock024_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 24 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock025_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 25 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock026_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 26 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock027_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 27 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock028_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 28 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock029_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 29 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock030_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 30 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock031_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 31 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 003. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk003_checker
    (block : Nat) (hlower : 24 ≤ block) (hupper : block < 32) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock024_checker,
      twentiethCatalogueOrbitProofDagNodeBlock025_checker,
      twentiethCatalogueOrbitProofDagNodeBlock026_checker,
      twentiethCatalogueOrbitProofDagNodeBlock027_checker,
      twentiethCatalogueOrbitProofDagNodeBlock028_checker,
      twentiethCatalogueOrbitProofDagNodeBlock029_checker,
      twentiethCatalogueOrbitProofDagNodeBlock030_checker,
      twentiethCatalogueOrbitProofDagNodeBlock031_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
