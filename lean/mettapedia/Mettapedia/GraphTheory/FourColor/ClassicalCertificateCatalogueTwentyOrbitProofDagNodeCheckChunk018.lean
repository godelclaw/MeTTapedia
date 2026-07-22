import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock144_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 144 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock145_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 145 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock146_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 146 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock147_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 147 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock148_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 148 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock149_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 149 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock150_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 150 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock151_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 151 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 018. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk018_checker
    (block : Nat) (hlower : 144 ≤ block) (hupper : block < 152) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock144_checker,
      twentiethCatalogueOrbitProofDagNodeBlock145_checker,
      twentiethCatalogueOrbitProofDagNodeBlock146_checker,
      twentiethCatalogueOrbitProofDagNodeBlock147_checker,
      twentiethCatalogueOrbitProofDagNodeBlock148_checker,
      twentiethCatalogueOrbitProofDagNodeBlock149_checker,
      twentiethCatalogueOrbitProofDagNodeBlock150_checker,
      twentiethCatalogueOrbitProofDagNodeBlock151_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
