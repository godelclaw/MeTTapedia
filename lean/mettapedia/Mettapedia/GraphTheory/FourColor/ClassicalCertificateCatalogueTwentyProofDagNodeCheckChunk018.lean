import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock144_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 144 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock145_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 145 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock146_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 146 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock147_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 147 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock148_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 148 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock149_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 149 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock150_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 150 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock151_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 151 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 018. -/
theorem twentiethCatalogueProofDagNodeChunk018_checker
    (block : Nat) (hlower : 144 ≤ block) (hupper : block < 152) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock144_checker, twentiethCatalogueProofDagNodeBlock145_checker, twentiethCatalogueProofDagNodeBlock146_checker, twentiethCatalogueProofDagNodeBlock147_checker, twentiethCatalogueProofDagNodeBlock148_checker, twentiethCatalogueProofDagNodeBlock149_checker, twentiethCatalogueProofDagNodeBlock150_checker, twentiethCatalogueProofDagNodeBlock151_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
