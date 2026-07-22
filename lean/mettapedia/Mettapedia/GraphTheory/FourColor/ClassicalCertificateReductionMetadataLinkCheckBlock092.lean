import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry368_checker :
    entryBoolean 368 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry369_checker :
    entryBoolean 369 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry370_checker :
    entryBoolean 370 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry371_checker :
    entryBoolean 371 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock092_checker :
    chunkBoolean 92 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry368_checker,
      classicalReductionMetadataLinkEntry369_checker,
      classicalReductionMetadataLinkEntry370_checker,
      classicalReductionMetadataLinkEntry371_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
