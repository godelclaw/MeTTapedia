import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry348_checker :
    entryBoolean 348 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry349_checker :
    entryBoolean 349 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry350_checker :
    entryBoolean 350 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry351_checker :
    entryBoolean 351 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock087_checker :
    chunkBoolean 87 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry348_checker,
      classicalReductionMetadataLinkEntry349_checker,
      classicalReductionMetadataLinkEntry350_checker,
      classicalReductionMetadataLinkEntry351_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
