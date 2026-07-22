import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry488_checker :
    entryBoolean 488 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry489_checker :
    entryBoolean 489 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry490_checker :
    entryBoolean 490 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry491_checker :
    entryBoolean 491 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock122_checker :
    chunkBoolean 122 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry488_checker,
      classicalReductionMetadataLinkEntry489_checker,
      classicalReductionMetadataLinkEntry490_checker,
      classicalReductionMetadataLinkEntry491_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
