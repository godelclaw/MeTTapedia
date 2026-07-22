import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry592_checker :
    entryBoolean 592 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry593_checker :
    entryBoolean 593 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry594_checker :
    entryBoolean 594 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry595_checker :
    entryBoolean 595 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock148_checker :
    chunkBoolean 148 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry592_checker,
      classicalReductionMetadataLinkEntry593_checker,
      classicalReductionMetadataLinkEntry594_checker,
      classicalReductionMetadataLinkEntry595_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
