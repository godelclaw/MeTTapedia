import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry556_checker :
    entryBoolean 556 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry557_checker :
    entryBoolean 557 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry558_checker :
    entryBoolean 558 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry559_checker :
    entryBoolean 559 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock139_checker :
    chunkBoolean 139 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry556_checker,
      classicalReductionMetadataLinkEntry557_checker,
      classicalReductionMetadataLinkEntry558_checker,
      classicalReductionMetadataLinkEntry559_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
