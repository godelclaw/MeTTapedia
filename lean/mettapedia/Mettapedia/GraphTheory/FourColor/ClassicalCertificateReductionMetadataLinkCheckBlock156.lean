import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry624_checker :
    entryBoolean 624 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry625_checker :
    entryBoolean 625 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry626_checker :
    entryBoolean 626 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry627_checker :
    entryBoolean 627 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock156_checker :
    chunkBoolean 156 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry624_checker,
      classicalReductionMetadataLinkEntry625_checker,
      classicalReductionMetadataLinkEntry626_checker,
      classicalReductionMetadataLinkEntry627_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
