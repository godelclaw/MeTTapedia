import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry548_checker :
    entryBoolean 548 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry549_checker :
    entryBoolean 549 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry550_checker :
    entryBoolean 550 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry551_checker :
    entryBoolean 551 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock137_checker :
    chunkBoolean 137 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry548_checker,
      classicalReductionMetadataLinkEntry549_checker,
      classicalReductionMetadataLinkEntry550_checker,
      classicalReductionMetadataLinkEntry551_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
