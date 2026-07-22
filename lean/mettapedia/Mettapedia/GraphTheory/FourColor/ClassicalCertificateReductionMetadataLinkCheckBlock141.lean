import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry564_checker :
    entryBoolean 564 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry565_checker :
    entryBoolean 565 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry566_checker :
    entryBoolean 566 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry567_checker :
    entryBoolean 567 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock141_checker :
    chunkBoolean 141 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry564_checker,
      classicalReductionMetadataLinkEntry565_checker,
      classicalReductionMetadataLinkEntry566_checker,
      classicalReductionMetadataLinkEntry567_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
