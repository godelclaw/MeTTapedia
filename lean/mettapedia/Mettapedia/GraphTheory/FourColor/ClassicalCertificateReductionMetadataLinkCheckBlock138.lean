import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry552_checker :
    entryBoolean 552 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry553_checker :
    entryBoolean 553 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry554_checker :
    entryBoolean 554 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry555_checker :
    entryBoolean 555 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock138_checker :
    chunkBoolean 138 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry552_checker,
      classicalReductionMetadataLinkEntry553_checker,
      classicalReductionMetadataLinkEntry554_checker,
      classicalReductionMetadataLinkEntry555_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
