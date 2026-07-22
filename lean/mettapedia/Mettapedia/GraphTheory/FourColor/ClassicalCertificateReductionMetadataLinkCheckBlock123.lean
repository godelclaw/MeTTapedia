import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry492_checker :
    entryBoolean 492 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry493_checker :
    entryBoolean 493 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry494_checker :
    entryBoolean 494 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry495_checker :
    entryBoolean 495 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock123_checker :
    chunkBoolean 123 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry492_checker,
      classicalReductionMetadataLinkEntry493_checker,
      classicalReductionMetadataLinkEntry494_checker,
      classicalReductionMetadataLinkEntry495_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
