import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry520_checker :
    entryBoolean 520 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry521_checker :
    entryBoolean 521 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry522_checker :
    entryBoolean 522 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry523_checker :
    entryBoolean 523 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock130_checker :
    chunkBoolean 130 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry520_checker,
      classicalReductionMetadataLinkEntry521_checker,
      classicalReductionMetadataLinkEntry522_checker,
      classicalReductionMetadataLinkEntry523_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
