import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry508_checker :
    entryBoolean 508 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry509_checker :
    entryBoolean 509 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry510_checker :
    entryBoolean 510 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry511_checker :
    entryBoolean 511 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock127_checker :
    chunkBoolean 127 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry508_checker,
      classicalReductionMetadataLinkEntry509_checker,
      classicalReductionMetadataLinkEntry510_checker,
      classicalReductionMetadataLinkEntry511_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
