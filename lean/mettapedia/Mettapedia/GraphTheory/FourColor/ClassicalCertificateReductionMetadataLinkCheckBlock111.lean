import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry444_checker :
    entryBoolean 444 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry445_checker :
    entryBoolean 445 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry446_checker :
    entryBoolean 446 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry447_checker :
    entryBoolean 447 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock111_checker :
    chunkBoolean 111 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry444_checker,
      classicalReductionMetadataLinkEntry445_checker,
      classicalReductionMetadataLinkEntry446_checker,
      classicalReductionMetadataLinkEntry447_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
