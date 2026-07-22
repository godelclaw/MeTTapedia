import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry400_checker :
    entryBoolean 400 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry401_checker :
    entryBoolean 401 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry402_checker :
    entryBoolean 402 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry403_checker :
    entryBoolean 403 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock100_checker :
    chunkBoolean 100 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry400_checker,
      classicalReductionMetadataLinkEntry401_checker,
      classicalReductionMetadataLinkEntry402_checker,
      classicalReductionMetadataLinkEntry403_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
