import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry388_checker :
    entryBoolean 388 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry389_checker :
    entryBoolean 389 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry390_checker :
    entryBoolean 390 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry391_checker :
    entryBoolean 391 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock097_checker :
    chunkBoolean 97 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry388_checker,
      classicalReductionMetadataLinkEntry389_checker,
      classicalReductionMetadataLinkEntry390_checker,
      classicalReductionMetadataLinkEntry391_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
