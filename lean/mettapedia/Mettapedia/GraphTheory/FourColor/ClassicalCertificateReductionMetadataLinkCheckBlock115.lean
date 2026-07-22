import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry460_checker :
    entryBoolean 460 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry461_checker :
    entryBoolean 461 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry462_checker :
    entryBoolean 462 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry463_checker :
    entryBoolean 463 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock115_checker :
    chunkBoolean 115 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry460_checker,
      classicalReductionMetadataLinkEntry461_checker,
      classicalReductionMetadataLinkEntry462_checker,
      classicalReductionMetadataLinkEntry463_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
