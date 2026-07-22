import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry316_checker :
    entryBoolean 316 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry317_checker :
    entryBoolean 317 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry318_checker :
    entryBoolean 318 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry319_checker :
    entryBoolean 319 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock079_checker :
    chunkBoolean 79 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry316_checker,
      classicalReductionMetadataLinkEntry317_checker,
      classicalReductionMetadataLinkEntry318_checker,
      classicalReductionMetadataLinkEntry319_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
