import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry356_checker :
    entryBoolean 356 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry357_checker :
    entryBoolean 357 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry358_checker :
    entryBoolean 358 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry359_checker :
    entryBoolean 359 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock089_checker :
    chunkBoolean 89 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry356_checker,
      classicalReductionMetadataLinkEntry357_checker,
      classicalReductionMetadataLinkEntry358_checker,
      classicalReductionMetadataLinkEntry359_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
