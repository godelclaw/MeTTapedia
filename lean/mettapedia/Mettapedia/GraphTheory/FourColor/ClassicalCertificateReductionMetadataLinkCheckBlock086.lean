import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry344_checker :
    entryBoolean 344 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry345_checker :
    entryBoolean 345 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry346_checker :
    entryBoolean 346 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry347_checker :
    entryBoolean 347 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock086_checker :
    chunkBoolean 86 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry344_checker,
      classicalReductionMetadataLinkEntry345_checker,
      classicalReductionMetadataLinkEntry346_checker,
      classicalReductionMetadataLinkEntry347_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
