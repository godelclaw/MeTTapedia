import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry364_checker :
    entryBoolean 364 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry365_checker :
    entryBoolean 365 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry366_checker :
    entryBoolean 366 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry367_checker :
    entryBoolean 367 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock091_checker :
    chunkBoolean 91 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry364_checker,
      classicalReductionMetadataLinkEntry365_checker,
      classicalReductionMetadataLinkEntry366_checker,
      classicalReductionMetadataLinkEntry367_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
