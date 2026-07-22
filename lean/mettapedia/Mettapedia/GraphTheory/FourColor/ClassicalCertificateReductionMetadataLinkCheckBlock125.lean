import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry500_checker :
    entryBoolean 500 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry501_checker :
    entryBoolean 501 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry502_checker :
    entryBoolean 502 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry503_checker :
    entryBoolean 503 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock125_checker :
    chunkBoolean 125 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry500_checker,
      classicalReductionMetadataLinkEntry501_checker,
      classicalReductionMetadataLinkEntry502_checker,
      classicalReductionMetadataLinkEntry503_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
