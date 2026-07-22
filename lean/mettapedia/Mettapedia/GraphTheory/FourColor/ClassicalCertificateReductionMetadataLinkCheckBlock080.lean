import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry320_checker :
    entryBoolean 320 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry321_checker :
    entryBoolean 321 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry322_checker :
    entryBoolean 322 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry323_checker :
    entryBoolean 323 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock080_checker :
    chunkBoolean 80 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry320_checker,
      classicalReductionMetadataLinkEntry321_checker,
      classicalReductionMetadataLinkEntry322_checker,
      classicalReductionMetadataLinkEntry323_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
