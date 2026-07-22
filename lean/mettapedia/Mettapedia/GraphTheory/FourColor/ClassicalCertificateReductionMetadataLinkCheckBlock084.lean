import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry336_checker :
    entryBoolean 336 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry337_checker :
    entryBoolean 337 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry338_checker :
    entryBoolean 338 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry339_checker :
    entryBoolean 339 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock084_checker :
    chunkBoolean 84 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry336_checker,
      classicalReductionMetadataLinkEntry337_checker,
      classicalReductionMetadataLinkEntry338_checker,
      classicalReductionMetadataLinkEntry339_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
