import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry372_checker :
    entryBoolean 372 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry373_checker :
    entryBoolean 373 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry374_checker :
    entryBoolean 374 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry375_checker :
    entryBoolean 375 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock093_checker :
    chunkBoolean 93 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry372_checker,
      classicalReductionMetadataLinkEntry373_checker,
      classicalReductionMetadataLinkEntry374_checker,
      classicalReductionMetadataLinkEntry375_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
