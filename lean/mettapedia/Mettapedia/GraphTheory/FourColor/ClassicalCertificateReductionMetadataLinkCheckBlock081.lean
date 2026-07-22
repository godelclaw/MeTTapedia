import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry324_checker :
    entryBoolean 324 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry325_checker :
    entryBoolean 325 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry326_checker :
    entryBoolean 326 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry327_checker :
    entryBoolean 327 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock081_checker :
    chunkBoolean 81 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry324_checker,
      classicalReductionMetadataLinkEntry325_checker,
      classicalReductionMetadataLinkEntry326_checker,
      classicalReductionMetadataLinkEntry327_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
