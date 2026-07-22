import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry312_checker :
    entryBoolean 312 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry313_checker :
    entryBoolean 313 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry314_checker :
    entryBoolean 314 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry315_checker :
    entryBoolean 315 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock078_checker :
    chunkBoolean 78 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry312_checker,
      classicalReductionMetadataLinkEntry313_checker,
      classicalReductionMetadataLinkEntry314_checker,
      classicalReductionMetadataLinkEntry315_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
