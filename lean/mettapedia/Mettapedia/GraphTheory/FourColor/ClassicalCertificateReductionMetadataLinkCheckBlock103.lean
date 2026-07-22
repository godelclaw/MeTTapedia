import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry412_checker :
    entryBoolean 412 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry413_checker :
    entryBoolean 413 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry414_checker :
    entryBoolean 414 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry415_checker :
    entryBoolean 415 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock103_checker :
    chunkBoolean 103 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry412_checker,
      classicalReductionMetadataLinkEntry413_checker,
      classicalReductionMetadataLinkEntry414_checker,
      classicalReductionMetadataLinkEntry415_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
