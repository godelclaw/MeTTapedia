import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyResponseCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyResponseSeal

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseCheck
open ClassicalCertificateIndexedLayeredKempe

theorem twentiethCatalogueResponseTable_checker :
    twentiethCatalogueIndexedKempeCertificate.responseTableBoolean = true := by
  rw [Certificate.responseTableBoolean,
    twentiethCatalogueResponseValueChunkCount]
  apply List.all_eq_true.2
  intro chunk hchunk
  have hlt : chunk < 25 := List.mem_range.1 hchunk
  interval_cases chunk <;>
    simp only [twentiethCatalogueResponseChunk00,
      twentiethCatalogueResponseChunk01,
      twentiethCatalogueResponseChunk02,
      twentiethCatalogueResponseChunk03,
      twentiethCatalogueResponseChunk04,
      twentiethCatalogueResponseChunk05,
      twentiethCatalogueResponseChunk06,
      twentiethCatalogueResponseChunk07,
      twentiethCatalogueResponseChunk08,
      twentiethCatalogueResponseChunk09,
      twentiethCatalogueResponseChunk10,
      twentiethCatalogueResponseChunk11,
      twentiethCatalogueResponseChunk12,
      twentiethCatalogueResponseChunk13,
      twentiethCatalogueResponseChunk14,
      twentiethCatalogueResponseChunk15,
      twentiethCatalogueResponseChunk16,
      twentiethCatalogueResponseChunk17,
      twentiethCatalogueResponseChunk18,
      twentiethCatalogueResponseChunk19,
      twentiethCatalogueResponseChunk20,
      twentiethCatalogueResponseChunk21,
      twentiethCatalogueResponseChunk22,
      twentiethCatalogueResponseChunk23,
      twentiethCatalogueResponseChunk24]

end ClassicalCertificateCatalogueTwentyResponseSeal

end Mettapedia.GraphTheory.FourColor
