import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsData

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueHypermaps

open ClassicalCertificateHypermapCatalogue

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalHypermapCatalogueChunk00_checker :
    classicalHypermapCatalogue.chunkBoolean 0 = true := by
  rfl

theorem classicalHypermapCatalogueChunk01_checker :
    classicalHypermapCatalogue.chunkBoolean 1 = true := by
  rfl

theorem classicalHypermapCatalogueChunk02_checker :
    classicalHypermapCatalogue.chunkBoolean 2 = true := by
  rfl

theorem classicalHypermapCatalogueChunk03_checker :
    classicalHypermapCatalogue.chunkBoolean 3 = true := by
  rfl

end ClassicalCertificateCatalogueHypermaps

end Mettapedia.GraphTheory.FourColor
