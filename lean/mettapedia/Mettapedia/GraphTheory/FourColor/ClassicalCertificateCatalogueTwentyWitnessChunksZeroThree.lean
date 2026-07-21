import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapData

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueWitnessChunk00_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 0 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk01_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 1 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk02_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 2 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk03_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 3 = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
