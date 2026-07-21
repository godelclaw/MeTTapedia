import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapData

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueWitnessChunk20_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 20 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk21_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 21 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk22_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 22 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk23_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 23 = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
