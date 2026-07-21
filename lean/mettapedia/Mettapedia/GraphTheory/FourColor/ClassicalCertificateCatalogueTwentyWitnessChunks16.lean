import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapData

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueWitnessChunk16_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 16 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk17_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 17 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk18_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 18 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk19_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 19 = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
