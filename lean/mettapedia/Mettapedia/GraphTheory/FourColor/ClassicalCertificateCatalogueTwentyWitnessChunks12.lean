import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapData

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueWitnessChunk12_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 12 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk13_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 13 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk14_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 14 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk15_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 15 = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
