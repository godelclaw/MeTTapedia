import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessMapData

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueWitnessChunk32_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 32 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk33_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 33 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk34_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 34 = true := by
  rfl

theorem twentiethCatalogueWitnessChunk35_checker :
    twentiethCatalogueWitnessCertificate.witnessChunkBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector 35 = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
