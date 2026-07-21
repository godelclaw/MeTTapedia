import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunksZeroThree
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks04
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks08
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks12
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks16
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks20
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks24
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks28
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks32
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks36
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks40
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks44
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks48
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyWitnessChunks52

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateIndexedTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueWitnessChunkCount :
    twentiethCatalogueWitnessCertificate.chunks.size = 53 := by
  rfl

/-- Every stored ordinary assignment is proper and realizes its stored ring
trace. -/
theorem twentiethCatalogueWitnessTable_checker :
    twentiethCatalogueWitnessCertificate.witnessTableBoolean
      twentiethCataloguePartitionValid twentiethCatalogueRingVector = true := by
  change
    (List.range 53).all (fun chunk =>
      twentiethCatalogueWitnessCertificate.witnessChunkBoolean
        twentiethCataloguePartitionValid twentiethCatalogueRingVector chunk) = true
  apply List.all_eq_true.2
  intro chunk hchunk
  have hlt : chunk < 53 := List.mem_range.1 hchunk
  interval_cases chunk <;>
    simp only [twentiethCatalogueWitnessChunk00_checker,
      twentiethCatalogueWitnessChunk01_checker,
      twentiethCatalogueWitnessChunk02_checker,
      twentiethCatalogueWitnessChunk03_checker,
      twentiethCatalogueWitnessChunk04_checker,
      twentiethCatalogueWitnessChunk05_checker,
      twentiethCatalogueWitnessChunk06_checker,
      twentiethCatalogueWitnessChunk07_checker,
      twentiethCatalogueWitnessChunk08_checker,
      twentiethCatalogueWitnessChunk09_checker,
      twentiethCatalogueWitnessChunk10_checker,
      twentiethCatalogueWitnessChunk11_checker,
      twentiethCatalogueWitnessChunk12_checker,
      twentiethCatalogueWitnessChunk13_checker,
      twentiethCatalogueWitnessChunk14_checker,
      twentiethCatalogueWitnessChunk15_checker,
      twentiethCatalogueWitnessChunk16_checker,
      twentiethCatalogueWitnessChunk17_checker,
      twentiethCatalogueWitnessChunk18_checker,
      twentiethCatalogueWitnessChunk19_checker,
      twentiethCatalogueWitnessChunk20_checker,
      twentiethCatalogueWitnessChunk21_checker,
      twentiethCatalogueWitnessChunk22_checker,
      twentiethCatalogueWitnessChunk23_checker,
      twentiethCatalogueWitnessChunk24_checker,
      twentiethCatalogueWitnessChunk25_checker,
      twentiethCatalogueWitnessChunk26_checker,
      twentiethCatalogueWitnessChunk27_checker,
      twentiethCatalogueWitnessChunk28_checker,
      twentiethCatalogueWitnessChunk29_checker,
      twentiethCatalogueWitnessChunk30_checker,
      twentiethCatalogueWitnessChunk31_checker,
      twentiethCatalogueWitnessChunk32_checker,
      twentiethCatalogueWitnessChunk33_checker,
      twentiethCatalogueWitnessChunk34_checker,
      twentiethCatalogueWitnessChunk35_checker,
      twentiethCatalogueWitnessChunk36_checker,
      twentiethCatalogueWitnessChunk37_checker,
      twentiethCatalogueWitnessChunk38_checker,
      twentiethCatalogueWitnessChunk39_checker,
      twentiethCatalogueWitnessChunk40_checker,
      twentiethCatalogueWitnessChunk41_checker,
      twentiethCatalogueWitnessChunk42_checker,
      twentiethCatalogueWitnessChunk43_checker,
      twentiethCatalogueWitnessChunk44_checker,
      twentiethCatalogueWitnessChunk45_checker,
      twentiethCatalogueWitnessChunk46_checker,
      twentiethCatalogueWitnessChunk47_checker,
      twentiethCatalogueWitnessChunk48_checker,
      twentiethCatalogueWitnessChunk49_checker,
      twentiethCatalogueWitnessChunk50_checker,
      twentiethCatalogueWitnessChunk51_checker,
      twentiethCatalogueWitnessChunk52_checker]

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
