import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk008
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk009
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk010
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk011
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk012
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk013
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk014
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk015
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk016
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk017
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk018
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk019
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk020
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk021
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk022
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk023
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk024
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk025
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk026
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk027
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheckChunk028

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

theorem twentiethCatalogueOrbitProofDagNodeBlock_checker
    (block : Nat) (hblock : block < 232) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  by_cases h0 : block < 8
  · exact twentiethCatalogueOrbitProofDagNodeChunk000_checker
      block (by omega) h0
  by_cases h1 : block < 16
  · exact twentiethCatalogueOrbitProofDagNodeChunk001_checker
      block (by omega) h1
  by_cases h2 : block < 24
  · exact twentiethCatalogueOrbitProofDagNodeChunk002_checker
      block (by omega) h2
  by_cases h3 : block < 32
  · exact twentiethCatalogueOrbitProofDagNodeChunk003_checker
      block (by omega) h3
  by_cases h4 : block < 40
  · exact twentiethCatalogueOrbitProofDagNodeChunk004_checker
      block (by omega) h4
  by_cases h5 : block < 48
  · exact twentiethCatalogueOrbitProofDagNodeChunk005_checker
      block (by omega) h5
  by_cases h6 : block < 56
  · exact twentiethCatalogueOrbitProofDagNodeChunk006_checker
      block (by omega) h6
  by_cases h7 : block < 64
  · exact twentiethCatalogueOrbitProofDagNodeChunk007_checker
      block (by omega) h7
  by_cases h8 : block < 72
  · exact twentiethCatalogueOrbitProofDagNodeChunk008_checker
      block (by omega) h8
  by_cases h9 : block < 80
  · exact twentiethCatalogueOrbitProofDagNodeChunk009_checker
      block (by omega) h9
  by_cases h10 : block < 88
  · exact twentiethCatalogueOrbitProofDagNodeChunk010_checker
      block (by omega) h10
  by_cases h11 : block < 96
  · exact twentiethCatalogueOrbitProofDagNodeChunk011_checker
      block (by omega) h11
  by_cases h12 : block < 104
  · exact twentiethCatalogueOrbitProofDagNodeChunk012_checker
      block (by omega) h12
  by_cases h13 : block < 112
  · exact twentiethCatalogueOrbitProofDagNodeChunk013_checker
      block (by omega) h13
  by_cases h14 : block < 120
  · exact twentiethCatalogueOrbitProofDagNodeChunk014_checker
      block (by omega) h14
  by_cases h15 : block < 128
  · exact twentiethCatalogueOrbitProofDagNodeChunk015_checker
      block (by omega) h15
  by_cases h16 : block < 136
  · exact twentiethCatalogueOrbitProofDagNodeChunk016_checker
      block (by omega) h16
  by_cases h17 : block < 144
  · exact twentiethCatalogueOrbitProofDagNodeChunk017_checker
      block (by omega) h17
  by_cases h18 : block < 152
  · exact twentiethCatalogueOrbitProofDagNodeChunk018_checker
      block (by omega) h18
  by_cases h19 : block < 160
  · exact twentiethCatalogueOrbitProofDagNodeChunk019_checker
      block (by omega) h19
  by_cases h20 : block < 168
  · exact twentiethCatalogueOrbitProofDagNodeChunk020_checker
      block (by omega) h20
  by_cases h21 : block < 176
  · exact twentiethCatalogueOrbitProofDagNodeChunk021_checker
      block (by omega) h21
  by_cases h22 : block < 184
  · exact twentiethCatalogueOrbitProofDagNodeChunk022_checker
      block (by omega) h22
  by_cases h23 : block < 192
  · exact twentiethCatalogueOrbitProofDagNodeChunk023_checker
      block (by omega) h23
  by_cases h24 : block < 200
  · exact twentiethCatalogueOrbitProofDagNodeChunk024_checker
      block (by omega) h24
  by_cases h25 : block < 208
  · exact twentiethCatalogueOrbitProofDagNodeChunk025_checker
      block (by omega) h25
  by_cases h26 : block < 216
  · exact twentiethCatalogueOrbitProofDagNodeChunk026_checker
      block (by omega) h26
  by_cases h27 : block < 224
  · exact twentiethCatalogueOrbitProofDagNodeChunk027_checker
      block (by omega) h27
  · exact twentiethCatalogueOrbitProofDagNodeChunk028_checker
      block (by omega) hblock

theorem twentiethCatalogueOrbitProofDagNodeCount_le_valueBound :
    decide (twentiethCatalogueOrbitProofDagCode.nodeCount ≤
      twentiethCatalogueOrbitProofDagCode.nodeValueBound) = true := by
  decide

theorem twentiethCatalogueOrbitProofDagNodeBlockCount :
    twentiethCatalogueOrbitProofDagCode.nodeBlockCount = 232 := by
  rfl

/-- Every orbit representative satisfies its local semantic rule, with all
shared chromogram responses pointing to earlier representatives. -/
theorem twentiethCatalogueOrbitProofDagNode_checker :
    nodeChecker twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode = true := by
  simp only [nodeChecker, Bool.and_eq_true]
  constructor
  · exact twentiethCatalogueOrbitProofDagNodeCount_le_valueBound
  · apply List.all_eq_true.2
    intro block hmember
    apply twentiethCatalogueOrbitProofDagNodeBlock_checker block
    have hblock : block < twentiethCatalogueOrbitProofDagCode.nodeBlockCount :=
      List.mem_range.1 hmember
    rw [twentiethCatalogueOrbitProofDagNodeBlockCount] at hblock
    exact hblock

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
