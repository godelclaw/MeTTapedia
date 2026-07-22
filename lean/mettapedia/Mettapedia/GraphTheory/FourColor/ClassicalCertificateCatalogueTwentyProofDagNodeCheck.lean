import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup008
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup009
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckGroup010

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

theorem twentiethCatalogueProofDagNodeBlock_checker
    (block : Nat) (hblock : block < 664) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h0 : block < 64
  · exact twentiethCatalogueProofDagNodeGroup000_checker
      block (by omega) h0
  by_cases h1 : block < 128
  · exact twentiethCatalogueProofDagNodeGroup001_checker
      block (by omega) h1
  by_cases h2 : block < 192
  · exact twentiethCatalogueProofDagNodeGroup002_checker
      block (by omega) h2
  by_cases h3 : block < 256
  · exact twentiethCatalogueProofDagNodeGroup003_checker
      block (by omega) h3
  by_cases h4 : block < 320
  · exact twentiethCatalogueProofDagNodeGroup004_checker
      block (by omega) h4
  by_cases h5 : block < 384
  · exact twentiethCatalogueProofDagNodeGroup005_checker
      block (by omega) h5
  by_cases h6 : block < 448
  · exact twentiethCatalogueProofDagNodeGroup006_checker
      block (by omega) h6
  by_cases h7 : block < 512
  · exact twentiethCatalogueProofDagNodeGroup007_checker
      block (by omega) h7
  by_cases h8 : block < 576
  · exact twentiethCatalogueProofDagNodeGroup008_checker
      block (by omega) h8
  by_cases h9 : block < 640
  · exact twentiethCatalogueProofDagNodeGroup009_checker
      block (by omega) h9
  · exact twentiethCatalogueProofDagNodeGroup010_checker
      block (by omega) hblock

theorem twentiethCatalogueProofDagNodeCount_le_valueBound :
    decide (twentiethCatalogueProofDagCode.nodeCount ≤
      twentiethCatalogueProofDagCode.nodeValueBound) = true := by
  decide

theorem twentiethCatalogueProofDagNodeBlockCount :
    twentiethCatalogueProofDagCode.nodeBlockCount = 664 := by
  rfl

/-- Every node of the exact cf020 proof DAG satisfies its local semantic
rule, and every recursive reference is bounded by the stored DAG. -/
theorem twentiethCatalogueProofDagNode_checker :
    nodeChecker twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode = true := by
  simp only [nodeChecker, Bool.and_eq_true]
  constructor
  · exact twentiethCatalogueProofDagNodeCount_le_valueBound
  · apply List.all_eq_true.2
    intro block hmember
    apply twentiethCatalogueProofDagNodeBlock_checker block
    have hblock : block < twentiethCatalogueProofDagCode.nodeBlockCount :=
      List.mem_range.1 hmember
    rw [twentiethCatalogueProofDagNodeBlockCount] at hblock
    exact hblock

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
