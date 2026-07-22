import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk007
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk008
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk009
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk010
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk011
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk012
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk013
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk014
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk015
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk016
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk017
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk018
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk019
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk020
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk021
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk022
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk023
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheckChunk024

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheck

open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagData
open ClassicalCertificateTraceResponseRankSummaryDag

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

theorem twentiethCatalogueOrbitRankSummaryDagNodeCount :
    twentiethCatalogueOrbitRankSummaryDag.nodeCount = 102140 := by
  rfl

theorem twentiethCatalogueOrbitRankSummaryDagLayerRootCount :
    twentiethCatalogueOrbitRankSummaryDag.layerRoots.length = 11 := by
  rfl

theorem twentiethCatalogueOrbitRankSummaryDagBlockCount :
    twentiethCatalogueOrbitRankSummaryDag.nodeBlockCount = 200 := by
  rfl

theorem twentiethCatalogueOrbitRankSummaryDagBlock_checker
    (block : Nat) (hblock : block < 200) :
    nodeBlockBoolean twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitRankSummaryDagBlock000_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock001_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock002_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock003_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock004_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock005_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock006_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock007_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock008_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock009_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock010_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock011_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock012_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock013_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock014_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock015_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock016_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock017_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock018_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock019_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock020_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock021_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock022_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock023_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock024_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock025_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock026_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock027_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock028_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock029_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock030_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock031_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock032_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock033_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock034_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock035_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock036_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock037_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock038_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock039_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock040_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock041_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock042_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock043_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock044_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock045_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock046_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock047_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock048_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock049_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock050_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock051_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock052_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock053_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock054_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock055_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock056_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock057_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock058_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock059_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock060_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock061_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock062_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock063_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock064_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock065_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock066_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock067_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock068_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock069_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock070_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock071_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock072_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock073_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock074_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock075_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock076_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock077_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock078_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock079_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock080_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock081_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock082_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock083_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock084_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock085_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock086_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock087_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock088_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock089_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock090_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock091_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock092_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock093_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock094_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock095_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock096_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock097_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock098_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock099_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock100_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock101_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock102_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock103_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock104_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock105_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock106_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock107_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock108_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock109_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock110_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock111_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock112_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock113_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock114_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock115_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock116_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock117_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock118_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock119_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock120_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock121_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock122_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock123_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock124_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock125_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock126_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock127_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock128_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock129_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock130_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock131_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock132_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock133_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock134_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock135_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock136_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock137_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock138_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock139_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock140_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock141_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock142_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock143_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock144_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock145_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock146_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock147_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock148_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock149_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock150_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock151_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock152_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock153_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock154_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock155_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock156_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock157_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock158_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock159_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock160_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock161_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock162_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock163_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock164_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock165_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock166_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock167_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock168_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock169_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock170_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock171_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock172_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock173_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock174_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock175_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock176_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock177_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock178_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock179_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock180_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock181_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock182_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock183_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock184_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock185_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock186_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock187_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock188_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock189_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock190_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock191_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock192_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock193_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock194_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock195_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock196_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock197_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock198_checker,
      twentiethCatalogueOrbitRankSummaryDagBlock199_checker]

theorem twentiethCatalogueOrbitRankSummaryDag_checker :
    checker twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag = true := by
  unfold checker
  rw [twentiethCatalogueOrbitRankSummaryDagBlockCount]
  apply List.all_eq_true.2
  intro block hblock
  exact twentiethCatalogueOrbitRankSummaryDagBlock_checker block
    (List.mem_range.1 hblock)

def twentiethCatalogueOrbitRankSummaryDagRootNode01 : NodeCode :=
  ⟨⟨12, 1566, some 30471, []⟩, 1, [10128, 56667, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode01_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 56669 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode01 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer01_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 1 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 56669 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode01 twentiethCatalogueOrbitRankSummaryDagRootNode01_isNode 1 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 1 12 1566
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode01] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode02 : NodeCode :=
  ⟨⟨12, 1857, some 30471, []⟩, 2, [62802, 75597, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode02_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 75598 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode02 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer02_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 2 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 75598 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode02 twentiethCatalogueOrbitRankSummaryDagRootNode02_isNode 2 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 2 12 1857
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode02] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode03 : NodeCode :=
  ⟨⟨12, 2038, some 30471, []⟩, 3, [78212, 89017, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode03_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 89018 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode03 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer03_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 3 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 89018 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode03 twentiethCatalogueOrbitRankSummaryDagRootNode03_isNode 3 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 3 12 2038
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode03] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode04 : NodeCode :=
  ⟨⟨12, 2150, some 30471, []⟩, 4, [90244, 94867, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode04_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 94868 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode04 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer04_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 4 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 94868 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode04 twentiethCatalogueOrbitRankSummaryDagRootNode04_isNode 4 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 4 12 2150
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode04] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode05 : NodeCode :=
  ⟨⟨12, 2210, some 30471, []⟩, 5, [95682, 98218, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode05_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 98219 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode05 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer05_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 5 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 98219 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode05 twentiethCatalogueOrbitRankSummaryDagRootNode05_isNode 5 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 5 12 2210
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode05] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode06 : NodeCode :=
  ⟨⟨12, 2242, some 30471, []⟩, 6, [98875, 99829, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode06_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 99830 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode06 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer06_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 6 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 99830 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode06 twentiethCatalogueOrbitRankSummaryDagRootNode06_isNode 6 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 6 12 2242
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode06] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode07 : NodeCode :=
  ⟨⟨12, 2263, some 30471, []⟩, 7, [100003, 101268, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode07_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 101269 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode07 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer07_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 7 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 101269 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode07 twentiethCatalogueOrbitRankSummaryDagRootNode07_isNode 7 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 7 12 2263
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode07] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode08 : NodeCode :=
  ⟨⟨12, 2277, some 30471, []⟩, 8, [101318, 101670, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode08_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 101671 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode08 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer08_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 8 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 101671 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode08 twentiethCatalogueOrbitRankSummaryDagRootNode08_isNode 8 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 8 12 2277
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode08] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode09 : NodeCode :=
  ⟨⟨12, 2282, some 30471, []⟩, 9, [101933, 101934, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode09_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 101935 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode09 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer09_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 9 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 101935 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode09 twentiethCatalogueOrbitRankSummaryDagRootNode09_isNode 9 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 9 12 2282
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode09] using hproduct

def twentiethCatalogueOrbitRankSummaryDagRootNode10 : NodeCode :=
  ⟨⟨12, 2289, some 30471, []⟩, 10, [101936, 102138, 56668]⟩

theorem twentiethCatalogueOrbitRankSummaryDagRootNode10_isNode :
    twentiethCatalogueOrbitRankSummaryDag.nodeAt? 102139 =
      some twentiethCatalogueOrbitRankSummaryDagRootNode10 := by
  rfl

theorem twentiethCatalogueOrbitProductLayer10_checker :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate 10 = true := by
  have hproduct := productBoolean_eq_true_of_checker_true
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitRankSummaryDag
        twentiethCatalogueOrbitRankSummaryDag_checker 102139 (by decide)
          twentiethCatalogueOrbitRankSummaryDagRootNode10 twentiethCatalogueOrbitRankSummaryDagRootNode10_isNode 10 (by decide)
  change ClassicalCertificateTraceResponseProduct.productBoolean
    twentiethCatalogueOrbitProductCertificate 10 12 2289
      (some 30471) [] = true
  simpa [twentiethCatalogueOrbitRankSummaryDagRootNode10] using hproduct

theorem twentiethCatalogueOrbitProductLayers_checker
    (layer : Nat) (hpositive : 0 < layer)
    (hlength : layer <
      twentiethCatalogueOrbitProductCertificate.deltaRoots.length) :
    ClassicalCertificateTraceResponseProduct.layerBoolean
      twentiethCatalogueOrbitProductCertificate layer = true := by
  have hupper : layer < 11 := by
    simpa [twentiethCatalogueOrbitProductCertificate] using hlength
  interval_cases layer <;>
    simp_all only [twentiethCatalogueOrbitProductLayer01_checker, twentiethCatalogueOrbitProductLayer02_checker, twentiethCatalogueOrbitProductLayer03_checker, twentiethCatalogueOrbitProductLayer04_checker, twentiethCatalogueOrbitProductLayer05_checker, twentiethCatalogueOrbitProductLayer06_checker, twentiethCatalogueOrbitProductLayer07_checker, twentiethCatalogueOrbitProductLayer08_checker, twentiethCatalogueOrbitProductLayer09_checker, twentiethCatalogueOrbitProductLayer10_checker]

end ClassicalCertificateCatalogueTwentyOrbitRankSummaryDagCheck

end Mettapedia.GraphTheory.FourColor
