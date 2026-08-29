import KrennCollapseComponentContainmentCertificateSegment00
import KrennCollapseComponentContainmentCertificateSegment01
import KrennCollapseComponentContainmentCertificateSegment02
import KrennCollapseComponentContainmentCertificateSegment03
import KrennCollapseComponentContainmentCertificateSegment04
import KrennCollapseComponentContainmentCertificateSegment05
import KrennCollapseComponentContainmentCertificateSegment06
import KrennCollapseComponentContainmentCertificateSegment07
import KrennCollapseComponentContainmentCertificateSegment08
import KrennCollapseComponentContainmentCertificateSegment09
import KrennCollapseComponentContainmentCertificateSegment10
import KrennCollapseComponentContainmentCertificateSegment11
import KrennCollapseComponentContainmentCertificateSegment12
import KrennCollapseComponentContainmentCertificateSegment13
import KrennCollapseComponentContainmentCertificateSegment14
import KrennCollapseComponentContainmentCertificateSegment15

/-! Aggregate interface for all 2,868 concrete support certificates. -/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.LatticeCombinationReflection
open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk : Fin 395 → List StratumCertificate :=
  ![
    certificateChunk000,
    certificateChunk001,
    certificateChunk002,
    certificateChunk003,
    certificateChunk004,
    certificateChunk005,
    certificateChunk006,
    certificateChunk007,
    certificateChunk008,
    certificateChunk009,
    certificateChunk010,
    certificateChunk011,
    certificateChunk012,
    certificateChunk013,
    certificateChunk014,
    certificateChunk015,
    certificateChunk016,
    certificateChunk017,
    certificateChunk018,
    certificateChunk019,
    certificateChunk020,
    certificateChunk021,
    certificateChunk022,
    certificateChunk023,
    certificateChunk024,
    certificateChunk025,
    certificateChunk026,
    certificateChunk027,
    certificateChunk028,
    certificateChunk029,
    certificateChunk030,
    certificateChunk031,
    certificateChunk032,
    certificateChunk033,
    certificateChunk034,
    certificateChunk035,
    certificateChunk036,
    certificateChunk037,
    certificateChunk038,
    certificateChunk039,
    certificateChunk040,
    certificateChunk041,
    certificateChunk042,
    certificateChunk043,
    certificateChunk044,
    certificateChunk045,
    certificateChunk046,
    certificateChunk047,
    certificateChunk048,
    certificateChunk049,
    certificateChunk050,
    certificateChunk051,
    certificateChunk052,
    certificateChunk053,
    certificateChunk054,
    certificateChunk055,
    certificateChunk056,
    certificateChunk057,
    certificateChunk058,
    certificateChunk059,
    certificateChunk060,
    certificateChunk061,
    certificateChunk062,
    certificateChunk063,
    certificateChunk064,
    certificateChunk065,
    certificateChunk066,
    certificateChunk067,
    certificateChunk068,
    certificateChunk069,
    certificateChunk070,
    certificateChunk071,
    certificateChunk072,
    certificateChunk073,
    certificateChunk074,
    certificateChunk075,
    certificateChunk076,
    certificateChunk077,
    certificateChunk078,
    certificateChunk079,
    certificateChunk080,
    certificateChunk081,
    certificateChunk082,
    certificateChunk083,
    certificateChunk084,
    certificateChunk085,
    certificateChunk086,
    certificateChunk087,
    certificateChunk088,
    certificateChunk089,
    certificateChunk090,
    certificateChunk091,
    certificateChunk092,
    certificateChunk093,
    certificateChunk094,
    certificateChunk095,
    certificateChunk096,
    certificateChunk097,
    certificateChunk098,
    certificateChunk099,
    certificateChunk100,
    certificateChunk101,
    certificateChunk102,
    certificateChunk103,
    certificateChunk104,
    certificateChunk105,
    certificateChunk106,
    certificateChunk107,
    certificateChunk108,
    certificateChunk109,
    certificateChunk110,
    certificateChunk111,
    certificateChunk112,
    certificateChunk113,
    certificateChunk114,
    certificateChunk115,
    certificateChunk116,
    certificateChunk117,
    certificateChunk118,
    certificateChunk119,
    certificateChunk120,
    certificateChunk121,
    certificateChunk122,
    certificateChunk123,
    certificateChunk124,
    certificateChunk125,
    certificateChunk126,
    certificateChunk127,
    certificateChunk128,
    certificateChunk129,
    certificateChunk130,
    certificateChunk131,
    certificateChunk132,
    certificateChunk133,
    certificateChunk134,
    certificateChunk135,
    certificateChunk136,
    certificateChunk137,
    certificateChunk138,
    certificateChunk139,
    certificateChunk140,
    certificateChunk141,
    certificateChunk142,
    certificateChunk143,
    certificateChunk144,
    certificateChunk145,
    certificateChunk146,
    certificateChunk147,
    certificateChunk148,
    certificateChunk149,
    certificateChunk150,
    certificateChunk151,
    certificateChunk152,
    certificateChunk153,
    certificateChunk154,
    certificateChunk155,
    certificateChunk156,
    certificateChunk157,
    certificateChunk158,
    certificateChunk159,
    certificateChunk160,
    certificateChunk161,
    certificateChunk162,
    certificateChunk163,
    certificateChunk164,
    certificateChunk165,
    certificateChunk166,
    certificateChunk167,
    certificateChunk168,
    certificateChunk169,
    certificateChunk170,
    certificateChunk171,
    certificateChunk172,
    certificateChunk173,
    certificateChunk174,
    certificateChunk175,
    certificateChunk176,
    certificateChunk177,
    certificateChunk178,
    certificateChunk179,
    certificateChunk180,
    certificateChunk181,
    certificateChunk182,
    certificateChunk183,
    certificateChunk184,
    certificateChunk185,
    certificateChunk186,
    certificateChunk187,
    certificateChunk188,
    certificateChunk189,
    certificateChunk190,
    certificateChunk191,
    certificateChunk192,
    certificateChunk193,
    certificateChunk194,
    certificateChunk195,
    certificateChunk196,
    certificateChunk197,
    certificateChunk198,
    certificateChunk199,
    certificateChunk200,
    certificateChunk201,
    certificateChunk202,
    certificateChunk203,
    certificateChunk204,
    certificateChunk205,
    certificateChunk206,
    certificateChunk207,
    certificateChunk208,
    certificateChunk209,
    certificateChunk210,
    certificateChunk211,
    certificateChunk212,
    certificateChunk213,
    certificateChunk214,
    certificateChunk215,
    certificateChunk216,
    certificateChunk217,
    certificateChunk218,
    certificateChunk219,
    certificateChunk220,
    certificateChunk221,
    certificateChunk222,
    certificateChunk223,
    certificateChunk224,
    certificateChunk225,
    certificateChunk226,
    certificateChunk227,
    certificateChunk228,
    certificateChunk229,
    certificateChunk230,
    certificateChunk231,
    certificateChunk232,
    certificateChunk233,
    certificateChunk234,
    certificateChunk235,
    certificateChunk236,
    certificateChunk237,
    certificateChunk238,
    certificateChunk239,
    certificateChunk240,
    certificateChunk241,
    certificateChunk242,
    certificateChunk243,
    certificateChunk244,
    certificateChunk245,
    certificateChunk246,
    certificateChunk247,
    certificateChunk248,
    certificateChunk249,
    certificateChunk250,
    certificateChunk251,
    certificateChunk252,
    certificateChunk253,
    certificateChunk254,
    certificateChunk255,
    certificateChunk256,
    certificateChunk257,
    certificateChunk258,
    certificateChunk259,
    certificateChunk260,
    certificateChunk261,
    certificateChunk262,
    certificateChunk263,
    certificateChunk264,
    certificateChunk265,
    certificateChunk266,
    certificateChunk267,
    certificateChunk268,
    certificateChunk269,
    certificateChunk270,
    certificateChunk271,
    certificateChunk272,
    certificateChunk273,
    certificateChunk274,
    certificateChunk275,
    certificateChunk276,
    certificateChunk277,
    certificateChunk278,
    certificateChunk279,
    certificateChunk280,
    certificateChunk281,
    certificateChunk282,
    certificateChunk283,
    certificateChunk284,
    certificateChunk285,
    certificateChunk286,
    certificateChunk287,
    certificateChunk288,
    certificateChunk289,
    certificateChunk290,
    certificateChunk291,
    certificateChunk292,
    certificateChunk293,
    certificateChunk294,
    certificateChunk295,
    certificateChunk296,
    certificateChunk297,
    certificateChunk298,
    certificateChunk299,
    certificateChunk300,
    certificateChunk301,
    certificateChunk302,
    certificateChunk303,
    certificateChunk304,
    certificateChunk305,
    certificateChunk306,
    certificateChunk307,
    certificateChunk308,
    certificateChunk309,
    certificateChunk310,
    certificateChunk311,
    certificateChunk312,
    certificateChunk313,
    certificateChunk314,
    certificateChunk315,
    certificateChunk316,
    certificateChunk317,
    certificateChunk318,
    certificateChunk319,
    certificateChunk320,
    certificateChunk321,
    certificateChunk322,
    certificateChunk323,
    certificateChunk324,
    certificateChunk325,
    certificateChunk326,
    certificateChunk327,
    certificateChunk328,
    certificateChunk329,
    certificateChunk330,
    certificateChunk331,
    certificateChunk332,
    certificateChunk333,
    certificateChunk334,
    certificateChunk335,
    certificateChunk336,
    certificateChunk337,
    certificateChunk338,
    certificateChunk339,
    certificateChunk340,
    certificateChunk341,
    certificateChunk342,
    certificateChunk343,
    certificateChunk344,
    certificateChunk345,
    certificateChunk346,
    certificateChunk347,
    certificateChunk348,
    certificateChunk349,
    certificateChunk350,
    certificateChunk351,
    certificateChunk352,
    certificateChunk353,
    certificateChunk354,
    certificateChunk355,
    certificateChunk356,
    certificateChunk357,
    certificateChunk358,
    certificateChunk359,
    certificateChunk360,
    certificateChunk361,
    certificateChunk362,
    certificateChunk363,
    certificateChunk364,
    certificateChunk365,
    certificateChunk366,
    certificateChunk367,
    certificateChunk368,
    certificateChunk369,
    certificateChunk370,
    certificateChunk371,
    certificateChunk372,
    certificateChunk373,
    certificateChunk374,
    certificateChunk375,
    certificateChunk376,
    certificateChunk377,
    certificateChunk378,
    certificateChunk379,
    certificateChunk380,
    certificateChunk381,
    certificateChunk382,
    certificateChunk383,
    certificateChunk384,
    certificateChunk385,
    certificateChunk386,
    certificateChunk387,
    certificateChunk388,
    certificateChunk389,
    certificateChunk390,
    certificateChunk391,
    certificateChunk392,
    certificateChunk393,
    certificateChunk394
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem certificateChunk_valid (index : Fin 395) :
    List.Forall StratumCertificate.Valid (certificateChunk index) := by
  fin_cases index
  · exact certificateChunk000_valid
  · exact certificateChunk001_valid
  · exact certificateChunk002_valid
  · exact certificateChunk003_valid
  · exact certificateChunk004_valid
  · exact certificateChunk005_valid
  · exact certificateChunk006_valid
  · exact certificateChunk007_valid
  · exact certificateChunk008_valid
  · exact certificateChunk009_valid
  · exact certificateChunk010_valid
  · exact certificateChunk011_valid
  · exact certificateChunk012_valid
  · exact certificateChunk013_valid
  · exact certificateChunk014_valid
  · exact certificateChunk015_valid
  · exact certificateChunk016_valid
  · exact certificateChunk017_valid
  · exact certificateChunk018_valid
  · exact certificateChunk019_valid
  · exact certificateChunk020_valid
  · exact certificateChunk021_valid
  · exact certificateChunk022_valid
  · exact certificateChunk023_valid
  · exact certificateChunk024_valid
  · exact certificateChunk025_valid
  · exact certificateChunk026_valid
  · exact certificateChunk027_valid
  · exact certificateChunk028_valid
  · exact certificateChunk029_valid
  · exact certificateChunk030_valid
  · exact certificateChunk031_valid
  · exact certificateChunk032_valid
  · exact certificateChunk033_valid
  · exact certificateChunk034_valid
  · exact certificateChunk035_valid
  · exact certificateChunk036_valid
  · exact certificateChunk037_valid
  · exact certificateChunk038_valid
  · exact certificateChunk039_valid
  · exact certificateChunk040_valid
  · exact certificateChunk041_valid
  · exact certificateChunk042_valid
  · exact certificateChunk043_valid
  · exact certificateChunk044_valid
  · exact certificateChunk045_valid
  · exact certificateChunk046_valid
  · exact certificateChunk047_valid
  · exact certificateChunk048_valid
  · exact certificateChunk049_valid
  · exact certificateChunk050_valid
  · exact certificateChunk051_valid
  · exact certificateChunk052_valid
  · exact certificateChunk053_valid
  · exact certificateChunk054_valid
  · exact certificateChunk055_valid
  · exact certificateChunk056_valid
  · exact certificateChunk057_valid
  · exact certificateChunk058_valid
  · exact certificateChunk059_valid
  · exact certificateChunk060_valid
  · exact certificateChunk061_valid
  · exact certificateChunk062_valid
  · exact certificateChunk063_valid
  · exact certificateChunk064_valid
  · exact certificateChunk065_valid
  · exact certificateChunk066_valid
  · exact certificateChunk067_valid
  · exact certificateChunk068_valid
  · exact certificateChunk069_valid
  · exact certificateChunk070_valid
  · exact certificateChunk071_valid
  · exact certificateChunk072_valid
  · exact certificateChunk073_valid
  · exact certificateChunk074_valid
  · exact certificateChunk075_valid
  · exact certificateChunk076_valid
  · exact certificateChunk077_valid
  · exact certificateChunk078_valid
  · exact certificateChunk079_valid
  · exact certificateChunk080_valid
  · exact certificateChunk081_valid
  · exact certificateChunk082_valid
  · exact certificateChunk083_valid
  · exact certificateChunk084_valid
  · exact certificateChunk085_valid
  · exact certificateChunk086_valid
  · exact certificateChunk087_valid
  · exact certificateChunk088_valid
  · exact certificateChunk089_valid
  · exact certificateChunk090_valid
  · exact certificateChunk091_valid
  · exact certificateChunk092_valid
  · exact certificateChunk093_valid
  · exact certificateChunk094_valid
  · exact certificateChunk095_valid
  · exact certificateChunk096_valid
  · exact certificateChunk097_valid
  · exact certificateChunk098_valid
  · exact certificateChunk099_valid
  · exact certificateChunk100_valid
  · exact certificateChunk101_valid
  · exact certificateChunk102_valid
  · exact certificateChunk103_valid
  · exact certificateChunk104_valid
  · exact certificateChunk105_valid
  · exact certificateChunk106_valid
  · exact certificateChunk107_valid
  · exact certificateChunk108_valid
  · exact certificateChunk109_valid
  · exact certificateChunk110_valid
  · exact certificateChunk111_valid
  · exact certificateChunk112_valid
  · exact certificateChunk113_valid
  · exact certificateChunk114_valid
  · exact certificateChunk115_valid
  · exact certificateChunk116_valid
  · exact certificateChunk117_valid
  · exact certificateChunk118_valid
  · exact certificateChunk119_valid
  · exact certificateChunk120_valid
  · exact certificateChunk121_valid
  · exact certificateChunk122_valid
  · exact certificateChunk123_valid
  · exact certificateChunk124_valid
  · exact certificateChunk125_valid
  · exact certificateChunk126_valid
  · exact certificateChunk127_valid
  · exact certificateChunk128_valid
  · exact certificateChunk129_valid
  · exact certificateChunk130_valid
  · exact certificateChunk131_valid
  · exact certificateChunk132_valid
  · exact certificateChunk133_valid
  · exact certificateChunk134_valid
  · exact certificateChunk135_valid
  · exact certificateChunk136_valid
  · exact certificateChunk137_valid
  · exact certificateChunk138_valid
  · exact certificateChunk139_valid
  · exact certificateChunk140_valid
  · exact certificateChunk141_valid
  · exact certificateChunk142_valid
  · exact certificateChunk143_valid
  · exact certificateChunk144_valid
  · exact certificateChunk145_valid
  · exact certificateChunk146_valid
  · exact certificateChunk147_valid
  · exact certificateChunk148_valid
  · exact certificateChunk149_valid
  · exact certificateChunk150_valid
  · exact certificateChunk151_valid
  · exact certificateChunk152_valid
  · exact certificateChunk153_valid
  · exact certificateChunk154_valid
  · exact certificateChunk155_valid
  · exact certificateChunk156_valid
  · exact certificateChunk157_valid
  · exact certificateChunk158_valid
  · exact certificateChunk159_valid
  · exact certificateChunk160_valid
  · exact certificateChunk161_valid
  · exact certificateChunk162_valid
  · exact certificateChunk163_valid
  · exact certificateChunk164_valid
  · exact certificateChunk165_valid
  · exact certificateChunk166_valid
  · exact certificateChunk167_valid
  · exact certificateChunk168_valid
  · exact certificateChunk169_valid
  · exact certificateChunk170_valid
  · exact certificateChunk171_valid
  · exact certificateChunk172_valid
  · exact certificateChunk173_valid
  · exact certificateChunk174_valid
  · exact certificateChunk175_valid
  · exact certificateChunk176_valid
  · exact certificateChunk177_valid
  · exact certificateChunk178_valid
  · exact certificateChunk179_valid
  · exact certificateChunk180_valid
  · exact certificateChunk181_valid
  · exact certificateChunk182_valid
  · exact certificateChunk183_valid
  · exact certificateChunk184_valid
  · exact certificateChunk185_valid
  · exact certificateChunk186_valid
  · exact certificateChunk187_valid
  · exact certificateChunk188_valid
  · exact certificateChunk189_valid
  · exact certificateChunk190_valid
  · exact certificateChunk191_valid
  · exact certificateChunk192_valid
  · exact certificateChunk193_valid
  · exact certificateChunk194_valid
  · exact certificateChunk195_valid
  · exact certificateChunk196_valid
  · exact certificateChunk197_valid
  · exact certificateChunk198_valid
  · exact certificateChunk199_valid
  · exact certificateChunk200_valid
  · exact certificateChunk201_valid
  · exact certificateChunk202_valid
  · exact certificateChunk203_valid
  · exact certificateChunk204_valid
  · exact certificateChunk205_valid
  · exact certificateChunk206_valid
  · exact certificateChunk207_valid
  · exact certificateChunk208_valid
  · exact certificateChunk209_valid
  · exact certificateChunk210_valid
  · exact certificateChunk211_valid
  · exact certificateChunk212_valid
  · exact certificateChunk213_valid
  · exact certificateChunk214_valid
  · exact certificateChunk215_valid
  · exact certificateChunk216_valid
  · exact certificateChunk217_valid
  · exact certificateChunk218_valid
  · exact certificateChunk219_valid
  · exact certificateChunk220_valid
  · exact certificateChunk221_valid
  · exact certificateChunk222_valid
  · exact certificateChunk223_valid
  · exact certificateChunk224_valid
  · exact certificateChunk225_valid
  · exact certificateChunk226_valid
  · exact certificateChunk227_valid
  · exact certificateChunk228_valid
  · exact certificateChunk229_valid
  · exact certificateChunk230_valid
  · exact certificateChunk231_valid
  · exact certificateChunk232_valid
  · exact certificateChunk233_valid
  · exact certificateChunk234_valid
  · exact certificateChunk235_valid
  · exact certificateChunk236_valid
  · exact certificateChunk237_valid
  · exact certificateChunk238_valid
  · exact certificateChunk239_valid
  · exact certificateChunk240_valid
  · exact certificateChunk241_valid
  · exact certificateChunk242_valid
  · exact certificateChunk243_valid
  · exact certificateChunk244_valid
  · exact certificateChunk245_valid
  · exact certificateChunk246_valid
  · exact certificateChunk247_valid
  · exact certificateChunk248_valid
  · exact certificateChunk249_valid
  · exact certificateChunk250_valid
  · exact certificateChunk251_valid
  · exact certificateChunk252_valid
  · exact certificateChunk253_valid
  · exact certificateChunk254_valid
  · exact certificateChunk255_valid
  · exact certificateChunk256_valid
  · exact certificateChunk257_valid
  · exact certificateChunk258_valid
  · exact certificateChunk259_valid
  · exact certificateChunk260_valid
  · exact certificateChunk261_valid
  · exact certificateChunk262_valid
  · exact certificateChunk263_valid
  · exact certificateChunk264_valid
  · exact certificateChunk265_valid
  · exact certificateChunk266_valid
  · exact certificateChunk267_valid
  · exact certificateChunk268_valid
  · exact certificateChunk269_valid
  · exact certificateChunk270_valid
  · exact certificateChunk271_valid
  · exact certificateChunk272_valid
  · exact certificateChunk273_valid
  · exact certificateChunk274_valid
  · exact certificateChunk275_valid
  · exact certificateChunk276_valid
  · exact certificateChunk277_valid
  · exact certificateChunk278_valid
  · exact certificateChunk279_valid
  · exact certificateChunk280_valid
  · exact certificateChunk281_valid
  · exact certificateChunk282_valid
  · exact certificateChunk283_valid
  · exact certificateChunk284_valid
  · exact certificateChunk285_valid
  · exact certificateChunk286_valid
  · exact certificateChunk287_valid
  · exact certificateChunk288_valid
  · exact certificateChunk289_valid
  · exact certificateChunk290_valid
  · exact certificateChunk291_valid
  · exact certificateChunk292_valid
  · exact certificateChunk293_valid
  · exact certificateChunk294_valid
  · exact certificateChunk295_valid
  · exact certificateChunk296_valid
  · exact certificateChunk297_valid
  · exact certificateChunk298_valid
  · exact certificateChunk299_valid
  · exact certificateChunk300_valid
  · exact certificateChunk301_valid
  · exact certificateChunk302_valid
  · exact certificateChunk303_valid
  · exact certificateChunk304_valid
  · exact certificateChunk305_valid
  · exact certificateChunk306_valid
  · exact certificateChunk307_valid
  · exact certificateChunk308_valid
  · exact certificateChunk309_valid
  · exact certificateChunk310_valid
  · exact certificateChunk311_valid
  · exact certificateChunk312_valid
  · exact certificateChunk313_valid
  · exact certificateChunk314_valid
  · exact certificateChunk315_valid
  · exact certificateChunk316_valid
  · exact certificateChunk317_valid
  · exact certificateChunk318_valid
  · exact certificateChunk319_valid
  · exact certificateChunk320_valid
  · exact certificateChunk321_valid
  · exact certificateChunk322_valid
  · exact certificateChunk323_valid
  · exact certificateChunk324_valid
  · exact certificateChunk325_valid
  · exact certificateChunk326_valid
  · exact certificateChunk327_valid
  · exact certificateChunk328_valid
  · exact certificateChunk329_valid
  · exact certificateChunk330_valid
  · exact certificateChunk331_valid
  · exact certificateChunk332_valid
  · exact certificateChunk333_valid
  · exact certificateChunk334_valid
  · exact certificateChunk335_valid
  · exact certificateChunk336_valid
  · exact certificateChunk337_valid
  · exact certificateChunk338_valid
  · exact certificateChunk339_valid
  · exact certificateChunk340_valid
  · exact certificateChunk341_valid
  · exact certificateChunk342_valid
  · exact certificateChunk343_valid
  · exact certificateChunk344_valid
  · exact certificateChunk345_valid
  · exact certificateChunk346_valid
  · exact certificateChunk347_valid
  · exact certificateChunk348_valid
  · exact certificateChunk349_valid
  · exact certificateChunk350_valid
  · exact certificateChunk351_valid
  · exact certificateChunk352_valid
  · exact certificateChunk353_valid
  · exact certificateChunk354_valid
  · exact certificateChunk355_valid
  · exact certificateChunk356_valid
  · exact certificateChunk357_valid
  · exact certificateChunk358_valid
  · exact certificateChunk359_valid
  · exact certificateChunk360_valid
  · exact certificateChunk361_valid
  · exact certificateChunk362_valid
  · exact certificateChunk363_valid
  · exact certificateChunk364_valid
  · exact certificateChunk365_valid
  · exact certificateChunk366_valid
  · exact certificateChunk367_valid
  · exact certificateChunk368_valid
  · exact certificateChunk369_valid
  · exact certificateChunk370_valid
  · exact certificateChunk371_valid
  · exact certificateChunk372_valid
  · exact certificateChunk373_valid
  · exact certificateChunk374_valid
  · exact certificateChunk375_valid
  · exact certificateChunk376_valid
  · exact certificateChunk377_valid
  · exact certificateChunk378_valid
  · exact certificateChunk379_valid
  · exact certificateChunk380_valid
  · exact certificateChunk381_valid
  · exact certificateChunk382_valid
  · exact certificateChunk383_valid
  · exact certificateChunk384_valid
  · exact certificateChunk385_valid
  · exact certificateChunk386_valid
  · exact certificateChunk387_valid
  · exact certificateChunk388_valid
  · exact certificateChunk389_valid
  · exact certificateChunk390_valid
  · exact certificateChunk391_valid
  · exact certificateChunk392_valid
  · exact certificateChunk393_valid
  · exact certificateChunk394_valid

set_option maxRecDepth 1000000 in
def certificates : List StratumCertificate :=
  (List.finRange 395).flatMap certificateChunk

set_option maxRecDepth 1000000 in
theorem certificates_valid :
    List.Forall StratumCertificate.Valid certificates := by
  rw [List.forall_iff_forall_mem]
  intro certificate member
  rcases List.mem_flatMap.mp member with ⟨index, _, inChunk⟩
  exact List.forall_iff_forall_mem.mp (certificateChunk_valid index)
    certificate inChunk

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem certificate_strata_exact :
    certificates.map StratumCertificate.stratum = strata := by
  decide

/-- The concrete composable bottom-up connector.  Once the LRAT cover
chooses a listed stratum, all normalized generators of its selected
component vanish at the same field point. -/
theorem component_generators_vanish_of_covers
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (stratum : GlobalFormula.Stratum) (inData : stratum ∈ strata)
    (pattern : Fin 26 → Prop) (values : Fin 26 → R)
    (covered : Covers stratum pattern)
    (support : ∀ coordinate, pattern coordinate ↔ values coordinate ≠ 0)
    (relationEq : ∀ index,
      monomial values (relation index).left =
        monomial values (relation index).right) :
    ∀ generator ∈ componentGenerators stratum.component,
      generatorEval values generator = 0 := by
  have mappedMember :
      stratum ∈ certificates.map StratumCertificate.stratum := by
    rw [certificate_strata_exact]
    exact inData
  obtain ⟨certificate, certificateMember, rfl⟩ :=
    List.mem_map.mp mappedMember
  have valid := List.forall_iff_forall_mem.mp certificates_valid
    certificate certificateMember
  exact component_generators_vanish_of_valid_certificate certificate
    pattern values covered support relationEq valid

/-- Top-down and bottom-up meet here: every feasible reduced support
pattern selects a certified component whose normalized generators all
vanish at the same point. -/
theorem exists_covered_component_generators_vanish
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (pattern : Fin 26 → Prop) (feasible : Feasible pattern)
    (values : Fin 26 → R)
    (support : ∀ coordinate, pattern coordinate ↔ values coordinate ≠ 0)
    (relationEq : ∀ index,
      monomial values (relation index).left =
        monomial values (relation index).right) :
    ∃ stratum ∈ strata, Covers stratum pattern ∧
      ∀ generator ∈ componentGenerators stratum.component,
        generatorEval values generator = 0 := by
  obtain ⟨stratum, inData, covered⟩ :=
    everyFeasiblePatternCovered pattern feasible
  exact ⟨stratum, inData, covered,
    component_generators_vanish_of_covers stratum inData pattern values
      covered support relationEq⟩

#print axioms component_generators_vanish_of_covers
#print axioms exists_covered_component_generators_vanish

end Krenn.CollapseComponentContainmentCertificates
