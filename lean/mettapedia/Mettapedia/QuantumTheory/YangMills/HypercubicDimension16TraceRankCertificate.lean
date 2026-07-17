import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateShape
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk000
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk001
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk002
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk003
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk004
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk005
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk006
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk007
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk008
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk009
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk010
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk011
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk012
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk013
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk014
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk015
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk016
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk017
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk018
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk019
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk020
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk021
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk022
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk023
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk024
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk025
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk026
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk027
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk028
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk029
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk030
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk031
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk032
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk033
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk034
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk035
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk036
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk037
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk038
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk039
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk040
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk041
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk042
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk043
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk044
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateChunk045

/-!
# Exact rank certificate for eight-field trace relations

The row-reduction replay is split into independently compiled ranges so that
each kernel proof stays sparse and bounded.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificate

def rationalReplayCheck : Bool :=
  certificateShapeCheck &&
    rationalReplayRangeCheck 0 256 &&
    rationalReplayRangeCheck 256 256 &&
    rationalReplayRangeCheck 512 256 &&
    rationalReplayRangeCheck 768 256 &&
    rationalReplayRangeCheck 1024 256 &&
    rationalReplayRangeCheck 1280 256 &&
    rationalReplayRangeCheck 1536 256 &&
    rationalReplayRangeCheck 1792 256 &&
    rationalReplayRangeCheck 2048 256 &&
    rationalReplayRangeCheck 2304 256 &&
    rationalReplayRangeCheck 2560 256 &&
    rationalReplayRangeCheck 2816 256 &&
    rationalReplayRangeCheck 3072 256 &&
    rationalReplayRangeCheck 3328 256 &&
    rationalReplayRangeCheck 3584 256 &&
    rationalReplayRangeCheck 3840 256 &&
    rationalReplayRangeCheck 4096 256 &&
    rationalReplayRangeCheck 4352 256 &&
    rationalReplayRangeCheck 4608 256 &&
    rationalReplayRangeCheck 4864 256 &&
    rationalReplayRangeCheck 5120 256 &&
    rationalReplayRangeCheck 5376 256 &&
    rationalReplayRangeCheck 5632 256 &&
    rationalReplayRangeCheck 5888 256 &&
    rationalReplayRangeCheck 6144 256 &&
    rationalReplayRangeCheck 6400 256 &&
    rationalReplayRangeCheck 6656 256 &&
    rationalReplayRangeCheck 6912 256 &&
    rationalReplayRangeCheck 7168 256 &&
    rationalReplayRangeCheck 7424 256 &&
    rationalReplayRangeCheck 7680 256 &&
    rationalReplayRangeCheck 7936 256 &&
    rationalReplayRangeCheck 8192 256 &&
    rationalReplayRangeCheck 8448 256 &&
    rationalReplayRangeCheck 8704 256 &&
    rationalReplayRangeCheck 8960 256 &&
    rationalReplayRangeCheck 9216 256 &&
    rationalReplayRangeCheck 9472 256 &&
    rationalReplayRangeCheck 9728 256 &&
    rationalReplayRangeCheck 9984 256 &&
    rationalReplayRangeCheck 10240 256 &&
    rationalReplayRangeCheck 10496 256 &&
    rationalReplayRangeCheck 10752 256 &&
    rationalReplayRangeCheck 11008 256 &&
    rationalReplayRangeCheck 11264 256 &&
    rationalReplayRangeCheck 11520 36

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rationalReplayCheck_certificate : rationalReplayCheck = true := by
  simp [rationalReplayCheck, certificateShapeCheck_certificate,
    rationalReplayRangeCheck_000,
    rationalReplayRangeCheck_001,
    rationalReplayRangeCheck_002,
    rationalReplayRangeCheck_003,
    rationalReplayRangeCheck_004,
    rationalReplayRangeCheck_005,
    rationalReplayRangeCheck_006,
    rationalReplayRangeCheck_007,
    rationalReplayRangeCheck_008,
    rationalReplayRangeCheck_009,
    rationalReplayRangeCheck_010,
    rationalReplayRangeCheck_011,
    rationalReplayRangeCheck_012,
    rationalReplayRangeCheck_013,
    rationalReplayRangeCheck_014,
    rationalReplayRangeCheck_015,
    rationalReplayRangeCheck_016,
    rationalReplayRangeCheck_017,
    rationalReplayRangeCheck_018,
    rationalReplayRangeCheck_019,
    rationalReplayRangeCheck_020,
    rationalReplayRangeCheck_021,
    rationalReplayRangeCheck_022,
    rationalReplayRangeCheck_023,
    rationalReplayRangeCheck_024,
    rationalReplayRangeCheck_025,
    rationalReplayRangeCheck_026,
    rationalReplayRangeCheck_027,
    rationalReplayRangeCheck_028,
    rationalReplayRangeCheck_029,
    rationalReplayRangeCheck_030,
    rationalReplayRangeCheck_031,
    rationalReplayRangeCheck_032,
    rationalReplayRangeCheck_033,
    rationalReplayRangeCheck_034,
    rationalReplayRangeCheck_035,
    rationalReplayRangeCheck_036,
    rationalReplayRangeCheck_037,
    rationalReplayRangeCheck_038,
    rationalReplayRangeCheck_039,
    rationalReplayRangeCheck_040,
    rationalReplayRangeCheck_041,
    rationalReplayRangeCheck_042,
    rationalReplayRangeCheck_043,
    rationalReplayRangeCheck_044,
    rationalReplayRangeCheck_045]

end HypercubicDimension16TraceRankCertificate
end YangMills
end QuantumTheory
end Mettapedia

