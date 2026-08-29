import KrennX5Case1Data

namespace Krenn.X5Case1Trace

open Krenn.MultilinearTrace
open Krenn.MultilinearTrace.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

abbrev certificate : Certificate := Krenn.X5Case1Data.certificate
def traceSHA256 : String := Krenn.X5Case1Data.traceSHA256
def traceSystemSHA256 : String := Krenn.X5Case1Data.traceSystemSHA256
def frozenSystemSemanticSHA256 : String := Krenn.X5Case1Data.frozenSystemSemanticSHA256
def frozenSystemFileSHA256 : String := Krenn.X5Case1Data.frozenSystemFileSHA256

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_0_64 : certificate.NodeChunkValid 0 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_64_128 : certificate.NodeChunkValid 64 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_128_192 : certificate.NodeChunkValid 128 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_192_256 : certificate.NodeChunkValid 192 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_256_320 : certificate.NodeChunkValid 256 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_320_384 : certificate.NodeChunkValid 320 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_384_448 : certificate.NodeChunkValid 384 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_448_512 : certificate.NodeChunkValid 448 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_512_576 : certificate.NodeChunkValid 512 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_576_640 : certificate.NodeChunkValid 576 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_640_704 : certificate.NodeChunkValid 640 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_704_768 : certificate.NodeChunkValid 704 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_768_832 : certificate.NodeChunkValid 768 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_832_896 : certificate.NodeChunkValid 832 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_896_960 : certificate.NodeChunkValid 896 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_960_1024 : certificate.NodeChunkValid 960 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1024_1088 : certificate.NodeChunkValid 1024 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1088_1152 : certificate.NodeChunkValid 1088 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1152_1216 : certificate.NodeChunkValid 1152 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1216_1280 : certificate.NodeChunkValid 1216 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1280_1344 : certificate.NodeChunkValid 1280 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1344_1408 : certificate.NodeChunkValid 1344 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1408_1472 : certificate.NodeChunkValid 1408 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1472_1536 : certificate.NodeChunkValid 1472 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1536_1600 : certificate.NodeChunkValid 1536 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1600_1664 : certificate.NodeChunkValid 1600 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1664_1728 : certificate.NodeChunkValid 1664 64 :=
  nodeChunkValid_of_checkNodes (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem chunk_1728_1746 : certificate.NodeChunkValid 1728 18 :=
  nodeChunkValid_of_checkNodes (by decide)

theorem valid : certificate.Valid := by
  refine ⟨by decide, by decide, validRootB_eq_true.mp (by decide), ?_⟩
  intro position inRange
  have positionBound : position < 1746 := by simpa using inRange
  by_cases before_64 : position < 64
  · exact chunk_0_64 position (by omega) before_64
  by_cases before_128 : position < 128
  · exact chunk_64_128 position (by omega) before_128
  by_cases before_192 : position < 192
  · exact chunk_128_192 position (by omega) before_192
  by_cases before_256 : position < 256
  · exact chunk_192_256 position (by omega) before_256
  by_cases before_320 : position < 320
  · exact chunk_256_320 position (by omega) before_320
  by_cases before_384 : position < 384
  · exact chunk_320_384 position (by omega) before_384
  by_cases before_448 : position < 448
  · exact chunk_384_448 position (by omega) before_448
  by_cases before_512 : position < 512
  · exact chunk_448_512 position (by omega) before_512
  by_cases before_576 : position < 576
  · exact chunk_512_576 position (by omega) before_576
  by_cases before_640 : position < 640
  · exact chunk_576_640 position (by omega) before_640
  by_cases before_704 : position < 704
  · exact chunk_640_704 position (by omega) before_704
  by_cases before_768 : position < 768
  · exact chunk_704_768 position (by omega) before_768
  by_cases before_832 : position < 832
  · exact chunk_768_832 position (by omega) before_832
  by_cases before_896 : position < 896
  · exact chunk_832_896 position (by omega) before_896
  by_cases before_960 : position < 960
  · exact chunk_896_960 position (by omega) before_960
  by_cases before_1024 : position < 1024
  · exact chunk_960_1024 position (by omega) before_1024
  by_cases before_1088 : position < 1088
  · exact chunk_1024_1088 position (by omega) before_1088
  by_cases before_1152 : position < 1152
  · exact chunk_1088_1152 position (by omega) before_1152
  by_cases before_1216 : position < 1216
  · exact chunk_1152_1216 position (by omega) before_1216
  by_cases before_1280 : position < 1280
  · exact chunk_1216_1280 position (by omega) before_1280
  by_cases before_1344 : position < 1344
  · exact chunk_1280_1344 position (by omega) before_1344
  by_cases before_1408 : position < 1408
  · exact chunk_1344_1408 position (by omega) before_1408
  by_cases before_1472 : position < 1472
  · exact chunk_1408_1472 position (by omega) before_1472
  by_cases before_1536 : position < 1536
  · exact chunk_1472_1536 position (by omega) before_1536
  by_cases before_1600 : position < 1600
  · exact chunk_1536_1600 position (by omega) before_1600
  by_cases before_1664 : position < 1664
  · exact chunk_1600_1664 position (by omega) before_1664
  by_cases before_1728 : position < 1728
  · exact chunk_1664_1728 position (by omega) before_1728
  exact chunk_1728_1746 position (by omega) (by omega)

theorem closed {R : Type*} [Field R] [CharZero R] :
    certificate.ClosedState (R := R) { zero := [], extras := [] } :=
  closed_root_of_valid valid

end Krenn.X5Case1Trace

#print axioms Krenn.X5Case1Trace.valid
#print axioms Krenn.X5Case1Trace.closed
