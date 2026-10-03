import MettapediaFourColor.WheelRepairRecord0
import MettapediaFourColor.WheelRepairRecord1
import MettapediaFourColor.WheelRepairRecord2
import MettapediaFourColor.WheelRepairRecord3
import MettapediaFourColor.WheelRepairRecord4
import MettapediaFourColor.WheelRepairRecord5
import MettapediaFourColor.WheelRepairRecord6
import MettapediaFourColor.WheelRepairRecord7
import MettapediaFourColor.WheelRepairRecord8
import MettapediaFourColor.WheelRepairRecord9
import MettapediaFourColor.WheelRepairRecord10
import MettapediaFourColor.WheelRepairRecord11
import MettapediaFourColor.WheelRepairRecord12
import MettapediaFourColor.WheelRepairRecord13
import MettapediaFourColor.WheelRepairRecord14
import MettapediaFourColor.WheelRepairRecord15
import MettapediaFourColor.WheelRepairRecord16
import MettapediaFourColor.WheelRepairInput0
import MettapediaFourColor.WheelRepairInput1
import MettapediaFourColor.WheelRepairInput2
import MettapediaFourColor.WheelRepairInput3
import MettapediaFourColor.WheelRepairInput4
import MettapediaFourColor.WheelRepairInput5
import MettapediaFourColor.WheelRepairInput6
import MettapediaFourColor.WheelRepairInput7
import MettapediaFourColor.WheelRepairInput8
import MettapediaFourColor.WheelRepairInput9
import MettapediaFourColor.WheelRepairInput10
import MettapediaFourColor.WheelRepairInput11
import MettapediaFourColor.WheelRepairInput12
import MettapediaFourColor.WheelRepairInput13
import MettapediaFourColor.WheelRepairInput14
import MettapediaFourColor.WheelRepairInput15
import MettapediaFourColor.WheelRepairInput16

/-! # Complete thirteen-port repair from checked finite data

Every supplied repair record and every proper input trace is checked. This
proves the finite D3009 repair contract. Ambient embedding, initial colouring
and strict reduction are separate geometric consumers.
-/
namespace FourColor.WheelRepairCertificate

set_option maxRecDepth 65536

set_option maxHeartbeats 4000000 in
-- Join the bounded shard proofs without rechecking their finite records.
theorem recordBlocks (b : Fin 2076) (j : Fin 32) :
    checkAt (32 * b.val + j.val) = true := by
  have hb := b.isLt
  by_cases h0 : b.val < 128
  · simpa only [Nat.zero_add] using recordShard0 ⟨b.val, h0⟩ j
  by_cases h1 : b.val < 256
  · have h := recordShard1 ⟨b.val - 128, by omega⟩ j
    have he : 128 + (b.val - 128) = b.val := by omega
    simpa only [he] using h
  by_cases h2 : b.val < 384
  · have h := recordShard2 ⟨b.val - 256, by omega⟩ j
    have he : 256 + (b.val - 256) = b.val := by omega
    simpa only [he] using h
  by_cases h3 : b.val < 512
  · have h := recordShard3 ⟨b.val - 384, by omega⟩ j
    have he : 384 + (b.val - 384) = b.val := by omega
    simpa only [he] using h
  by_cases h4 : b.val < 640
  · have h := recordShard4 ⟨b.val - 512, by omega⟩ j
    have he : 512 + (b.val - 512) = b.val := by omega
    simpa only [he] using h
  by_cases h5 : b.val < 768
  · have h := recordShard5 ⟨b.val - 640, by omega⟩ j
    have he : 640 + (b.val - 640) = b.val := by omega
    simpa only [he] using h
  by_cases h6 : b.val < 896
  · have h := recordShard6 ⟨b.val - 768, by omega⟩ j
    have he : 768 + (b.val - 768) = b.val := by omega
    simpa only [he] using h
  by_cases h7 : b.val < 1024
  · have h := recordShard7 ⟨b.val - 896, by omega⟩ j
    have he : 896 + (b.val - 896) = b.val := by omega
    simpa only [he] using h
  by_cases h8 : b.val < 1152
  · have h := recordShard8 ⟨b.val - 1024, by omega⟩ j
    have he : 1024 + (b.val - 1024) = b.val := by omega
    simpa only [he] using h
  by_cases h9 : b.val < 1280
  · have h := recordShard9 ⟨b.val - 1152, by omega⟩ j
    have he : 1152 + (b.val - 1152) = b.val := by omega
    simpa only [he] using h
  by_cases h10 : b.val < 1408
  · have h := recordShard10 ⟨b.val - 1280, by omega⟩ j
    have he : 1280 + (b.val - 1280) = b.val := by omega
    simpa only [he] using h
  by_cases h11 : b.val < 1536
  · have h := recordShard11 ⟨b.val - 1408, by omega⟩ j
    have he : 1408 + (b.val - 1408) = b.val := by omega
    simpa only [he] using h
  by_cases h12 : b.val < 1664
  · have h := recordShard12 ⟨b.val - 1536, by omega⟩ j
    have he : 1536 + (b.val - 1536) = b.val := by omega
    simpa only [he] using h
  by_cases h13 : b.val < 1792
  · have h := recordShard13 ⟨b.val - 1664, by omega⟩ j
    have he : 1664 + (b.val - 1664) = b.val := by omega
    simpa only [he] using h
  by_cases h14 : b.val < 1920
  · have h := recordShard14 ⟨b.val - 1792, by omega⟩ j
    have he : 1792 + (b.val - 1792) = b.val := by omega
    simpa only [he] using h
  by_cases h15 : b.val < 2048
  · have h := recordShard15 ⟨b.val - 1920, by omega⟩ j
    have he : 1920 + (b.val - 1920) = b.val := by omega
    simpa only [he] using h
  have h := recordShard16 ⟨b.val - 2048, by omega⟩ j
  have he : 2048 + (b.val - 2048) = b.val := by omega
  simpa only [he] using h

set_option maxHeartbeats 4000000 in
-- Join the bounded shard proofs without rechecking their finite records.
theorem inputBlocks (b : Fin 2076) (j : Fin 256) :
    inputAt (256 * b.val + j.val) = true := by
  have hb := b.isLt
  by_cases h0 : b.val < 128
  · simpa only [Nat.zero_add] using inputShard0 ⟨b.val, h0⟩ j
  by_cases h1 : b.val < 256
  · have h := inputShard1 ⟨b.val - 128, by omega⟩ j
    have he : 128 + (b.val - 128) = b.val := by omega
    simpa only [he] using h
  by_cases h2 : b.val < 384
  · have h := inputShard2 ⟨b.val - 256, by omega⟩ j
    have he : 256 + (b.val - 256) = b.val := by omega
    simpa only [he] using h
  by_cases h3 : b.val < 512
  · have h := inputShard3 ⟨b.val - 384, by omega⟩ j
    have he : 384 + (b.val - 384) = b.val := by omega
    simpa only [he] using h
  by_cases h4 : b.val < 640
  · have h := inputShard4 ⟨b.val - 512, by omega⟩ j
    have he : 512 + (b.val - 512) = b.val := by omega
    simpa only [he] using h
  by_cases h5 : b.val < 768
  · have h := inputShard5 ⟨b.val - 640, by omega⟩ j
    have he : 640 + (b.val - 640) = b.val := by omega
    simpa only [he] using h
  by_cases h6 : b.val < 896
  · have h := inputShard6 ⟨b.val - 768, by omega⟩ j
    have he : 768 + (b.val - 768) = b.val := by omega
    simpa only [he] using h
  by_cases h7 : b.val < 1024
  · have h := inputShard7 ⟨b.val - 896, by omega⟩ j
    have he : 896 + (b.val - 896) = b.val := by omega
    simpa only [he] using h
  by_cases h8 : b.val < 1152
  · have h := inputShard8 ⟨b.val - 1024, by omega⟩ j
    have he : 1024 + (b.val - 1024) = b.val := by omega
    simpa only [he] using h
  by_cases h9 : b.val < 1280
  · have h := inputShard9 ⟨b.val - 1152, by omega⟩ j
    have he : 1152 + (b.val - 1152) = b.val := by omega
    simpa only [he] using h
  by_cases h10 : b.val < 1408
  · have h := inputShard10 ⟨b.val - 1280, by omega⟩ j
    have he : 1280 + (b.val - 1280) = b.val := by omega
    simpa only [he] using h
  by_cases h11 : b.val < 1536
  · have h := inputShard11 ⟨b.val - 1408, by omega⟩ j
    have he : 1408 + (b.val - 1408) = b.val := by omega
    simpa only [he] using h
  by_cases h12 : b.val < 1664
  · have h := inputShard12 ⟨b.val - 1536, by omega⟩ j
    have he : 1536 + (b.val - 1536) = b.val := by omega
    simpa only [he] using h
  by_cases h13 : b.val < 1792
  · have h := inputShard13 ⟨b.val - 1664, by omega⟩ j
    have he : 1664 + (b.val - 1664) = b.val := by omega
    simpa only [he] using h
  by_cases h14 : b.val < 1920
  · have h := inputShard14 ⟨b.val - 1792, by omega⟩ j
    have he : 1792 + (b.val - 1792) = b.val := by omega
    simpa only [he] using h
  by_cases h15 : b.val < 2048
  · have h := inputShard15 ⟨b.val - 1920, by omega⟩ j
    have he : 1920 + (b.val - 1920) = b.val := by omega
    simpa only [he] using h
  have h := inputShard16 ⟨b.val - 2048, by omega⟩ j
  have he : 2048 + (b.val - 2048) = b.val := by omega
  simpa only [he] using h

set_option maxHeartbeats 4000000 in
-- Convert the bounded blocks into complete state coverage.
theorem checked (i : State) : check i = true := by
  have hi : i.val < 66430 := i.isLt
  have h := recordBlocks ⟨i.val / 32, by omega⟩ ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩
  change checkAt (32 * (i.val / 32) + i.val % 32) = true at h
  have hn : 32 * (i.val / 32) + i.val % 32 = i.val := by omega
  simpa only [hn, checkAt, Nat.mod_eq_of_lt i.isLt] using h

set_option maxHeartbeats 4000000 in
-- Convert the bounded blocks into complete input coverage.
theorem coverage (i : Fin (3 ^ 12)) : inputCheck i = true := by
  have hi : i.val < 531441 := i.isLt
  have h := inputBlocks ⟨i.val / 256, by omega⟩ ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩
  change inputAt (256 * (i.val / 256) + i.val % 256) = true at h
  have hn : 256 * (i.val / 256) + i.val % 256 = i.val := by omega
  simpa only [hn, inputAt, Nat.mod_eq_of_lt i.isLt] using h

/-- Every proper thirteen-port trace admits a compatible D3009 repair. -/
theorem repair : KempeBoundarySplit.Repairs Supports 13 := repair_of_checks checked coverage

end FourColor.WheelRepairCertificate
