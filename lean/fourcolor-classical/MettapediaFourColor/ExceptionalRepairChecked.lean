import MettapediaFourColor.ExceptionalRepairCertificate

/-! # Kernel checks of every D1774 repair record and every proper input

Generated finite obligations are split into bounded blocks. Each declaration
uses kernel reduction. The final theorems quantify over all certificate
records and all eleven-port proper zero-sum traces.
-/

namespace FourColor.ExceptionalRepairCertificate

set_option maxRecDepth 65536

def checkAt (n : ℕ) : Bool := check ⟨n % ExceptionalRepairData.count, Nat.mod_lt _ (by decide)⟩
def inputAt (n : ℕ) : Bool := inputCheck (n % (3 ^ 10))

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock0 : ∀ j : Fin 64, checkAt (0 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock1 : ∀ j : Fin 64, checkAt (64 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock2 : ∀ j : Fin 64, checkAt (128 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock3 : ∀ j : Fin 64, checkAt (192 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock4 : ∀ j : Fin 64, checkAt (256 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock5 : ∀ j : Fin 64, checkAt (320 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock6 : ∀ j : Fin 64, checkAt (384 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock7 : ∀ j : Fin 64, checkAt (448 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock8 : ∀ j : Fin 64, checkAt (512 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock9 : ∀ j : Fin 64, checkAt (576 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock10 : ∀ j : Fin 64, checkAt (640 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock11 : ∀ j : Fin 64, checkAt (704 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock12 : ∀ j : Fin 64, checkAt (768 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock13 : ∀ j : Fin 64, checkAt (832 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock14 : ∀ j : Fin 64, checkAt (896 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock15 : ∀ j : Fin 64, checkAt (960 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock16 : ∀ j : Fin 64, checkAt (1024 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock17 : ∀ j : Fin 64, checkAt (1088 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock18 : ∀ j : Fin 64, checkAt (1152 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock19 : ∀ j : Fin 64, checkAt (1216 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock20 : ∀ j : Fin 64, checkAt (1280 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock21 : ∀ j : Fin 64, checkAt (1344 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock22 : ∀ j : Fin 64, checkAt (1408 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock23 : ∀ j : Fin 64, checkAt (1472 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock24 : ∀ j : Fin 64, checkAt (1536 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock25 : ∀ j : Fin 64, checkAt (1600 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock26 : ∀ j : Fin 64, checkAt (1664 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock27 : ∀ j : Fin 64, checkAt (1728 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock28 : ∀ j : Fin 64, checkAt (1792 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock29 : ∀ j : Fin 64, checkAt (1856 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock30 : ∀ j : Fin 64, checkAt (1920 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock31 : ∀ j : Fin 64, checkAt (1984 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock32 : ∀ j : Fin 64, checkAt (2048 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock33 : ∀ j : Fin 64, checkAt (2112 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock34 : ∀ j : Fin 64, checkAt (2176 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock35 : ∀ j : Fin 64, checkAt (2240 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock36 : ∀ j : Fin 64, checkAt (2304 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock37 : ∀ j : Fin 64, checkAt (2368 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock38 : ∀ j : Fin 64, checkAt (2432 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock39 : ∀ j : Fin 64, checkAt (2496 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock40 : ∀ j : Fin 64, checkAt (2560 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock41 : ∀ j : Fin 64, checkAt (2624 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock42 : ∀ j : Fin 64, checkAt (2688 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock43 : ∀ j : Fin 64, checkAt (2752 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock44 : ∀ j : Fin 64, checkAt (2816 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock45 : ∀ j : Fin 64, checkAt (2880 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock46 : ∀ j : Fin 64, checkAt (2944 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock47 : ∀ j : Fin 64, checkAt (3008 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock48 : ∀ j : Fin 64, checkAt (3072 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock49 : ∀ j : Fin 64, checkAt (3136 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock50 : ∀ j : Fin 64, checkAt (3200 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock51 : ∀ j : Fin 64, checkAt (3264 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock52 : ∀ j : Fin 64, checkAt (3328 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock53 : ∀ j : Fin 64, checkAt (3392 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock54 : ∀ j : Fin 64, checkAt (3456 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock55 : ∀ j : Fin 64, checkAt (3520 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock56 : ∀ j : Fin 64, checkAt (3584 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock57 : ∀ j : Fin 64, checkAt (3648 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock58 : ∀ j : Fin 64, checkAt (3712 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock59 : ∀ j : Fin 64, checkAt (3776 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock60 : ∀ j : Fin 64, checkAt (3840 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock61 : ∀ j : Fin 64, checkAt (3904 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock62 : ∀ j : Fin 64, checkAt (3968 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock63 : ∀ j : Fin 64, checkAt (4032 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock64 : ∀ j : Fin 64, checkAt (4096 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock65 : ∀ j : Fin 64, checkAt (4160 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock66 : ∀ j : Fin 64, checkAt (4224 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock67 : ∀ j : Fin 64, checkAt (4288 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock68 : ∀ j : Fin 64, checkAt (4352 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock69 : ∀ j : Fin 64, checkAt (4416 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock70 : ∀ j : Fin 64, checkAt (4480 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock71 : ∀ j : Fin 64, checkAt (4544 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock72 : ∀ j : Fin 64, checkAt (4608 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock73 : ∀ j : Fin 64, checkAt (4672 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock74 : ∀ j : Fin 64, checkAt (4736 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock75 : ∀ j : Fin 64, checkAt (4800 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock76 : ∀ j : Fin 64, checkAt (4864 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock77 : ∀ j : Fin 64, checkAt (4928 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock78 : ∀ j : Fin 64, checkAt (4992 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock79 : ∀ j : Fin 64, checkAt (5056 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock80 : ∀ j : Fin 64, checkAt (5120 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock81 : ∀ j : Fin 64, checkAt (5184 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock82 : ∀ j : Fin 64, checkAt (5248 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock83 : ∀ j : Fin 64, checkAt (5312 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock84 : ∀ j : Fin 64, checkAt (5376 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock85 : ∀ j : Fin 64, checkAt (5440 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock86 : ∀ j : Fin 64, checkAt (5504 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock87 : ∀ j : Fin 64, checkAt (5568 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock88 : ∀ j : Fin 64, checkAt (5632 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock89 : ∀ j : Fin 64, checkAt (5696 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock90 : ∀ j : Fin 64, checkAt (5760 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock91 : ∀ j : Fin 64, checkAt (5824 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock92 : ∀ j : Fin 64, checkAt (5888 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock93 : ∀ j : Fin 64, checkAt (5952 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock94 : ∀ j : Fin 64, checkAt (6016 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock95 : ∀ j : Fin 64, checkAt (6080 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock96 : ∀ j : Fin 64, checkAt (6144 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock97 : ∀ j : Fin 64, checkAt (6208 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock98 : ∀ j : Fin 64, checkAt (6272 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock99 : ∀ j : Fin 64, checkAt (6336 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock100 : ∀ j : Fin 64, checkAt (6400 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock101 : ∀ j : Fin 64, checkAt (6464 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock102 : ∀ j : Fin 64, checkAt (6528 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock103 : ∀ j : Fin 64, checkAt (6592 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock104 : ∀ j : Fin 64, checkAt (6656 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock105 : ∀ j : Fin 64, checkAt (6720 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock106 : ∀ j : Fin 64, checkAt (6784 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock107 : ∀ j : Fin 64, checkAt (6848 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock108 : ∀ j : Fin 64, checkAt (6912 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock109 : ∀ j : Fin 64, checkAt (6976 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock110 : ∀ j : Fin 64, checkAt (7040 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock111 : ∀ j : Fin 64, checkAt (7104 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock112 : ∀ j : Fin 64, checkAt (7168 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock113 : ∀ j : Fin 64, checkAt (7232 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock114 : ∀ j : Fin 64, checkAt (7296 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem recordBlock115 : ∀ j : Fin 64, checkAt (7360 + j.val) = true := by decide +kernel

theorem recordBlocks (b : Fin 116) (j : Fin 64) :
    checkAt (64 * b.val + j.val) = true := by
  fin_cases b
  · exact recordBlock0 j
  · exact recordBlock1 j
  · exact recordBlock2 j
  · exact recordBlock3 j
  · exact recordBlock4 j
  · exact recordBlock5 j
  · exact recordBlock6 j
  · exact recordBlock7 j
  · exact recordBlock8 j
  · exact recordBlock9 j
  · exact recordBlock10 j
  · exact recordBlock11 j
  · exact recordBlock12 j
  · exact recordBlock13 j
  · exact recordBlock14 j
  · exact recordBlock15 j
  · exact recordBlock16 j
  · exact recordBlock17 j
  · exact recordBlock18 j
  · exact recordBlock19 j
  · exact recordBlock20 j
  · exact recordBlock21 j
  · exact recordBlock22 j
  · exact recordBlock23 j
  · exact recordBlock24 j
  · exact recordBlock25 j
  · exact recordBlock26 j
  · exact recordBlock27 j
  · exact recordBlock28 j
  · exact recordBlock29 j
  · exact recordBlock30 j
  · exact recordBlock31 j
  · exact recordBlock32 j
  · exact recordBlock33 j
  · exact recordBlock34 j
  · exact recordBlock35 j
  · exact recordBlock36 j
  · exact recordBlock37 j
  · exact recordBlock38 j
  · exact recordBlock39 j
  · exact recordBlock40 j
  · exact recordBlock41 j
  · exact recordBlock42 j
  · exact recordBlock43 j
  · exact recordBlock44 j
  · exact recordBlock45 j
  · exact recordBlock46 j
  · exact recordBlock47 j
  · exact recordBlock48 j
  · exact recordBlock49 j
  · exact recordBlock50 j
  · exact recordBlock51 j
  · exact recordBlock52 j
  · exact recordBlock53 j
  · exact recordBlock54 j
  · exact recordBlock55 j
  · exact recordBlock56 j
  · exact recordBlock57 j
  · exact recordBlock58 j
  · exact recordBlock59 j
  · exact recordBlock60 j
  · exact recordBlock61 j
  · exact recordBlock62 j
  · exact recordBlock63 j
  · exact recordBlock64 j
  · exact recordBlock65 j
  · exact recordBlock66 j
  · exact recordBlock67 j
  · exact recordBlock68 j
  · exact recordBlock69 j
  · exact recordBlock70 j
  · exact recordBlock71 j
  · exact recordBlock72 j
  · exact recordBlock73 j
  · exact recordBlock74 j
  · exact recordBlock75 j
  · exact recordBlock76 j
  · exact recordBlock77 j
  · exact recordBlock78 j
  · exact recordBlock79 j
  · exact recordBlock80 j
  · exact recordBlock81 j
  · exact recordBlock82 j
  · exact recordBlock83 j
  · exact recordBlock84 j
  · exact recordBlock85 j
  · exact recordBlock86 j
  · exact recordBlock87 j
  · exact recordBlock88 j
  · exact recordBlock89 j
  · exact recordBlock90 j
  · exact recordBlock91 j
  · exact recordBlock92 j
  · exact recordBlock93 j
  · exact recordBlock94 j
  · exact recordBlock95 j
  · exact recordBlock96 j
  · exact recordBlock97 j
  · exact recordBlock98 j
  · exact recordBlock99 j
  · exact recordBlock100 j
  · exact recordBlock101 j
  · exact recordBlock102 j
  · exact recordBlock103 j
  · exact recordBlock104 j
  · exact recordBlock105 j
  · exact recordBlock106 j
  · exact recordBlock107 j
  · exact recordBlock108 j
  · exact recordBlock109 j
  · exact recordBlock110 j
  · exact recordBlock111 j
  · exact recordBlock112 j
  · exact recordBlock113 j
  · exact recordBlock114 j
  · exact recordBlock115 j

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock0 : ∀ j : Fin 256, inputAt (0 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock1 : ∀ j : Fin 256, inputAt (256 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock2 : ∀ j : Fin 256, inputAt (512 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock3 : ∀ j : Fin 256, inputAt (768 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock4 : ∀ j : Fin 256, inputAt (1024 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock5 : ∀ j : Fin 256, inputAt (1280 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock6 : ∀ j : Fin 256, inputAt (1536 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock7 : ∀ j : Fin 256, inputAt (1792 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock8 : ∀ j : Fin 256, inputAt (2048 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock9 : ∀ j : Fin 256, inputAt (2304 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock10 : ∀ j : Fin 256, inputAt (2560 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock11 : ∀ j : Fin 256, inputAt (2816 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock12 : ∀ j : Fin 256, inputAt (3072 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock13 : ∀ j : Fin 256, inputAt (3328 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock14 : ∀ j : Fin 256, inputAt (3584 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock15 : ∀ j : Fin 256, inputAt (3840 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock16 : ∀ j : Fin 256, inputAt (4096 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock17 : ∀ j : Fin 256, inputAt (4352 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock18 : ∀ j : Fin 256, inputAt (4608 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock19 : ∀ j : Fin 256, inputAt (4864 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock20 : ∀ j : Fin 256, inputAt (5120 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock21 : ∀ j : Fin 256, inputAt (5376 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock22 : ∀ j : Fin 256, inputAt (5632 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock23 : ∀ j : Fin 256, inputAt (5888 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock24 : ∀ j : Fin 256, inputAt (6144 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock25 : ∀ j : Fin 256, inputAt (6400 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock26 : ∀ j : Fin 256, inputAt (6656 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock27 : ∀ j : Fin 256, inputAt (6912 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock28 : ∀ j : Fin 256, inputAt (7168 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock29 : ∀ j : Fin 256, inputAt (7424 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock30 : ∀ j : Fin 256, inputAt (7680 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock31 : ∀ j : Fin 256, inputAt (7936 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock32 : ∀ j : Fin 256, inputAt (8192 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock33 : ∀ j : Fin 256, inputAt (8448 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock34 : ∀ j : Fin 256, inputAt (8704 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock35 : ∀ j : Fin 256, inputAt (8960 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock36 : ∀ j : Fin 256, inputAt (9216 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock37 : ∀ j : Fin 256, inputAt (9472 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock38 : ∀ j : Fin 256, inputAt (9728 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock39 : ∀ j : Fin 256, inputAt (9984 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock40 : ∀ j : Fin 256, inputAt (10240 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock41 : ∀ j : Fin 256, inputAt (10496 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock42 : ∀ j : Fin 256, inputAt (10752 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock43 : ∀ j : Fin 256, inputAt (11008 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock44 : ∀ j : Fin 256, inputAt (11264 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock45 : ∀ j : Fin 256, inputAt (11520 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock46 : ∀ j : Fin 256, inputAt (11776 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock47 : ∀ j : Fin 256, inputAt (12032 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock48 : ∀ j : Fin 256, inputAt (12288 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock49 : ∀ j : Fin 256, inputAt (12544 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock50 : ∀ j : Fin 256, inputAt (12800 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock51 : ∀ j : Fin 256, inputAt (13056 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock52 : ∀ j : Fin 256, inputAt (13312 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock53 : ∀ j : Fin 256, inputAt (13568 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock54 : ∀ j : Fin 256, inputAt (13824 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock55 : ∀ j : Fin 256, inputAt (14080 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock56 : ∀ j : Fin 256, inputAt (14336 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock57 : ∀ j : Fin 256, inputAt (14592 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock58 : ∀ j : Fin 256, inputAt (14848 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock59 : ∀ j : Fin 256, inputAt (15104 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock60 : ∀ j : Fin 256, inputAt (15360 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock61 : ∀ j : Fin 256, inputAt (15616 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock62 : ∀ j : Fin 256, inputAt (15872 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock63 : ∀ j : Fin 256, inputAt (16128 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock64 : ∀ j : Fin 256, inputAt (16384 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock65 : ∀ j : Fin 256, inputAt (16640 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock66 : ∀ j : Fin 256, inputAt (16896 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock67 : ∀ j : Fin 256, inputAt (17152 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock68 : ∀ j : Fin 256, inputAt (17408 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock69 : ∀ j : Fin 256, inputAt (17664 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock70 : ∀ j : Fin 256, inputAt (17920 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock71 : ∀ j : Fin 256, inputAt (18176 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock72 : ∀ j : Fin 256, inputAt (18432 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock73 : ∀ j : Fin 256, inputAt (18688 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock74 : ∀ j : Fin 256, inputAt (18944 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock75 : ∀ j : Fin 256, inputAt (19200 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock76 : ∀ j : Fin 256, inputAt (19456 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock77 : ∀ j : Fin 256, inputAt (19712 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock78 : ∀ j : Fin 256, inputAt (19968 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock79 : ∀ j : Fin 256, inputAt (20224 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock80 : ∀ j : Fin 256, inputAt (20480 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock81 : ∀ j : Fin 256, inputAt (20736 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock82 : ∀ j : Fin 256, inputAt (20992 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock83 : ∀ j : Fin 256, inputAt (21248 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock84 : ∀ j : Fin 256, inputAt (21504 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock85 : ∀ j : Fin 256, inputAt (21760 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock86 : ∀ j : Fin 256, inputAt (22016 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock87 : ∀ j : Fin 256, inputAt (22272 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock88 : ∀ j : Fin 256, inputAt (22528 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock89 : ∀ j : Fin 256, inputAt (22784 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock90 : ∀ j : Fin 256, inputAt (23040 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock91 : ∀ j : Fin 256, inputAt (23296 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock92 : ∀ j : Fin 256, inputAt (23552 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock93 : ∀ j : Fin 256, inputAt (23808 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock94 : ∀ j : Fin 256, inputAt (24064 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock95 : ∀ j : Fin 256, inputAt (24320 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock96 : ∀ j : Fin 256, inputAt (24576 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock97 : ∀ j : Fin 256, inputAt (24832 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock98 : ∀ j : Fin 256, inputAt (25088 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock99 : ∀ j : Fin 256, inputAt (25344 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock100 : ∀ j : Fin 256, inputAt (25600 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock101 : ∀ j : Fin 256, inputAt (25856 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock102 : ∀ j : Fin 256, inputAt (26112 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock103 : ∀ j : Fin 256, inputAt (26368 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock104 : ∀ j : Fin 256, inputAt (26624 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock105 : ∀ j : Fin 256, inputAt (26880 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock106 : ∀ j : Fin 256, inputAt (27136 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock107 : ∀ j : Fin 256, inputAt (27392 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock108 : ∀ j : Fin 256, inputAt (27648 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock109 : ∀ j : Fin 256, inputAt (27904 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock110 : ∀ j : Fin 256, inputAt (28160 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock111 : ∀ j : Fin 256, inputAt (28416 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock112 : ∀ j : Fin 256, inputAt (28672 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock113 : ∀ j : Fin 256, inputAt (28928 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock114 : ∀ j : Fin 256, inputAt (29184 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock115 : ∀ j : Fin 256, inputAt (29440 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock116 : ∀ j : Fin 256, inputAt (29696 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock117 : ∀ j : Fin 256, inputAt (29952 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock118 : ∀ j : Fin 256, inputAt (30208 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock119 : ∀ j : Fin 256, inputAt (30464 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock120 : ∀ j : Fin 256, inputAt (30720 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock121 : ∀ j : Fin 256, inputAt (30976 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock122 : ∀ j : Fin 256, inputAt (31232 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock123 : ∀ j : Fin 256, inputAt (31488 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock124 : ∀ j : Fin 256, inputAt (31744 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock125 : ∀ j : Fin 256, inputAt (32000 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock126 : ∀ j : Fin 256, inputAt (32256 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock127 : ∀ j : Fin 256, inputAt (32512 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock128 : ∀ j : Fin 256, inputAt (32768 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock129 : ∀ j : Fin 256, inputAt (33024 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock130 : ∀ j : Fin 256, inputAt (33280 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock131 : ∀ j : Fin 256, inputAt (33536 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock132 : ∀ j : Fin 256, inputAt (33792 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock133 : ∀ j : Fin 256, inputAt (34048 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock134 : ∀ j : Fin 256, inputAt (34304 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock135 : ∀ j : Fin 256, inputAt (34560 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock136 : ∀ j : Fin 256, inputAt (34816 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock137 : ∀ j : Fin 256, inputAt (35072 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock138 : ∀ j : Fin 256, inputAt (35328 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock139 : ∀ j : Fin 256, inputAt (35584 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock140 : ∀ j : Fin 256, inputAt (35840 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock141 : ∀ j : Fin 256, inputAt (36096 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock142 : ∀ j : Fin 256, inputAt (36352 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock143 : ∀ j : Fin 256, inputAt (36608 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock144 : ∀ j : Fin 256, inputAt (36864 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock145 : ∀ j : Fin 256, inputAt (37120 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock146 : ∀ j : Fin 256, inputAt (37376 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock147 : ∀ j : Fin 256, inputAt (37632 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock148 : ∀ j : Fin 256, inputAt (37888 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock149 : ∀ j : Fin 256, inputAt (38144 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock150 : ∀ j : Fin 256, inputAt (38400 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock151 : ∀ j : Fin 256, inputAt (38656 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock152 : ∀ j : Fin 256, inputAt (38912 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock153 : ∀ j : Fin 256, inputAt (39168 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock154 : ∀ j : Fin 256, inputAt (39424 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock155 : ∀ j : Fin 256, inputAt (39680 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock156 : ∀ j : Fin 256, inputAt (39936 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock157 : ∀ j : Fin 256, inputAt (40192 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock158 : ∀ j : Fin 256, inputAt (40448 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock159 : ∀ j : Fin 256, inputAt (40704 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock160 : ∀ j : Fin 256, inputAt (40960 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock161 : ∀ j : Fin 256, inputAt (41216 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock162 : ∀ j : Fin 256, inputAt (41472 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock163 : ∀ j : Fin 256, inputAt (41728 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock164 : ∀ j : Fin 256, inputAt (41984 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock165 : ∀ j : Fin 256, inputAt (42240 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock166 : ∀ j : Fin 256, inputAt (42496 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock167 : ∀ j : Fin 256, inputAt (42752 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock168 : ∀ j : Fin 256, inputAt (43008 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock169 : ∀ j : Fin 256, inputAt (43264 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock170 : ∀ j : Fin 256, inputAt (43520 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock171 : ∀ j : Fin 256, inputAt (43776 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock172 : ∀ j : Fin 256, inputAt (44032 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock173 : ∀ j : Fin 256, inputAt (44288 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock174 : ∀ j : Fin 256, inputAt (44544 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock175 : ∀ j : Fin 256, inputAt (44800 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock176 : ∀ j : Fin 256, inputAt (45056 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock177 : ∀ j : Fin 256, inputAt (45312 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock178 : ∀ j : Fin 256, inputAt (45568 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock179 : ∀ j : Fin 256, inputAt (45824 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock180 : ∀ j : Fin 256, inputAt (46080 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock181 : ∀ j : Fin 256, inputAt (46336 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock182 : ∀ j : Fin 256, inputAt (46592 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock183 : ∀ j : Fin 256, inputAt (46848 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock184 : ∀ j : Fin 256, inputAt (47104 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock185 : ∀ j : Fin 256, inputAt (47360 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock186 : ∀ j : Fin 256, inputAt (47616 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock187 : ∀ j : Fin 256, inputAt (47872 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock188 : ∀ j : Fin 256, inputAt (48128 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock189 : ∀ j : Fin 256, inputAt (48384 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock190 : ∀ j : Fin 256, inputAt (48640 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock191 : ∀ j : Fin 256, inputAt (48896 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock192 : ∀ j : Fin 256, inputAt (49152 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock193 : ∀ j : Fin 256, inputAt (49408 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock194 : ∀ j : Fin 256, inputAt (49664 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock195 : ∀ j : Fin 256, inputAt (49920 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock196 : ∀ j : Fin 256, inputAt (50176 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock197 : ∀ j : Fin 256, inputAt (50432 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock198 : ∀ j : Fin 256, inputAt (50688 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock199 : ∀ j : Fin 256, inputAt (50944 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock200 : ∀ j : Fin 256, inputAt (51200 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock201 : ∀ j : Fin 256, inputAt (51456 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock202 : ∀ j : Fin 256, inputAt (51712 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock203 : ∀ j : Fin 256, inputAt (51968 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock204 : ∀ j : Fin 256, inputAt (52224 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock205 : ∀ j : Fin 256, inputAt (52480 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock206 : ∀ j : Fin 256, inputAt (52736 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock207 : ∀ j : Fin 256, inputAt (52992 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock208 : ∀ j : Fin 256, inputAt (53248 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock209 : ∀ j : Fin 256, inputAt (53504 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock210 : ∀ j : Fin 256, inputAt (53760 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock211 : ∀ j : Fin 256, inputAt (54016 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock212 : ∀ j : Fin 256, inputAt (54272 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock213 : ∀ j : Fin 256, inputAt (54528 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock214 : ∀ j : Fin 256, inputAt (54784 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock215 : ∀ j : Fin 256, inputAt (55040 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock216 : ∀ j : Fin 256, inputAt (55296 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock217 : ∀ j : Fin 256, inputAt (55552 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock218 : ∀ j : Fin 256, inputAt (55808 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock219 : ∀ j : Fin 256, inputAt (56064 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock220 : ∀ j : Fin 256, inputAt (56320 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock221 : ∀ j : Fin 256, inputAt (56576 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock222 : ∀ j : Fin 256, inputAt (56832 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock223 : ∀ j : Fin 256, inputAt (57088 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock224 : ∀ j : Fin 256, inputAt (57344 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock225 : ∀ j : Fin 256, inputAt (57600 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock226 : ∀ j : Fin 256, inputAt (57856 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock227 : ∀ j : Fin 256, inputAt (58112 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock228 : ∀ j : Fin 256, inputAt (58368 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock229 : ∀ j : Fin 256, inputAt (58624 + j.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- Validate a bounded block of the finite certificate.
theorem inputBlock230 : ∀ j : Fin 256, inputAt (58880 + j.val) = true := by decide +kernel

theorem inputBlocks (b : Fin 231) (j : Fin 256) :
    inputAt (256 * b.val + j.val) = true := by
  fin_cases b
  · exact inputBlock0 j
  · exact inputBlock1 j
  · exact inputBlock2 j
  · exact inputBlock3 j
  · exact inputBlock4 j
  · exact inputBlock5 j
  · exact inputBlock6 j
  · exact inputBlock7 j
  · exact inputBlock8 j
  · exact inputBlock9 j
  · exact inputBlock10 j
  · exact inputBlock11 j
  · exact inputBlock12 j
  · exact inputBlock13 j
  · exact inputBlock14 j
  · exact inputBlock15 j
  · exact inputBlock16 j
  · exact inputBlock17 j
  · exact inputBlock18 j
  · exact inputBlock19 j
  · exact inputBlock20 j
  · exact inputBlock21 j
  · exact inputBlock22 j
  · exact inputBlock23 j
  · exact inputBlock24 j
  · exact inputBlock25 j
  · exact inputBlock26 j
  · exact inputBlock27 j
  · exact inputBlock28 j
  · exact inputBlock29 j
  · exact inputBlock30 j
  · exact inputBlock31 j
  · exact inputBlock32 j
  · exact inputBlock33 j
  · exact inputBlock34 j
  · exact inputBlock35 j
  · exact inputBlock36 j
  · exact inputBlock37 j
  · exact inputBlock38 j
  · exact inputBlock39 j
  · exact inputBlock40 j
  · exact inputBlock41 j
  · exact inputBlock42 j
  · exact inputBlock43 j
  · exact inputBlock44 j
  · exact inputBlock45 j
  · exact inputBlock46 j
  · exact inputBlock47 j
  · exact inputBlock48 j
  · exact inputBlock49 j
  · exact inputBlock50 j
  · exact inputBlock51 j
  · exact inputBlock52 j
  · exact inputBlock53 j
  · exact inputBlock54 j
  · exact inputBlock55 j
  · exact inputBlock56 j
  · exact inputBlock57 j
  · exact inputBlock58 j
  · exact inputBlock59 j
  · exact inputBlock60 j
  · exact inputBlock61 j
  · exact inputBlock62 j
  · exact inputBlock63 j
  · exact inputBlock64 j
  · exact inputBlock65 j
  · exact inputBlock66 j
  · exact inputBlock67 j
  · exact inputBlock68 j
  · exact inputBlock69 j
  · exact inputBlock70 j
  · exact inputBlock71 j
  · exact inputBlock72 j
  · exact inputBlock73 j
  · exact inputBlock74 j
  · exact inputBlock75 j
  · exact inputBlock76 j
  · exact inputBlock77 j
  · exact inputBlock78 j
  · exact inputBlock79 j
  · exact inputBlock80 j
  · exact inputBlock81 j
  · exact inputBlock82 j
  · exact inputBlock83 j
  · exact inputBlock84 j
  · exact inputBlock85 j
  · exact inputBlock86 j
  · exact inputBlock87 j
  · exact inputBlock88 j
  · exact inputBlock89 j
  · exact inputBlock90 j
  · exact inputBlock91 j
  · exact inputBlock92 j
  · exact inputBlock93 j
  · exact inputBlock94 j
  · exact inputBlock95 j
  · exact inputBlock96 j
  · exact inputBlock97 j
  · exact inputBlock98 j
  · exact inputBlock99 j
  · exact inputBlock100 j
  · exact inputBlock101 j
  · exact inputBlock102 j
  · exact inputBlock103 j
  · exact inputBlock104 j
  · exact inputBlock105 j
  · exact inputBlock106 j
  · exact inputBlock107 j
  · exact inputBlock108 j
  · exact inputBlock109 j
  · exact inputBlock110 j
  · exact inputBlock111 j
  · exact inputBlock112 j
  · exact inputBlock113 j
  · exact inputBlock114 j
  · exact inputBlock115 j
  · exact inputBlock116 j
  · exact inputBlock117 j
  · exact inputBlock118 j
  · exact inputBlock119 j
  · exact inputBlock120 j
  · exact inputBlock121 j
  · exact inputBlock122 j
  · exact inputBlock123 j
  · exact inputBlock124 j
  · exact inputBlock125 j
  · exact inputBlock126 j
  · exact inputBlock127 j
  · exact inputBlock128 j
  · exact inputBlock129 j
  · exact inputBlock130 j
  · exact inputBlock131 j
  · exact inputBlock132 j
  · exact inputBlock133 j
  · exact inputBlock134 j
  · exact inputBlock135 j
  · exact inputBlock136 j
  · exact inputBlock137 j
  · exact inputBlock138 j
  · exact inputBlock139 j
  · exact inputBlock140 j
  · exact inputBlock141 j
  · exact inputBlock142 j
  · exact inputBlock143 j
  · exact inputBlock144 j
  · exact inputBlock145 j
  · exact inputBlock146 j
  · exact inputBlock147 j
  · exact inputBlock148 j
  · exact inputBlock149 j
  · exact inputBlock150 j
  · exact inputBlock151 j
  · exact inputBlock152 j
  · exact inputBlock153 j
  · exact inputBlock154 j
  · exact inputBlock155 j
  · exact inputBlock156 j
  · exact inputBlock157 j
  · exact inputBlock158 j
  · exact inputBlock159 j
  · exact inputBlock160 j
  · exact inputBlock161 j
  · exact inputBlock162 j
  · exact inputBlock163 j
  · exact inputBlock164 j
  · exact inputBlock165 j
  · exact inputBlock166 j
  · exact inputBlock167 j
  · exact inputBlock168 j
  · exact inputBlock169 j
  · exact inputBlock170 j
  · exact inputBlock171 j
  · exact inputBlock172 j
  · exact inputBlock173 j
  · exact inputBlock174 j
  · exact inputBlock175 j
  · exact inputBlock176 j
  · exact inputBlock177 j
  · exact inputBlock178 j
  · exact inputBlock179 j
  · exact inputBlock180 j
  · exact inputBlock181 j
  · exact inputBlock182 j
  · exact inputBlock183 j
  · exact inputBlock184 j
  · exact inputBlock185 j
  · exact inputBlock186 j
  · exact inputBlock187 j
  · exact inputBlock188 j
  · exact inputBlock189 j
  · exact inputBlock190 j
  · exact inputBlock191 j
  · exact inputBlock192 j
  · exact inputBlock193 j
  · exact inputBlock194 j
  · exact inputBlock195 j
  · exact inputBlock196 j
  · exact inputBlock197 j
  · exact inputBlock198 j
  · exact inputBlock199 j
  · exact inputBlock200 j
  · exact inputBlock201 j
  · exact inputBlock202 j
  · exact inputBlock203 j
  · exact inputBlock204 j
  · exact inputBlock205 j
  · exact inputBlock206 j
  · exact inputBlock207 j
  · exact inputBlock208 j
  · exact inputBlock209 j
  · exact inputBlock210 j
  · exact inputBlock211 j
  · exact inputBlock212 j
  · exact inputBlock213 j
  · exact inputBlock214 j
  · exact inputBlock215 j
  · exact inputBlock216 j
  · exact inputBlock217 j
  · exact inputBlock218 j
  · exact inputBlock219 j
  · exact inputBlock220 j
  · exact inputBlock221 j
  · exact inputBlock222 j
  · exact inputBlock223 j
  · exact inputBlock224 j
  · exact inputBlock225 j
  · exact inputBlock226 j
  · exact inputBlock227 j
  · exact inputBlock228 j
  · exact inputBlock229 j
  · exact inputBlock230 j

theorem checked (i : State) : check i = true := by
  have hi : i.val < 7381 := i.isLt
  have h := recordBlocks ⟨i.val / 64, by omega⟩ ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  change checkAt (64 * (i.val / 64) + i.val % 64) = true at h
  have hn : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [hn, checkAt, Nat.mod_eq_of_lt i.isLt] using h

theorem coverage (i : Fin (3 ^ 10)) : inputCheck i = true := by
  have hi : i.val < 59049 := i.isLt
  have h := inputBlocks ⟨i.val / 256, by omega⟩ ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩
  change inputAt (256 * (i.val / 256) + i.val % 256) = true at h
  have hn : 256 * (i.val / 256) + i.val % 256 = i.val := by omega
  simpa only [hn, inputAt, Nat.mod_eq_of_lt i.isLt] using h

/-- Every proper eleven-port zero-sum trace admits compatible D1774 repair. -/
theorem repair : KempeBoundarySplit.Repairs Supports 11 := repair_of_checks checked coverage

end FourColor.ExceptionalRepairCertificate
