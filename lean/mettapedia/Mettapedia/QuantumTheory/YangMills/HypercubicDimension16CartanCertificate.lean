import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock0
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock1
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock2
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock3
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock4
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock5
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock6
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock7
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock8
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock9
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock10
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock11
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock12
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock13
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock14
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock15
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock16
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock17
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock18
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock19
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock20
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock21
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock22
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock23
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock24
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock25
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock26
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock27
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock28
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock29
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock30
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock31
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock32
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock33
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock34
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock35
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock36
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock37
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock38

/-! # Kernel-checked dimension-sixteen Cartan census certificate -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open V14HypercubicQuarticCensus

theorem canonicalOcticData_valid :
    ∀ index : Fin 1287,
      octicCode (canonicalOctic index) = canonicalOcticCode index ∧
        (canonicalOcticCertificate index).Valid (canonicalOctic index) ∧
        canonicalOcticIndexOfCode (canonicalOcticCode index) = index := by
  intro index
  by_cases h0 : index.1 < 33
  · let entry : Fin 33 := ⟨index.1 - 0, by omega⟩
    have valid := canonicalOcticData_valid_block0 entry
    have hindex : octicWitnessBlockIndex 0 (by decide) entry = index := by
      apply Fin.ext
      change 0 + (index.1 - 0) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h1 : index.1 < 66
  · let entry : Fin 33 := ⟨index.1 - 33, by omega⟩
    have valid := canonicalOcticData_valid_block1 entry
    have hindex : octicWitnessBlockIndex 33 (by decide) entry = index := by
      apply Fin.ext
      change 33 + (index.1 - 33) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h2 : index.1 < 99
  · let entry : Fin 33 := ⟨index.1 - 66, by omega⟩
    have valid := canonicalOcticData_valid_block2 entry
    have hindex : octicWitnessBlockIndex 66 (by decide) entry = index := by
      apply Fin.ext
      change 66 + (index.1 - 66) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h3 : index.1 < 132
  · let entry : Fin 33 := ⟨index.1 - 99, by omega⟩
    have valid := canonicalOcticData_valid_block3 entry
    have hindex : octicWitnessBlockIndex 99 (by decide) entry = index := by
      apply Fin.ext
      change 99 + (index.1 - 99) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h4 : index.1 < 165
  · let entry : Fin 33 := ⟨index.1 - 132, by omega⟩
    have valid := canonicalOcticData_valid_block4 entry
    have hindex : octicWitnessBlockIndex 132 (by decide) entry = index := by
      apply Fin.ext
      change 132 + (index.1 - 132) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h5 : index.1 < 198
  · let entry : Fin 33 := ⟨index.1 - 165, by omega⟩
    have valid := canonicalOcticData_valid_block5 entry
    have hindex : octicWitnessBlockIndex 165 (by decide) entry = index := by
      apply Fin.ext
      change 165 + (index.1 - 165) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h6 : index.1 < 231
  · let entry : Fin 33 := ⟨index.1 - 198, by omega⟩
    have valid := canonicalOcticData_valid_block6 entry
    have hindex : octicWitnessBlockIndex 198 (by decide) entry = index := by
      apply Fin.ext
      change 198 + (index.1 - 198) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h7 : index.1 < 264
  · let entry : Fin 33 := ⟨index.1 - 231, by omega⟩
    have valid := canonicalOcticData_valid_block7 entry
    have hindex : octicWitnessBlockIndex 231 (by decide) entry = index := by
      apply Fin.ext
      change 231 + (index.1 - 231) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h8 : index.1 < 297
  · let entry : Fin 33 := ⟨index.1 - 264, by omega⟩
    have valid := canonicalOcticData_valid_block8 entry
    have hindex : octicWitnessBlockIndex 264 (by decide) entry = index := by
      apply Fin.ext
      change 264 + (index.1 - 264) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h9 : index.1 < 330
  · let entry : Fin 33 := ⟨index.1 - 297, by omega⟩
    have valid := canonicalOcticData_valid_block9 entry
    have hindex : octicWitnessBlockIndex 297 (by decide) entry = index := by
      apply Fin.ext
      change 297 + (index.1 - 297) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h10 : index.1 < 363
  · let entry : Fin 33 := ⟨index.1 - 330, by omega⟩
    have valid := canonicalOcticData_valid_block10 entry
    have hindex : octicWitnessBlockIndex 330 (by decide) entry = index := by
      apply Fin.ext
      change 330 + (index.1 - 330) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h11 : index.1 < 396
  · let entry : Fin 33 := ⟨index.1 - 363, by omega⟩
    have valid := canonicalOcticData_valid_block11 entry
    have hindex : octicWitnessBlockIndex 363 (by decide) entry = index := by
      apply Fin.ext
      change 363 + (index.1 - 363) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h12 : index.1 < 429
  · let entry : Fin 33 := ⟨index.1 - 396, by omega⟩
    have valid := canonicalOcticData_valid_block12 entry
    have hindex : octicWitnessBlockIndex 396 (by decide) entry = index := by
      apply Fin.ext
      change 396 + (index.1 - 396) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h13 : index.1 < 462
  · let entry : Fin 33 := ⟨index.1 - 429, by omega⟩
    have valid := canonicalOcticData_valid_block13 entry
    have hindex : octicWitnessBlockIndex 429 (by decide) entry = index := by
      apply Fin.ext
      change 429 + (index.1 - 429) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h14 : index.1 < 495
  · let entry : Fin 33 := ⟨index.1 - 462, by omega⟩
    have valid := canonicalOcticData_valid_block14 entry
    have hindex : octicWitnessBlockIndex 462 (by decide) entry = index := by
      apply Fin.ext
      change 462 + (index.1 - 462) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h15 : index.1 < 528
  · let entry : Fin 33 := ⟨index.1 - 495, by omega⟩
    have valid := canonicalOcticData_valid_block15 entry
    have hindex : octicWitnessBlockIndex 495 (by decide) entry = index := by
      apply Fin.ext
      change 495 + (index.1 - 495) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h16 : index.1 < 561
  · let entry : Fin 33 := ⟨index.1 - 528, by omega⟩
    have valid := canonicalOcticData_valid_block16 entry
    have hindex : octicWitnessBlockIndex 528 (by decide) entry = index := by
      apply Fin.ext
      change 528 + (index.1 - 528) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h17 : index.1 < 594
  · let entry : Fin 33 := ⟨index.1 - 561, by omega⟩
    have valid := canonicalOcticData_valid_block17 entry
    have hindex : octicWitnessBlockIndex 561 (by decide) entry = index := by
      apply Fin.ext
      change 561 + (index.1 - 561) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h18 : index.1 < 627
  · let entry : Fin 33 := ⟨index.1 - 594, by omega⟩
    have valid := canonicalOcticData_valid_block18 entry
    have hindex : octicWitnessBlockIndex 594 (by decide) entry = index := by
      apply Fin.ext
      change 594 + (index.1 - 594) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h19 : index.1 < 660
  · let entry : Fin 33 := ⟨index.1 - 627, by omega⟩
    have valid := canonicalOcticData_valid_block19 entry
    have hindex : octicWitnessBlockIndex 627 (by decide) entry = index := by
      apply Fin.ext
      change 627 + (index.1 - 627) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h20 : index.1 < 693
  · let entry : Fin 33 := ⟨index.1 - 660, by omega⟩
    have valid := canonicalOcticData_valid_block20 entry
    have hindex : octicWitnessBlockIndex 660 (by decide) entry = index := by
      apply Fin.ext
      change 660 + (index.1 - 660) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h21 : index.1 < 726
  · let entry : Fin 33 := ⟨index.1 - 693, by omega⟩
    have valid := canonicalOcticData_valid_block21 entry
    have hindex : octicWitnessBlockIndex 693 (by decide) entry = index := by
      apply Fin.ext
      change 693 + (index.1 - 693) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h22 : index.1 < 759
  · let entry : Fin 33 := ⟨index.1 - 726, by omega⟩
    have valid := canonicalOcticData_valid_block22 entry
    have hindex : octicWitnessBlockIndex 726 (by decide) entry = index := by
      apply Fin.ext
      change 726 + (index.1 - 726) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h23 : index.1 < 792
  · let entry : Fin 33 := ⟨index.1 - 759, by omega⟩
    have valid := canonicalOcticData_valid_block23 entry
    have hindex : octicWitnessBlockIndex 759 (by decide) entry = index := by
      apply Fin.ext
      change 759 + (index.1 - 759) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h24 : index.1 < 825
  · let entry : Fin 33 := ⟨index.1 - 792, by omega⟩
    have valid := canonicalOcticData_valid_block24 entry
    have hindex : octicWitnessBlockIndex 792 (by decide) entry = index := by
      apply Fin.ext
      change 792 + (index.1 - 792) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h25 : index.1 < 858
  · let entry : Fin 33 := ⟨index.1 - 825, by omega⟩
    have valid := canonicalOcticData_valid_block25 entry
    have hindex : octicWitnessBlockIndex 825 (by decide) entry = index := by
      apply Fin.ext
      change 825 + (index.1 - 825) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h26 : index.1 < 891
  · let entry : Fin 33 := ⟨index.1 - 858, by omega⟩
    have valid := canonicalOcticData_valid_block26 entry
    have hindex : octicWitnessBlockIndex 858 (by decide) entry = index := by
      apply Fin.ext
      change 858 + (index.1 - 858) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h27 : index.1 < 924
  · let entry : Fin 33 := ⟨index.1 - 891, by omega⟩
    have valid := canonicalOcticData_valid_block27 entry
    have hindex : octicWitnessBlockIndex 891 (by decide) entry = index := by
      apply Fin.ext
      change 891 + (index.1 - 891) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h28 : index.1 < 957
  · let entry : Fin 33 := ⟨index.1 - 924, by omega⟩
    have valid := canonicalOcticData_valid_block28 entry
    have hindex : octicWitnessBlockIndex 924 (by decide) entry = index := by
      apply Fin.ext
      change 924 + (index.1 - 924) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h29 : index.1 < 990
  · let entry : Fin 33 := ⟨index.1 - 957, by omega⟩
    have valid := canonicalOcticData_valid_block29 entry
    have hindex : octicWitnessBlockIndex 957 (by decide) entry = index := by
      apply Fin.ext
      change 957 + (index.1 - 957) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h30 : index.1 < 1023
  · let entry : Fin 33 := ⟨index.1 - 990, by omega⟩
    have valid := canonicalOcticData_valid_block30 entry
    have hindex : octicWitnessBlockIndex 990 (by decide) entry = index := by
      apply Fin.ext
      change 990 + (index.1 - 990) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h31 : index.1 < 1056
  · let entry : Fin 33 := ⟨index.1 - 1023, by omega⟩
    have valid := canonicalOcticData_valid_block31 entry
    have hindex : octicWitnessBlockIndex 1023 (by decide) entry = index := by
      apply Fin.ext
      change 1023 + (index.1 - 1023) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h32 : index.1 < 1089
  · let entry : Fin 33 := ⟨index.1 - 1056, by omega⟩
    have valid := canonicalOcticData_valid_block32 entry
    have hindex : octicWitnessBlockIndex 1056 (by decide) entry = index := by
      apply Fin.ext
      change 1056 + (index.1 - 1056) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h33 : index.1 < 1122
  · let entry : Fin 33 := ⟨index.1 - 1089, by omega⟩
    have valid := canonicalOcticData_valid_block33 entry
    have hindex : octicWitnessBlockIndex 1089 (by decide) entry = index := by
      apply Fin.ext
      change 1089 + (index.1 - 1089) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h34 : index.1 < 1155
  · let entry : Fin 33 := ⟨index.1 - 1122, by omega⟩
    have valid := canonicalOcticData_valid_block34 entry
    have hindex : octicWitnessBlockIndex 1122 (by decide) entry = index := by
      apply Fin.ext
      change 1122 + (index.1 - 1122) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h35 : index.1 < 1188
  · let entry : Fin 33 := ⟨index.1 - 1155, by omega⟩
    have valid := canonicalOcticData_valid_block35 entry
    have hindex : octicWitnessBlockIndex 1155 (by decide) entry = index := by
      apply Fin.ext
      change 1155 + (index.1 - 1155) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h36 : index.1 < 1221
  · let entry : Fin 33 := ⟨index.1 - 1188, by omega⟩
    have valid := canonicalOcticData_valid_block36 entry
    have hindex : octicWitnessBlockIndex 1188 (by decide) entry = index := by
      apply Fin.ext
      change 1188 + (index.1 - 1188) = index.1
      omega
    simpa only [hindex] using valid
  by_cases h37 : index.1 < 1254
  · let entry : Fin 33 := ⟨index.1 - 1221, by omega⟩
    have valid := canonicalOcticData_valid_block37 entry
    have hindex : octicWitnessBlockIndex 1221 (by decide) entry = index := by
      apply Fin.ext
      change 1221 + (index.1 - 1221) = index.1
      omega
    simpa only [hindex] using valid
  · let entry : Fin 33 := ⟨index.1 - 1254, by omega⟩
    have valid := canonicalOcticData_valid_block38 entry
    have hindex : octicWitnessBlockIndex 1254 (by decide) entry = index := by
      apply Fin.ext
      change 1254 + (index.1 - 1254) = index.1
      omega
    simpa only [hindex] using valid

theorem canonicalOcticCode_injective :
    Function.Injective canonicalOcticCode := by
  exact Function.LeftInverse.injective
    (fun index => (canonicalOcticData_valid index).2.2)

theorem canonicalOctic_injective : Function.Injective canonicalOctic := by
  intro left right heq
  apply canonicalOcticCode_injective
  rw [← (canonicalOcticData_valid left).1,
    ← (canonicalOcticData_valid right).1, heq]

theorem canonicalOctic_bijective : Function.Bijective canonicalOctic := by
  apply (Fintype.bijective_iff_injective_and_card canonicalOctic).2
  exact ⟨canonicalOctic_injective, by simp [card_octicMonomial]⟩

theorem canonicalOctic_surjective : Function.Surjective canonicalOctic :=
  canonicalOctic_bijective.2

theorem octic_signedOrbit_classification (monomial : OcticMonomial) :
    (∃ coordinate : Fin 17,
      InSignedOcticOrbit (octicRepresentative coordinate) monomial) ∨
      HasNegativeOcticStabilizer monomial := by
  obtain ⟨index, rfl⟩ := canonicalOctic_surjective monomial
  have valid := (canonicalOcticData_valid index).2.1
  generalize certificateEquation :
    canonicalOcticCertificate index = certificate at valid
  cases certificate with
  | orbit coordinate permutation reflectionMask =>
      left
      exact ⟨coordinate, decodeHypercubic permutation reflectionMask, valid⟩
  | killed permutation reflectionMask =>
      right
      exact ⟨decodeHypercubic permutation reflectionMask, valid⟩

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
