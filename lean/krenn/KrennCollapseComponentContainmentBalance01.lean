import KrennCollapseComponentContainmentDataDefs

/-!
Kernel-checked signed-chain balances 13 through 25.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentData

open Krenn.LatticeCombinationReflection

set_option maxHeartbeats 1000000 in
theorem chainBalance013 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 13).target)
      (chainCertificate 13).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance014 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 14).target)
      (chainCertificate 14).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance015 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 15).target)
      (chainCertificate 15).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance016 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 16).target)
      (chainCertificate 16).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance017 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 17).target)
      (chainCertificate 17).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance018 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 18).target)
      (chainCertificate 18).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance019 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 19).target)
      (chainCertificate 19).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance020 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 20).target)
      (chainCertificate 20).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance021 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 21).target)
      (chainCertificate 21).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance022 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 22).target)
      (chainCertificate 22).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance023 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 23).target)
      (chainCertificate 23).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance024 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 24).target)
      (chainCertificate 24).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

set_option maxHeartbeats 1000000 in
theorem chainBalance025 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 25).target)
      (chainCertificate 25).steps := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [leftAuxiliaryExponent,
      rightAuxiliaryExponent, relation, relationLeftSupport,
      relationRightSupport, generatorBinomial, generatorPositive,
      generatorNegative, generatorPositiveSupport,
      generatorNegativeSupport, chainCertificate] <;>
    decide

end Krenn.CollapseComponentContainmentData
