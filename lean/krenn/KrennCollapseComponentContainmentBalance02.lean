import KrennCollapseComponentContainmentDataDefs

/-!
Kernel-checked signed-chain balances 26 through 38.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentData

open Krenn.LatticeCombinationReflection

set_option maxHeartbeats 1000000 in
theorem chainBalance026 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 26).target)
      (chainCertificate 26).steps := by
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
theorem chainBalance027 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 27).target)
      (chainCertificate 27).steps := by
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
theorem chainBalance028 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 28).target)
      (chainCertificate 28).steps := by
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
theorem chainBalance029 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 29).target)
      (chainCertificate 29).steps := by
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
theorem chainBalance030 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 30).target)
      (chainCertificate 30).steps := by
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
theorem chainBalance031 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 31).target)
      (chainCertificate 31).steps := by
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
theorem chainBalance032 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 32).target)
      (chainCertificate 32).steps := by
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
theorem chainBalance033 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 33).target)
      (chainCertificate 33).steps := by
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
theorem chainBalance034 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 34).target)
      (chainCertificate 34).steps := by
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
theorem chainBalance035 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 35).target)
      (chainCertificate 35).steps := by
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
theorem chainBalance036 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 36).target)
      (chainCertificate 36).steps := by
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
theorem chainBalance037 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 37).target)
      (chainCertificate 37).steps := by
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
theorem chainBalance038 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 38).target)
      (chainCertificate 38).steps := by
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
