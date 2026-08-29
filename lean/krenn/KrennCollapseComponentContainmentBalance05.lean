import KrennCollapseComponentContainmentDataDefs

/-!
Kernel-checked signed-chain balances 65 through 77.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentData

open Krenn.LatticeCombinationReflection

set_option maxHeartbeats 1000000 in
theorem chainBalance065 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 65).target)
      (chainCertificate 65).steps := by
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
theorem chainBalance066 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 66).target)
      (chainCertificate 66).steps := by
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
theorem chainBalance067 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 67).target)
      (chainCertificate 67).steps := by
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
theorem chainBalance068 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 68).target)
      (chainCertificate 68).steps := by
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
theorem chainBalance069 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 69).target)
      (chainCertificate 69).steps := by
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
theorem chainBalance070 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 70).target)
      (chainCertificate 70).steps := by
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
theorem chainBalance071 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 71).target)
      (chainCertificate 71).steps := by
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
theorem chainBalance072 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 72).target)
      (chainCertificate 72).steps := by
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
theorem chainBalance073 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 73).target)
      (chainCertificate 73).steps := by
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
theorem chainBalance074 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 74).target)
      (chainCertificate 74).steps := by
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
theorem chainBalance075 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 75).target)
      (chainCertificate 75).steps := by
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
theorem chainBalance076 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 76).target)
      (chainCertificate 76).steps := by
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
theorem chainBalance077 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 77).target)
      (chainCertificate 77).steps := by
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
