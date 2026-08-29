import KrennCollapseComponentContainmentDataDefs

/-!
Kernel-checked signed-chain balances 52 through 64.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentData

open Krenn.LatticeCombinationReflection

set_option maxHeartbeats 1000000 in
theorem chainBalance052 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 52).target)
      (chainCertificate 52).steps := by
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
theorem chainBalance053 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 53).target)
      (chainCertificate 53).steps := by
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
theorem chainBalance054 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 54).target)
      (chainCertificate 54).steps := by
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
theorem chainBalance055 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 55).target)
      (chainCertificate 55).steps := by
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
theorem chainBalance056 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 56).target)
      (chainCertificate 56).steps := by
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
theorem chainBalance057 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 57).target)
      (chainCertificate 57).steps := by
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
theorem chainBalance058 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 58).target)
      (chainCertificate 58).steps := by
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
theorem chainBalance059 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 59).target)
      (chainCertificate 59).steps := by
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
theorem chainBalance060 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 60).target)
      (chainCertificate 60).steps := by
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
theorem chainBalance061 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 61).target)
      (chainCertificate 61).steps := by
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
theorem chainBalance062 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 62).target)
      (chainCertificate 62).steps := by
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
theorem chainBalance063 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 63).target)
      (chainCertificate 63).steps := by
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
theorem chainBalance064 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 64).target)
      (chainCertificate 64).steps := by
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
