import KrennCollapseComponentContainmentDataDefs

/-!
Kernel-checked signed-chain balances 0 through 12.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentData

open Krenn.LatticeCombinationReflection

set_option maxHeartbeats 1000000 in
theorem chainBalance000 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 0).target)
      (chainCertificate 0).steps := by
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
theorem chainBalance001 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 1).target)
      (chainCertificate 1).steps := by
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
theorem chainBalance002 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 2).target)
      (chainCertificate 2).steps := by
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
theorem chainBalance003 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 3).target)
      (chainCertificate 3).steps := by
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
theorem chainBalance004 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 4).target)
      (chainCertificate 4).steps := by
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
theorem chainBalance005 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 5).target)
      (chainCertificate 5).steps := by
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
theorem chainBalance006 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 6).target)
      (chainCertificate 6).steps := by
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
theorem chainBalance007 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 7).target)
      (chainCertificate 7).steps := by
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
theorem chainBalance008 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 8).target)
      (chainCertificate 8).steps := by
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
theorem chainBalance009 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 9).target)
      (chainCertificate 9).steps := by
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
theorem chainBalance010 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 10).target)
      (chainCertificate 10).steps := by
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
theorem chainBalance011 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 11).target)
      (chainCertificate 11).steps := by
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
theorem chainBalance012 :
    ExponentBalance relation
      (generatorBinomial (chainCertificate 12).target)
      (chainCertificate 12).steps := by
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
