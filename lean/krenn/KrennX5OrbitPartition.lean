import Mathlib

/-!
Exact finite partition for the 336 normalized representatives of the
`X = {01,02,03,04,15}` support orbit.

This module checks the finite bookkeeping only: 317 historical
multilinear closures and 19 strictly reflected residual closures are
distinct and exhaust the audited representative list.  The semantic
symmetry/normalization action remains a separate theorem.
-/

namespace Krenn.X5OrbitPartition

def historicalLogSHA256 : String := "60d36e85cb31e3a6ed493837dd36554f182498d0794d84d6108dc1874c80be0c"
def residualManifestSHA256 : String := "a3660e27b91639fb5b6b4756097aaa886d5d9b4989da6b0f41974c6508a51163"

def exactRepresentativeIndices : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
   21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 42, 43, 44, 45,
   46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
   65, 66, 67, 68, 69, 70, 71, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 126, 127, 128, 129,
   130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 168,
   169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 210, 211, 212, 213,
   214, 215, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270,
   271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
   286, 287, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312,
   313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 342, 343, 344, 345,
   346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 384,
   385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 426, 427, 428, 429,
   430, 431, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528,
   529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 558, 559, 560, 561,
   562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 600,
   601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 642, 643, 644, 645,
   646, 647, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786,
   787, 788, 789, 790, 791, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825,
   826, 827, 858, 859, 860, 861, 862, 863, 1032, 1033, 1034, 1035, 1036, 1037,
   1038, 1039, 1040, 1041, 1042, 1043, 1074, 1075, 1076, 1077, 1078, 1079,
   1290, 1291, 1292, 1293, 1294, 1295]

def historicalClosedIndices : List Nat :=
  [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
   22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 42, 43, 44, 45, 46,
   47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
   66, 67, 68, 69, 70, 71, 85, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 99,
   100, 101, 103, 104, 105, 106, 107, 126, 127, 128, 129, 130, 132, 133, 134,
   135, 136, 137, 138, 139, 140, 141, 142, 143, 168, 169, 171, 172, 173, 174,
   175, 176, 177, 178, 179, 210, 211, 212, 213, 214, 215, 258, 259, 260, 261,
   262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276,
   277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 300, 301, 302, 303,
   305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 317, 318, 319, 320,
   321, 322, 323, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353,
   354, 355, 356, 357, 358, 359, 384, 386, 387, 389, 390, 391, 392, 393, 394,
   395, 426, 427, 428, 430, 431, 517, 518, 519, 520, 521, 522, 523, 524, 525,
   526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 558,
   559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573,
   574, 575, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 643,
   644, 645, 646, 647, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784,
   785, 786, 787, 788, 789, 790, 791, 816, 818, 819, 820, 821, 822, 823, 824,
   825, 826, 827, 858, 859, 860, 862, 1032, 1034, 1035, 1036, 1037, 1038,
   1039, 1040, 1041, 1042, 1043, 1074, 1075, 1076, 1077, 1078, 1079, 1290,
   1291, 1292, 1294, 1295]

def residualIndices : List Nat :=
  [5, 84, 86, 98, 102, 131, 170, 304, 316, 385, 388, 429, 516, 642, 817, 861,
   863, 1033, 1293]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem exactRepresentativeIndices_length :
    exactRepresentativeIndices.length = 336 := by decide

theorem historicalClosedIndices_length :
    historicalClosedIndices.length = 317 := by decide

theorem residualIndices_length : residualIndices.length = 19 := by decide

theorem exactRepresentativeIndices_nodup :
    exactRepresentativeIndices.Nodup := by decide

theorem historicalClosedIndices_nodup : historicalClosedIndices.Nodup := by decide

theorem residualIndices_nodup : residualIndices.Nodup := by decide

theorem closed_residual_disjoint :
    Disjoint historicalClosedIndices.toFinset residualIndices.toFinset := by decide

theorem representative_partition :
    exactRepresentativeIndices.toFinset =
      historicalClosedIndices.toFinset ∪ residualIndices.toFinset := by decide

#print axioms Krenn.X5OrbitPartition.representative_partition

end Krenn.X5OrbitPartition
