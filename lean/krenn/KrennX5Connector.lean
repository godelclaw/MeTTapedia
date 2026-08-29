import Mathlib

/-! # X5 connector: the 36-element symmetry action and the 7776 → 336 normalisation

Support orbit `01,02,03,04,15`: each of the five support edges carries one of the
six off-diagonal colour channels, giving `6^5 = 7776` cases.  The symmetry group
is the setwise stabiliser of the support in `S_6` (order 6) times `S_3` acting on
colours (order 6), so `|G| = 36`.  The tables below are exact witnesses; the group
laws and the normalisation theorem are checked by the kernel. -/

set_option maxRecDepth 100000

namespace KrennX5

/-- A case assigns one of six off-diagonal colour channels to each support edge. -/
abbrev Case := Fin 5 → Fin 6

/-- Source support-edge index for each target index, per group element. -/
def posOf : Fin 36 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,3,4],![0,1,2,3,4],![0,1,2,3,4],![0,1,2,3,4],![0,1,2,3,4],![0,1,3,2,4],![0,1,3,2,4],![0,1,3,2,4],![0,1,3,2,4],![0,1,3,2,4],![0,1,3,2,4],![0,2,1,3,4],![0,2,1,3,4],![0,2,1,3,4],![0,2,1,3,4],![0,2,1,3,4],![0,2,1,3,4],![0,3,1,2,4],![0,3,1,2,4],![0,3,1,2,4],![0,3,1,2,4],![0,3,1,2,4],![0,3,1,2,4],![0,2,3,1,4],![0,2,3,1,4],![0,2,3,1,4],![0,2,3,1,4],![0,2,3,1,4],![0,2,3,1,4],![0,3,2,1,4],![0,3,2,1,4],![0,3,2,1,4],![0,3,2,1,4],![0,3,2,1,4],![0,3,2,1,4]]

/-- Channel relabelling at each target index, per group element. -/
def valOf : Fin 36 → Fin 5 → Fin 6 → Fin 6 := ![![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5]],![![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3]],![![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4]],![![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1]],![![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2]],![![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0]],![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5]],![![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3]],![![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4]],![![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1]],![![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2]],![![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0]],![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5]],![![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3]],![![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4]],![![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1]],![![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2]],![![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0]],![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5]],![![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3]],![![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4]],![![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1]],![![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2]],![![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0]],![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5]],![![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3]],![![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4]],![![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1]],![![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2]],![![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0]],![![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5],![0,1,2,3,4,5]],![![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3],![1,0,4,5,2,3]],![![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4],![2,3,0,1,5,4]],![![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1],![3,2,5,4,0,1]],![![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2],![4,5,1,0,3,2]],![![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0],![5,4,3,2,1,0]]]

/-- Group multiplication witness: `mulOf g h` composes `g` after `h`. -/
def mulOf : Fin 36 → Fin 36 → Fin 36 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35],![1,0,4,5,2,3,7,6,10,11,8,9,13,12,16,17,14,15,19,18,22,23,20,21,25,24,28,29,26,27,31,30,34,35,32,33],![2,3,0,1,5,4,8,9,6,7,11,10,14,15,12,13,17,16,20,21,18,19,23,22,26,27,24,25,29,28,32,33,30,31,35,34],![3,2,5,4,0,1,9,8,11,10,6,7,15,14,17,16,12,13,21,20,23,22,18,19,27,26,29,28,24,25,33,32,35,34,30,31],![4,5,1,0,3,2,10,11,7,6,9,8,16,17,13,12,15,14,22,23,19,18,21,20,28,29,25,24,27,26,34,35,31,30,33,32],![5,4,3,2,1,0,11,10,9,8,7,6,17,16,15,14,13,12,23,22,21,20,19,18,29,28,27,26,25,24,35,34,33,32,31,30],![6,7,8,9,10,11,0,1,2,3,4,5,24,25,26,27,28,29,30,31,32,33,34,35,12,13,14,15,16,17,18,19,20,21,22,23],![7,6,10,11,8,9,1,0,4,5,2,3,25,24,28,29,26,27,31,30,34,35,32,33,13,12,16,17,14,15,19,18,22,23,20,21],![8,9,6,7,11,10,2,3,0,1,5,4,26,27,24,25,29,28,32,33,30,31,35,34,14,15,12,13,17,16,20,21,18,19,23,22],![9,8,11,10,6,7,3,2,5,4,0,1,27,26,29,28,24,25,33,32,35,34,30,31,15,14,17,16,12,13,21,20,23,22,18,19],![10,11,7,6,9,8,4,5,1,0,3,2,28,29,25,24,27,26,34,35,31,30,33,32,16,17,13,12,15,14,22,23,19,18,21,20],![11,10,9,8,7,6,5,4,3,2,1,0,29,28,27,26,25,24,35,34,33,32,31,30,17,16,15,14,13,12,23,22,21,20,19,18],![12,13,14,15,16,17,18,19,20,21,22,23,0,1,2,3,4,5,6,7,8,9,10,11,30,31,32,33,34,35,24,25,26,27,28,29],![13,12,16,17,14,15,19,18,22,23,20,21,1,0,4,5,2,3,7,6,10,11,8,9,31,30,34,35,32,33,25,24,28,29,26,27],![14,15,12,13,17,16,20,21,18,19,23,22,2,3,0,1,5,4,8,9,6,7,11,10,32,33,30,31,35,34,26,27,24,25,29,28],![15,14,17,16,12,13,21,20,23,22,18,19,3,2,5,4,0,1,9,8,11,10,6,7,33,32,35,34,30,31,27,26,29,28,24,25],![16,17,13,12,15,14,22,23,19,18,21,20,4,5,1,0,3,2,10,11,7,6,9,8,34,35,31,30,33,32,28,29,25,24,27,26],![17,16,15,14,13,12,23,22,21,20,19,18,5,4,3,2,1,0,11,10,9,8,7,6,35,34,33,32,31,30,29,28,27,26,25,24],![18,19,20,21,22,23,12,13,14,15,16,17,30,31,32,33,34,35,24,25,26,27,28,29,0,1,2,3,4,5,6,7,8,9,10,11],![19,18,22,23,20,21,13,12,16,17,14,15,31,30,34,35,32,33,25,24,28,29,26,27,1,0,4,5,2,3,7,6,10,11,8,9],![20,21,18,19,23,22,14,15,12,13,17,16,32,33,30,31,35,34,26,27,24,25,29,28,2,3,0,1,5,4,8,9,6,7,11,10],![21,20,23,22,18,19,15,14,17,16,12,13,33,32,35,34,30,31,27,26,29,28,24,25,3,2,5,4,0,1,9,8,11,10,6,7],![22,23,19,18,21,20,16,17,13,12,15,14,34,35,31,30,33,32,28,29,25,24,27,26,4,5,1,0,3,2,10,11,7,6,9,8],![23,22,21,20,19,18,17,16,15,14,13,12,35,34,33,32,31,30,29,28,27,26,25,24,5,4,3,2,1,0,11,10,9,8,7,6],![24,25,26,27,28,29,30,31,32,33,34,35,6,7,8,9,10,11,0,1,2,3,4,5,18,19,20,21,22,23,12,13,14,15,16,17],![25,24,28,29,26,27,31,30,34,35,32,33,7,6,10,11,8,9,1,0,4,5,2,3,19,18,22,23,20,21,13,12,16,17,14,15],![26,27,24,25,29,28,32,33,30,31,35,34,8,9,6,7,11,10,2,3,0,1,5,4,20,21,18,19,23,22,14,15,12,13,17,16],![27,26,29,28,24,25,33,32,35,34,30,31,9,8,11,10,6,7,3,2,5,4,0,1,21,20,23,22,18,19,15,14,17,16,12,13],![28,29,25,24,27,26,34,35,31,30,33,32,10,11,7,6,9,8,4,5,1,0,3,2,22,23,19,18,21,20,16,17,13,12,15,14],![29,28,27,26,25,24,35,34,33,32,31,30,11,10,9,8,7,6,5,4,3,2,1,0,23,22,21,20,19,18,17,16,15,14,13,12],![30,31,32,33,34,35,24,25,26,27,28,29,18,19,20,21,22,23,12,13,14,15,16,17,6,7,8,9,10,11,0,1,2,3,4,5],![31,30,34,35,32,33,25,24,28,29,26,27,19,18,22,23,20,21,13,12,16,17,14,15,7,6,10,11,8,9,1,0,4,5,2,3],![32,33,30,31,35,34,26,27,24,25,29,28,20,21,18,19,23,22,14,15,12,13,17,16,8,9,6,7,11,10,2,3,0,1,5,4],![33,32,35,34,30,31,27,26,29,28,24,25,21,20,23,22,18,19,15,14,17,16,12,13,9,8,11,10,6,7,3,2,5,4,0,1],![34,35,31,30,33,32,28,29,25,24,27,26,22,23,19,18,21,20,16,17,13,12,15,14,10,11,7,6,9,8,4,5,1,0,3,2],![35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]]

/-- Inverse witness. -/
def invOf : Fin 36 → Fin 36 := ![0,1,2,4,3,5,6,7,8,10,9,11,12,13,14,16,15,17,24,25,26,28,27,29,18,19,20,22,21,23,30,31,32,34,33,35]

/-- The action of a group element on a case. -/
def act (g : Fin 36) (c : Case) : Case := fun k => valOf g k (c (posOf g k))

set_option maxHeartbeats 2000000 in
private theorem pos_mul_0 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 0 h) k = posOf h (posOf 0 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_1 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 1 h) k = posOf h (posOf 1 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_2 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 2 h) k = posOf h (posOf 2 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_3 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 3 h) k = posOf h (posOf 3 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_4 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 4 h) k = posOf h (posOf 4 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_5 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 5 h) k = posOf h (posOf 5 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_6 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 6 h) k = posOf h (posOf 6 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_7 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 7 h) k = posOf h (posOf 7 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_8 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 8 h) k = posOf h (posOf 8 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_9 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 9 h) k = posOf h (posOf 9 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_10 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 10 h) k = posOf h (posOf 10 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_11 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 11 h) k = posOf h (posOf 11 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_12 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 12 h) k = posOf h (posOf 12 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_13 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 13 h) k = posOf h (posOf 13 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_14 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 14 h) k = posOf h (posOf 14 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_15 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 15 h) k = posOf h (posOf 15 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_16 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 16 h) k = posOf h (posOf 16 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_17 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 17 h) k = posOf h (posOf 17 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_18 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 18 h) k = posOf h (posOf 18 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_19 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 19 h) k = posOf h (posOf 19 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_20 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 20 h) k = posOf h (posOf 20 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_21 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 21 h) k = posOf h (posOf 21 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_22 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 22 h) k = posOf h (posOf 22 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_23 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 23 h) k = posOf h (posOf 23 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_24 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 24 h) k = posOf h (posOf 24 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_25 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 25 h) k = posOf h (posOf 25 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_26 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 26 h) k = posOf h (posOf 26 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_27 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 27 h) k = posOf h (posOf 27 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_28 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 28 h) k = posOf h (posOf 28 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_29 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 29 h) k = posOf h (posOf 29 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_30 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 30 h) k = posOf h (posOf 30 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_31 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 31 h) k = posOf h (posOf 31 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_32 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 32 h) k = posOf h (posOf 32 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_33 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 33 h) k = posOf h (posOf 33 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_34 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 34 h) k = posOf h (posOf 34 k) := by decide
set_option maxHeartbeats 2000000 in
private theorem pos_mul_35 : ∀ h : Fin 36, ∀ k : Fin 5, posOf (mulOf 35 h) k = posOf h (posOf 35 k) := by decide
theorem pos_mul : ∀ g h : Fin 36, ∀ k : Fin 5, posOf (mulOf g h) k = posOf h (posOf g k) := by
  intro g
  fin_cases g <;>
    first
      | exact pos_mul_0
      | exact pos_mul_1
      | exact pos_mul_2
      | exact pos_mul_3
      | exact pos_mul_4
      | exact pos_mul_5
      | exact pos_mul_6
      | exact pos_mul_7
      | exact pos_mul_8
      | exact pos_mul_9
      | exact pos_mul_10
      | exact pos_mul_11
      | exact pos_mul_12
      | exact pos_mul_13
      | exact pos_mul_14
      | exact pos_mul_15
      | exact pos_mul_16
      | exact pos_mul_17
      | exact pos_mul_18
      | exact pos_mul_19
      | exact pos_mul_20
      | exact pos_mul_21
      | exact pos_mul_22
      | exact pos_mul_23
      | exact pos_mul_24
      | exact pos_mul_25
      | exact pos_mul_26
      | exact pos_mul_27
      | exact pos_mul_28
      | exact pos_mul_29
      | exact pos_mul_30
      | exact pos_mul_31
      | exact pos_mul_32
      | exact pos_mul_33
      | exact pos_mul_34
      | exact pos_mul_35

set_option maxHeartbeats 2000000 in
private theorem val_mul_0 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 0 h) k x = valOf 0 k (valOf h (posOf 0 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_1 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 1 h) k x = valOf 1 k (valOf h (posOf 1 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_2 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 2 h) k x = valOf 2 k (valOf h (posOf 2 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_3 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 3 h) k x = valOf 3 k (valOf h (posOf 3 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_4 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 4 h) k x = valOf 4 k (valOf h (posOf 4 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_5 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 5 h) k x = valOf 5 k (valOf h (posOf 5 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_6 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 6 h) k x = valOf 6 k (valOf h (posOf 6 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_7 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 7 h) k x = valOf 7 k (valOf h (posOf 7 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_8 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 8 h) k x = valOf 8 k (valOf h (posOf 8 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_9 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 9 h) k x = valOf 9 k (valOf h (posOf 9 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_10 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 10 h) k x = valOf 10 k (valOf h (posOf 10 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_11 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 11 h) k x = valOf 11 k (valOf h (posOf 11 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_12 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 12 h) k x = valOf 12 k (valOf h (posOf 12 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_13 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 13 h) k x = valOf 13 k (valOf h (posOf 13 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_14 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 14 h) k x = valOf 14 k (valOf h (posOf 14 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_15 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 15 h) k x = valOf 15 k (valOf h (posOf 15 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_16 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 16 h) k x = valOf 16 k (valOf h (posOf 16 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_17 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 17 h) k x = valOf 17 k (valOf h (posOf 17 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_18 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 18 h) k x = valOf 18 k (valOf h (posOf 18 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_19 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 19 h) k x = valOf 19 k (valOf h (posOf 19 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_20 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 20 h) k x = valOf 20 k (valOf h (posOf 20 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_21 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 21 h) k x = valOf 21 k (valOf h (posOf 21 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_22 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 22 h) k x = valOf 22 k (valOf h (posOf 22 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_23 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 23 h) k x = valOf 23 k (valOf h (posOf 23 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_24 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 24 h) k x = valOf 24 k (valOf h (posOf 24 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_25 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 25 h) k x = valOf 25 k (valOf h (posOf 25 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_26 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 26 h) k x = valOf 26 k (valOf h (posOf 26 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_27 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 27 h) k x = valOf 27 k (valOf h (posOf 27 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_28 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 28 h) k x = valOf 28 k (valOf h (posOf 28 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_29 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 29 h) k x = valOf 29 k (valOf h (posOf 29 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_30 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 30 h) k x = valOf 30 k (valOf h (posOf 30 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_31 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 31 h) k x = valOf 31 k (valOf h (posOf 31 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_32 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 32 h) k x = valOf 32 k (valOf h (posOf 32 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_33 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 33 h) k x = valOf 33 k (valOf h (posOf 33 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_34 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 34 h) k x = valOf 34 k (valOf h (posOf 34 k) x) := by decide
set_option maxHeartbeats 2000000 in
private theorem val_mul_35 : ∀ h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf 35 h) k x = valOf 35 k (valOf h (posOf 35 k) x) := by decide
theorem val_mul : ∀ g h : Fin 36, ∀ k : Fin 5, ∀ x : Fin 6, valOf (mulOf g h) k x = valOf g k (valOf h (posOf g k) x) := by
  intro g
  fin_cases g <;>
    first
      | exact val_mul_0
      | exact val_mul_1
      | exact val_mul_2
      | exact val_mul_3
      | exact val_mul_4
      | exact val_mul_5
      | exact val_mul_6
      | exact val_mul_7
      | exact val_mul_8
      | exact val_mul_9
      | exact val_mul_10
      | exact val_mul_11
      | exact val_mul_12
      | exact val_mul_13
      | exact val_mul_14
      | exact val_mul_15
      | exact val_mul_16
      | exact val_mul_17
      | exact val_mul_18
      | exact val_mul_19
      | exact val_mul_20
      | exact val_mul_21
      | exact val_mul_22
      | exact val_mul_23
      | exact val_mul_24
      | exact val_mul_25
      | exact val_mul_26
      | exact val_mul_27
      | exact val_mul_28
      | exact val_mul_29
      | exact val_mul_30
      | exact val_mul_31
      | exact val_mul_32
      | exact val_mul_33
      | exact val_mul_34
      | exact val_mul_35

theorem pos_one : ∀ k : Fin 5, posOf 0 k = k := by decide

theorem val_one : ∀ k : Fin 5, ∀ x : Fin 6, valOf 0 k x = x := by decide

set_option maxHeartbeats 4000000 in
/-- Right multiplication by any element is surjective, with an explicit preimage. -/
theorem mul_right_surj : ∀ g₀ h : Fin 36, mulOf (mulOf h (invOf g₀)) g₀ = h := by decide

theorem act_mul (g h : Fin 36) (c : Case) : act g (act h c) = act (mulOf g h) c := by
  funext k
  simp only [act, pos_mul, val_mul]

theorem act_one (c : Case) : act 0 c = c := by
  funext k
  simp only [act, pos_one, val_one]


/-! ### The 7776 → 336 normalisation -/

/-- Base-six code of a case. -/
def code (c : Case) : ℕ :=
  (c 0).val + 6 * ((c 1).val + 6 * ((c 2).val + 6 * ((c 3).val + 6 * (c 4).val)))

/-- The codes of every case in the orbit of `c`. -/
def orbCodes (c : Case) : Finset ℕ :=
  Finset.image (fun g : Fin 36 => code (act g c)) Finset.univ

lemma orbCodes_nonempty (c : Case) : (orbCodes c).Nonempty :=
  ⟨code (act 0 c), Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩

/-- An orbit is determined by any of its members. -/
lemma orbCodes_act (g : Fin 36) (c : Case) : orbCodes (act g c) = orbCodes c := by
  ext n
  simp only [orbCodes, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨mulOf h g, by rw [act_mul]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨mulOf h (invOf g), by rw [act_mul, mul_right_surj]⟩

/-- The canonical code of a case: the least code in its orbit. -/
def canon (c : Case) : WithTop ℕ := (orbCodes c).min

lemma canon_act (g : Fin 36) (c : Case) : canon (act g c) = canon c := by
  unfold canon
  rw [orbCodes_act]

/-- A case is a representative exactly when it realises its own canonical code. -/
def IsRep (c : Case) : Prop := canon c = (code c : WithTop ℕ)

/-- Every case is carried into a representative by some group element. -/
lemma exists_rep (c : Case) : ∃ g : Fin 36, IsRep (act g c) := by
  obtain ⟨n, hn⟩ := Finset.min_of_nonempty (orbCodes_nonempty c)
  obtain ⟨g, -, hg⟩ := Finset.mem_image.mp (Finset.mem_of_min hn)
  refine ⟨g, ?_⟩
  unfold IsRep canon
  rw [orbCodes_act, hn, hg]
  rfl

/-- **Normalisation.**  A property invariant under the 36-element action that
fails on every representative fails on every one of the 7776 cases.  This is the
exact sense in which refuting the 336 representatives refutes the whole orbit. -/
theorem normalization {P : Case → Prop}
    (hinv : ∀ (g : Fin 36) (c : Case), P (act g c) ↔ P c)
    (hrep : ∀ c : Case, IsRep c → ¬ P c) :
    ∀ c : Case, ¬ P c := by
  intro c hc
  obtain ⟨g, hg⟩ := exists_rep c
  exact hrep (act g c) hg ((hinv g c).mpr hc)

end KrennX5

#print axioms KrennX5.pos_mul
#print axioms KrennX5.val_mul
#print axioms KrennX5.pos_one
#print axioms KrennX5.val_one
#print axioms KrennX5.mul_right_surj
#print axioms KrennX5.act_mul
#print axioms KrennX5.act_one
#print axioms KrennX5.orbCodes_act
#print axioms KrennX5.canon_act
#print axioms KrennX5.exists_rep
#print axioms KrennX5.normalization
