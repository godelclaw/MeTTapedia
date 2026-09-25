import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlatCheck

/-!
# The fork-code audit at interface bound 2

The closure `Reach 2` has 19 classes of codes with at least one position,
under renaming of positions.  The certificate lists one flat code per class.
Each page checks, by kernel evaluation, every legal planar fork of one member
with every member: a fork with no positions must not be rejecting, and the
canonical form of any other fork must be a member.  The soundness theorem of
the checker turns the pages into the audit.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

def cert_two : List ℕ :=
  [2, 0, 0, 1, 0, 3, 0, 4, 8, 4, 7, 8, 29, 30, 2, 1, 1, 0, 1, 3, 0, 4, 8, 2, 7, 8, 2, 1, 1, 1, 0,
  3, 0, 4, 8, 2, 7, 8, 2, 0, 1, 0, 1, 3, 0, 4, 8, 4, 7, 8, 29, 30, 2, 0, 1, 1, 0, 3, 0, 4, 8, 4,
  7, 8, 29, 30, 2, 0, 0, 0, 1, 3, 0, 4, 8, 4, 7, 8, 29, 30, 2, 1, 1, 0, 1, 3, 0, 4, 8, 4, 7, 8,
  29, 30, 1, 1, 0, 0, 2, 3, 4, 2, 1, 1, 1, 0, 3, 0, 4, 8, 4, 7, 8, 29, 30, 1, 0, 0, 0, 4, 3, 4,
  14, 15, 1, 1, 0, 0, 4, 3, 4, 14, 15, 2, 0, 1, 1, 0, 0, 6, 7, 8, 28, 29, 30, 31, 2, 1, 1, 0, 1,
  0, 6, 7, 8, 28, 29, 30, 31, 2, 1, 1, 1, 0, 0, 6, 7, 8, 28, 29, 30, 31, 2, 0, 1, 0, 1, 0, 6, 7,
  8, 28, 29, 30, 31, 2, 0, 0, 1, 0, 0, 6, 7, 8, 28, 29, 30, 31, 2, 0, 0, 0, 1, 0, 6, 7, 8, 28,
  29, 30, 31, 2, 1, 1, 0, 1, 0, 4, 7, 8, 28, 31, 2, 1, 1, 1, 0, 0, 4, 7, 8, 28, 31]

theorem certCodes_two_length : (certCodes cert_two).length = 19 := by decide +kernel

theorem leaf_two : leafOk (certCodes cert_two) = true := by decide +kernel

theorem roots_two : rootsOk (certCodes cert_two) = true := by decide +kernel

theorem page_two_0 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 0 leafF) = true := by
  decide +kernel

theorem page_two_1 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 1 leafF) = true := by
  decide +kernel

theorem page_two_2 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 2 leafF) = true := by
  decide +kernel

theorem page_two_3 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 3 leafF) = true := by
  decide +kernel

theorem page_two_4 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 4 leafF) = true := by
  decide +kernel

theorem page_two_5 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 5 leafF) = true := by
  decide +kernel

theorem page_two_6 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 6 leafF) = true := by
  decide +kernel

theorem page_two_7 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 7 leafF) = true := by
  decide +kernel

theorem page_two_8 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 8 leafF) = true := by
  decide +kernel

theorem page_two_9 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 9 leafF) = true := by
  decide +kernel

theorem page_two_10 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 10 leafF) = true := by
  decide +kernel

theorem page_two_11 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 11 leafF) = true := by
  decide +kernel

theorem page_two_12 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 12 leafF) = true := by
  decide +kernel

theorem page_two_13 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 13 leafF) = true := by
  decide +kernel

theorem page_two_14 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 14 leafF) = true := by
  decide +kernel

theorem page_two_15 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 15 leafF) = true := by
  decide +kernel

theorem page_two_16 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 16 leafF) = true := by
  decide +kernel

theorem page_two_17 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 17 leafF) = true := by
  decide +kernel

theorem page_two_18 :
    pageOk 2 (certCodes cert_two) ((certCodes cert_two).getD 18 leafF) = true := by
  decide +kernel

theorem pages_two : ∀ L ∈ (certCodes cert_two), pageOk 2 (certCodes cert_two) L = true := by
  apply forall_mem_of_getD
  rw [certCodes_two_length]
  intro i hi
  match i, hi with
  | 0, _ => exact page_two_0
  | 1, _ => exact page_two_1
  | 2, _ => exact page_two_2
  | 3, _ => exact page_two_3
  | 4, _ => exact page_two_4
  | 5, _ => exact page_two_5
  | 6, _ => exact page_two_6
  | 7, _ => exact page_two_7
  | 8, _ => exact page_two_8
  | 9, _ => exact page_two_9
  | 10, _ => exact page_two_10
  | 11, _ => exact page_two_11
  | 12, _ => exact page_two_12
  | 13, _ => exact page_two_13
  | 14, _ => exact page_two_14
  | 15, _ => exact page_two_15
  | 16, _ => exact page_two_16
  | 17, _ => exact page_two_17
  | 18, _ => exact page_two_18
  | _ + 19, h => exact absurd h (by omega)

/-- **The audit at interface bound 2.**  No root code of the closure
`Reach 2` is rejecting. -/
theorem audit_two : PhysicalForkCode.Audit 2 :=
  audit_of_checks leaf_two pages_two roots_two

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
