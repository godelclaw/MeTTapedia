import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages0
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages1
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages3
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages4
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages5
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages6
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages7
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages8
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages9
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages10
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages11
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages12
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages13
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages14
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages15
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages16
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages17
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages18
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages20
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages21
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages22
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages23
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages24
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages25
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreePages26
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk8x0
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk8x1
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk9x0
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk9x1
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk76x0
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk76x1
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk77x0
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThreeChunk77x1
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlatSplit

/-!
# The fork-code audit at interface bound 3

The closure `Reach 3` has 97 classes of codes with at least one position,
under renaming of positions.  The certificate lists one flat code per class.
Each page checks, by kernel evaluation, every legal planar fork of one member
with every member: a fork with no positions must not be rejecting, and the
canonical form of any other fork must be a member.  The soundness theorem of
the checker turns the pages into the audit.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

theorem page_three_8 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 8 leafF) = true :=
  pageOk_of_chunks 49 (by norm_num) fun t ht =>
    match t, ht with
    | 0, _ => page_three_8_c0
    | 1, _ => page_three_8_c1
    | _ + 2, h => absurd h (by rw [certCodes_three_length]; omega)

theorem page_three_9 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 9 leafF) = true :=
  pageOk_of_chunks 49 (by norm_num) fun t ht =>
    match t, ht with
    | 0, _ => page_three_9_c0
    | 1, _ => page_three_9_c1
    | _ + 2, h => absurd h (by rw [certCodes_three_length]; omega)

theorem page_three_76 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 76 leafF) = true :=
  pageOk_of_chunks 49 (by norm_num) fun t ht =>
    match t, ht with
    | 0, _ => page_three_76_c0
    | 1, _ => page_three_76_c1
    | _ + 2, h => absurd h (by rw [certCodes_three_length]; omega)

theorem page_three_77 :
    pageOk 3 (certCodes cert_three) ((certCodes cert_three).getD 77 leafF) = true :=
  pageOk_of_chunks 49 (by norm_num) fun t ht =>
    match t, ht with
    | 0, _ => page_three_77_c0
    | 1, _ => page_three_77_c1
    | _ + 2, h => absurd h (by rw [certCodes_three_length]; omega)

theorem pages_three : ∀ L ∈ (certCodes cert_three), pageOk 3 (certCodes cert_three) L = true := by
  apply forall_mem_of_getD
  rw [certCodes_three_length]
  intro i hi
  match i, hi with
  | 0, _ => exact page_three_0
  | 1, _ => exact page_three_1
  | 2, _ => exact page_three_2
  | 3, _ => exact page_three_3
  | 4, _ => exact page_three_4
  | 5, _ => exact page_three_5
  | 6, _ => exact page_three_6
  | 7, _ => exact page_three_7
  | 8, _ => exact page_three_8
  | 9, _ => exact page_three_9
  | 10, _ => exact page_three_10
  | 11, _ => exact page_three_11
  | 12, _ => exact page_three_12
  | 13, _ => exact page_three_13
  | 14, _ => exact page_three_14
  | 15, _ => exact page_three_15
  | 16, _ => exact page_three_16
  | 17, _ => exact page_three_17
  | 18, _ => exact page_three_18
  | 19, _ => exact page_three_19
  | 20, _ => exact page_three_20
  | 21, _ => exact page_three_21
  | 22, _ => exact page_three_22
  | 23, _ => exact page_three_23
  | 24, _ => exact page_three_24
  | 25, _ => exact page_three_25
  | 26, _ => exact page_three_26
  | 27, _ => exact page_three_27
  | 28, _ => exact page_three_28
  | 29, _ => exact page_three_29
  | 30, _ => exact page_three_30
  | 31, _ => exact page_three_31
  | 32, _ => exact page_three_32
  | 33, _ => exact page_three_33
  | 34, _ => exact page_three_34
  | 35, _ => exact page_three_35
  | 36, _ => exact page_three_36
  | 37, _ => exact page_three_37
  | 38, _ => exact page_three_38
  | 39, _ => exact page_three_39
  | 40, _ => exact page_three_40
  | 41, _ => exact page_three_41
  | 42, _ => exact page_three_42
  | 43, _ => exact page_three_43
  | 44, _ => exact page_three_44
  | 45, _ => exact page_three_45
  | 46, _ => exact page_three_46
  | 47, _ => exact page_three_47
  | 48, _ => exact page_three_48
  | 49, _ => exact page_three_49
  | 50, _ => exact page_three_50
  | 51, _ => exact page_three_51
  | 52, _ => exact page_three_52
  | 53, _ => exact page_three_53
  | 54, _ => exact page_three_54
  | 55, _ => exact page_three_55
  | 56, _ => exact page_three_56
  | 57, _ => exact page_three_57
  | 58, _ => exact page_three_58
  | 59, _ => exact page_three_59
  | 60, _ => exact page_three_60
  | 61, _ => exact page_three_61
  | 62, _ => exact page_three_62
  | 63, _ => exact page_three_63
  | 64, _ => exact page_three_64
  | 65, _ => exact page_three_65
  | 66, _ => exact page_three_66
  | 67, _ => exact page_three_67
  | 68, _ => exact page_three_68
  | 69, _ => exact page_three_69
  | 70, _ => exact page_three_70
  | 71, _ => exact page_three_71
  | 72, _ => exact page_three_72
  | 73, _ => exact page_three_73
  | 74, _ => exact page_three_74
  | 75, _ => exact page_three_75
  | 76, _ => exact page_three_76
  | 77, _ => exact page_three_77
  | 78, _ => exact page_three_78
  | 79, _ => exact page_three_79
  | 80, _ => exact page_three_80
  | 81, _ => exact page_three_81
  | 82, _ => exact page_three_82
  | 83, _ => exact page_three_83
  | 84, _ => exact page_three_84
  | 85, _ => exact page_three_85
  | 86, _ => exact page_three_86
  | 87, _ => exact page_three_87
  | 88, _ => exact page_three_88
  | 89, _ => exact page_three_89
  | 90, _ => exact page_three_90
  | 91, _ => exact page_three_91
  | 92, _ => exact page_three_92
  | 93, _ => exact page_three_93
  | 94, _ => exact page_three_94
  | 95, _ => exact page_three_95
  | 96, _ => exact page_three_96
  | _ + 97, h => exact absurd h (by omega)

/-- **The audit at interface bound 3.**  No root code of the closure
`Reach 3` is rejecting. -/
theorem audit_three : PhysicalForkCode.Audit 3 :=
  audit_of_checks leaf_three pages_three roots_three

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
