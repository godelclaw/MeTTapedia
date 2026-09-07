import Mettapedia.GraphTheory.FourColor.MeshRegionOrderChecks0
import Mettapedia.GraphTheory.FourColor.MeshRegionOrderChecks1
import Mettapedia.GraphTheory.FourColor.MeshRegionOrderChecks2
import Mettapedia.GraphTheory.FourColor.MeshRegionOrderChecks3
import Mettapedia.GraphTheory.FourColor.MeshRegionOrderChecks4
import Mettapedia.GraphTheory.FourColor.MeshRegionOrderChecks5
import Mathlib.Tactic.FinCases

/-! Assembly of the individually checked component witnesses. -/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
open MeshRegionOrderData

theorem cases_checked : ∀ t : Cases, caseCheck t = true := by
  intro t
  fin_cases t
  · exact case_checked_0
  · exact case_checked_1
  · exact case_checked_2
  · exact case_checked_3
  · exact case_checked_4
  · exact case_checked_5
  · exact case_checked_6
  · exact case_checked_7
  · exact case_checked_8
  · exact case_checked_9
  · exact case_checked_10
  · exact case_checked_11
  · exact case_checked_12
  · exact case_checked_13
  · exact case_checked_14
  · exact case_checked_15
  · exact case_checked_16
  · exact case_checked_17
  · exact case_checked_18
  · exact case_checked_19
  · exact case_checked_20
  · exact case_checked_21
  · exact case_checked_22
  · exact case_checked_23
  · exact case_checked_24
  · exact case_checked_25
  · exact case_checked_26
  · exact case_checked_27
  · exact case_checked_28
  · exact case_checked_29
  · exact case_checked_30
  · exact case_checked_31
  · exact case_checked_32
  · exact case_checked_33
  · exact case_checked_34
  · exact case_checked_35
  · exact case_checked_36
  · exact case_checked_37
  · exact case_checked_38
  · exact case_checked_39
  · exact case_checked_40
  · exact case_checked_41

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
