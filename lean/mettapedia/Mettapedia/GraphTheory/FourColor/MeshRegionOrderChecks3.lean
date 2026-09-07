import Mettapedia.GraphTheory.FourColor.MeshRegionOrderCheckCore

/-! Kernel checks of complete ranked components and full cuts. -/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
set_option maxRecDepth 100000

theorem case_checked_21 : caseCheck 21 = true := by decide +kernel
theorem case_checked_22 : caseCheck 22 = true := by decide +kernel
theorem case_checked_23 : caseCheck 23 = true := by decide +kernel
theorem case_checked_24 : caseCheck 24 = true := by decide +kernel
theorem case_checked_25 : caseCheck 25 = true := by decide +kernel
theorem case_checked_26 : caseCheck 26 = true := by decide +kernel
theorem case_checked_27 : caseCheck 27 = true := by decide +kernel

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
