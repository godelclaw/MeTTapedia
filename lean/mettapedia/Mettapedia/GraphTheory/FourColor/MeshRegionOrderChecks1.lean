import Mettapedia.GraphTheory.FourColor.MeshRegionOrderCheckCore

/-! Kernel checks of complete ranked components and full cuts. -/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
set_option maxRecDepth 100000

theorem case_checked_7 : caseCheck 7 = true := by decide +kernel
theorem case_checked_8 : caseCheck 8 = true := by decide +kernel
theorem case_checked_9 : caseCheck 9 = true := by decide +kernel
theorem case_checked_10 : caseCheck 10 = true := by decide +kernel
theorem case_checked_11 : caseCheck 11 = true := by decide +kernel
theorem case_checked_12 : caseCheck 12 = true := by decide +kernel
theorem case_checked_13 : caseCheck 13 = true := by decide +kernel

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
