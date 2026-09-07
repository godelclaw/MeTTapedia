import Mettapedia.GraphTheory.FourColor.MeshRegionOrderCheckCore

/-! Kernel checks of complete ranked components and full cuts. -/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
set_option maxRecDepth 100000

theorem case_checked_0 : caseCheck 0 = true := by decide +kernel
theorem case_checked_1 : caseCheck 1 = true := by decide +kernel
theorem case_checked_2 : caseCheck 2 = true := by decide +kernel
theorem case_checked_3 : caseCheck 3 = true := by decide +kernel
theorem case_checked_4 : caseCheck 4 = true := by decide +kernel
theorem case_checked_5 : caseCheck 5 = true := by decide +kernel
theorem case_checked_6 : caseCheck 6 = true := by decide +kernel

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
