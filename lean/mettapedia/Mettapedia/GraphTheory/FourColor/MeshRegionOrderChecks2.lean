import Mettapedia.GraphTheory.FourColor.MeshRegionOrderCheckCore

/-! Kernel checks of complete ranked components and full cuts. -/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
set_option maxRecDepth 100000

theorem case_checked_14 : caseCheck 14 = true := by decide +kernel
theorem case_checked_15 : caseCheck 15 = true := by decide +kernel
theorem case_checked_16 : caseCheck 16 = true := by decide +kernel
theorem case_checked_17 : caseCheck 17 = true := by decide +kernel
theorem case_checked_18 : caseCheck 18 = true := by decide +kernel
theorem case_checked_19 : caseCheck 19 = true := by decide +kernel
theorem case_checked_20 : caseCheck 20 = true := by decide +kernel

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
