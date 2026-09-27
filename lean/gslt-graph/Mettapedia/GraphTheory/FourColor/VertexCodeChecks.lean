import Mettapedia.GraphTheory.FourColor.ExecutableVertexCode

/-! # Kernel controls for physical code compilation and evaluation -/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeChecks

open TubeSlab.VertexTransfer VertexCodePartition VertexCodeTrace
open ExecutableVertexCode

set_option Elab.async false
set_option maxRecDepth 16000

theorem returns_to_single_marker :
    FiniteFaceReturn.time VertexAttachmentTransfer.turn (fun i => i = 0) ⟨0, rfl⟩ = 3 := by
  decide +kernel

theorem returns_to_next_marker :
    FiniteFaceReturn.time VertexAttachmentTransfer.turn (fun i => i ≠ 1)
      ⟨0, by decide⟩ = 2 := by decide +kernel

def birth : Code 0 3 := ⟨Sum.inr, fun _ => none⟩
def close (reverse : Bool) : Code 3 0 :=
  ⟨fun t => Sum.inl (if reverse then -t else t), Fin.elim0⟩

theorem birth_valid : Valid birth := by decide +kernel
theorem close_valid (reverse : Bool) : Valid (close reverse) := by
  cases reverse <;> decide +kernel

def twoStars (reverse : Bool) : Trace 0 :=
  .step (.first birth birth_valid) (close reverse) (close_valid reverse)

theorem flat_mass : (evaluate (twoStars true)).mass = 4 := by decide +kernel
theorem twisted_mass : (evaluate (twoStars false)).mass = 0 := by decide +kernel
theorem flat_colourable : accepts (twoStars true) = true := by decide +kernel
theorem twisted_colourable : accepts (twoStars false) = true := by decide +kernel
theorem same_cut_data : (evaluate (twoStars true)).cuts =
    (evaluate (twoStars false)).cuts := by decide +kernel

def persistent : Code 4 3 :=
  ⟨![Sum.inl 0, Sum.inl 1, Sum.inr 2], ![some 3, some 2, none]⟩

theorem persistent_valid : Valid persistent := by decide +kernel
theorem persistent_input_inverse :
    (inputEquiv persistent persistent_valid).symm 3 =
      Sum.inl ⟨(0, 3), rfl⟩ := by decide +kernel
theorem persistent_output_inverse : (outputEquiv persistent).symm 2 =
    Sum.inr ⟨2, rfl⟩ := by decide +kernel

def duplicateWire : Code 4 3 :=
  ⟨persistent.1, ![some 2, some 2, none]⟩
theorem duplicate_rejected : ¬ Valid duplicateWire := by decide +kernel

end Mettapedia.GraphTheory.FourColor.VertexCodeChecks
