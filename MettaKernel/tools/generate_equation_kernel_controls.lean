/-
Writes the Lean-generated controls of the equation kernel into `MettaKernel/kernel/`:
`equation_kernel_controls_v0.metta`, `equation_kernel_space_controls_v0.metta`,
`equation_kernel_mutants_v0.metta` and `equation_kernel_compressed_controls_v0.metta`.
Every expected value is the Lean kernel's (`Languages/MeTTa/EquationKernel/Controls`).
Run from `lean/mettapedia`: `lake env lean ../../MettaKernel/tools/generate_equation_kernel_controls.lean`.
-/
import Mettapedia.Languages.MeTTa.EquationKernel.Controls

open Mettapedia.Languages.MeTTa.EquationKernel.Controls

/-- The kernel directory, relative to `lean/mettapedia`. -/
def kernelDir : System.FilePath := "../../MettaKernel/kernel"

#eval do
  IO.FS.writeFile (kernelDir / "equation_kernel_controls_v0.metta") controlsText
  IO.FS.writeFile (kernelDir / "equation_kernel_space_controls_v0.metta") spaceControlsText
  IO.FS.writeFile (kernelDir / "equation_kernel_mutants_v0.metta") mutantsText
  IO.FS.writeFile (kernelDir / "equation_kernel_compressed_controls_v0.metta") compressedControlsText
