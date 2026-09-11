import Mettapedia.GraphTheory.FourColor.BoundarySmallCutExecutable

/-! # Kernel controls for the structural profile implementation

These are generic multigraph unit tests, not colouring configurations.
They check that the executable definitions themselves reduce, distinguish
a bridge from parallel alternatives, and retain saturated records.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundarySmallCutChecks

open GoertzelV24BoundaryEssentialGluing BoundarySmallCutExecutable
open BoundarySmallCutTransfer

def parallel (n : Nat) : Multigraph (Fin 2) (Fin n) := ⟨fun _ => 0, fun _ => 1⟩

theorem disconnected_rejected : accepts (extract (parallel 0) id) = false := by decide +kernel
theorem bridge_rejected : accepts (extract (parallel 1) id) = false := by decide +kernel
theorem parallel_accepted : accepts (extract (parallel 2) id) = true := by decide +kernel

theorem saturation_retained :
    ((extract (parallel 3) id).filter (fun s => s.cost.val = 2)).card = 2 := by decide +kernel

def outerPorts : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

theorem actual_open_transfer :
    transfer (extract (parallel 3) outerPorts) (extract (parallel 1) outerPorts) =
      extract (glue (parallel 3) (parallel 1) (fun _ : Fin 1 => 1) (fun _ => 0))
        (outsidePorts (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2))) := by
  decide +kernel

open GoertzelV24OpenTangleComposition

/-- A toy two-sided tangle: the core constructor does not require cubicity. -/
def edgeTangle : TwoSidedOpenTangleData (Fin 2) (Fin 2) (Fin 1) (Fin 1) where
  interiorVert := id
  leftVert := fun _ => 0
  rightVert := fun _ => 1
  interiorAlpha := Equiv.swap 0 1
  interiorAlpha_involutive := by decide +kernel
  interiorAlpha_fixfree := by decide +kernel
  rho := Equiv.refl _
  vert_rho := by intro d; rfl
  interior_no_self_loops := by decide +kernel
  outer := .inl 0

theorem literal_dart_extraction :
    extractTangle edgeTangle = extract (parallel 1) outerPorts := by decide +kernel

theorem literal_serial_transfer :
    extractTangle (edgeTangle.serialCompose edgeTangle (Equiv.refl (Fin 1))) =
      transfer (extractTangle edgeTangle) (extractTangle edgeTangle) := by decide +kernel

end Mettapedia.GraphTheory.FourColor.BoundarySmallCutChecks
