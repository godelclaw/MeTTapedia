import Mettapedia.GraphTheory.FourColor.VertexAttachmentTransfer
import Mettapedia.GraphTheory.FourColor.BoundarySmallCutChecks

/-! # Kernel controls for the literal vertex attachment

The same two stars form a sphere or a torus according to the second
cyclic order. Connectivity and the small-cut profile alone cannot
distinguish them. The component column counter is checked separately
on empty selections, repeated ports and disconnected old pieces.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexAttachmentChecks

set_option Elab.async false

open VertexAttachmentTransfer BoundarySmallCutChecks BoundaryComponentCount
open BoundarySmallCutExecutable SerialTangleSmallCutTransfer OpenTangleMarkedFace

def allOut : Fin 3 ≃ Fin 0 ⊕ Fin 3 where
  toFun := Sum.inr
  invFun := Sum.elim Fin.elim0 id
  left_inv _ := rfl
  right_inv := by rintro (e | b); exact e.elim0; rfl

def allIn (reverse : Bool) : Fin 3 ≃ Fin 3 ⊕ Fin 0 where
  toFun i := .inl (if reverse then -i else i)
  invFun := Sum.elim (fun i => if reverse then -i else i) Fin.elim0
  left_inv := by cases reverse <;> decide +kernel
  right_inv := by cases reverse <;> decide +kernel

noncomputable def closed (reverse : Bool) := append (star allOut) (allIn reverse)

def splitOrder (h : Nat) (hh : h ≤ 3) : Fin 3 ≃ Fin h ⊕ Fin (3 - h) :=
  (finCongr (by omega : 3 = h + (3 - h))).trans finSumFinEquiv.symm

noncomputable def oneSeam :=
  append (star (splitOrder 2 (by decide))) (splitOrder 1 (by decide))

noncomputable def twoSeams :=
  append (star (splitOrder 1 (by decide))) (splitOrder 2 (by decide))

noncomputable def noSeam :=
  append (star (splitOrder 3 (by decide))) (splitOrder 0 (by decide))

theorem one_seam_faces : (openPhi (asOpen oneSeam)).partition.parts.card = 1 := by
  decide +kernel

theorem two_seam_faces : (openPhi (asOpen twoSeams)).partition.parts.card = 2 := by
  decide +kernel

theorem no_seam_faces : (openPhi (asOpen noSeam)).partition.parts.card = 2 := by
  decide +kernel

theorem no_seam_components :
    count (extractTangle noSeam) (id : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3) = 2 := by
  decide +kernel

theorem persistent_and_new_ports_connected :
    count (extractTangle oneSeam) (id : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2) = 1 := by
  decide +kernel

theorem three_ports_one_component :
    count (extractTangle (star allOut)) (Sum.inr : Fin 3 → Fin 0 ⊕ Fin 3) = 1 := by
  decide +kernel

theorem empty_selection : count (extract (parallel 0) id) (Fin.elim0 : Fin 0 → Fin 2) = 0 := by
  decide +kernel

theorem disconnected_components : count (extract (parallel 0) id) id = 2 := by
  decide +kernel

theorem repeated_ports : count (extract (parallel 0) id) (![0, 1, 1] : Fin 3 → Fin 2) = 2 := by
  decide +kernel

theorem connected_components : count (extract (parallel 2) id) id = 1 := by
  decide +kernel

theorem flat_faces : (openPhi (asOpen (closed true))).partition.parts.card = 3 := by
  decide +kernel

theorem twisted_faces : (openPhi (asOpen (closed false))).partition.parts.card = 1 := by
  decide +kernel

theorem flat_mass : OpenTangleReplacementEuler.eulerMass (asOpen (closed true)) = 4 := by
  decide +kernel

theorem twisted_mass : OpenTangleReplacementEuler.eulerMass (asOpen (closed false)) = 0 := by
  decide +kernel

theorem same_cut_profile : extractTangle (closed true) = extractTangle (closed false) := by
  decide +kernel

theorem flat_connected_bridgeless : accepts (extractTangle (closed true)) = true := by
  decide +kernel

theorem twisted_connected_bridgeless : accepts (extractTangle (closed false)) = true := by
  decide +kernel

end Mettapedia.GraphTheory.FourColor.VertexAttachmentChecks
