import MettapediaFourColor.TwoFiveWheelRepair
import MettapediaFourColor.WheelColouringGSLT
import MettapediaFourColor.BoundaryRepairTransport

/-!
# Exact cyclic semantics for every two-five wheel

All six target graphs have the same boundary, centre and cyclic-rim
construction. Their actual colouring witnesses compose from two GSLT sectors
using one shared centre colour and both shared seam colours. Boundary repair
therefore produces compatible sector witnesses for the same exterior.
-/

namespace FourColor.TwoFiveWheelColouring

open D3009Wheel CyclicColourRoute

variable (p : Fin 6)

set_option maxRecDepth 32768

def boundaryGraph : SimpleGraph (Fin 12) :=
  (TwoFiveWheelData.input p).graph.comap (fun b => b.castAdd 8)
instance : DecidableRel (boundaryGraph p).Adj := by unfold boundaryGraph; infer_instance

def touch (i : Fin 7) (b : Fin 12) : Prop :=
  (TwoFiveWheelData.input p).graph.Adj ((rim i).natAdd 12) (b.castAdd 8)
instance (i : Fin 7) (b : Fin 12) : Decidable ((touch p) i b) := by unfold touch; infer_instance

def wheel : SimpleGraph (WheelColouring.Vertex (Fin 12) (Fin 7)) :=
  WheelColouring.graph (boundaryGraph p) (CyclicColourRoute.next (by decide)) (touch p)
    (next_ne (by decide))
instance : DecidableRel (wheel p).Adj := by unfold wheel; infer_instance

/-- Source labels retain the boundary order and the centre's rim order. -/
def source : (wheel p) ≃g (TwoFiveWheelData.input p).graph where
  toEquiv :=
    { toFun := fun v => v.elim (fun b => b.castAdd 8)
        (fun i => i.elim 12 (fun j => (rim j).natAdd 12))
      invFun := fun v => if h : v.val < 12 then .inl ⟨v.val, h⟩
        else .inr (position ⟨v.val - 12, by omega⟩)
      left_inv := by revert p; decide +kernel
      right_inv := by revert p; decide +kernel }
  map_rel_iff' := by revert p; decide +kernel

@[simp] theorem source_boundary (b : Fin 12) : (source p) (.inl b) = b.castAdd 8 := rfl

def coloringEquiv {C : Type*} : (TwoFiveWheelData.input p).graph.Coloring C ≃
    (Σ k : (boundaryGraph p).Coloring C,
      WheelColouring.Witness (CyclicColourRoute.next (by decide)) (touch p) k) :=
  (BoundaryRepairTransport.coloring (source p)).symm.trans
    (WheelColouring.coloringEquiv (boundaryGraph p) _ (touch p) _)

/-- Reconstruction fixes every exterior-facing colour. -/
theorem extends_iff {C : Type*} (k : (boundaryGraph p).Coloring C) :
    (∃ full : (TwoFiveWheelData.input p).graph.Coloring C, ∀ b : Fin 12, full (b.castAdd 8) = k b) ↔
      Nonempty (WheelColouring.Witness (CyclicColourRoute.next (by decide)) (touch p) k) := by
  have h := BoundaryRepairTransport.boundary_iff (source p)
    (fun b : Fin 12 => Sum.inl b) (fun f => ∀ b, f b = k b)
  change (∃ full : (wheel p).Coloring C, ∀ b, full (.inl b) = k b) ↔
    (∃ full : (TwoFiveWheelData.input p).graph.Coloring C,
      ∀ b : Fin 12, full (b.castAdd 8) = k b) at h
  rw [← h]
  exact WheelColouring.extends_iff (boundaryGraph p) _ (touch p) _ k

/-- The common centre and both sector endpoint colours are retained. -/
theorem two_sectors_iff {C : Type*} (k : (boundaryGraph p).Coloring C) :
    (∃ full : (TwoFiveWheelData.input p).graph.Coloring C, ∀ b : Fin 12, full (b.castAdd 8) = k b) ↔
      ∃ z a b,
        (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) (touch p) k z).Supports
          (route 0 3) a b ∧
        (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) (touch p) k z).Supports
          (route 3 4) b a := by
  rw [extends_iff]
  exact WheelColouringGSLT.split_iff (by decide) (touch p) k 3 4 rfl

theorem ordered_boundary : (TwoFiveWheelData.input p).boundary =
    (List.finRange 12).map (fun b => b.castAdd 8) := by
  revert p; decide +kernel

theorem graphTrace_iff (et : List Color) :
    KempeBoundarySplit.GraphTrace (TwoFiveWheelData.input p).graph
      (TwoFiveWheelData.input p).boundary et ↔
      ∃ k : (boundaryGraph p).Coloring Color,
        et = trace ((List.finRange 12).map k) ∧
          Nonempty (WheelColouring.Witness (CyclicColourRoute.next (by decide)) (touch p) k) := by
  constructor
  · rintro ⟨full, ht⟩
    let k : (boundaryGraph p).Coloring Color :=
      .mk (fun b => full (b.castAdd 8)) (fun {_ _} h => full.valid h)
    refine ⟨k, ?_, (extends_iff p k).mp ⟨full, fun _ => rfl⟩⟩
    change et = trace ((List.finRange 12).map (fun b => full (b.castAdd 8)))
    simpa only [ordered_boundary, List.map_map, Function.comp_def] using ht
  · rintro ⟨k, ht, witness⟩
    obtain ⟨full, fixed⟩ := (extends_iff p k).mpr witness
    refine ⟨full, ?_⟩
    simpa only [ordered_boundary, List.map_map, Function.comp_def, fixed] using ht

/-- A repaired full colouring splits into two independently constructed
sectors, whose common centre and seam choices agree. -/
theorem repaired_sectors (base : KempeBoundarySplit.Repairs
    (KempeBoundarySplit.GraphTrace D3009Wheel.input.graph D3009Wheel.input.boundary) 13)
    (et : List Color) (length : et.length = 12) (proper : (0 : Color) ∉ et)
    (conserved : et.sum = 0) (Q : List Color → Prop)
    (closed : KempeClosed Q) (outside : Q et) :
    ∃ k : (boundaryGraph p).Coloring Color,
      Q (trace ((List.finRange 12).map k)) ∧
        ∃ z a b,
          (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) (touch p) k z).Supports
            (route 0 3) a b ∧
          (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) (touch p) k z).Supports
            (route 3 4) b a := by
  obtain ⟨es, repaired, compatible⟩ :=
    TwoFiveWheelRepair.transfer base p et length proper conserved Q closed outside
  obtain ⟨k, rfl, witness⟩ := (graphTrace_iff p es).mp repaired
  exact ⟨k, compatible, (WheelColouringGSLT.split_iff (by decide) (touch p) k 3 4 rfl).mp witness⟩

end FourColor.TwoFiveWheelColouring
