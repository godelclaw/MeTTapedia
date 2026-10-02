import MettapediaFourColor.D3009Construction
import MettapediaFourColor.WheelColouringGSLT
import MettapediaFourColor.BoundaryRepairTransport

/-!
# The pinned wheel source consumes the uniform cyclic-colouring law

The exact source graph is isomorphic to the boundary-and-wheel construction.
Every source colouring is therefore equivalent to a joint choice of boundary,
centre and cyclic rim colours. The thirteen ordered ports are unchanged.
The source's Y/H construction has exactly the same closed-route semantics.
-/

namespace FourColor.D3009Colouring

open D3009Wheel CyclicColourRoute

set_option maxRecDepth 32768

def boundaryGraph : SimpleGraph (Fin 13) := input.graph.comap (fun b => b.castAdd 8)
instance : DecidableRel boundaryGraph.Adj := by unfold boundaryGraph; infer_instance

def touch (i : Fin 7) (b : Fin 13) : Prop :=
  input.graph.Adj ((rim i).natAdd 13) (b.castAdd 8)
instance (i : Fin 7) (b : Fin 13) : Decidable (touch i b) := by unfold touch; infer_instance

def wheel : SimpleGraph (WheelColouring.Vertex (Fin 13) (Fin 7)) :=
  WheelColouring.graph boundaryGraph (CyclicColourRoute.next (by decide)) touch
    (next_ne (by decide))
instance : DecidableRel wheel.Adj := by unfold wheel; infer_instance

/-- Source labels retain the boundary order and the centre's rim order. -/
def source : wheel ≃g input.graph where
  toEquiv :=
    { toFun := fun v => v.elim (fun b => b.castAdd 8)
        (fun i => i.elim 13 (fun j => (rim j).natAdd 13))
      invFun := fun v => if h : v.val < 13 then .inl ⟨v.val, h⟩
        else .inr (position ⟨v.val - 13, by omega⟩)
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  map_rel_iff' := by decide +kernel

@[simp] theorem source_boundary (b : Fin 13) : source (.inl b) = b.castAdd 8 := rfl

def coloringEquiv {C : Type*} : input.graph.Coloring C ≃
    (Σ k : boundaryGraph.Coloring C,
      WheelColouring.Witness (CyclicColourRoute.next (by decide)) touch k) :=
  (BoundaryRepairTransport.coloring source).symm.trans
    (WheelColouring.coloringEquiv boundaryGraph _ touch _)

/-- Reconstruction fixes every exterior-facing colour. -/
theorem extends_iff {C : Type*} (k : boundaryGraph.Coloring C) :
    (∃ full : input.graph.Coloring C, ∀ b : Fin 13, full (b.castAdd 8) = k b) ↔
      Nonempty (WheelColouring.Witness (CyclicColourRoute.next (by decide)) touch k) := by
  have h := BoundaryRepairTransport.boundary_iff source
    (fun b : Fin 13 => Sum.inl b) (fun f => ∀ b, f b = k b)
  change (∃ full : wheel.Coloring C, ∀ b, full (.inl b) = k b) ↔
    (∃ full : input.graph.Coloring C, ∀ b : Fin 13, full (b.castAdd 8) = k b) at h
  rw [← h]
  exact WheelColouring.extends_iff boundaryGraph _ touch _ k

/-- The common centre and both sector endpoint colours are retained. -/
theorem two_sectors_iff {C : Type*} (k : boundaryGraph.Coloring C) :
    (∃ full : input.graph.Coloring C, ∀ b : Fin 13, full (b.castAdd 8) = k b) ↔
      ∃ z a b,
        (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch k z).Supports
          (route 0 3) a b ∧
        (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch k z).Supports
          (route 3 4) b a := by
  rw [extends_iff]
  exact WheelColouringGSLT.split_iff (by decide) touch k 3 4 rfl

theorem ordered_boundary : input.boundary = (List.finRange 13).map (fun b => b.castAdd 8) := by
  decide +kernel

theorem graphTrace_iff (et : List Color) :
    KempeBoundarySplit.GraphTrace input.graph input.boundary et ↔
      ∃ k : boundaryGraph.Coloring Color,
        et = trace ((List.finRange 13).map k) ∧
          Nonempty (WheelColouring.Witness (CyclicColourRoute.next (by decide)) touch k) := by
  constructor
  · rintro ⟨full, ht⟩
    let k : boundaryGraph.Coloring Color :=
      .mk (fun b => full (b.castAdd 8)) (fun {_ _} h => full.valid h)
    refine ⟨k, ?_, (extends_iff k).mp ⟨full, fun _ => rfl⟩⟩
    change et = trace ((List.finRange 13).map (fun b => full (b.castAdd 8)))
    simpa only [ordered_boundary, List.map_map, Function.comp_def] using ht
  · rintro ⟨k, ht, witness⟩
    obtain ⟨full, fixed⟩ := (extends_iff k).mpr witness
    refine ⟨full, ?_⟩
    simpa only [ordered_boundary, List.map_map, Function.comp_def, fixed] using ht

/-- The source construction and the operational cycle permit exactly the same traces. -/
theorem constructionTrace_iff (et : List Color) :
    (cfmap D3009Construction.config).map.RingTrace
      (cfring D3009Construction.config).reverse et ↔
      ∃ k : boundaryGraph.Coloring Color,
        et = trace ((List.finRange 13).map k) ∧
          ∃ z a, (WheelColouringGSLT.semantics (by decide : 2 ≤ 7) touch k z).Supports
            (route 0 7) a a := by
  rw [D3009Construction.ringTrace_iff, graphTrace_iff]
  simp_rw [WheelColouringGSLT.witness_iff (by decide : 2 ≤ 7)]
  rfl

end FourColor.D3009Colouring
