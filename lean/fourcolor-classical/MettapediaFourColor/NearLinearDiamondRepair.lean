import MettapediaFourColor.NearLinearDiamondData
import MettapediaFourColor.BoundaryRepairTransport
import MettapediaFourColor.DiamondProfileReducibility

/-!
# Shared repair for the first two near-linear configurations

The exact source presentations inherit the existing coupled-profile repair
and boundary-split transfer. Neither configuration's original reference rank
certificate is used. The shared finite profile certificate remains.

The conclusion is repair against every Kempe-closed exterior relation, with
actual graph-colouring witnesses. The construction history records compatible
insertion choices; it is not an executable sequence of exterior Kempe swaps.
This bridge does not establish new geometric coverage or a runtime bound.
-/

namespace FourColor.NearLinearDiamondRepair

open NearLinearDiamondData DiamondConfigurations KempeBoundarySplit

open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

local instance : DecidableRel (subdivide input0000.graph 1 2 7).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [subdivide, removed] <;> infer_instance

set_option maxRecDepth 32768 in
/-- The two source files differ by the same actual boundary-triangle insertion. -/
def sourceInsertion : subdivide input0000.graph 1 2 7 ≃g input0001.graph where
  toEquiv := (Equiv.optionCongr iso0000.toEquiv).trans
    (DiamondInsertion.insert12.toEquiv.trans iso0001.symm.toEquiv)
  map_rel_iff' := by decide +kernel

set_option maxRecDepth 32768 in
theorem sourceInsertion_rotation : ∀ v : Option (Fin 10), ∃ shift : Fin 7,
    stars0001 (sourceInsertion v) =
      ((ConfigurationFaceGraph.triangleStar stars0000 1 2 7 v).map sourceInsertion).rotate
        shift.val := by
  decide +kernel

theorem sourceInsertion_boundary :
    ((ConfigurationFaceGraph.triangleBoundary input0000.boundary 1).map sourceInsertion).rotate 4 =
      input0001.boundary := by
  decide +kernel

/-- Relabelling commutes with the insertion on every old and new vertex. -/
theorem sourceInsertion_commutes (v : Option (Fin 10)) :
    iso0001 (sourceInsertion v) = DiamondInsertion.insert12 (v.map iso0000) := by
  exact iso0001.apply_symm_apply _

/-- Every colouring, with all its interior choices, transports exactly. -/
def coloring0000 (C : Type*) : input0000.graph.Coloring C ≃ graph001.Coloring C :=
  BoundaryRepairTransport.coloring iso0000

def coloring0001 (C : Type*) : input0001.graph.Coloring C ≃ graph002.Coloring C :=
  BoundaryRepairTransport.coloring iso0001

theorem boundary0000_iff {Port C : Type*} (ports : Port → Fin 10)
    (accepts : (Port → C) → Prop) :
    (∃ k : input0000.graph.Coloring C, accepts (fun p => k (ports p))) ↔
      ∃ k : graph001.Coloring C, accepts (fun p => k (iso0000 (ports p))) :=
  BoundaryRepairTransport.boundary_iff iso0000 ports accepts

theorem boundary0001_iff {Port C : Type*} (ports : Port → Fin 11)
    (accepts : (Port → C) → Prop) :
    (∃ k : input0001.graph.Coloring C, accepts (fun p => k (ports p))) ↔
      ∃ k : graph002.Coloring C, accepts (fun p => k (iso0001 (ports p))) :=
  BoundaryRepairTransport.boundary_iff iso0001 ports accepts

/-- The first source entry inherits repair by the same split law as configuration 1. -/
theorem repair0000 : Repairs (GraphTrace input0000.graph input0000.boundary) 6 := by
  apply BoundaryRepairTransport.repairs iso0000 input0000.boundary boundary001.reverse 5
    NearLinearDiamondData.boundary0000
  intro et hlen hzero hsum Q hQ hq
  obtain ⟨es, hs, hqs⟩ :=
    DiamondProfileReducibility.transferred001 et hlen hzero hsum Q hQ hq
  exact ⟨es, (reducibilityTrace001 es).mp hs, hqs⟩

/-- The second source entry inherits the common profile's D-repair contract. -/
theorem repair0001 : Repairs (GraphTrace input0001.graph input0001.boundary) 7 := by
  apply BoundaryRepairTransport.repairs iso0001 input0001.boundary boundary002.reverse 4
    NearLinearDiamondData.boundary0001
  intro et hlen hzero hsum Q hQ hq
  obtain ⟨es, hs, hqs⟩ := DiamondProfileReducibility.repair002 et hlen hzero hsum Q hQ hq
  exact ⟨es, (reducibilityTrace002 es).mp hs, hqs⟩

open Mettapedia.GSLT.Ultrainfinite

/-- The already-proved first insertion, with no new rewriting language. -/
def insertionRoute : Route DiamondInsertionGSLT.Event .alternatives .firstInserted :=
  .cons .first (.refl _)

def insertionStart (k : input0001.graph.Coloring (Fin 4)) :
    DiamondInsertionGSLT.State .alternatives :=
  .inl (DiamondInsertion.alternatives12.symm (coloring0001 (Fin 4) k))

def insertionEnd (k : input0001.graph.Coloring (Fin 4)) :
    DiamondInsertionGSLT.State .firstInserted := .inl (coloring0001 (Fin 4) k)

/-- Every source colouring retains a compatible choice at the actual insertion. -/
theorem construction_history0001 (k : input0001.graph.Coloring (Fin 4)) :
    DiamondInsertionGSLT.semantics.Supports insertionRoute (insertionStart k) (insertionEnd k) := by
  refine ⟨⟨insertionEnd k, ⟨⟨?_⟩⟩, ⟨⟨rfl⟩⟩⟩⟩
  change Sum.inl (DiamondInsertion.alternatives12
    (DiamondInsertion.alternatives12.symm (coloring0001 (Fin 4) k))) = _
  rw [Equiv.apply_symm_apply]
  rfl

def fourColors (k : input0001.graph.Coloring Color) : input0001.graph.Coloring (Fin 4) :=
  SimpleGraph.recolorOfEquiv input0001.graph ConfigurationFaceGraph.colorEquiv.symm k

/-- Exterior compatibility and the construction history refer to the same witness. -/
theorem compatible_repair0001 (et : List Color) (hlen : et.length = 7)
    (hzero : (0 : Color) ∉ et) (hsum : et.sum = 0)
    (Q : List Color → Prop) (closed : KempeClosed Q) (outside : Q et) :
    ∃ es, ∃ k : input0001.graph.Coloring Color,
      es = trace (input0001.boundary.map k) ∧ Q es ∧
      DiamondInsertionGSLT.semantics.Supports insertionRoute
        (insertionStart (fourColors k)) (insertionEnd (fourColors k)) := by
  obtain ⟨es, ⟨k, hk⟩, hQ⟩ := repair0001 et hlen hzero hsum Q closed outside
  exact ⟨es, k, hk, hQ, construction_history0001 (fourColors k)⟩

end FourColor.NearLinearDiamondRepair
