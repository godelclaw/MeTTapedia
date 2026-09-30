import MettapediaFourColor.DiamondCoupledWiringWitness
import MettapediaFourColor.ConfigurationTable

/-!
# The joint diamond as a fourteen-vertex cubic piece

The literal darts and rotations are extracted from reference configuration 4.
Face differences reconstruct genuine colourings of this piece. Colouring a
smaller coupled wiring starts the existing shared repair and reconstructs the
whole closed graph, with one compatible exterior assignment at every port.

Wire separation and physical Kempe closure are explicit hypotheses. This
colouring theorem does not yet establish preservation of the spherical map
class or geometric recognition of occurrences in arbitrary maps.
-/

namespace FourColor.JointDiamondPatch.Tangle

open ConfigurationTable
open Color KempeBoundarySplit

abbrev graph := DiamondConfigurations.graph004
abbrev boundary := DiamondConfigurations.boundary004.reverse
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition
open Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

abbrev Dart := Fin 34 ⊕ Fin 8

def index : Dart ≃ Fin 42 where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr i => ⟨34 + i.val, by omega⟩
  invFun i := if h : i.val < 34 then .inl ⟨i.val, h⟩
    else .inr ⟨i.val - 34, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertexCodes : String := "ABCDBEECFGGHHAIJJKKFDLLIKMMHENNLNMBAGFJIDC"
def rotationCodes : String := "dEjUc]FCfKe\\LAhQgYRIi`VOSbZMGa^W_[BNJTPXDH"
def inverseCodes : String := "NcHiBG]jTeJM\\dXgPSYfDW`hR[bLF_aV^ZEAKIQOUC"
def leftCodes : String := "FKDJEKEJHLGLGKBIAIALCJCILILKJKJIIKFGHABCDE"
def rightCodes : String := "KFJDKEJELHLGKGIBIALAJCICILKLKJIJKIEFGHABCD"
def alphaCodes : String := "BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_ba"

def referenceCodes : String := "CDIJMNOPSTWXYZ]^abcdefghijklmnopqrEBUR_\\KH"

def vertex (d : Dart) : Fin 14 := lookup vertexCodes (index d)
def left (d : Dart) : Fin 12 := lookup leftCodes (index d)
def right (d : Dart) : Fin 12 := lookup rightCodes (index d)
def referenceDart (d : Dart) : Fin 50 := lookup referenceCodes (index d)

def rotate (s : String) (d : Dart) : Dart :=
  index.symm (lookup s (index d))

def rho : Equiv.Perm Dart where
  toFun := rotate rotationCodes
  invFun := rotate inverseCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alpha : Equiv.Perm (Fin 34) where
  toFun := lookup alphaCodes
  invFun := lookup alphaCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Literal cyclic orders and half-edges of the fourteen-vertex cubic piece. -/
def piece : OpenTangleData (Fin 14) (Fin 34) (Fin 8) where
  interiorVert i := vertex (.inl i)
  boundaryVert i := vertex (.inr i)
  interiorAlpha := alpha
  interiorAlpha_involutive := by decide +kernel
  interiorAlpha_fixfree := by decide +kernel
  rho := rho
  vert_rho := by decide +kernel
  interior_no_self_loops := by decide +kernel
  outer := .inr 0

@[simp] theorem piece_vertex (d : Dart) : piece.vertOf d = vertex d := by
  cases d <;> rfl

/-- Each original cubic vertex retains all three incident darts. -/
theorem cubic (v : Fin 14) : ∃ a b c : Dart,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ d, vertex d = v ↔ d = a ∨ d = b ∨ d = c := by
  let a : Dart := index.symm (lookup "ABCDFIJLOPRVZ^" v)
  refine ⟨a, rho a, rho (rho a), ?_⟩
  revert v
  decide +kernel

/-- The table retains the literal reference darts, including every cyclic
vertex rotation, internal edge, and adjacent face label. -/
theorem reference_geometry :
    Function.Injective referenceDart ∧
      (∀ d, referenceDart (rho d) = DiamondConfigurations.table004.map.node (referenceDart d)) ∧
      (∀ i, referenceDart (.inl (alpha i)) =
        DiamondConfigurations.table004.map.edge (referenceDart (.inl i))) ∧
      (∀ d, left d = DiamondConfigurations.vertex004 (referenceDart d) ∧
        right d = DiamondConfigurations.vertex004
          (DiamondConfigurations.table004.map.edge (referenceDart d))) := by
  decide +kernel

private theorem edge_faces : ∀ i : Fin 34,
    left (.inl (alpha i)) = right (.inl i) ∧
      right (.inl (alpha i)) = left (.inl i) := by
  decide +kernel

private theorem face_adjacent : ∀ d : Dart, graph.Adj (left d) (right d) := by
  decide +kernel

/-- Distinct incident edges share one face; their other two faces are adjacent. -/
private theorem incident_faces : ∀ d e : Dart, vertex d = vertex e → d ≠ e →
    (left d = left e ∧ graph.Adj (right d) (right e)) ∨
    (left d = right e ∧ graph.Adj (right d) (left e)) ∨
    (right d = left e ∧ graph.Adj (left d) (right e)) ∨
    (right d = right e ∧ graph.Adj (left d) (left e)) := by
  decide +kernel

def referenceColour (k : graph.Coloring Color) (d : Dart) : Color :=
  k (left d) + k (right d)

theorem referenceColour_proper (k : graph.Coloring Color) {d e : Dart}
    (hv : vertex d = vertex e) (hne : d ≠ e) :
    referenceColour k d ≠ referenceColour k e := by
  intro h
  change k (left d) + k (right d) = k (left e) + k (right e) at h
  rcases incident_faces d e hv hne with ⟨he, ha⟩ | ⟨he, ha⟩ | ⟨he, ha⟩ | ⟨he, ha⟩
  · rw [he] at h
    exact k.valid ha (add_left_cancel h)
  · rw [he, add_comm (k (left e))] at h
    exact k.valid ha (add_left_cancel h)
  · rw [he, add_comm (k (left d))] at h
    exact k.valid ha (add_left_cancel h)
  · rw [he] at h
    exact k.valid ha (add_right_cancel h)

/-- Reuse the common exact identification of the two Klein palettes. -/
abbrev palette := PhysicalKempeBoundary.palette

def colouring (k : graph.Coloring Color) :
    Dart → Mettapedia.GraphTheory.FourColor.Color := fun d => palette (referenceColour k d)

/-- Colourings reconstruct on actual darts, respecting every internal edge and vertex. -/
theorem colouring_valid (k : graph.Coloring Color) :
    OpenTangleClosedWitness.IsColor piece (colouring k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply congrArg palette
    change k (left (.inl (alpha i))) + k (right (.inl (alpha i))) =
      k (left (.inl i)) + k (right (.inl i))
    rw [(edge_faces i).1, (edge_faces i).2, add_comm]
  · intro d e hv hn h
    exact referenceColour_proper k (by simpa using hv) hn (palette.injective h)
  · intro d h
    have hz : referenceColour k d = 0 := palette.injective h
    exact k.valid (face_adjacent d) (Color.add_eq_zero_iff.mp hz)

/-- Boundary extraction commutes with the graph-to-tangle reconstruction. -/
theorem boundary_reference (k : graph.Coloring Color) :
    (List.finRange 8).map (fun i => referenceColour k (.inr i)) =
      trace (boundary.map k) := by
  change _ = trace [k 4, k 5, k 6, k 7, k 0, k 1, k 2, k 3]
  simp only [trace_cons, List.cons_append, List.nil_append, pairmap_cons, pairmap_nil]
  simp only [List.finRange_succ, List.map_cons]
  change [k 5 + k 4, k 6 + k 5, k 7 + k 6, k 0 + k 7,
    k 1 + k 0, k 2 + k 1, k 3 + k 2, k 4 + k 3] = _
  simp only [add_comm]

theorem boundary_colouring (k : graph.Coloring Color) :
    (List.finRange 8).map (fun i => colouring k (.inr i)) =
      (trace (boundary.map k)).map palette := by
  rw [← boundary_reference, List.map_map]
  rfl


noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin 8)) (h : DiamondCoupledWiring.Rotation.Separated O)

/-- Colouring the actual two-vertex wiring permits reconstruction of the
fourteen-vertex piece. The selected exterior may be recoloured, but remains
one whole witness shared by all eight ports. -/
theorem colorable_of_wiring
    (hc : GoertzelV24TwoEdgeCutMinimality.RotationSystemTaitColorable
      (DiamondCoupledWiring.Rotation.closed O h))
    (hclosed : KempeClosed (OpenTangleKempeRepair.Trace O (Equiv.refl _))) :
    GoertzelV24TwoEdgeCutMinimality.RotationSystemTaitColorable
      (O.composeRotationSystem piece (Equiv.refl _)) := by
  obtain ⟨k, hk⟩ := (DiamondCoupledWiring.Rotation.colorable_iff O h).mp hc
  obtain ⟨et, ht, l, hl, he⟩ := DiamondCoupledWiring.repair k _ hclosed hk
  obtain ⟨c, rfl⟩ := (DiamondConfigurations.reducibilityTrace004 et).mp ht
  have hm (i : Fin 8) : l (.inr i) = colouring c (.inr i) := by
    exact List.map_inj_left.mp (he.trans (boundary_colouring c).symm) i (List.mem_finRange i)
  obtain ⟨c', hc', _⟩ := OpenTangleClosedWitness.glueOpen O piece (Equiv.refl _)
    l (colouring c) hl (colouring_valid c) hm
  exact ⟨c', hc'⟩

omit [DecidableEq V] in
/-- The two displayed closed graphs differ by twelve vertices, counting
the two introduced vertices. Ambient class preservation is separate. -/
theorem vertex_decrease : Fintype.card (V ⊕ Fin 2) + 12 = Fintype.card (V ⊕ Fin 14) := by
  simp only [Fintype.card_sum, Fintype.card_fin]

end
end FourColor.JointDiamondPatch.Tangle
