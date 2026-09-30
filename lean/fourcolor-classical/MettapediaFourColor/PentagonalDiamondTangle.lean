import MettapediaFourColor.DiamondProfileReducibility
import MettapediaFourColor.ConfigurationTable
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness

/-!
# The pentagonal diamond as an actual open cubic piece

The twelve vertices, fifteen internal edges and six ordered half-edges form
the dual of reference configuration 1. Face differences reconstruct genuine
cubic colourings and commute exactly with the shared boundary observation.
The integrated joint-profile theorem supplies repair; no new colouring
certificate is introduced for this representation.
-/

namespace FourColor.PentagonalDiamondPatch.Tangle

open ConfigurationTable
open Color KempeBoundarySplit

abbrev graph := DiamondConfigurations.graph001
abbrev boundary := DiamondConfigurations.boundary001.reverse
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition
open Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

abbrev Dart := Fin 30 ⊕ Fin 6

def index : Dart ≃ Fin 36 where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr i => ⟨30 + i.val, by omega⟩
  invFun i := if h : i.val < 30 then .inl ⟨i.val, h⟩
    else .inr ⟨i.val - 30, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertexCodes : String := "AABBCCCDDEEEFFGGHHIIIJJJKKKLLLABDFGH"
def rotationCodes : String := "_A`CFGEaHKLJbMPcdQTUSWXVZ[Y]^\\BDINOR"
def inverseCodes : String := "B_D`GEFIaLJKNbcORdUSTXVW[YZ^\\]ACHMPQ"
def leftCodes : String := "JFJAGJAGBHGBHCDHIEIHDIGHIJGIEJEFABCD"
def rightCodes : String := "EJFJJAGAGGBHBHHCDIHDIGHIJGIEJIFABCDE"
def alphaCodes : String := "]CBFZDHGKWIMLPTNU\\XOQ[JS^EVRAY"

def vertex (d : Dart) : Fin 12 := lookup vertexCodes (index d)
def left (d : Dart) : Fin 10 := lookup leftCodes (index d)
def right (d : Dart) : Fin 10 := lookup rightCodes (index d)

def rotate (s : String) (d : Dart) : Dart :=
  index.symm (lookup s (index d))

def rho : Equiv.Perm Dart where
  toFun := rotate rotationCodes
  invFun := rotate inverseCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alpha : Equiv.Perm (Fin 30) where
  toFun := lookup alphaCodes
  invFun := lookup alphaCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Literal cyclic orders and half-edges of the twelve-vertex cubic piece. -/
def piece : OpenTangleData (Fin 12) (Fin 30) (Fin 6) where
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
theorem cubic (v : Fin 12) : ∃ a b c : Dart,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ d, vertex d = v ↔ d = a ∨ d = b ∨ d = c := by
  let a : Dart := index.symm (lookup "A`EaJbOQSVY\\" v)
  refine ⟨a, rho a, rho (rho a), ?_⟩
  revert v
  decide +kernel

private theorem edge_faces : ∀ i : Fin 30,
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

/-- The four reference colours identified with the tangle's Klein palette. -/
def palette : Color ↪ Mettapedia.GraphTheory.FourColor.Color where
  toFun
    | .c0 => 0
    | .c1 => Mettapedia.GraphTheory.FourColor.red
    | .c2 => Mettapedia.GraphTheory.FourColor.blue
    | .c3 => Mettapedia.GraphTheory.FourColor.purple
  inj' := by decide +kernel

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
    (List.finRange 6).map (fun i => referenceColour k (.inr i)) =
      trace (boundary.map k) := by
  change _ = trace [k 4, k 5, k 0, k 1, k 2, k 3]
  rw [trace_cons]
  rfl

theorem boundary_colouring (k : graph.Coloring Color) :
    (List.finRange 6).map (fun i => colouring k (.inr i)) =
      (trace (boundary.map k)).map palette := by
  rw [← boundary_reference, List.map_map]
  rfl

/-- Reuse the integrated joint-profile proof of the reference diamond. -/
theorem repair : Repairs (GraphTrace graph boundary) 6 := by
  intro et hlen hzero hsum Q hQ hold
  obtain ⟨es, hs, ho⟩ := DiamondProfileReducibility.repair001 et hlen hzero hsum Q hQ hold
  exact ⟨es, (DiamondConfigurations.reducibilityTrace001 es).mp hs, ho⟩

theorem compatible_colouring {Q : List Color → Prop} (hQ : KempeClosed Q)
    (et : List Color) (hlen : et.length = 6) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : Q et) :
    ∃ k : graph.Coloring Color, Q (trace (boundary.map k)) := by
  obtain ⟨es, ⟨k, rfl⟩, hk⟩ := repair et hlen hzero hsum Q hQ hold
  exact ⟨k, hk⟩

end FourColor.PentagonalDiamondPatch.Tangle
