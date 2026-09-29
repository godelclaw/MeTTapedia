import MettapediaFourColor.PentagonalLobePatch
import MettapediaFourColor.ConfigurationTable
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness

/-!
# The pentagonal lobe's literal open tangle

The sixteen vertices, twenty-one internal edges, six boundary half-edges
and cyclic orders are retained explicitly. Face differences turn every
colouring of the dual disk into a genuine tangle colouring, with exactly
the ordered six-port trace used by the repair theorem.

The final consumer glues the repaired patch to an actual exterior whose
boundary relation is Kempe-closed. Embedded recognition, deriving that
closure from exterior geometry, and strict reduction are separate tasks.
-/

namespace FourColor.PentagonalLobePatch.Tangle

open ConfigurationTable
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition
open Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

abbrev Dart := Fin 42 ⊕ Fin 6

def index : Dart ≃ Fin 48 where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr i => ⟨42 + i.val, by omega⟩
  invFun i := if h : i.val < 42 then .inl ⟨i.val, h⟩
    else .inr ⟨i.val - 42, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertexCodes : String := "ABACADBEBFCGDHEHEIFGFJGKHLIJIMJNKOLMMPNONPKCDLPO"
def rotationCodes : String := "CGEKAmIOBUlTFYQNH]JWS\\LaPnR_[dVikhZe^o`pgfXDMcjb"
def inverseCodes : String := "EIAlCMBQGSDWmPHYO[ULJ_TkNc]VRe\\gXpn^djib`oaKFZfh"
def leftCodes : String := "GHHCCGGIIHHBDGGJJIKHIKKBDJLIJLLKKAEJELFKLFABCDEF"
def rightCodes : String := "HGCHGCIGHIBHGDJGIJHKKIBKJDILLJKLAKJELEKFFLBCDEFA"
def alphaCodes : String := "BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badcfehgji"

def vertex (d : Dart) : Fin 16 := lookup vertexCodes (index d)
def left (d : Dart) : Fin 12 := lookup leftCodes (index d)
def right (d : Dart) : Fin 12 := lookup rightCodes (index d)

def rotate (s : String) (d : Dart) : Dart :=
  index.symm (lookup s (index d))

def rho : Equiv.Perm Dart where
  toFun := rotate rotationCodes
  invFun := rotate inverseCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alpha : Equiv.Perm (Fin 42) where
  toFun := lookup alphaCodes
  invFun := lookup alphaCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Literal cyclic orders and half-edges of the sixteen-vertex cubic piece. -/
def piece : OpenTangleData (Fin 16) (Fin 42) (Fin 6) where
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
theorem cubic (v : Fin 16) : ∃ a b c : Dart,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ d, vertex d = v ↔ d = a ∨ d = b ∨ d = c := by
  let a : Dart := index.symm (lookup "ABDFHJLNRVXZ^`bf" v)
  refine ⟨a, rho a, rho (rho a), ?_⟩
  revert v
  decide +kernel

private theorem edge_faces : ∀ i : Fin 42,
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
  change _ = trace [k 0, k 1, k 2, k 3, k 4, k 5]
  rw [trace_cons]
  rfl

theorem boundary_colouring (k : graph.Coloring Color) :
    (List.finRange 6).map (fun i => colouring k (.inr i)) =
      (trace (boundary.map k)).map palette := by
  rw [← boundary_reference, List.map_map]
  rfl

section Exterior

variable {W J L R : Type*}
  (outside : TwoSidedOpenTangleData W J L R) (seam : Fin 6 ≃ L ⊕ R)

/-- The entire exterior assignment is retained behind the observed boundary. -/
def ExteriorTrace (et : List Color) : Prop :=
  ∃ r : outside.Coloring, outside.IsTaitColoring r ∧
    (List.finRange 6).map (fun i => r (.inr (seam i))) = et.map palette

/-- Joint repair supplies genuine assignments that agree at every sewn port. -/
theorem compatible_darts
    (hclosed : KempeClosed (ExteriorTrace outside seam))
    (et : List Color) (hlen : et.length = 6) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : ExteriorTrace outside seam et) :
    ∃ k : graph.Coloring Color, ∃ r : outside.Coloring,
      outside.IsTaitColoring r ∧
        ∀ i, colouring k (.inr i) = r (.inr (seam i)) := by
  obtain ⟨k, r, hr, he⟩ := compatible_colouring hclosed et hlen hzero hsum hold
  refine ⟨k, r, hr, ?_⟩
  have hmaps := (boundary_colouring k).trans he.symm
  intro i
  exact List.map_inj_left.mp hmaps i (List.mem_finRange i)

variable [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The repaired joint relation has an actual closed-map colouring as its consumer. -/
theorem sewn_colorable
    (hclosed : KempeClosed (ExteriorTrace outside seam))
    (et : List Color) (hlen : et.length = 6) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : ExteriorTrace outside seam et) :
    ∃ c : (OpenTangleClosedWitness.sewn piece outside seam).EdgeColoring
        Mettapedia.GraphTheory.FourColor.Color,
      (OpenTangleClosedWitness.sewn piece outside seam).IsTaitEdgeColoring c := by
  obtain ⟨k, r, hr, hm⟩ := compatible_darts outside seam hclosed et hlen hzero hsum hold
  obtain ⟨c, hc, _⟩ := OpenTangleClosedWitness.glue piece outside seam
    (colouring k) r (colouring_valid k) hr hm
  exact ⟨c, hc⟩

end Exterior

end FourColor.PentagonalLobePatch.Tangle
