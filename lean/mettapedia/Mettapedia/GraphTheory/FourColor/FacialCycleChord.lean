import Mettapedia.GraphTheory.FourColor.FacialCycleTangle
import Mettapedia.GraphTheory.FourColor.CyclicPortChordExclusion
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType

/-!
# Chordlessness derived from short incident faces

An alternating facial boundary whose port faces are pentagons or hexagons
has no ambient chord. Both oriented port families have three-step face
arcs; a short face would propagate a chord to a smaller cyclic gap. The
result constructs the induced-cycle input to the physical slab theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.FacialCycleChord

open InducedCycleLayer FacialCycleLayer SimpleGraphDartRotation ZigzagRing
open GoertzelV24FaceOrbitIncidence GoertzelV24HexFaceRungType
open PhysicalForkCodeFaces CyclicPortChordExclusion

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
variable {k : ℕ} [NeZero k] {C : Frame G k} {hk : 2 ≤ k}
  {hG : G.IsRegularOfDegree 3} {data : Data G}

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable {R : Finset (OrbitFace (RS data))}
variable (h : BoundsFaces C hk hG data R) (hC : Cubic3 (RS data))
  (ha : AlternatingDegrees C data R)

include h hC ha

theorem incoming_rotation (i : Fin k) :
    (RS data).rho (C.star hk hG (.inl i) 0) = C.star hk hG (.inl i) 1 ∧
    (RS data).rho (C.star hk hG (.inl i) 1) = C.star hk hG (.inl i) 2 ∧
    (RS data).rho (C.star hk hG (.inl i) 2) = C.star hk hG (.inl i) 0 := by
  exact ((h.rotation_at hC (.inl i)).resolve_right (fun hh => by
    have := ha.1 i; omega)).2

theorem outgoing_rotation (i : Fin k) :
    (RS data).rho (C.star hk hG (.inr i) 0) = C.star hk hG (.inr i) 2 ∧
    (RS data).rho (C.star hk hG (.inr i) 1) = C.star hk hG (.inr i) 0 ∧
    (RS data).rho (C.star hk hG (.inr i) 2) = C.star hk hG (.inr i) 1 := by
  exact ((h.rotation_at hC (.inr i)).resolve_left (fun hh => by
    have := ha.2 i; omega)).2

def incomingArcs : Arcs (RS data).phi (RS data).alpha k where
  port i := C.star hk hG (.inl i) 0
  first i := C.star hk hG (.inl i) 1
  second i := C.star hk hG (.inr i) 1
  start i := by
    rw [RotationSystem.phi_apply, (RS data).alpha_involutive]
    exact (incoming_rotation h hC ha i).1
  middle i := by
    change (RS data).rho (C.star hk hG (.inl i) 1).symm = _
    rw [star_forward_symm]
    exact (outgoing_rotation h hC ha i).2.2
  finish i := by
    change (RS data).rho (C.star hk hG (.inr i) 1).symm = _
    rw [star_forward_symm]
    exact (incoming_rotation h hC ha (i + 1)).2.2
  disjoint i j := by
    intro he
    have hh := congrArg Prod.snd (C.star_injective hk hG (a₁ := (.inl i, 0)) (a₂ := (.inl j, 1)) he)
    norm_num at hh

/-- Reversing the output indices makes its face arcs advance by one too. -/
def outgoingArcs : Arcs (RS data).phi (RS data).alpha k where
  port i := C.star hk hG (.inr (-i)) 0
  first i := C.star hk hG (.inr (-i)) 2
  second i := C.star hk hG (.inl (-i)) 2
  start i := by
    rw [RotationSystem.phi_apply, (RS data).alpha_involutive]
    exact (outgoing_rotation h hC ha (-i)).1
  middle i := by
    change (RS data).rho (C.star hk hG (.inr (-i)) 2).symm = _
    rw [star_backward_symm]
    exact (incoming_rotation h hC ha (-i)).2.1
  finish i := by
    change (RS data).rho (C.star hk hG (.inl (-i)) 2).symm = _
    rw [star_backward_symm]
    simpa only [prev, neg_add, sub_eq_add_neg] using
      (outgoing_rotation h hC ha (-i - 1)).2.1
  disjoint i j := by
    intro he
    have hh := congrArg Prod.snd (C.star_injective hk hG (a₁ := (.inr (-i), 0)) (a₂ := (.inr (-j), 2)) he)
    exact (by decide : (0 : Fin 3) ≠ 2) hh

omit h hC ha [G.LocallyFinite] in
theorem arcs_no_chord (A : Arcs (RS data).phi (RS data).alpha k)
    (hs : ∀ i, ((RS data).faceOrbit (A.port i)).card = 5 ∨
      ((RS data).faceOrbit (A.port i)).card = 6) (i j : Fin k) :
    (RS data).alpha (A.port i) ≠ A.port j := by
  apply A.no_chord (RS data).alpha_involutive (RS data).alpha_fixfree
  · intro a
    have hp := (faceOrbit_isCycleOn (RS data) (A.port a)).pow_card_apply
      ((RS data).mem_faceOrbit_self (A.port a))
    rcases hs a with hh | hh
    · exact Or.inl (hh ▸ hp)
    · exact Or.inr (hh ▸ hp)
  · intro a hp
    have hdvd := (faceOrbit_isCycleOn (RS data) (A.port a)).pow_apply_eq
      ((RS data).mem_faceOrbit_self (A.port a)) |>.mp hp
    rcases hs a with hh | hh <;> norm_num [hh] at hdvd

variable (hs : ∀ v, ((RS data).faceOrbit (C.star hk hG v 0)).card = 5 ∨
  ((RS data).faceOrbit (C.star hk hG v 0)).card = 6)

include hs

theorem alpha_port_ne_port (v w : Vtx k) :
    (RS data).alpha (C.star hk hG v 0) ≠ C.star hk hG w 0 := by
  have hi (i j : Fin k) := arcs_no_chord (incomingArcs h hC ha)
    (fun a => hs (.inl a)) i j
  have ho (i j : Fin k) := arcs_no_chord (outgoingArcs h hC ha)
    (fun a => hs (.inr (-a))) (-i) (-j)
  have cross (i j : Fin k) :
      (RS data).alpha (C.star hk hG (.inl i) 0) ≠ C.star hk hG (.inr j) 0 := by
    intro he
    have hin := (h.port_faces hC (.inl i)).2.mpr (ha.1 i)
    change dartOrbitFace (RS data) ((RS data).alpha (C.star hk hG (.inl i) 0)) ∈ R at hin
    rw [he] at hin
    have hh := (h.port_faces hC (.inr j)).1.mp hin
    have := ha.2 j
    omega
  rcases v with i | i <;> rcases w with j | j
  · exact hi i j
  · exact cross i j
  · intro he
    exact cross j i (by rw [← he, (RS data).alpha_involutive])
  · simpa only [outgoingArcs, neg_neg] using ho i j

/-- Every third edge leaves the original row. No connectedness of the
strict interior is needed for this local short-face argument. -/
theorem port_off_row (v w : Vtx k) : C.port hk hG v ≠ C.vertex w := by
  intro he
  obtain ⟨j, hj⟩ := C.star_surjective_at hk hG w (C.star hk hG v 0).symm he
  fin_cases j
  · exact alpha_port_ne_port h hC ha hs v w hj.symm
  · have hh := congrArg SimpleGraph.Dart.symm hj
    change (C.star hk hG w 1).symm = (C.star hk hG v 0).symm.symm at hh
    rw [star_forward_symm] at hh
    simp only [SimpleGraph.Dart.symm_symm] at hh
    have hh' := congrArg Prod.snd (C.star_injective hk hG (a₁ := (next k w, 2)) (a₂ := (v, 0)) hh)
    exact (by decide : (2 : Fin 3) ≠ 0) hh'
  · have hh := congrArg SimpleGraph.Dart.symm hj
    change (C.star hk hG w 2).symm = (C.star hk hG v 0).symm.symm at hh
    rw [star_backward_symm] at hh
    simp only [SimpleGraph.Dart.symm_symm] at hh
    have hh' := congrArg Prod.snd (C.star_injective hk hG (a₁ := (prev k w, 1)) (a₂ := (v, 0)) hh)
    norm_num at hh'

/-- The induced-cycle object is a conclusion of the face geometry. -/
def toCycle : Cycle G k where
  toFrame := C
  induced u v hv := by
    rcases (C.adjacent_iff hk hG u (C.vertex v)).mp hv with he | he | he
    · exact (port_off_row h hC ha hs u v he.symm).elim
    · exact Or.inl (C.injective he)
    · exact Or.inr (C.injective he)

omit hs in
/-- In a map with no short port faces, an ambient chord forces a face of
length at least seven at the row. The exceptional geometry is localized. -/
theorem chord_forces_long_face
    (hmin : ∀ v, 5 ≤ ((RS data).faceOrbit (C.star hk hG v 0)).card)
    {u v : Vtx k} (hadj : G.Adj (C.vertex u) (C.vertex v))
    (hn : v ≠ next k u) (hp : v ≠ prev k u) :
    ∃ w, 7 ≤ ((RS data).faceOrbit (C.star hk hG w 0)).card := by
  by_contra! hh
  have hshort : ∀ w, ((RS data).faceOrbit (C.star hk hG w 0)).card = 5 ∨
      ((RS data).faceOrbit (C.star hk hG w 0)).card = 6 := by
    intro w
    have := hmin w
    have := hh w
    omega
  rcases (toCycle h hC ha hshort).induced u v hadj with he | he
  · exact hn he
  · exact hp he

/-- The constructed cycle gives the same open-face transport theorem,
now with chordlessness proved from the local face sizes. -/
theorem face_conjugate :
    (FacialCycleTangle.coordinate (toCycle h hC ha hs) hk hG data).permCongr (face k) =
      OpenTangleMarkedFace.openPhi
        (FacialCycleTangle.tangle (toCycle h hC ha hs) hk hG data) :=
  FacialCycleTangle.face_conjugate (C := toCycle h hC ha hs) h hC ha

open GoertzelV24TwoEdgeCutMinimality GoertzelV24PrimalCycleFacialBond

variable (ambient : BridgelessSphericalCubicMapData (RS data))
  (hR : ((orbitFaceDualGraph data).induce (R : Set _)).Connected)
  (hRc : ((orbitFaceDualGraph data).induce (R : Set _)ᶜ).Connected)

/-- A physical layer from an alternating facial cycle and short port faces,
without assuming chordlessness or the attachment conditions. -/
def toSlab : TubeSlab.ZigzagSlab (RS data) k (Interior data R) :=
  h.toSlab (C := toCycle h
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) ha hs) ambient hR hRc ha

def colouringEquiv :
    TubeSlab.SideColoring (RS data) (toSlab h ha hs ambient hR hRc).inner' ≃
      (toSlab h ha hs ambient hR hRc).CompatibleColorings :=
  (toSlab h ha hs ambient hR hRc).colouringEquiv

end
end Mettapedia.GraphTheory.FourColor.FacialCycleChord
