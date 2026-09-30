import Mettapedia.GraphTheory.FourColor.PaddedCycleCapFaceTraversal
import Mettapedia.GraphTheory.FourColor.PaddedCycleCapSource
import Mettapedia.GraphTheory.FourColor.Compositional.ShortFacePortExclusion

/-!
# The final ports of a face-traced cap leave its vertex set

An injective vertex trace gives injective dart coordinates. The cap's actual
three-step boundary arcs then consume the width-independent short-face law:
no port edge can return to another cap port. Internal reversals and complete
cubic stars exclude every other return into the cap.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal

open Equiv Equiv.Perm PhysicalForkCodeFaces

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (m : ℕ) [NeZero m] (root : RS.D)
  (hC : Cubic3 RS) (hf : FaceLengths RS m root)

include hC in
omit [NeZero m] in
private theorem slot_injective (d : RS.D) :
    Function.Injective (fun s : Fin 3 => (RS.rho ^ s.val) d) := by
  have htwo : RS.rho (RS.rho d) ≠ d := by
    intro he
    have hh := congrArg RS.rho he
    rw [hC.cube] at hh
    exact hC.moves d hh.symm
  intro s t he
  fin_cases s <;> fin_cases t <;>
    simp only [pow_succ', pow_zero, Perm.mul_apply, Perm.one_apply] at he
  · rfl
  · exact (hC.moves d he.symm).elim
  · exact (htwo he.symm).elim
  · exact (hC.moves d he).elim
  · rfl
  · exact (hC.moves (RS.rho d) he.symm).elim
  · exact (htwo he).elim
  · exact (hC.moves (RS.rho d) he).elim
  · rfl

omit [NeZero m] in
theorem atStar_vertex (p : Position m) :
    RS.vertOf (atStar RS m root p) = vertex RS m root (p.1,p.2.1) := by
  rcases p with ⟨i,v,s⟩
  fin_cases s <;> simp [atStar, vertex, pow_succ', RS.vert_rho]

include hC in
omit [NeZero m] in
theorem atStar_injective (hv : Function.Injective (vertex RS m root)) :
    Function.Injective (atStar RS m root) := by
  rintro ⟨i,v,s⟩ ⟨j,w,t⟩ he
  have hh := congrArg RS.vertOf he
  rw [atStar_vertex, atStar_vertex] at hh
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (hv hh)
  have hs := slot_injective RS hC (base RS m root i v) he
  cases hs
  rfl

include hC in
theorem dart_injective (hv : Function.Injective (vertex RS m root)) :
    Function.Injective (dart RS m root) :=
  (atStar_injective RS m root hC hv).comp (coordinates m).injective

include hC in
omit [NeZero m] in
/-- The three interpreted slots exhaust the actual ambient cubic star. -/
theorem atStar_surjective_at (v : Vertex m) (d : RS.D)
    (hd : RS.vertOf d = vertex RS m root v) :
    ∃ s : Fin 3, atStar RS m root (v.1,v.2,s) = d := by
  rcases hC.fiber (base RS m root v.1 v.2) d hd with he | he | he
  · exact ⟨0,he.symm⟩
  · exact ⟨1,he.symm⟩
  · exact ⟨2, by simpa [atStar, pow_succ'] using he.symm⟩

def port (j : Fin (m*2)) : RS.D :=
  dart RS m root (.inr (.inr ((portIndex m).symm j)))

theorem boundary_dart_false (i : Fin m) :
    dart RS m root (.inr (.inr (i,false))) =
      RS.rho (RS.rho (outerFirst RS m root i)) := by
  simp [dart, position, atStar, base, pow_succ']

theorem boundary_dart_true (i : Fin m) :
    dart RS m root (.inr (.inr (i,true))) =
      RS.rho (RS.rho (outerLast RS m root i)) := by
  simp [dart, position, atStar, base, pow_succ']

include hC hf in
theorem boundary_arc_false (i : Fin m) :
    (RS.phi ^ 2) (RS.rho (dart RS m root (.inr (.inr (i,false))))) =
      dart RS m root (.inr (.inr (i-1,true))) := by
  have he := congrArg RS.alpha (outer_closing RS m root hC hf (i-1))
  have hprev : RS.alpha (RS.rho (RS.rho (outerIncoming RS m root i))) =
      RS.rho (outerLast RS m root (i-1)) := by
    simpa [base, sub_add_cancel, RS.alpha_involutive] using he.symm
  rw [boundary_dart_false RS m root, boundary_dart_true RS m root, hC.cube]
  change RS.rho (RS.alpha (RS.rho (RS.alpha (outerFirst RS m root i)))) = _
  rw [show RS.alpha (outerFirst RS m root i) = RS.rho (outerIncoming RS m root i) by
    simp [outerFirst, RS.alpha_involutive], hprev]

include hC hf in
theorem boundary_arc_true (i : Fin m) :
    (RS.phi ^ 2) (RS.rho (dart RS m root (.inr (.inr (i,true))))) =
      dart RS m root (.inr (.inr (i,false))) := by
  have he := congrArg RS.alpha (outer_middle_edge RS m root hC hf i)
  have hback : RS.alpha (RS.rho (RS.rho (outerMiddle RS m root i))) =
      RS.rho (outerFirst RS m root i) := by
    simpa only [RS.alpha_involutive] using he.symm
  rw [boundary_dart_true RS m root, boundary_dart_false RS m root, hC.cube]
  change RS.rho (RS.alpha (RS.rho (RS.alpha (outerLast RS m root i)))) = _
  rw [show RS.alpha (outerLast RS m root i) = RS.rho (outerMiddle RS m root i) by
    simp [outerLast, RS.alpha_involutive], hback]

include hC hf in
theorem port_arc (j : Fin (m*2)) :
    (RS.phi ^ 2) (RS.rho (port RS m root j)) = port RS m root (j-1) := by
  obtain ⟨⟨i,b⟩,rfl⟩ := (portIndex m).surjective j
  cases b
  · have he : portIndex m (i-1,true) = portIndex m (i,false)-1 := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [sub_add_cancel] using portIndex_true_next m (i-1)
    rw [← he]
    simpa only [port, Equiv.symm_apply_apply] using boundary_arc_false RS m root hC hf i
  · have he : portIndex m (i,false) = portIndex m (i,true)-1 :=
      eq_sub_iff_add_eq.mpr (portIndex_false_next m i)
    rw [← he]
    simpa only [port, Equiv.symm_apply_apply] using boundary_arc_true RS m root hC hf i

include hC in
theorem port_ne_interior (hv : Function.Injective (vertex RS m root))
    (i : Fin (m*2)) (d : Interior m) :
    port RS m root i ≠ dart RS m root (.inl d) := by
  intro he
  have hh := dart_injective RS m root hC hv he
  cases hh

include hC hf in
/-- The two-step predecessor of a boundary port is internal. Its identity
is proved on the actual dart carrier, before any exposure assumption. -/
theorem port_two_apart (hv : Function.Injective (vertex RS m root))
    (i j : Fin (m*2)) : (RS.phi ^ 2) (port RS m root i) ≠ port RS m root j := by
  intro he
  obtain ⟨⟨k,b⟩,rfl⟩ := (portIndex m).surjective j
  cases b
  · have hback : (RS.phi ^ 2) (dart RS m root (.inl (k,10,true))) =
        port RS m root (portIndex m (k,false)) := by
      have hh := boundary_arc_true RS m root hC hf k
      simpa [port, boundary_dart_true RS m root,
        dart_true RS m root hC, hC.cube] using hh
    exact port_ne_interior RS m root hC hv i _ ((RS.phi ^ 2).injective (he.trans hback.symm))
  · have hback : (RS.phi ^ 2) (dart RS m root (.inl (k+1,8,true))) =
        port RS m root (portIndex m (k,true)) := by
      have hh := boundary_arc_false RS m root hC hf (k+1)
      simpa [port, boundary_dart_false RS m root,
        dart_true RS m root hC, hC.cube] using hh
    exact port_ne_interior RS m root hC hv i _ ((RS.phi ^ 2).injective (he.trans hback.symm))

def BoundaryShortFaces : Prop :=
  ∀ i, (RS.faceOrbit (port RS m root i)).card = 5 ∨
    (RS.faceOrbit (port RS m root i)).card = 6

include hC hf in
/-- Short actual seam faces rule out all internal port connections. -/
theorem no_port_edge (hv : Function.Injective (vertex RS m root))
    (hs : BoundaryShortFaces RS m root) (i j : Fin (m*2)) :
    RS.alpha (port RS m root i) ≠ port RS m root j :=
  Compositional.ShortFacePortExclusion.no_port_edge RS (port RS m root)
    (port_arc RS m root hC hf) (port_two_apart RS m root hC hf hv) hs i j

include hC hf in
/-- Every final port leaves the entire traced cap vertex set. No induced
patch or explicit boundary-exposure hypothesis is supplied. -/
theorem port_outside (hv : Function.Injective (vertex RS m root))
    (hs : BoundaryShortFaces RS m root) (i : Fin (m*2)) (v : Vertex m) :
    RS.vertOf (RS.alpha (port RS m root i)) ≠ vertex RS m root v := by
  intro he
  obtain ⟨s,hd⟩ := atStar_surjective_at RS m root hC v _ he
  have hh : dart RS m root (star m (v.1,v.2,s)) = RS.alpha (port RS m root i) := by
    simpa only [dart, position_star] using hd
  cases hdart : star m (v.1,v.2,s) with
  | inl d =>
    rw [hdart] at hh
    have hr := congrArg RS.alpha hh
    rw [← dart_alpha RS m root hC hf, RS.alpha_involutive] at hr
    exact port_ne_interior RS m root hC hv i _ hr.symm
  | inr b =>
    rw [hdart] at hh
    cases b with
    | inl e => exact nomatch e
    | inr b =>
      have hr : RS.alpha (port RS m root i) = port RS m root (portIndex m b) := by
        simpa only [port, Equiv.symm_apply_apply] using hh.symm
      exact no_port_edge RS m root hC hf hv hs i _ hr

end Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal
