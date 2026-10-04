import MettapediaFourColor.StripSixRelease
import MettapediaFourColor.GraphTriangulationEuler
import MettapediaFourColor.PatchBoundaryGluing

/-! # A fixed continuation fails and a neighbour release repairs it

The actual 32-vertex sphere retains the D0099 core and has degrees five
through seven. Its original component hits port six but not eight, and
its zero/two component joins ports seven, two and four. The prescribed
zero/one then zero/three-at-six history fails to extend. Releasing port
three instead consumes the uniform old-neighbour law and reconstructs.
The short-cycle census is separate program evidence.
-/

namespace FourColor.StripSixReleaseExample

open Color SimpleGraph StripResponseSummary
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
set_option maxRecDepth 10000

def star : Fin 32 → List (Fin 32) := ![[1,31,10,13,23],[0,23,2,29,31],[1,23,12,15,3,29],[2,15,22,4,26,29],[3,22,5,27,26],[4,22,18,14,6,27],[5,14,11,7,24,27],[6,11,20,8,24],[7,20,9,28,25,24],[8,20,16,13,10,30,28],[0,31,30,9,13],[6,14,17,20,7],[2,23,13,21,19,15],[0,10,9,16,21,12,23],[5,18,17,11,6],[2,12,19,18,22,3],[9,20,17,21,13],[11,14,18,19,21,16,20],[5,22,15,19,17,14],[12,21,17,18,15],[7,11,17,16,9,8],[12,13,16,17,19],[3,15,18,5,4],[0,13,12,2,1],[6,7,8,25,27],[8,28,26,27,24],[3,4,27,25,28,30,29],[4,5,6,24,25,26],[8,9,30,26,25],[1,2,3,26,30,31],[9,10,31,29,26,28],[0,1,29,30,10]]
theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel

def ambient : SimpleGraph (Fin 32) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel ambient.Adj := by unfold ambient; infer_instance

def rows : GraphRotationRows.Rows ambient := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : ambient.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
def faceStep (p : Fin 32 × Fin 32) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u, (star u).all (fun v => decide
    (faceStep (faceStep (faceStep (u,v))) = (u,v))) = true := by decide +kernel

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  intro d
  apply Dart.ext
  change faceStep (faceStep (faceStep d.toProd)) = d.toProd
  exact of_decide_eq_true (List.all_eq_true.mp (face_check d.fst) d.snd d.adj)

def tour : List (Fin 32) := [0,1,2,3,4,5,6,7,8,9,10,13,12,15,18,14,11,17,16,20,16,21,19,21,16,17,11,14,18,22,18,15,12,23,12,13,10,30,26,25,24,27,24,25,28,25,26,29,31,29,26,30,10,9,8,7,6,5,4,3,2,1,0]
theorem tour_chain : tour.IsChain ambient.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 32, v ∈ tour := by decide +kernel

theorem connected : ambient.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 32) : ambient.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card ambient.Dart = 180 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin, dart_count])

theorem degree_eq (v : Fin 32) : ambient.degree v = (star v).length := by
  have same : ambient.degree v =
      @SimpleGraph.degree (Fin 32) ambient v (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 32) ambient v) (Subsingleton.elim _ _)
  exact same.trans (rows.degree v)

theorem minimum_degree (v : Fin 32) : 5 ≤ ambient.degree v := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 32, 5 ≤ (star v).length) v

theorem maximum_degree (v : Fin 32) : ambient.degree v ≤ 7 := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 32, (star v).length ≤ 7) v

def neighbours : Fin 24 → List (Fin 24) := ![[1,10,13,23],[0,2,23],[1,3,12,15,23],[2,4,15,22],[3,5,22],[4,6,14,18,22],[5,7,11,14],[6,8,11,20],[7,9,20],[8,10,13,16,20],[0,9,13],[6,7,14,17,20],[2,13,15,19,21,23],[0,9,10,12,16,21,23],[5,6,11,17,18],[2,3,12,18,19,22],[9,13,17,20,21],[11,14,16,18,19,20,21],[5,14,15,17,19,22],[12,15,17,18,21],[7,8,9,11,16,17],[12,13,16,17,19],[3,4,5,15,18],[0,1,2,12,13]]
theorem neighbours_symm : ∀ u v, v ∈ neighbours u → u ∈ neighbours v := by decide +kernel
theorem neighbours_loopless : ∀ v, v ∉ neighbours v := by decide +kernel

def exterior : SimpleGraph (Fin 24) where
  Adj u v := v ∈ neighbours u
  symm := ⟨neighbours_symm⟩
  loopless := ⟨neighbours_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def includeExterior (v : Fin 24) : Fin 32 := v.castAdd 8
theorem exterior_adj : ∀ u v, exterior.Adj u v ↔
    ambient.Adj (includeExterior u) (includeExterior v) := by decide +kernel

def port (i : Fin 11) : Fin 24 := i.castLE (by decide)
def sourceVertex (v : Fin 19) : Fin 32 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 32)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 24) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    ambient.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel
theorem source_injective : Function.Injective sourceVertex := by decide +kernel
theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 32,
    ambient.Adj (i.natAdd 24) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (i.natAdd 11) j ∧
        sourceVertex j = v := by decide +kernel
theorem boundary_aligned : ∀ i, sourceVertex (StripResponseSummary.port i) =
    includeExterior (port i) := by decide +kernel

def values : Fin 3 → Fin 24 → Color
  | 0 => ![c0,c1,c0,c3,c2,c3,c1,c2,c1,c3,c1,c3,c1,c2,c0,c2,c1,c2,c1,c0,c0,c3,c0,c3]
  | 1 => ![c1,c0,c1,c3,c2,c3,c0,c2,c1,c3,c0,c3,c0,c2,c1,c2,c1,c2,c0,c1,c0,c3,c1,c3]
  | 2 => ![c1,c0,c1,c3,c2,c0,c3,c2,c1,c0,c3,c0,c0,c2,c1,c2,c1,c2,c3,c1,c3,c3,c1,c3]
theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel
def state (s : Fin 3) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
theorem initial_form : ∀ i, state 0 (port i) = StripSixConnection.input true i := by decide +kernel
theorem port_edges : ∀ i j, TriangleStripAnchors.input0099.graph.Adj
    (StripResponseSummary.port i) (StripResponseSummary.port j) → exterior.Adj (port i) (port j) := by
  decide +kernel
theorem port_injective : Function.Injective port := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h)

def firstChain : List (Fin 24) := [1,0,10,0,1,2,12,19,18,14,6,14,18,22,18,19,12,2,1]
theorem first_checked : (1 : Fin 24) ∈ firstChain ∧
    firstChain.IsChain exterior.Adj ∧
    (∀ x ∈ firstChain, state 0 x = c0 ∨ state 0 x = c1) ∧
    (∀ x ∈ firstChain, ∀ y, exterior.Adj x y →
      (state 0 y = c0 ∨ state 0 y = c1) → y ∈ firstChain) := by decide +kernel
def first : KempeSeparatedChains.Certificate (state 0) c0 c1 where
  vertices := firstChain
  root := 1
  root_mem := first_checked.1
  connected := first_checked.2.1
  active := first_checked.2.2.1
  closed := first_checked.2.2.2

def jointChain : List (Fin 24) := [7,20,17,14,17,19,15,2,15,22,4,22,15,19,17,20,7]
theorem joint_checked : (7 : Fin 24) ∈ jointChain ∧
    jointChain.IsChain exterior.Adj ∧
    (∀ x ∈ jointChain, state 0 x = c0 ∨ state 0 x = c2) ∧
    (∀ x ∈ jointChain, ∀ y, exterior.Adj x y →
      (state 0 y = c0 ∨ state 0 y = c2) → y ∈ jointChain) := by decide +kernel
def joint : KempeSeparatedChains.Certificate (state 0) c0 c2 where
  vertices := jointChain
  root := 7
  root_mem := joint_checked.1
  connected := joint_checked.2.1
  active := joint_checked.2.2.1
  closed := joint_checked.2.2.2

def failedChain : List (Fin 24) := [6,5,18,5,6,11,20,9,10,9,20,11,6]
theorem failed_checked : (6 : Fin 24) ∈ failedChain ∧
    failedChain.IsChain exterior.Adj ∧
    (∀ x ∈ failedChain, state 1 x = c0 ∨ state 1 x = c3) ∧
    (∀ x ∈ failedChain, ∀ y, exterior.Adj x y →
      (state 1 y = c0 ∨ state 1 y = c3) → y ∈ failedChain) := by decide +kernel
def failed : KempeSeparatedChains.Certificate (state 1) c0 c3 where
  vertices := failedChain
  root := 6
  root_mem := failed_checked.1
  connected := failed_checked.2.1
  active := failed_checked.2.2.1
  closed := failed_checked.2.2.2

theorem first_eq : first.swap = state 1 := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact (by decide +kernel : ∀ x : Fin 24,
    (if x ∈ firstChain then Equiv.swap c0 c1 (state 0 x) else state 0 x) = state 1 x) x

theorem failed_eq : failed.swap = state 2 := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact (by decide +kernel : ∀ x : Fin 24,
    (if x ∈ failedChain then Equiv.swap c0 c3 (state 1 x) else state 1 x) = state 2 x) x

theorem at_one : port 1 ∈ (state 0).kempeComponentSet c0 c1 first.component :=
  (first.component_mem _).mpr (by decide +kernel)
theorem at_six : port 6 ∈ (state 0).kempeComponentSet c0 c1 first.component :=
  (first.component_mem _).mpr (by decide +kernel)
theorem avoids_eight : port 8 ∉ (state 0).kempeComponentSet c0 c1 first.component := by
  rw [first.component_mem]
  decide +kernel

theorem joint_case : port 7 ∈ (state 0).kempeComponentSet c0 c2 joint.component ∧
    port 2 ∈ (state 0).kempeComponentSet c0 c2 joint.component ∧
    port 4 ∈ (state 0).kempeComponentSet c0 c2 joint.component := by
  simp only [joint.component_mem]
  decide +kernel

noncomputable def failedHistory : History (state 0) (state 2) :=
  .cons (first_eq ▸ first.step) (.cons (failed_eq ▸ failed.step) (.refl _))
theorem failed_length : failedHistory.length = 2 := rfl

def badBoundary (i : Fin 11) : Color := state 2 (port i)
theorem empty_terminal : ¬ ∃ a c, r5 badBoundary a c := by decide +kernel

theorem failed_nonextension : ¬ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
    ∀ i, k (StripResponseSummary.port i) = state 2 (port i) := by
  rintro ⟨k,hk⟩
  exact empty_terminal ((terminal_iff badBoundary).mpr
    ⟨_,valid_of_colouring badBoundary k hk⟩)

theorem exits : ∀ y, exterior.Adj (port 3) y → state 0 y = c0 →
    y ∈ (state 0).kempeComponentSet c0 c1 first.component := by
  intro y edge colour
  rw [first.component_mem]
  exact (by decide +kernel : ∀ y, exterior.Adj (port 3) y → state 0 y = c0 → y ∈ firstChain)
    y edge colour

theorem no_entry : ∀ y ∈ (state 0).kempeComponentSet c0 c1 first.component,
    exterior.Adj (port 3) y → state 0 y ≠ c1 := by
  intro y hy edge
  have member := (first.component_mem y).mp hy
  exact (by decide +kernel : ∀ y ∈ firstChain, exterior.Adj (port 3) y → state 0 y ≠ c1)
    y member edge

theorem source : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) :=
  StripSixRelease.repair (state 0) port port_edges initial_form first.component
    at_one at_six avoids_eight port_injective exits no_entry

def sourceHom : TriangleStripAnchors.input0099.graph →g ambient := ⟨sourceVertex,fun h =>
  source_edges _ _ h⟩
def interior : Set (Fin 19) := {v | 11 ≤ v.val}
def exteriorVertex (v : Fin 32) : Fin 24 := ⟨v.val % 24,Nat.mod_lt _ (by decide)⟩

instance (v : Fin 32) : Decidable (v ∈ sourceHom '' interior) :=
  inferInstanceAs (Decidable (∃ a : Fin 19, 11 ≤ a.val ∧ sourceVertex a = v))

theorem source_core (i : Fin 8) : sourceHom (i.natAdd 11) = i.natAdd 24 := by
  simp [sourceHom,sourceVertex]

theorem no_capture (a : Fin 19) (ha : a ∉ interior) : sourceHom a ∉ sourceHom '' interior := by
  rintro ⟨i,hi,heq⟩
  exact ha ((source_injective heq) ▸ hi)

theorem covers (i : Fin 19) (hi : i ∈ interior) (v : Fin 32)
    (edge : ambient.Adj (sourceHom i) v) :
    ∃ a, TriangleStripAnchors.input0099.graph.Adj i a ∧ sourceHom a = v := by
  revert hi edge
  refine Fin.addCases (m := 11) (n := 8)
    (motive := fun i => i ∈ interior → ambient.Adj (sourceHom i) v →
      ∃ a, TriangleStripAnchors.input0099.graph.Adj i a ∧ sourceHom a = v)
    (fun j hj _ => ?_) (fun j _ edge => ?_) i
  · have h : 11 ≤ j.val := hj
    omega
  · rw [source_core] at edge
    exact (core_stars j v).mp edge

theorem exterior_edges : ∀ v w,
    v ∉ sourceHom '' interior → w ∉ sourceHom '' interior → ambient.Adj v w →
      exterior.Adj (exteriorVertex v) (exteriorVertex w) := by decide +kernel
theorem boundary_position : ∀ i,
    exteriorVertex (sourceHom (StripResponseSummary.port i)) = port i := by decide +kernel
theorem exterior_position : ∀ v, exteriorVertex (includeExterior v) = v := by decide +kernel
theorem exterior_outside : ∀ v, includeExterior v ∉ sourceHom '' interior := by decide +kernel

/-- Every source witness fitting an actual exterior colours the whole sphere. -/
theorem assemble (D : exterior.Coloring Color)
    (k : TriangleStripAnchors.input0099.graph.Coloring Color)
    (agree : ∀ i, k (StripResponseSummary.port i) = D (port i)) :
    ∃ whole : ambient.Coloring Color, ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨whole,_,outside⟩ := PatchBoundaryGluing.reconstruct sourceHom interior
    source_injective.injOn no_capture covers k (fun v => D (exteriorVertex v))
    (fun hv hw edge => D.valid (exterior_edges _ _ hv hw edge)) (by
      intro a
      refine Fin.addCases (m := 11) (n := 8)
        (motive := fun a => a ∉ interior → k a = D (exteriorVertex (sourceHom a)))
        (fun i _ => ?_) (fun i hi => ?_) a
      · have eq : Fin.castAdd 8 i = StripResponseSummary.port i := by ext; rfl
        rw [eq,boundary_position]
        exact agree i
      · exact (hi (by change 11 ≤ 11 + i.val; omega)).elim)
  refine ⟨whole,fun v => ?_⟩
  rw [outside _ (exterior_outside v),exterior_position]

theorem reconstructed : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ whole : ambient.Coloring Color,
      ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨D,h,length,k,agree⟩ := source
  exact ⟨D,h,length,assemble D k agree⟩

end FourColor.StripSixReleaseExample
