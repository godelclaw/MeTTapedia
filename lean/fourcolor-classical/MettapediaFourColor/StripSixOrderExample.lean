import MettapediaFourColor.StripSixDetachment
import MettapediaFourColor.StripSixPhaseChoice
import MettapediaFourColor.GraphTriangulationEuler
import MettapediaFourColor.PatchBoundaryGluing

/-! # A fixed pair order fails, while silent detachment reconstructs

A triangulated sphere realizes the original joint branch but admits no
source extension after any zero/one phase followed by any one/three phase.
A silent zero/three switch instead detaches a two/three component. The
shared detachment theorem reconstructs a whole colouring in two steps.
The short-cycle census remains independent program evidence.
-/

namespace FourColor.StripSixOrderExample

open Color SimpleGraph StripResponseSummary
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
set_option maxRecDepth 10000

def star : Fin 41 → List (Fin 41) := ![[1,40,10,32,30,29,17,22],[0,22,13,20,2,38,40],[1,20,12,3,38],[2,12,23,24,4,35,38],[3,24,5,36,35],[4,24,21,27,6,36],[5,27,7,33,36],[6,27,31,26,8,33],[7,26,9,37,34,33],[8,26,32,10,39,37],[0,40,39,9,32],[19,26,31,21,24,23],[2,20,16,23,3],[1,22,25,15,20],[18,29,30,26,28],[13,25,18,28,16,20],[12,20,15,28,19,23],[0,29,18,25,22],[14,28,15,25,17,29],[11,23,16,28,26],[1,13,15,16,12,2],[5,24,11,31,27],[0,17,25,13,1],[3,12,16,19,11,24],[3,23,11,21,5,4],[13,22,17,18,15],[7,31,11,19,28,14,30,32,9,8],[5,21,31,7,6],[14,26,19,16,15,18],[0,30,14,18,17],[0,32,26,14,29],[7,27,21,11,26],[0,10,9,26,30],[6,7,8,34,36],[8,37,35,36,33],[3,4,36,34,37,39,38],[4,5,6,33,34,35],[8,9,39,35,34],[1,2,3,35,39,40],[9,10,40,38,35,37],[0,1,38,39,10]]
theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel

def ambient : SimpleGraph (Fin 41) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel ambient.Adj := by unfold ambient; infer_instance

def rows : GraphRotationRows.Rows ambient := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : ambient.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
def faceStep (p : Fin 41 × Fin 41) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u, (star u).all (fun v => decide
    (faceStep (faceStep (faceStep (u,v))) = (u,v))) = true := by decide +kernel

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  intro d
  apply Dart.ext
  change faceStep (faceStep (faceStep d.toProd)) = d.toProd
  exact of_decide_eq_true (List.all_eq_true.mp (face_check d.fst) d.snd d.adj)

def tour : List (Fin 41) := [0,1,2,3,4,5,6,7,8,9,10,32,26,11,19,16,12,20,13,15,18,14,28,14,29,17,22,25,22,17,29,30,29,14,18,15,13,20,12,23,24,21,27,31,27,21,24,23,12,16,19,11,26,32,10,39,35,34,33,36,33,34,37,34,35,38,40,38,35,39,10,9,8,7,6,5,4,3,2,1,0]
theorem tour_chain : tour.IsChain ambient.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 41, v ∈ tour := by decide +kernel

theorem connected : ambient.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 41) : ambient.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card ambient.Dart = 234 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin, dart_count])

theorem degree_eq (v : Fin 41) : ambient.degree v = (star v).length := by
  have same : ambient.degree v =
      @SimpleGraph.degree (Fin 41) ambient v (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 41) ambient v) (Subsingleton.elim _ _)
  exact same.trans (rows.degree v)

theorem minimum_degree (v : Fin 41) : 5 ≤ ambient.degree v := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 41, 5 ≤ (star v).length) v

theorem maximum_degree (v : Fin 41) : ambient.degree v ≤ 10 := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 41, (star v).length ≤ 10) v

def neighbours : Fin 33 → List (Fin 33) := ![[1,10,17,22,29,30,32],[0,2,13,20,22],[1,3,12,20],[2,4,12,23,24],[3,5,24],[4,6,21,24,27],[5,7,27],[6,8,26,27,31],[7,9,26],[8,10,26,32],[0,9,32],[19,21,23,24,26,31],[2,3,16,20,23],[1,15,20,22,25],[18,26,28,29,30],[13,16,18,20,25,28],[12,15,19,20,23,28],[0,18,22,25,29],[14,15,17,25,28,29],[11,16,23,26,28],[1,2,12,13,15,16],[5,11,24,27,31],[0,1,13,17,25],[3,11,12,16,19,24],[3,4,5,11,21,23],[13,15,17,18,22],[7,8,9,11,14,19,28,30,31,32],[5,6,7,21,31],[14,15,16,18,19,26],[0,14,17,18,30],[0,14,26,29,32],[7,11,21,26,27],[0,9,10,26,30]]
theorem neighbours_symm : ∀ u v, v ∈ neighbours u → u ∈ neighbours v := by decide +kernel
theorem neighbours_loopless : ∀ v, v ∉ neighbours v := by decide +kernel

def exterior : SimpleGraph (Fin 33) where
  Adj u v := v ∈ neighbours u
  symm := ⟨neighbours_symm⟩
  loopless := ⟨neighbours_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def includeExterior (v : Fin 33) : Fin 41 := v.castAdd 8
theorem exterior_adj : ∀ u v, exterior.Adj u v ↔
    ambient.Adj (includeExterior u) (includeExterior v) := by decide +kernel

def port (i : Fin 11) : Fin 33 := i.castLE (by decide)
def sourceVertex (v : Fin 19) : Fin 41 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 41)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 33) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    ambient.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel
theorem source_injective : Function.Injective sourceVertex := by decide +kernel
theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 41,
    ambient.Adj (i.natAdd 33) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (i.natAdd 11) j ∧
        sourceVertex j = v := by decide +kernel
theorem boundary_aligned : ∀ i, sourceVertex (StripResponseSummary.port i) =
    includeExterior (port i) := by decide +kernel

theorem face_data : ∀ a b c, (a,b,c) ∈ StripSixBarrierGeometry.triangles →
    ambient.Adj (sourceVertex a) (sourceVertex b) ∧
    ambient.Adj (sourceVertex b) (sourceVertex c) ∧
    ambient.Adj (sourceVertex c) (sourceVertex a) ∧
    faceStep (sourceVertex a,sourceVertex b) = (sourceVertex b,sourceVertex c) ∧
    faceStep (sourceVertex b,sourceVertex c) = (sourceVertex c,sourceVertex a) ∧
    faceStep (sourceVertex c,sourceVertex a) = (sourceVertex a,sourceVertex b) := by
  decide +kernel

def patch : StripSixBarrierGeometry.Patch rotation where
  point := sourceVertex
  injective := source_injective
  adjacent := source_edges
  facial := by
    intro a b c h
    obtain ⟨ab,bc,ca,hab,hbc,hca⟩ := face_data a b c h
    refine ⟨ab,bc,ca,?_,?_,?_⟩
    · apply Dart.ext; exact hab
    · apply Dart.ext; exact hbc
    · apply Dart.ext; exact hca

def exteriorEmbedding : exterior ↪g ambient where
  toFun := includeExterior
  inj' := by intro u v h; exact Fin.ext (congrArg (fun x : Fin 41 => x.val) h)
  map_rel_iff' := fun {_ _} => (exterior_adj _ _).symm

def reading : StripSixBarrierGeometry.ExteriorReading patch exterior where
  embedding := exteriorEmbedding
  outside := by
    intro w i hi h
    change includeExterior w = sourceVertex i at h
    have shape : ∀ i : Fin 19, 11 ≤ i.val → 33 ≤ (sourceVertex i).val := by decide +kernel
    have eq := congrArg (fun x : Fin 41 => x.val) h
    have bound := shape i hi
    change w.val = (sourceVertex i).val at eq
    omega
  ports := port
  boundary := fun i => (boundary_aligned i).symm


def values : Fin 4 → Fin 33 → Color
  | 0 => ![c0,c1,c0,c3,c2,c3,c1,c2,c1,c3,c1,c2,c2,c0,c1,c1,c0,c1,c3,c3,c3,c1,c3,c1,c0,c2,c0,c0,c2,c2,c3,c3,c2]
  | 1 => ![c0,c1,c0,c3,c2,c3,c1,c2,c0,c3,c1,c2,c2,c0,c0,c1,c0,c1,c3,c3,c3,c1,c3,c1,c0,c2,c1,c0,c2,c2,c3,c3,c2]
  | 2 => ![c1,c0,c1,c3,c2,c3,c0,c2,c1,c3,c0,c2,c2,c1,c1,c0,c1,c0,c3,c3,c3,c0,c3,c0,c1,c2,c0,c1,c2,c2,c3,c3,c2]
  | 3 => ![c1,c0,c1,c3,c2,c3,c0,c2,c0,c3,c0,c2,c2,c1,c0,c0,c1,c0,c3,c3,c3,c0,c3,c0,c1,c2,c1,c1,c2,c2,c3,c3,c2]
theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel
def state (s : Fin 4) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
theorem initial_form : ∀ i, state 0 (port i) = StripSixConnection.input true i := by decide +kernel
theorem missing_colour : ∀ v, exterior.Adj (port 1) v → state 0 v ≠ c2 := by decide +kernel
theorem port_edges : ∀ i j, TriangleStripAnchors.input0099.graph.Adj
    (StripResponseSummary.port i) (StripResponseSummary.port j) → exterior.Adj (port i) (port j) := by
  decide +kernel

def firstChain : List (Fin 33) := [1,0,10,0,17,0,1,2,1,13,15,16,23,24,21,27,6,27,21,24,23,16,15,13,1]
theorem first_checked : (1 : Fin 33) ∈ firstChain ∧
    firstChain.IsChain exterior.Adj ∧
    (∀ x ∈ firstChain, state 0 x = c0 ∨ state 0 x = c1) ∧
    (∀ x ∈ firstChain, ∀ y, exterior.Adj x y →
      (state 0 y = c0 ∨ state 0 y = c1) → y ∈ firstChain) := by decide +kernel
def first : KempeSeparatedChains.Certificate (state 0) c0 c1 :=
  ⟨firstChain,1,first_checked.1,first_checked.2.1,
    first_checked.2.2.1,first_checked.2.2.2⟩

def eightChain : List (Fin 33) := [8,26,14,26,8]
theorem eight_checked : (8 : Fin 33) ∈ eightChain ∧
    eightChain.IsChain exterior.Adj ∧
    (∀ x ∈ eightChain, state 0 x = c0 ∨ state 0 x = c1) ∧
    (∀ x ∈ eightChain, ∀ y, exterior.Adj x y →
      (state 0 y = c0 ∨ state 0 y = c1) → y ∈ eightChain) := by decide +kernel
def eight : KempeSeparatedChains.Certificate (state 0) c0 c1 :=
  ⟨eightChain,8,eight_checked.1,eight_checked.2.1,
    eight_checked.2.2.1,eight_checked.2.2.2⟩

def jointChain : List (Fin 33) := [7,26,11,24,4,24,11,26,28,16,12,2,12,16,28,26,32,0,29,0,32,26,7,27,7]
theorem joint_checked : (7 : Fin 33) ∈ jointChain ∧
    jointChain.IsChain exterior.Adj ∧
    (∀ x ∈ jointChain, state 0 x = c0 ∨ state 0 x = c2) ∧
    (∀ x ∈ jointChain, ∀ y, exterior.Adj x y →
      (state 0 y = c0 ∨ state 0 y = c2) → y ∈ jointChain) := by decide +kernel
def joint : KempeSeparatedChains.Certificate (state 0) c0 c2 :=
  ⟨jointChain,7,joint_checked.1,joint_checked.2.1,
    joint_checked.2.2.1,joint_checked.2.2.2⟩

def hiddenChain : List (Fin 33) := [18]
theorem hidden_checked : (18 : Fin 33) ∈ hiddenChain ∧
    hiddenChain.IsChain exterior.Adj ∧
    (∀ x ∈ hiddenChain, state 0 x = c3 ∨ state 0 x = c0) ∧
    (∀ x ∈ hiddenChain, ∀ y, exterior.Adj x y →
      (state 0 y = c3 ∨ state 0 y = c0) → y ∈ hiddenChain) := by decide +kernel
def hidden : KempeSeparatedChains.Certificate (state 0) c3 c0 :=
  ⟨hiddenChain,18,hidden_checked.1,hidden_checked.2.1,
    hidden_checked.2.2.1,hidden_checked.2.2.2⟩

theorem original_joint : port 1 ∈ (state 0).kempeComponentSet c0 c1 first.component ∧
    port 6 ∈ (state 0).kempeComponentSet c0 c1 first.component ∧
    port 8 ∉ (state 0).kempeComponentSet c0 c1 first.component ∧
    port 2 ∈ (state 0).kempeComponentSet c0 c2 joint.component ∧
    port 4 ∈ (state 0).kempeComponentSet c0 c2 joint.component ∧
    port 7 ∈ (state 0).kempeComponentSet c0 c2 joint.component := by
  simp only [first.component_mem,joint.component_mem]
  decide +kernel

def firstRoot : Fin 2 → Fin 33 := ![1,8]
def firstLabel : Fin 33 → Fin 2 := ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
def firstRoute : Fin 33 → List (Fin 33) := ![[1,0],[1],[1,2],[3],[4],[5],[1,13,15,16,23,24,21,27,6],[7],[8],[9],[1,0,10],[11],[12],[1,13],[8,26,14],[1,13,15],[1,13,15,16],[1,0,17],[18],[19],[20],[1,13,15,16,23,24,21],[22],[1,13,15,16,23],[1,13,15,16,23,24],[25],[8,26],[1,13,15,16,23,24,21,27],[28],[29],[30],[31],[32]]
def ActiveFirst (v : Fin 33) : Prop := state 0 v = c0 ∨ state 0 v = c1
instance (v) : Decidable (ActiveFirst v) := inferInstanceAs (Decidable (_ ∨ _))
theorem first_nonempty : ∀ v, firstRoute v ≠ [] := by decide +kernel
theorem first_chain : ∀ v, (firstRoute v).IsChain exterior.Adj := by decide +kernel
theorem first_head : ∀ v, ActiveFirst v →
    (firstRoute v).head (first_nonempty v) = firstRoot (firstLabel v) := by decide +kernel
theorem first_last : ∀ v, (firstRoute v).getLast (first_nonempty v) = v := by decide +kernel
theorem first_active : ∀ v, ActiveFirst v → ∀ x ∈ firstRoute v, ActiveFirst x := by decide +kernel

theorem first_routes (v) (h : ActiveFirst v) :
    ∃ p : exterior.Walk (firstRoot (firstLabel v)) v,
      ∀ x ∈ p.support, ActiveFirst x := by
  let p := (Walk.ofSupport (firstRoute v) (first_nonempty v) (first_chain v)).copy
    (first_head v h) (first_last v)
  exact ⟨p,fun x hx => first_active v h x (by simpa [p] using hx)⟩

def index (a b : Bool) : Fin 4 := if a then (if b then 3 else 2) else (if b then 1 else 0)
theorem first_values : ∀ a b v,
    (if (![a,b] : Fin 2 → Bool) (firstLabel v) then Equiv.swap c0 c1 (state 0 v)
      else state 0 v) = state (index a b) v := by
  intro a b
  cases a <;> cases b <;> decide +kernel

/-- Every first phase, including all silent switches, has one of these four
whole-exterior colourings. Only original bichromatic routes are used. -/
theorem first_normal_form (D : exterior.Coloring Color)
    (phase : Relation.ReflTransGen (KempePairHistory.Step c0 c1) (state 0) D) :
    ∃ s : Fin 4, D = state s := by
  obtain ⟨bits,values⟩ := KempePhaseBoundary.phase (state 0) D c0 c1 id
    firstRoot firstLabel first_routes phase
  have bits_eq : bits = ![bits 0,bits 1] := by funext i; fin_cases i <;> rfl
  refine ⟨index (bits 0) (bits 1),?_⟩
  ext v
  exact (values v).trans (by simpa only [id_eq,← bits_eq] using first_values (bits 0) (bits 1) v)

def roots : Fin 4 → Fin 4 → Fin 33
  | 0 => ![1,3,5,8]
  | 1 => ![1,3,0,0]
  | 2 => ![0,8,0,0]
  | 3 => ![0,0,0,0]
def label : Fin 4 → Fin 11 → Fin 4
  | 0 => ![0,0,0,1,0,2,2,0,3,3,3]
  | 1 => ![0,0,0,1,0,1,1,0,0,1,1]
  | 2 => ![0,0,0,0,0,0,0,0,1,1,0]
  | 3 => ![0,0,0,0,0,0,0,0,0,0,0]
def routeList : Fin 4 → Fin 11 → List (Fin 33)
  | 0 => ![[0],[1],[2],[3],[4],[5],[5,6],[7],[8],[8,9],[8,9,10]]
  | 1 => ![[0],[1],[2],[3],[4],[3,23,19,26,31,21,5],[3,23,19,26,31,21,5,6],[7],[8],[3,23,19,26,9],[3,23,19,26,9,10]]
  | 2 => ![[0],[1],[0,22,13,20,2],[0,22,13,20,2,3],[4],[0,22,13,20,2,3,24,5],[6],[7],[8],[8,9],[10]]
  | 3 => ![[0],[1],[0,22,13,20,2],[0,22,13,20,2,3],[4],[0,30,26,31,27,5],[6],[7],[8],[0,30,26,9],[10]]
def Active (s : Fin 4) (v : Fin 33) : Prop := state s v = c1 ∨ state s v = c3
instance (s v) : Decidable (Active s v) := inferInstanceAs (Decidable (_ ∨ _))
theorem route_nonempty : ∀ s j, routeList s j ≠ [] := by decide +kernel
theorem route_chain : ∀ s j, (routeList s j).IsChain exterior.Adj := by decide +kernel
theorem route_head : ∀ s j, Active s (port j) →
    (routeList s j).head (route_nonempty s j) = roots s (label s j) := by decide +kernel
theorem route_last : ∀ s j,
    (routeList s j).getLast (route_nonempty s j) = port j := by decide +kernel
theorem route_active : ∀ s j, Active s (port j) →
    ∀ x ∈ routeList s j, Active s x := by decide +kernel

theorem routes (s : Fin 4) (j : Fin 11) (h : Active s (port j)) :
    ∃ p : exterior.Walk (roots s (label s j)) (port j),
      ∀ x ∈ p.support, Active s x := by
  let p := (Walk.ofSupport (routeList s j) (route_nonempty s j) (route_chain s j)).copy
    (route_head s j h) (route_last s j)
  exact ⟨p,fun x hx => route_active s j h x (by simpa [p] using hx)⟩

def word (s : Fin 4) (bits : Fin 4 → Bool) : Boundary :=
  fun j => if bits (label s j) then Equiv.swap c1 c3 (state s (port j)) else state s (port j)

theorem terminal_empty : ∀ s (a b c d : Bool), ¬ ∃ x y, r5 (word s ![a,b,c,d]) x y := by
  intro s a b c d
  fin_cases s <;> cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

/-- No finite continuation in the second pair extends any first-phase state. -/
theorem no_second_phase (s : Fin 4) (D : exterior.Coloring Color)
    (phase : Relation.ReflTransGen (KempePairHistory.Step c1 c3) (state s) D) :
    ¬ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) := by
  rintro ⟨k,agree⟩
  obtain ⟨bits,values⟩ := KempePhaseBoundary.phase (state s) D c1 c3 port
    (roots s) (label s) (routes s) phase
  have valid := StripResponseSummary.valid_of_colouring (word s bits) k
    (fun i => (agree i).trans (values i))
  have bits_eq : bits = ![bits 0,bits 1,bits 2,bits 3] := by funext i; fin_cases i <;> rfl
  have terminal := (StripResponseSummary.terminal_iff _).mpr ⟨_,valid⟩
  rw [bits_eq] at terminal
  exact terminal_empty s _ _ _ _ terminal

/-- The pair order fails for arbitrary phase lengths and arbitrary choices
of components, not only for one prescribed repair recipe. -/
theorem no_two_phases (D E : exterior.Coloring Color)
    (first : Relation.ReflTransGen (KempePairHistory.Step c0 c1) (state 0) D)
    (second : Relation.ReflTransGen (KempePairHistory.Step c1 c3) D E) :
    ¬ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = E (port i) := by
  obtain ⟨s,rfl⟩ := first_normal_form D first
  exact no_second_phase s E second

def detachedChain : List (Fin 33) := [7,31,11,19,28,19,11,31,7]
theorem detachment_checked :
    detachedChain.IsChain exterior.Adj ∧ port 7 ∈ detachedChain ∧
    (∀ x ∈ detachedChain, state 0 x = c3 ∨ state 0 x = c2) ∧
    (∀ i, port i ∈ detachedChain ↔ i = 7) ∧
    (∀ x ∈ detachedChain, x ∉ hiddenChain) ∧
    (∀ i, port i ∉ hiddenChain) ∧
    (∀ x ∈ detachedChain, ∀ y, y ∉ detachedChain → exterior.Adj x y →
      (state 0 y = c3 ∨ state 0 y = c2) → y ∈ hiddenChain) ∧
    (∀ x ∈ detachedChain, ∀ y ∈ hiddenChain, exterior.Adj x y → state 0 y ≠ c0) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem source : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) := by
  obtain ⟨connected,at7,active,boundary_only,apart,silent,exits,no_entry⟩ := detachment_checked
  exact StripSixDetachment.repair (state 0) port port_edges true initial_form hidden.component
    (fun i h => silent i ((hidden.component_mem _).mp h))
    detachedChain connected at7 active boundary_only
    (fun x hx h => apart x hx ((hidden.component_mem _).mp h))
    (fun x hx y hy edge active => (hidden.component_mem _).mpr (exits x hx y hy edge active))
    (fun x hx y hy edge => no_entry x hx y ((hidden.component_mem _).mp hy) edge)

def sourceHom : TriangleStripAnchors.input0099.graph →g ambient := ⟨sourceVertex,fun h =>
  source_edges _ _ h⟩
def interior : Set (Fin 19) := {v | 11 ≤ v.val}
def exteriorVertex (v : Fin 41) : Fin 33 := ⟨v.val % 33,Nat.mod_lt _ (by decide)⟩

instance (v : Fin 41) : Decidable (v ∈ sourceHom '' interior) :=
  inferInstanceAs (Decidable (∃ a : Fin 19, 11 ≤ a.val ∧ sourceVertex a = v))

theorem source_core (i : Fin 8) : sourceHom (i.natAdd 11) = i.natAdd 33 := by
  simp [sourceHom,sourceVertex]

theorem no_capture (a : Fin 19) (ha : a ∉ interior) : sourceHom a ∉ sourceHom '' interior := by
  rintro ⟨i,hi,heq⟩
  exact ha ((source_injective heq) ▸ hi)

theorem covers (i : Fin 19) (hi : i ∈ interior) (v : Fin 41)
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
  obtain ⟨D,h,two,k,agree⟩ := source
  exact ⟨D,h,two,assemble D k agree⟩

end FourColor.StripSixOrderExample
