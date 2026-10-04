import MettapediaFourColor.StripSixPhaseChoice
import MettapediaFourColor.GraphTriangulationEuler
import MettapediaFourColor.PatchBoundaryGluing

/-! # A blocked path and a successful paired-port choice

A 39-vertex triangulated sphere has the original joint branch, but its
first switch leaves both protective paths blocked. Switching at port three
then fails. The exact phase criterion selects the component through ports
five and six and reconstructs the whole colouring. A boundary-preserving extra first-phase switch blocks every subsequent
one/three phase. The short-cycle census is independent program evidence, not a hypothesis supplied by this module.
-/

namespace FourColor.StripSixPhaseExample

open Color SimpleGraph StripResponseSummary
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
set_option maxRecDepth 10000

def star : Fin 39 → List (Fin 39) := ![[1,38,10,18,15],[0,15,2,36,38],[1,15,12,29,3,36],[2,29,14,24,4,33,36],[3,24,5,34,33],[4,24,21,6,34],[5,21,30,7,31,34],[6,30,11,23,8,31],[7,23,9,35,32,31],[8,23,16,17,10,37,35],[0,38,37,9,17,18],[7,30,27,16,23],[2,15,25,26,22,29],[18,20,19,26,25],[3,29,22,19,20,24],[0,18,25,12,2,1],[9,23,11,27,17],[9,16,27,28,18,10],[0,10,17,28,20,13,25,15],[13,20,14,22,26],[13,18,28,24,14,19],[5,24,28,30,6],[12,26,19,14,29],[7,11,16,9,8],[3,14,20,28,21,5,4],[12,15,18,13,26],[12,25,13,19,22],[11,30,28,17,16],[17,27,30,21,24,20,18],[2,12,22,14,3],[6,21,28,27,11,7],[6,7,8,32,34],[8,35,33,34,31],[3,4,34,32,35,37,36],[4,5,6,31,32,33],[8,9,37,33,32],[1,2,3,33,37,38],[9,10,38,36,33,35],[0,1,36,37,10]]
theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel

def ambient : SimpleGraph (Fin 39) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel ambient.Adj := by unfold ambient; infer_instance

def rows : GraphRotationRows.Rows ambient := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : ambient.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
def faceStep (p : Fin 39 × Fin 39) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u, (star u).all (fun v => decide
    (faceStep (faceStep (faceStep (u,v))) = (u,v))) = true := by decide +kernel

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  intro d
  apply Dart.ext
  change faceStep (faceStep (faceStep d.toProd)) = d.toProd
  exact of_decide_eq_true (List.all_eq_true.mp (face_check d.fst) d.snd d.adj)

def tour : List (Fin 39) := [0,1,2,3,4,5,6,7,8,9,10,17,16,11,23,11,27,28,18,13,19,14,20,24,21,30,21,24,20,14,22,12,15,25,26,25,15,12,29,12,22,14,19,13,18,28,27,11,16,17,10,37,33,32,31,34,31,32,35,32,33,36,38,36,33,37,10,9,8,7,6,5,4,3,2,1,0]
theorem tour_chain : tour.IsChain ambient.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 39, v ∈ tour := by decide +kernel

theorem connected : ambient.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 39) : ambient.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card ambient.Dart = 222 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin, dart_count])

theorem degree_eq (v : Fin 39) : ambient.degree v = (star v).length := by
  have same : ambient.degree v =
      @SimpleGraph.degree (Fin 39) ambient v (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 39) ambient v) (Subsingleton.elim _ _)
  exact same.trans (rows.degree v)

theorem minimum_degree (v : Fin 39) : 5 ≤ ambient.degree v := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 39, 5 ≤ (star v).length) v

theorem maximum_degree (v : Fin 39) : ambient.degree v ≤ 8 := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 39, (star v).length ≤ 8) v

def neighbours : Fin 31 → List (Fin 31) := ![[1,10,15,18],[0,2,15],[1,3,12,15,29],[2,4,14,24,29],[3,5,24],[4,6,21,24],[5,7,21,30],[6,8,11,23,30],[7,9,23],[8,10,16,17,23],[0,9,17,18],[7,16,23,27,30],[2,15,22,25,26,29],[18,19,20,25,26],[3,19,20,22,24,29],[0,1,2,12,18,25],[9,11,17,23,27],[9,10,16,18,27,28],[0,10,13,15,17,20,25,28],[13,14,20,22,26],[13,14,18,19,24,28],[5,6,24,28,30],[12,14,19,26,29],[7,8,9,11,16],[3,4,5,14,20,21,28],[12,13,15,18,26],[12,13,19,22,25],[11,16,17,28,30],[17,18,20,21,24,27,30],[2,3,12,14,22],[6,7,11,21,27,28]]
theorem neighbours_symm : ∀ u v, v ∈ neighbours u → u ∈ neighbours v := by decide +kernel
theorem neighbours_loopless : ∀ v, v ∉ neighbours v := by decide +kernel

def exterior : SimpleGraph (Fin 31) where
  Adj u v := v ∈ neighbours u
  symm := ⟨neighbours_symm⟩
  loopless := ⟨neighbours_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def includeExterior (v : Fin 31) : Fin 39 := v.castAdd 8
theorem exterior_adj : ∀ u v, exterior.Adj u v ↔
    ambient.Adj (includeExterior u) (includeExterior v) := by decide +kernel

def port (i : Fin 11) : Fin 31 := i.castLE (by decide)
def sourceVertex (v : Fin 19) : Fin 39 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 39)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 31) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    ambient.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel
theorem source_injective : Function.Injective sourceVertex := by decide +kernel
theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 39,
    ambient.Adj (i.natAdd 31) v ↔ ∃ j : Fin 19,
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
  inj' := by intro u v h; exact Fin.ext (congrArg (fun x : Fin 39 => x.val) h)
  map_rel_iff' := fun {_ _} => (exterior_adj _ _).symm

def reading : StripSixBarrierGeometry.ExteriorReading patch exterior where
  embedding := exteriorEmbedding
  outside := by
    intro w i hi h
    change includeExterior w = sourceVertex i at h
    have shape : ∀ i : Fin 19, 11 ≤ i.val → 31 ≤ (sourceVertex i).val := by decide +kernel
    have eq := congrArg (fun x : Fin 39 => x.val) h
    have bound := shape i hi
    change w.val = (sourceVertex i).val at eq
    omega
  ports := port
  boundary := fun i => (boundary_aligned i).symm


def values : Fin 4 → Fin 31 → Color
  | 0 => ![c0,c1,c0,c3,c2,c3,c1,c2,c1,c3,c1,c3,c2,c3,c2,c3,c2,c0,c2,c0,c1,c2,c3,c0,c0,c0,c1,c1,c3,c1,c0]
  | 1 => ![c0,c1,c0,c3,c2,c3,c1,c2,c0,c3,c1,c3,c2,c3,c2,c3,c2,c0,c2,c0,c1,c2,c3,c1,c0,c0,c1,c1,c3,c1,c0]
  | 2 => ![c0,c1,c0,c1,c2,c3,c1,c2,c0,c1,c3,c1,c2,c1,c2,c3,c2,c0,c2,c0,c3,c2,c1,c3,c0,c0,c3,c3,c1,c3,c0]
  | 3 => ![c0,c1,c0,c3,c2,c3,c1,c2,c0,c3,c1,c3,c2,c3,c2,c3,c2,c0,c2,c1,c0,c2,c3,c1,c1,c1,c0,c1,c3,c1,c0]
theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel
def state (s : Fin 4) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
theorem initial_form : ∀ i, state 0 (port i) = StripSixConnection.input true i := by decide +kernel
theorem missing_colour : ∀ v, exterior.Adj (port 1) v → state 0 v ≠ c2 := by
  decide +kernel

theorem middle_form : ∀ i, state 1 (port i) = StripSixBarrierRepair.middle i := by decide +kernel
theorem port_edges : ∀ i j, TriangleStripAnchors.input0099.graph.Adj
    (StripResponseSummary.port i) (StripResponseSummary.port j) → exterior.Adj (port i) (port j) := by
  decide +kernel

def firstChain : List (Fin 31) := [1,0,10,17,27,30,6,30,27,17,10,0,1,2,29,2,1]
theorem first_checked : (1 : Fin 31) ∈ firstChain ∧
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

def jointChain : List (Fin 31) := [7,23,16,17,18,0,18,25,12,2,12,25,18,17,16,23,7,30,21,24,4,24,14,19,14,24,21,30,7]
theorem joint_checked : (7 : Fin 31) ∈ jointChain ∧
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

def eightChain : List (Fin 31) := [8,23,8]
theorem eight_checked : (8 : Fin 31) ∈ eightChain ∧
    eightChain.IsChain exterior.Adj ∧
    (∀ x ∈ eightChain, state 0 x = c0 ∨ state 0 x = c1) ∧
    (∀ x ∈ eightChain, ∀ y, exterior.Adj x y →
      (state 0 y = c0 ∨ state 0 y = c1) → y ∈ eightChain) := by decide +kernel
def eight : KempeSeparatedChains.Certificate (state 0) c0 c1 where
  vertices := eightChain
  root := 8
  root_mem := eight_checked.1
  connected := eight_checked.2.1
  active := eight_checked.2.2.1
  closed := eight_checked.2.2.2

def failedChain : List (Fin 31) := [3,29,22,26,13,20,28,27,11,23,9,10,9,23,11,27,28,20,13,26,22,29,3]
theorem failed_checked : (3 : Fin 31) ∈ failedChain ∧
    failedChain.IsChain exterior.Adj ∧
    (∀ x ∈ failedChain, state 1 x = c1 ∨ state 1 x = c3) ∧
    (∀ x ∈ failedChain, ∀ y, exterior.Adj x y →
      (state 1 y = c1 ∨ state 1 y = c3) → y ∈ failedChain) := by decide +kernel
def failed : KempeSeparatedChains.Certificate (state 1) c1 c3 where
  vertices := failedChain
  root := 3
  root_mem := failed_checked.1
  connected := failed_checked.2.1
  active := failed_checked.2.2.1
  closed := failed_checked.2.2.2

def pairedChain : List (Fin 31) := [6,5,6]
theorem paired_checked : (6 : Fin 31) ∈ pairedChain ∧
    pairedChain.IsChain exterior.Adj ∧
    (∀ x ∈ pairedChain, state 1 x = c1 ∨ state 1 x = c3) ∧
    (∀ x ∈ pairedChain, ∀ y, exterior.Adj x y →
      (state 1 y = c1 ∨ state 1 y = c3) → y ∈ pairedChain) := by decide +kernel
def paired : KempeSeparatedChains.Certificate (state 1) c1 c3 where
  vertices := pairedChain
  root := 6
  root_mem := paired_checked.1
  connected := paired_checked.2.1
  active := paired_checked.2.2.1
  closed := paired_checked.2.2.2

def postChain : List (Fin 31) := [2,12,25,18,0,18,17,16,17,18,25,12,2]
theorem post_checked : (2 : Fin 31) ∈ postChain ∧
    postChain.IsChain exterior.Adj ∧
    (∀ x ∈ postChain, state 1 x = c0 ∨ state 1 x = c2) ∧
    (∀ x ∈ postChain, ∀ y, exterior.Adj x y →
      (state 1 y = c0 ∨ state 1 y = c2) → y ∈ postChain) := by decide +kernel
def post : KempeSeparatedChains.Certificate (state 1) c0 c2 where
  vertices := postChain
  root := 2
  root_mem := post_checked.1
  connected := post_checked.2.1
  active := post_checked.2.2.1
  closed := post_checked.2.2.2


def hiddenChain : List (Fin 31) := [19,20,24,20,19,26,25,26,19]
theorem hidden_checked : (19 : Fin 31) ∈ hiddenChain ∧
    hiddenChain.IsChain exterior.Adj ∧
    (∀ x ∈ hiddenChain, state 1 x = c0 ∨ state 1 x = c1) ∧
    (∀ x ∈ hiddenChain, ∀ y, exterior.Adj x y →
      (state 1 y = c0 ∨ state 1 y = c1) → y ∈ hiddenChain) := by decide +kernel
def hidden : KempeSeparatedChains.Certificate (state 1) c0 c1 where
  vertices := hiddenChain
  root := 19
  root_mem := hidden_checked.1
  connected := hidden_checked.2.1
  active := hidden_checked.2.2.1
  closed := hidden_checked.2.2.2

def lockedChain : List (Fin 31) := [3,24,5,6,5,24,28,27,11,23,9,10,9,23,11,27,28,24,3,29,22,19,13,25,15,1,15,25,13,19,22,29,3]
theorem locked_checked : (3 : Fin 31) ∈ lockedChain ∧
    lockedChain.IsChain exterior.Adj ∧
    (∀ x ∈ lockedChain, state 3 x = c1 ∨ state 3 x = c3) ∧
    (∀ x ∈ lockedChain, ∀ y, exterior.Adj x y →
      (state 3 y = c1 ∨ state 3 y = c3) → y ∈ lockedChain) := by decide +kernel
def locked : KempeSeparatedChains.Certificate (state 3) c1 c3 where
  vertices := lockedChain
  root := 3
  root_mem := locked_checked.1
  connected := locked_checked.2.1
  active := locked_checked.2.2.1
  closed := locked_checked.2.2.2

theorem eight_eq : eight.swap = state 1 := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact (by decide +kernel : ∀ x : Fin 31,
    (if x ∈ eightChain then Equiv.swap c0 c1 (state 0 x) else state 0 x) = state 1 x) x

theorem failed_eq : failed.swap = state 2 := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact (by decide +kernel : ∀ x : Fin 31,
    (if x ∈ failedChain then Equiv.swap c1 c3 (state 1 x) else state 1 x) = state 2 x) x

theorem original_joint : port 1 ∈ (state 0).kempeComponentSet c0 c1 first.component ∧
    port 6 ∈ (state 0).kempeComponentSet c0 c1 first.component ∧
    port 8 ∉ (state 0).kempeComponentSet c0 c1 first.component ∧
    port 2 ∈ (state 0).kempeComponentSet c0 c2 joint.component ∧
    port 4 ∈ (state 0).kempeComponentSet c0 c2 joint.component ∧
    port 7 ∈ (state 0).kempeComponentSet c0 c2 joint.component := by
  simp only [first.component_mem,joint.component_mem]
  decide +kernel

theorem blocked : port 2 ∈ (state 1).kempeComponentSet c0 c2 post.component ∧
    port 4 ∉ (state 1).kempeComponentSet c0 c2 post.component ∧
    port 7 ∉ (state 1).kempeComponentSet c0 c2 post.component := by
  simp only [post.component_mem]
  decide +kernel

theorem no_protective_path (long : Bool)
    (p : exterior.Walk (reading.ports 2) (reading.ports (StripSixBarrierGeometry.targetPort long)))
    (active : ∀ x ∈ p.support, state 1 x = c0 ∨ state 1 x = c2) : False := by
  have reach {u v : Fin 31} (q : exterior.Walk u v) (hu : u ∈ postChain)
      (ha : ∀ x ∈ q.support, state 1 x = c0 ∨ state 1 x = c2) : v ∈ postChain := by
    induction q with
    | nil => exact hu
    | @cons u w v edge q ih =>
        have tailActive : ∀ x ∈ q.support, state 1 x = c0 ∨ state 1 x = c2 :=
          fun x hx => ha x (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr hx)
        exact ih (post_checked.2.2.2 u hu w edge (tailActive w q.start_mem_support)) tailActive
  have member := reach p (by decide +kernel) active
  have impossible : port (StripSixBarrierGeometry.targetPort long) ∉ postChain := by
    cases long <;> decide +kernel
  exact impossible member

theorem failed_nonextension : ¬ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
    ∀ i, k (StripResponseSummary.port i) = state 2 (port i) := by
  rintro ⟨k,agree⟩
  have form : ∀ i, state 2 (port i) = StripSixPhaseChoice.boundary false true false true i := by
    decide +kernel
  have valid := StripResponseSummary.valid_of_colouring _ k (fun i => (agree i).trans (form i))
  have good := StripSixPhaseChoice.terminal_necessary false true false true
    ((StripResponseSummary.terminal_iff _).mpr ⟨_,valid⟩)
  exact (by decide : ¬ StripSixPhaseChoice.Good false true false true) good

theorem free : StripSixPhaseChoice.Free (state 1) port := by
  refine ⟨6,Or.inr rfl,paired.component,?_,?_⟩
  · rw [paired.component_mem]; decide +kernel
  · intro o ho
    rw [paired.component_mem]
    exact (by decide +kernel : ∀ o ∈ StripSixPhaseChoice.outer, port o ∉ pairedChain) o ho


theorem hidden_eq : hidden.swap = state 3 := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact (by decide +kernel : ∀ x : Fin 31,
    (if x ∈ hiddenChain then Equiv.swap c0 c1 (state 1 x) else state 1 x) = state 3 x) x

theorem same_boundary : ∀ i, state 3 (port i) = state 1 (port i) := by decide +kernel

theorem bad_preparation :
    Relation.ReflTransGen (KempePairHistory.Step c0 c1) (state 0) (state 3) :=
  (Relation.ReflTransGen.single ⟨eight.component,eight_eq.symm⟩).trans
    (.single ⟨hidden.component,hidden_eq.symm⟩)

theorem no_free_component : ¬ StripSixPhaseChoice.Free (state 3) port := by
  rintro ⟨r,central,K,mr,avoid⟩
  have here : port r ∈ (state 3).kempeComponentSet c1 c3 locked.component := by
    rw [locked.component_mem]
    rcases central with h | h <;> subst r <;> decide +kernel
  have same : locked.component = K := here.choose_spec.symm.trans mr.choose_spec
  have at_one : port 1 ∈ (state 3).kempeComponentSet c1 c3 locked.component := by
    rw [locked.component_mem]; decide +kernel
  exact avoid 1 (by decide) (same ▸ at_one)

/-- The bad preparation cannot be repaired by any finite phase of this
pair, even though it retains the successful preparation's boundary colours. -/
theorem no_late_phase_repair (D : exterior.Coloring Color)
    (phase : Relation.ReflTransGen (KempePairHistory.Step c1 c3) (state 3) D) :
    ¬ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) := by
  rintro ⟨k,agree⟩
  exact no_free_component (StripSixPhaseChoice.free_of_phase (state 3) D port port_edges
    (fun i => (same_boundary i).trans (middle_form i))
    (KempePairHistory.pointwise phase) k agree)

theorem source : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) := by
  obtain ⟨D,h,one,_,k,agree⟩ := StripSixPhaseChoice.single_repair (state 1) port port_edges middle_form free
  exact ⟨D,.cons (eight_eq ▸ eight.step) h,by change h.length + 1 = 2; omega,k,agree⟩

def sourceHom : TriangleStripAnchors.input0099.graph →g ambient := ⟨sourceVertex,fun h =>
  source_edges _ _ h⟩
def interior : Set (Fin 19) := {v | 11 ≤ v.val}
def exteriorVertex (v : Fin 39) : Fin 31 := ⟨v.val % 31,Nat.mod_lt _ (by decide)⟩

instance (v : Fin 39) : Decidable (v ∈ sourceHom '' interior) :=
  inferInstanceAs (Decidable (∃ a : Fin 19, 11 ≤ a.val ∧ sourceVertex a = v))

theorem source_core (i : Fin 8) : sourceHom (i.natAdd 11) = i.natAdd 31 := by
  simp [sourceHom,sourceVertex]

theorem no_capture (a : Fin 19) (ha : a ∉ interior) : sourceHom a ∉ sourceHom '' interior := by
  rintro ⟨i,hi,heq⟩
  exact ha ((source_injective heq) ▸ hi)

theorem covers (i : Fin 19) (hi : i ∈ interior) (v : Fin 39)
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

end FourColor.StripSixPhaseExample
