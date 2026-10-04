import MettapediaFourColor.StripGuardedOrbit
import MettapediaFourColor.GraphTriangulationEuler
import Mettapedia.GraphTheory.Kempe.PhaseBoundary
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-!
# A spherical anchor trap with a two-switch escape

The 24-vertex sphere has minimum degree five and the exact induced D0099
core stars. The shared palette-orbit theorem excludes every finite guarded
history. Two physical component switches, which first sacrifice one of four
joint choices, reconstruct a full colouring.

The accompanying short-cycle census is independent program evidence;
absence of short separating cycles is not a theorem of this module.
-/

namespace FourColor.StripStrongAnchorTrap

open Color SimpleGraph StripResponseSummary StripAnchoredExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
set_option maxRecDepth 10000

def star : Fin 24 → List (Fin 24) := ![[1,13,15,11,7,10,23],
    [0,23,21,2,13],
    [1,21,3,12,13],
    [2,21,18,4,14,12],
    [3,18,19,5,14],
    [4,19,6,11,14],
    [5,19,16,7,11],
    [0,11,6,16,8,9,10],
    [7,16,17,20,9],
    [7,8,20,22,10],
    [0,7,9,22,23],
    [0,15,14,5,6,7],
    [2,3,14,15,13],
    [0,1,2,12,15],
    [3,4,5,11,15,12],
    [0,13,12,14,11],
    [6,19,17,8,7],
    [8,16,19,18,20],
    [3,21,22,20,17,19,4],
    [4,18,17,16,6,5],
    [8,17,18,22,9],
    [1,23,22,18,3,2],
    [9,20,18,21,23,10],
    [0,10,22,21,1]]
theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel

def ambient : SimpleGraph (Fin 24) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel ambient.Adj := by unfold ambient; infer_instance

def rows : GraphRotationRows.Rows ambient := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : ambient.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
def faceStep (p : Fin 24 × Fin 24) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u, (star u).all (fun v => decide
    (faceStep (faceStep (faceStep (u,v))) = (u,v))) = true := by decide +kernel

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  intro d
  apply Dart.ext
  change faceStep (faceStep (faceStep d.toProd)) = d.toProd
  exact of_decide_eq_true (List.all_eq_true.mp (face_check d.fst) d.snd d.adj)

def tour : List (Fin 24) := [0,1,2,3,4,5,6,7,8,9,10,22,18,17,16,19,16,17,20,17,18,21,23,21,18,22,10,9,8,7,11,14,12,13,15,13,12,14,11,7,6,5,4,3,2,1,0]
theorem tour_chain : tour.IsChain ambient.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 24, v ∈ tour := by decide +kernel

theorem connected : ambient.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 24) : ambient.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card ambient.Dart = 132 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin, dart_count])

theorem degree_eq (v : Fin 24) : ambient.degree v = (star v).length := by
  have same : ambient.degree v =
      @SimpleGraph.degree (Fin 24) ambient v (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 24) ambient v) (Subsingleton.elim _ _)
  exact same.trans (rows.degree v)

theorem minimum_degree (v : Fin 24) : 5 ≤ ambient.degree v := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 24, 5 ≤ (star v).length) v

theorem maximum_degree (v : Fin 24) : ambient.degree v ≤ 7 := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 24, (star v).length ≤ 7) v

def neighbours : Fin 16 → List (Fin 16) := ![[1,7,10,11,13,15],
    [0,2,13],
    [1,3,12,13],
    [2,4,12,14],
    [3,5,14],
    [4,6,11,14],
    [5,7,11],
    [0,6,8,9,10,11],
    [7,9],
    [7,8,10],
    [0,7,9],
    [0,5,6,7,14,15],
    [2,3,13,14,15],
    [0,1,2,12,15],
    [3,4,5,11,12,15],
    [0,11,12,13,14]]
theorem neighbours_symm : ∀ u v, v ∈ neighbours u → u ∈ neighbours v := by decide +kernel
theorem neighbours_loopless : ∀ v, v ∉ neighbours v := by decide +kernel

def exterior : SimpleGraph (Fin 16) where
  Adj u v := v ∈ neighbours u
  symm := ⟨neighbours_symm⟩
  loopless := ⟨neighbours_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def includeExterior (v : Fin 16) : Fin 24 := v.castAdd 8
theorem exterior_adj : ∀ u v, exterior.Adj u v ↔
    ambient.Adj (includeExterior u) (includeExterior v) := by decide +kernel

def port (i : Fin 11) : Fin 16 := i.castLE (by decide)
def sourceVertex (v : Fin 19) : Fin 24 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 24)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 16) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    ambient.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel
theorem source_injective : Function.Injective sourceVertex := by decide +kernel
theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 24,
    ambient.Adj (i.natAdd 16) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (i.natAdd 11) j ∧
        sourceVertex j = v := by decide +kernel
theorem boundary_aligned : ∀ i, sourceVertex (StripResponseSummary.port i) =
    includeExterior (port i) := by decide +kernel

def values : Fin 3 → Fin 16 → Color
  | 0 => ![c0,c1,c0,c2,c3,c2,c1,c2,c1,c3,c1,c3,c1,c3,c0,c2]
  | 1 => ![c1,c0,c1,c2,c3,c2,c1,c2,c1,c3,c0,c3,c0,c3,c1,c2]
  | 2 => ![c1,c2,c1,c2,c3,c2,c1,c2,c1,c3,c0,c3,c0,c3,c1,c2]
theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel
def state (s : Fin 3) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
def read (c : Fin 16 → Color) : Boundary := fun i => c (port i)
theorem base_profile : ¬ Full (read (values 0)) ∧ (choices (read (values 0))).card = 4 := by
  decide +kernel

def pair : Fin 6 → Color × Color := ![(c0,c1),(c0,c2),(c0,c3),(c1,c2),(c1,c3),(c2,c3)]
def roots : Fin 6 → Fin 4 → Fin 16
  | 0 => ![0,6,8,0]
  | 1 => ![0,0,0,0]
  | 2 => ![0,9,0,0]
  | 3 => ![1,3,5,1]
  | 4 => ![1,4,6,8]
  | 5 => ![3,3,3,3]
def label : Fin 6 → Fin 16 → Fin 4
  | 0 => ![0,0,0,0,0,0,1,0,2,0,0,0,0,0,0,0]
  | 1 => ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | 2 => ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
  | 3 => ![0,0,0,1,0,2,2,2,2,0,2,0,1,0,0,1]
  | 4 => ![0,0,0,0,1,0,2,0,3,3,3,2,0,0,0,0]
  | 5 => ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def routeList : Fin 6 → Fin 16 → List (Fin 16)
  | 0 => ![[0],
    [0,1],
    [0,1,2],
    [3],
    [4],
    [5],
    [6],
    [7],
    [8],
    [9],
    [0,10],
    [11],
    [0,1,2,12],
    [13],
    [0,1,2,12,14],
    [15]]
  | 1 => ![[0],
    [1],
    [0,15,14,3,2],
    [0,15,14,3],
    [4],
    [0,15,14,5],
    [6],
    [0,7],
    [8],
    [9],
    [10],
    [11],
    [12],
    [13],
    [0,15,14],
    [0,15]]
  | 2 => ![[0],
    [1],
    [0,13,2],
    [3],
    [0,11,14,4],
    [5],
    [6],
    [7],
    [8],
    [9],
    [10],
    [0,11],
    [12],
    [0,13],
    [0,11,14],
    [15]]
  | 3 => ![[0],
    [1],
    [2],
    [3],
    [4],
    [5],
    [5,6],
    [5,6,7],
    [5,6,7,8],
    [9],
    [5,6,7,10],
    [11],
    [3,12],
    [13],
    [14],
    [3,12,15]]
  | 4 => ![[0],
    [1],
    [2],
    [3],
    [4],
    [5],
    [6],
    [7],
    [8],
    [8,9],
    [8,9,10],
    [6,11],
    [1,13,12],
    [1,13],
    [14],
    [15]]
  | 5 => ![[0],
    [1],
    [2],
    [3],
    [3,4],
    [3,4,5],
    [6],
    [3,4,5,11,7],
    [8],
    [3,4,5,11,7,9],
    [10],
    [3,4,5,11],
    [12],
    [3,4,5,11,15,13],
    [14],
    [3,4,5,11,15]]
def Active (s : Fin 6) (v : Fin 16) : Prop :=
  state 0 v = (pair s).1 ∨ state 0 v = (pair s).2
instance (s v) : Decidable (Active s v) := inferInstanceAs (Decidable (_ ∨ _))

theorem route_nonempty : ∀ s j, routeList s j ≠ [] := by decide +kernel
theorem route_chain : ∀ s j, (routeList s j).IsChain exterior.Adj := by decide +kernel
theorem route_head : ∀ s j, Active s j →
    (routeList s j).head (route_nonempty s j) = roots s (label s j) := by decide +kernel
theorem route_last : ∀ s j,
    (routeList s j).getLast (route_nonempty s j) = j := by decide +kernel
theorem route_active : ∀ s j, Active s j → ∀ x ∈ routeList s j, Active s x := by decide +kernel

theorem routes (s : Fin 6) (j : Fin 16) (h : Active s j) :
    ∃ p : exterior.Walk (roots s (label s j)) j, ∀ x ∈ p.support, Active s x := by
  let p := (Walk.ofSupport (routeList s j) (route_nonempty s j) (route_chain s j)).copy
    (route_head s j h) (route_last s j)
  refine ⟨p, ?_⟩
  intro x hx
  exact route_active s j h x (by simpa [p] using hx)

def answer (s : Fin 6) (bits : Fin 4 → Bool) (v : Fin 16) : Color :=
  if bits (label s v) then Equiv.swap (pair s).1 (pair s).2 (values 0 v) else values 0 v

def Orbit (c : Fin 16 → Color) : Prop := ∃ g : Equiv.Perm Color, ∀ v, c v = g (values 0 v)
instance (c) : Decidable (Orbit c) := by unfold Orbit; infer_instance

theorem answer_barrier : ∀ s bits,
    Orbit (answer s bits) ∨ (¬ Full (read (answer s bits)) ∧
      (choices (read (answer s bits))).card < 4) := by decide +kernel

theorem pair_cases : ∀ a b : Color, a = b ∨ ∃ s : Fin 6,
    (a = (pair s).1 ∧ b = (pair s).2) ∨ (a = (pair s).2 ∧ b = (pair s).1) := by
  decide +kernel

theorem indexed_barrier (s : Fin 6) (D : exterior.Coloring Color)
    (hp : ∀ v, D v = state 0 v ∨ D v = Equiv.swap (pair s).1 (pair s).2 (state 0 v)) :
    Orbit D ∨ (¬ Full (read D) ∧ (choices (read D)).card < 4) := by
  obtain ⟨bits,hb⟩ := KempePhaseBoundary.endpoint (state 0) D _ _ hp
    id (roots s) (label s) (routes s)
  have eq : (D : Fin 16 → Color) = answer s bits := funext hb
  rw [eq]
  exact answer_barrier s bits

theorem base_barrier (a b : Color) (D : exterior.Coloring Color)
    (hp : ∀ v, D v = state 0 v ∨ D v = Equiv.swap a b (state 0 v)) :
    Orbit D ∨ (¬ Full (read D) ∧ (choices (read D)).card < 4) := by
  rcases pair_cases a b with eq | ⟨s,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
  · left
    refine ⟨Equiv.refl _,fun v => ?_⟩
    change D v = state 0 v
    simpa [eq] using hp v
  · exact indexed_barrier s D hp
  · exact indexed_barrier s D (by simpa only [Equiv.swap_comm] using hp)

def Phase := StripGuardedOrbit.Phase (G := exterior) port

theorem history_nonextension {D : exterior.Coloring Color}
    (history : Relation.ReflTransGen Phase (state 0) D) : ¬ Full (read D) :=
  StripGuardedOrbit.history_nonextension port (state 0) 4 base_profile base_barrier history

/-- Every guarded history fails to reconstruct an ambient colouring fixing
its final exterior, although an unrestricted two-switch history succeeds. -/
theorem no_guarded_reconstruction {D : exterior.Coloring Color}
    (history : Relation.ReflTransGen Phase (state 0) D)
    (K : ambient.Coloring Color) (fixed : ∀ v, K (includeExterior v) = D v) : False := by
  apply history_nonextension history
  apply (full_iff _).mpr
  let k : TriangleStripAnchors.input0099.graph.Coloring Color :=
    .mk (fun v => K (sourceVertex v)) (fun h => K.valid (source_edges _ _ h))
  refine ⟨_,StripResponseSummary.valid_of_colouring (read D) k ?_⟩
  intro i
  change K (sourceVertex (StripResponseSummary.port i)) = _
  rw [boundary_aligned, fixed]
  rfl

def repairPair : Fin 2 → Color × Color := ![(c0,c1),(c0,c2)]
def repairChain : Fin 2 → List (Fin 16) := ![[0,1,2,12,14,12,2,1,0,10,0],
    [1]]
def repairRoot (s : Fin 2) : Fin 16 := (repairChain s).head!

theorem repair_checked : ∀ s,
    repairRoot s ∈ repairChain s ∧ (repairChain s).IsChain exterior.Adj ∧
    (∀ x ∈ repairChain s, state s.castSucc x = (repairPair s).1 ∨
      state s.castSucc x = (repairPair s).2) ∧
    (∀ x ∈ repairChain s, ∀ y, exterior.Adj x y →
      (state s.castSucc y = (repairPair s).1 ∨ state s.castSucc y = (repairPair s).2) →
      y ∈ repairChain s) ∧
    (∀ x, state s.succ x = if x ∈ repairChain s then
      Equiv.swap (repairPair s).1 (repairPair s).2 (state s.castSucc x)
      else state s.castSucc x) := by decide +kernel

def repairCertificate (s : Fin 2) :
    KempeSeparatedChains.Certificate (state s.castSucc) (repairPair s).1 (repairPair s).2 where
  vertices := repairChain s
  root := repairRoot s
  root_mem := (repair_checked s).1
  connected := (repair_checked s).2.1
  active := (repair_checked s).2.2.1
  closed := (repair_checked s).2.2.2.1

theorem repair_eq (s : Fin 2) : (repairCertificate s).swap = state s.succ := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact ((repair_checked s).2.2.2.2 x).symm

noncomputable def repairStep (s : Fin 2) : Step (state s.castSucc) (state s.succ) :=
  repair_eq s ▸ (repairCertificate s).step

noncomputable def repairHistory : History (state 0) (state 2) :=
  .cons (repairStep 0) (.cons (repairStep 1) (.refl _))

theorem repair_length : repairHistory.length = 2 := rfl

theorem intermediate_profile : ¬ Full (read (values 1)) ∧
    (choices (read (values 1))).card = 3 := by decide +kernel

def finalCore : Fin 8 → Color := ![c3,c2,c1,c0,c0,c0,c2,c3]
theorem final_valid : ValidCore (read (values 2)) finalCore := by
  unfold ValidCore
  decide +kernel

/-- The escape first reduces the number of optimal one-hole choices from
four to three; its second actual component switch restores all vertices. -/
theorem escape_profiles :
    (¬ Full (read (state 0)) ∧ (choices (read (state 0))).card = 4) ∧
    (¬ Full (read (state 1)) ∧ (choices (read (state 1))).card = 3) ∧
    Full (read (state 2)) :=
  ⟨base_profile,intermediate_profile,(full_iff _).mpr ⟨finalCore,final_valid⟩⟩

def finalValues (v : Fin 24) : Color :=
  Fin.addCases (m := 16) (n := 8) (motive := fun _ => Color)
    (fun x => state 2 x) finalCore v
theorem whole_valid : ∀ u v, ambient.Adj u v → finalValues u ≠ finalValues v := by decide +kernel
def finalColouring : ambient.Coloring Color := .mk finalValues (fun h => whole_valid _ _ h)
theorem final_exterior (v : Fin 16) : finalColouring (includeExterior v) = state 2 v := by
  change Fin.addCases (m := 16) (n := 8) (motive := fun _ => Color)
    (fun x => state 2 x) finalCore (v.castAdd 8) = _
  simp

theorem reconstructed : ∃ D : exterior.Coloring Color, ∃ history : History (state 0) D,
    history.length = 2 ∧ ∃ K : ambient.Coloring Color,
      ∀ v, K (includeExterior v) = D v :=
  ⟨state 2,repairHistory,repair_length,finalColouring,final_exterior⟩

end FourColor.StripStrongAnchorTrap
