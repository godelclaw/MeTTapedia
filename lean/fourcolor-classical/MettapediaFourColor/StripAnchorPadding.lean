import MettapediaFourColor.StripAnchorTrapTransport
import MettapediaFourColor.GraphTriangulationEuler

/-!
# A minimum-degree-five consumer of the anchor obstruction

Four triangular faces of the trap exterior are filled by nine-vertex
icosahedral patches. The resulting sphere has 56 vertices, all of degree
at least five. Restriction to the old exterior transfers the arbitrary-
history obstruction without another boundary-state enumeration. Two actual
component switches still reconstruct a full colouring. Separating triangles
remain; this is not an internally highly connected counterexample.
-/

namespace FourColor.StripAnchorPadding

open Color SimpleGraph StripAnchoredExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
set_option maxRecDepth 10000

def star : Fin 56 → List (Fin 56) := ![[1,55,10,15,14,20],
    [0,20,16,17,10,11,26,25,29,2,53,55],
    [1,29,23,24,11,3,53],
    [2,11,4,50,53],
    [3,11,10,7,6,35,34,38,5,51,50],
    [4,38,32,33,6,51],
    [4,7,48,51,5,33,30,35],
    [4,10,8,48,6],
    [7,10,44,43,47,9,52,49,48],
    [8,47,41,42,10,54,52],
    [0,55,54,9,42,39,44,8,7,4,11,1,17,12,15],
    [1,10,4,3,2,24,21,26],
    [10,17,18,13,15],
    [12,18,19,14,15],
    [0,15,13,19,20],
    [0,10,12,13,14],
    [1,20,19,18,17],
    [1,16,18,12,10],
    [12,17,16,19,13],
    [13,18,16,20,14],
    [0,14,19,16,1],
    [11,24,22,27,26],
    [21,24,23,28,27],
    [2,29,28,22,24],
    [2,23,22,21,11],
    [1,26,27,28,29],
    [1,11,21,27,25],
    [21,22,28,25,26],
    [22,23,29,25,27],
    [1,25,28,23,2],
    [6,33,31,36,35],
    [30,33,32,37,36],
    [5,38,37,31,33],
    [5,32,31,30,6],
    [4,35,36,37,38],
    [4,6,30,36,34],
    [30,31,37,34,35],
    [31,32,38,34,36],
    [4,34,37,32,5],
    [10,42,40,45,44],
    [39,42,41,46,45],
    [9,47,46,40,42],
    [9,41,40,39,10],
    [8,44,45,46,47],
    [8,10,39,45,43],
    [39,40,46,43,44],
    [40,41,47,43,45],
    [8,43,46,41,9],
    [6,7,8,49,51],
    [8,52,50,51,48],
    [3,4,51,49,52,54,53],
    [4,5,6,48,49,50],
    [8,9,54,50,49],
    [1,2,3,50,54,55],
    [9,10,55,53,50,52],
    [0,1,53,54,10]]
theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel

def ambient : SimpleGraph (Fin 56) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel ambient.Adj := by unfold ambient; infer_instance

def rows : GraphRotationRows.Rows ambient := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : ambient.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
def faceStep (p : Fin 56 × Fin 56) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u, (star u).all (fun v => decide
    (faceStep (faceStep (faceStep (u,v))) = (u,v))) = true := by decide +kernel

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  intro d
  apply Dart.ext
  change faceStep (faceStep (faceStep d.toProd)) = d.toProd
  exact of_decide_eq_true (List.all_eq_true.mp (face_check d.fst) d.snd d.adj)

def tour : List (Fin 56) := [0,1,2,3,4,5,6,7,8,9,10,11,21,22,23,24,23,28,25,26,27,26,25,29,25,28,23,22,21,11,10,12,13,14,15,14,19,16,17,18,17,16,20,16,19,14,13,12,10,39,40,41,42,41,46,43,44,45,44,43,47,43,46,41,40,39,10,54,50,49,48,51,48,49,52,49,50,53,55,53,50,54,10,9,8,7,6,30,31,32,33,32,37,34,35,36,35,34,38,34,37,32,31,30,6,5,4,3,2,1,0]
theorem tour_chain : tour.IsChain ambient.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 56, v ∈ tour := by decide +kernel

theorem connected : ambient.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 56) : ambient.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card ambient.Dart = 324 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin, dart_count])

theorem minimum_degree (v : Fin 56) : 5 ≤ ambient.degree v := by
  have degree : ambient.degree v = (star v).length := by
    have same : ambient.degree v =
        @SimpleGraph.degree (Fin 56) ambient v (Subtype.fintype _) :=
      congrArg (@SimpleGraph.degree (Fin 56) ambient v) (Subsingleton.elim _ _)
    exact same.trans (rows.degree v)
  rw [degree]
  exact (by decide +kernel : ∀ v : Fin 56, 5 ≤ (star v).length) v

def neighbours : Fin 48 → List (Fin 48) := ![[1,10,14,15,20],
    [0,2,10,11,16,17,20,25,26,29],
    [1,3,11,23,24,29],
    [2,4,11],
    [3,5,6,7,10,11,34,35,38],
    [4,6,32,33,38],
    [4,5,7,30,33,35],
    [4,6,8,10],
    [7,9,10,43,44,47],
    [8,10,41,42,47],
    [0,1,4,7,8,9,11,12,15,17,39,42,44],
    [1,2,3,4,10,21,24,26],
    [10,13,15,17,18],
    [12,14,15,18,19],
    [0,13,15,19,20],
    [0,10,12,13,14],
    [1,17,18,19,20],
    [1,10,12,16,18],
    [12,13,16,17,19],
    [13,14,16,18,20],
    [0,1,14,16,19],
    [11,22,24,26,27],
    [21,23,24,27,28],
    [2,22,24,28,29],
    [2,11,21,22,23],
    [1,26,27,28,29],
    [1,11,21,25,27],
    [21,22,25,26,28],
    [22,23,25,27,29],
    [1,2,23,25,28],
    [6,31,33,35,36],
    [30,32,33,36,37],
    [5,31,33,37,38],
    [5,6,30,31,32],
    [4,35,36,37,38],
    [4,6,30,34,36],
    [30,31,34,35,37],
    [31,32,34,36,38],
    [4,5,32,34,37],
    [10,40,42,44,45],
    [39,41,42,45,46],
    [9,40,42,46,47],
    [9,10,39,40,41],
    [8,44,45,46,47],
    [8,10,39,43,45],
    [39,40,43,44,46],
    [40,41,43,45,47],
    [8,9,41,43,46]]
theorem neighbours_symm : ∀ u v, v ∈ neighbours u → u ∈ neighbours v := by decide +kernel
theorem neighbours_loopless : ∀ v, v ∉ neighbours v := by decide +kernel

def exterior : SimpleGraph (Fin 48) where
  Adj u v := v ∈ neighbours u
  symm := ⟨neighbours_symm⟩
  loopless := ⟨neighbours_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def includeExterior (v : Fin 48) : Fin 56 := v.castAdd 8
theorem exterior_adj : ∀ u v, exterior.Adj u v ↔
    ambient.Adj (includeExterior u) (includeExterior v) := by decide +kernel

def oldVertex (v : Fin 12) : Fin 48 := v.castLE (by decide)
theorem old_edges : ∀ u v, StripAnchorTrap.exterior.Adj u v →
    exterior.Adj (oldVertex u) (oldVertex v) := by decide +kernel

def oldHom : StripAnchorTrap.exterior →g exterior where
  toFun := oldVertex
  map_rel' := old_edges _ _

def sourceVertex (v : Fin 19) : Fin 56 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 56)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 48) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    ambient.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel
theorem source_injective : Function.Injective sourceVertex := by decide +kernel
theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 56,
    ambient.Adj (i.natAdd 48) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (i.natAdd 11) j ∧
        sourceVertex j = v := by decide +kernel
theorem boundary_aligned : ∀ i, sourceVertex (StripResponseSummary.port i) =
    includeExterior (oldVertex (StripAnchorTrap.port i)) := by decide +kernel

def values : Fin 3 → Fin 48 → Color
  | 0 => ![c0,c1,c3,c2,c1,c3,c2,c3,c0,c3,c2,c0,c0,c3,c2,c1,c2,c3,c1,c0,c3,c3,c2,c0,c1,c0,c2,c1,c3,c2,c3,c0,c2,c1,c2,c0,c1,c3,c0,c3,c1,c2,c0,c2,c1,c0,c3,c1]
  | 1 => ![c1,c0,c3,c2,c0,c3,c2,c3,c0,c3,c2,c1,c1,c3,c2,c0,c2,c3,c0,c1,c3,c3,c2,c1,c0,c1,c2,c0,c3,c2,c3,c1,c2,c0,c2,c1,c0,c3,c1,c3,c1,c2,c0,c2,c1,c0,c3,c1]
  | 2 => ![c1,c0,c3,c2,c0,c3,c2,c1,c0,c3,c2,c1,c1,c3,c2,c0,c2,c3,c0,c1,c3,c3,c2,c1,c0,c1,c2,c0,c3,c2,c3,c1,c2,c0,c2,c1,c0,c3,c1,c3,c1,c2,c0,c2,c1,c0,c3,c1]
theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel
def state (s : Fin 3) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
theorem state_agrees : ∀ s v, state s (oldVertex v) = StripAnchorTrap.state s v := by decide +kernel

theorem initial_orbit : StripAnchorTrap.Orbit (StripAnchorTrapTransport.restrict oldHom (state 0)) :=
  ⟨Equiv.refl _,state_agrees 0⟩

/-- Arbitrarily many guarded phases on the larger graph cannot reconstruct
any proper ambient colouring fixing the resulting exterior. -/
theorem no_guarded_reconstruction {D : exterior.Coloring Color}
    (history : Relation.ReflTransGen (StripAnchorTrapTransport.Phase oldHom) (state 0) D)
    (K : ambient.Coloring Color) (fixed : ∀ v, K (includeExterior v) = D v) : False := by
  apply StripAnchorTrapTransport.history_no_source oldHom initial_orbit history
  refine ⟨.mk (fun v => K (sourceVertex v)) (fun h => K.valid (source_edges _ _ h)), ?_⟩
  intro i
  change K (sourceVertex (StripResponseSummary.port i)) = _
  rw [boundary_aligned, fixed]
  rfl

def repairChain : Fin 2 → List (Fin 48) := ![[0,1,11,4,35,36,31,33,31,36,35,4,38,4,11,24,23,24,11,1,25,27,25,1,0,15,12,18,19,18,12,15,0],
    [7]]
def repairRoot (s : Fin 2) : Fin 48 := (repairChain s).head!
theorem repair_checked : ∀ s,
    repairRoot s ∈ repairChain s ∧ (repairChain s).IsChain exterior.Adj ∧
    (∀ x ∈ repairChain s, state s.castSucc x = (StripAnchorTrap.repairPair s).1 ∨
      state s.castSucc x = (StripAnchorTrap.repairPair s).2) ∧
    (∀ x ∈ repairChain s, ∀ y, exterior.Adj x y →
      (state s.castSucc y = (StripAnchorTrap.repairPair s).1 ∨
       state s.castSucc y = (StripAnchorTrap.repairPair s).2) → y ∈ repairChain s) ∧
    (∀ x, state s.succ x = if x ∈ repairChain s then
      Equiv.swap (StripAnchorTrap.repairPair s).1 (StripAnchorTrap.repairPair s).2 (state s.castSucc x)
      else state s.castSucc x) := by decide +kernel

def repairCertificate (s : Fin 2) : KempeSeparatedChains.Certificate (state s.castSucc)
    (StripAnchorTrap.repairPair s).1 (StripAnchorTrap.repairPair s).2 where
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

def finalValues (v : Fin 56) : Color :=
  Fin.addCases (m := 48) (n := 8) (motive := fun _ => Color)
    (fun x => state 2 x) StripAnchorTrap.finalCore v
theorem whole_valid : ∀ u v, ambient.Adj u v → finalValues u ≠ finalValues v := by decide +kernel
def finalColouring : ambient.Coloring Color := .mk finalValues (fun h => whole_valid _ _ h)
theorem final_exterior (v : Fin 48) : finalColouring (includeExterior v) = state 2 v := by
  change Fin.addCases (m := 48) (n := 8) (motive := fun _ => Color)
    (fun x => state 2 x) StripAnchorTrap.finalCore (v.castAdd 8) = _
  simp

theorem reconstructed : ∃ D : exterior.Coloring Color, ∃ history : History (state 0) D,
    history.length = 2 ∧ ∃ K : ambient.Coloring Color,
      ∀ v, K (includeExterior v) = D v :=
  ⟨state 2,repairHistory,repair_length,finalColouring,final_exterior⟩

/-- The first padding patch is isolated after removing its attachment
triangle. Both its interior and the remaining exterior are nonempty. -/
def Island (v : Fin 56) : Prop := 12 ≤ v.val ∧ v.val < 21
def Seam (v : Fin 56) : Prop := v = 0 ∨ v = 1 ∨ v = 10
instance (v) : Decidable (Island v) := by unfold Island; infer_instance
instance (v) : Decidable (Seam v) := by unfold Seam; infer_instance
theorem separating_seam :
    ambient.Adj 0 1 ∧ ambient.Adj 1 10 ∧ ambient.Adj 10 0 ∧
    Island 12 ∧ ¬ Seam 12 ∧ ¬ Island 21 ∧ ¬ Seam 21 ∧
    (∀ u v, Island u → ambient.Adj u v → Island v ∨ Seam v) := by decide +kernel

end FourColor.StripAnchorPadding
