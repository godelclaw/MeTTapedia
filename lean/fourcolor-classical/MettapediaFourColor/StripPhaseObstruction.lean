import MettapediaFourColor.StripPartialColouring
import Mettapedia.GraphTheory.Kempe.PhaseBoundary
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-!
# A physical obstruction to strict progress in one colour pair

A proper colouring of a 23-vertex exterior requires at least two omitted
D0099 core vertices after every fixed-pair phase, regardless of its length.
Retained bichromatic routes give the boundary normal forms. Two disjoint
uncolourable pieces certify every lower bound. A three-step mixed-pair
history nevertheless reconstructs a colouring of the entire 31-vertex graph.

The accompanying program checks the triangulated-disk embedding. The
example has low-degree vertices; minimal-counterexample geometry is not
asserted. No obstruction to unrestricted repair follows from this result.
-/

namespace FourColor.StripPhaseObstruction

open Color SimpleGraph StripResponseSummary StripSourceExtension StripPartialColouring
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

set_option maxRecDepth 10000

def exteriorEdges : List (Fin 23 × Fin 23) :=
  [(0,1),
    (0,2),
    (0,10),
    (0,11),
    (0,14),
    (0,15),
    (0,16),
    (0,19),
    (0,20),
    (0,22),
    (1,2),
    (2,3),
    (2,19),
    (3,4),
    (3,16),
    (3,19),
    (3,22),
    (4,5),
    (4,6),
    (4,7),
    (4,21),
    (4,22),
    (5,6),
    (6,7),
    (7,8),
    (7,12),
    (7,13),
    (7,17),
    (7,18),
    (7,21),
    (8,9),
    (8,15),
    (8,18),
    (9,10),
    (9,15),
    (9,20),
    (10,20),
    (11,13),
    (11,14),
    (11,15),
    (12,13),
    (12,15),
    (12,17),
    (13,14),
    (13,15),
    (13,21),
    (13,22),
    (14,22),
    (15,17),
    (15,18),
    (15,20),
    (16,19),
    (16,22),
    (17,18),
    (21,22)]

def exterior : SimpleGraph (Fin 23) where
  Adj u v := (u,v) ∈ exteriorEdges ∨ (v,u) ∈ exteriorEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def ports (i : Fin 11) : Fin 23 := i.castLE (by decide)

def values : Fin 4 → Fin 23 → Color
  | 0 => ![c0,c1,c3,c0,c1,c0,c2,c0,c1,c0,c3,c2,c2,c1,c3,c3,c3,c1,c2,c2,c2,c3,c2]
  | 1 => ![c1,c0,c3,c0,c1,c0,c2,c0,c1,c0,c3,c2,c2,c1,c3,c3,c3,c1,c2,c2,c2,c3,c2]
  | 2 => ![c1,c0,c3,c2,c1,c0,c2,c0,c1,c0,c3,c2,c2,c1,c3,c3,c3,c1,c2,c0,c2,c3,c0]
  | 3 => ![c1,c3,c0,c2,c1,c0,c2,c3,c1,c0,c3,c2,c2,c1,c0,c3,c0,c1,c2,c3,c2,c0,c3]

theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel

def state (s : Fin 4) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)

def pair : Fin 6 → Color × Color := ![(c0,c1),(c0,c2),(c0,c3),(c1,c2),(c1,c3),(c2,c3)]

def roots : Fin 6 → Fin 3 → Fin 23
  | 0 => ![0,3,0]
  | 1 => ![0,5,0]
  | 2 => ![0,5,7]
  | 3 => ![1,4,1]
  | 4 => ![1,4,10]
  | 5 => ![2,6,2]

def label : Fin 6 → Fin 11 → Fin 3
  | 0 => ![0,0,0,1,1,1,0,1,1,1,0]
  | 1 => ![0,0,0,0,0,1,1,1,0,0,0]
  | 2 => ![0,0,0,0,0,1,0,2,0,0,0]
  | 3 => ![0,0,0,0,1,0,1,0,1,0,0]
  | 4 => ![0,0,0,0,1,0,0,0,1,0,2]
  | 5 => ![0,0,0,0,0,0,1,0,0,0,0]

def routeList : Fin 6 → Fin 11 → List (Fin 23)
  | 0 => ![[0],[0,1],[2],[3],[3,4],[3,4,5],[6],[3,4,7],[3,4,7,8],[3,4,7,8,9],[10]]
  | 1 => ![[0],[1],[2],[0,19,3],[4],[5],[5,6],[5,6,7],[8],[0,20,9],[10]]
  | 2 => ![[0],[1],[0,2],[0,2,3],[4],[5],[6],[7],[8],[0,10,9],[0,10]]
  | 3 => ![[0],[1],[2],[3],[4],[5],[4,6],[7],[4,22,13,12,17,18,8],[9],[10]]
  | 4 => ![[0],[1],[1,2],[3],[4],[5],[6],[7],[4,21,13,15,8],[9],[10]]
  | 5 => ![[0],[1],[2],[3],[4],[5],[6],[7],[8],[9],[2,19,16,22,14,11,15,20,10]]

def Active (s : Fin 6) (v : Fin 23) : Prop :=
  state 0 v = (pair s).1 ∨ state 0 v = (pair s).2
instance (s v) : Decidable (Active s v) := inferInstanceAs (Decidable (_ ∨ _))

theorem route_nonempty : ∀ s j, routeList s j ≠ [] := by decide +kernel
theorem route_chain : ∀ s j, (routeList s j).IsChain exterior.Adj := by decide +kernel
theorem route_head : ∀ s j, Active s (ports j) →
    (routeList s j).head (route_nonempty s j) = roots s (label s j) := by decide +kernel
theorem route_last : ∀ s j,
    (routeList s j).getLast (route_nonempty s j) = ports j := by decide +kernel
theorem route_active : ∀ s j, Active s (ports j) →
    ∀ x ∈ routeList s j, Active s x := by decide +kernel

theorem routes (s : Fin 6) (j : Fin 11) (h : Active s (ports j)) :
    ∃ p : exterior.Walk (roots s (label s j)) (ports j),
      ∀ x ∈ p.support, Active s x := by
  let p := (Walk.ofSupport (routeList s j) (route_nonempty s j) (route_chain s j)).copy
    (route_head s j h) (route_last s j)
  refine ⟨p, ?_⟩
  intro x hx
  exact route_active s j h x (by simpa [p] using hx)

def word (s : Fin 6) (bits : Fin 3 → Bool) : Boundary :=
  fun j => if bits (label s j) then Equiv.swap (pair s).1 (pair s).2 (state 0 (ports j))
    else state 0 (ports j)

/-- A whole phase retains one common choice for each routed boundary block. -/
theorem phase_word (s : Fin 6) (D : exterior.Coloring Color)
    (h : Relation.ReflTransGen (KempePairHistory.Step (pair s).1 (pair s).2) (state 0) D) :
    ∃ bits, ∀ j, D (ports j) = word s bits j :=
  KempePhaseBoundary.phase (state 0) D _ _ ports (roots s) (label s) (routes s) h

/-- Five small obstruction shapes, reused by all phase endpoints. -/
def piece : Fin 5 → List (Fin 8) := ![[0,3], [5,7], [5,6,7], [2,4,6], [0,1,2,3,4]]

def Conflict (b : Boundary) (vs : List (Fin 8)) : Prop :=
  ∀ f : Fin vs.length → Color, ¬ ((∀ i, unary b (vs.get i) (f i)) ∧
    ∀ i j, (vs.get i, vs.get j) ∈ StripResponseSummary.edges → f i ≠ f j)

instance (b vs) : Decidable (Conflict b vs) := by unfold Conflict; infer_instance

private instance (xs ys : List (Fin 8)) : Decidable (xs.Disjoint ys) :=
  decidable_of_iff (∀ x ∈ xs, x ∉ ys) List.disjoint_left.symm

/-- The finite check evaluates at most five local colour variables; it does
not enumerate full source colourings or exterior histories. -/
theorem endpoint_conflicts : ∀ s bits, ∃ i j : Fin 5,
    (piece i).Disjoint (piece j) ∧ Conflict (word s bits) (piece i) ∧
      Conflict (word s bits) (piece j) := by decide +kernel

private theorem conflict_hits {b : Boundary} {vs : List (Fin 8)}
    (bad : Conflict b vs) {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (valid : ValidExcept b h f) : ∃ v ∈ vs, v ∈ h := by
  classical
  by_contra! no
  apply bad (fun i => f (vs.get i))
  constructor
  · intro i
    exact valid.1 _ (no _ (List.get_mem _ _))
  · intro i j edge
    exact valid.2 _ edge (no _ (List.get_mem _ _)) (no _ (List.get_mem _ _))

theorem conflict_bound {b : Boundary} {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (conflicts : ∃ i j : Fin 5, (piece i).Disjoint (piece j) ∧
      Conflict b (piece i) ∧ Conflict b (piece j))
    (valid : ValidExcept b h f) : 2 ≤ h.card := by
  obtain ⟨i,j,apart,hi,hj⟩ := conflicts
  obtain ⟨x,hx,hxh⟩ := conflict_hits hi valid
  obtain ⟨y,hy,hyh⟩ := conflict_hits hj valid
  have ne : x ≠ y := fun e => List.disjoint_left.mp apart hx (e.symm ▸ hy)
  have sub : ({x,y} : Finset (Fin 8)) ⊆ h := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  simpa [ne] using Finset.card_le_card sub

theorem two_holes (s : Fin 6) (bits : Fin 3 → Bool) {h : Finset (Fin 8)}
    {f : Fin 8 → Color} (valid : ValidExcept (word s bits) h f) : 2 ≤ h.card :=
  conflict_bound (endpoint_conflicts s bits) valid

theorem prefix_conflicts : ∀ t : Fin 3, ∃ i j : Fin 5,
    (piece i).Disjoint (piece j) ∧ Conflict (fun j => state t.castSucc (ports j)) (piece i) ∧
      Conflict (fun j => state t.castSucc (ports j)) (piece j) := by decide +kernel

/-- The first two successful moves still leave at least two necessary holes. -/
theorem prefix_lower_bound (t : Fin 3) {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (valid : ValidExcept (fun j => state t.castSucc (ports j)) h f) : 2 ≤ h.card :=
  conflict_bound (prefix_conflicts t) valid

/-- The lower bound depends only on the initial port colours and these
bichromatic routes. It applies to arbitrary exteriors containing them. -/
theorem routed_requires_two {V : Type*} {G : SimpleGraph V}
    (C D : G.Coloring Color) (p : Fin 11 → V) (s : Fin 6)
    (r : Fin 3 → V)
    (boundary : ∀ j, C (p j) = state 0 (ports j))
    (paths : ∀ j, (C (p j) = (pair s).1 ∨ C (p j) = (pair s).2) →
      ∃ q : G.Walk (r (label s j)) (p j),
        ∀ x ∈ q.support, C x = (pair s).1 ∨ C x = (pair s).2)
    (history : Relation.ReflTransGen (KempePairHistory.Step (pair s).1 (pair s).2) C D)
    {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (valid : ValidExcept (fun j => D (p j)) h f) : 2 ≤ h.card := by
  obtain ⟨bits,hb⟩ := KempePhaseBoundary.phase C D _ _ p r (label s) paths history
  have eq : (fun j => D (p j)) = word s bits := by
    funext j
    simpa only [word, boundary] using hb j
  rw [eq] at valid
  exact two_holes s bits valid

/-- Every phase of any one of the six unordered colour pairs leaves at
least two holes, even if the omitted core vertices and their colours change. -/
theorem phase_requires_two (s : Fin 6) (D : exterior.Coloring Color)
    (history : Relation.ReflTransGen (KempePairHistory.Step (pair s).1 (pair s).2) (state 0) D)
    {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (valid : ValidExcept (fun j => D (ports j)) h f) : 2 ≤ h.card := by
  exact routed_requires_two (state 0) D ports s (roots s) (fun _ => rfl)
    (routes s) history valid

def initialCore : Fin 8 → Color := ![c0,c0,c2,c3,c3,c0,c1,c2]

theorem initial_two : ValidExcept (fun j => state 0 (ports j)) {0,5} initialCore := by
  unfold ValidExcept
  decide +kernel

private theorem colour_pairs : ∀ a b : Color, a = b ∨
    ∃ s, (a = (pair s).1 ∧ b = (pair s).2) ∨
      (a = (pair s).2 ∧ b = (pair s).1) := by decide +kernel

/-- Every ordering of every colour pair has the same lower bound. -/
theorem any_pair_requires_two (a b : Color) (D : exterior.Coloring Color)
    (history : Relation.ReflTransGen (KempePairHistory.Step a b) (state 0) D)
    {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (valid : ValidExcept (fun j => D (ports j)) h f) : 2 ≤ h.card := by
  have cases := colour_pairs a b
  rcases cases with rfl | ⟨s, he | he⟩
  · have eq : D = state 0 := by
      ext v
      have hv := KempePairHistory.pointwise history v
      simpa using hv
    subst D
    exact phase_requires_two 0 (state 0) .refl valid
  · rcases he with ⟨rfl,rfl⟩
    exact phase_requires_two s D history valid
  · rcases he with ⟨rfl,rfl⟩
    have pw := KempePairHistory.pointwise history
    have pw' : ∀ v, D v = state 0 v ∨
        D v = Equiv.swap (pair s).1 (pair s).2 (state 0 v) := by
      simpa only [Equiv.swap_comm] using pw
    obtain ⟨bits,hb⟩ := KempePhaseBoundary.endpoint (state 0) D _ _ pw'
      ports (roots s) (label s) (routes s)
    have eq : (fun j => D (ports j)) = word s bits := funext hb
    rw [eq] at valid
    exact two_holes s bits valid

def repairPair : Fin 3 → Color × Color := ![(c0,c1),(c0,c2),(c0,c3)]
def repairChain : Fin 3 → List (Fin 23) :=
  ![[0,1,0],
    [3,19,3,22,3],
    [1,2,19,16,22,14,22,21,7,21,22,16,19,2,1]]

def repairRoot (t : Fin 3) : Fin 23 := (repairChain t).head!

theorem repair_checked : ∀ t,
    repairRoot t ∈ repairChain t ∧ (repairChain t).IsChain exterior.Adj ∧
    (∀ x ∈ repairChain t, state t.castSucc x = (repairPair t).1 ∨
      state t.castSucc x = (repairPair t).2) ∧
    (∀ x ∈ repairChain t, ∀ y, exterior.Adj x y →
      (state t.castSucc y = (repairPair t).1 ∨ state t.castSucc y = (repairPair t).2) →
      y ∈ repairChain t) ∧
    (∀ x, state t.succ x = if x ∈ repairChain t then
      Equiv.swap (repairPair t).1 (repairPair t).2 (state t.castSucc x)
      else state t.castSucc x) := by decide +kernel

def repairCertificate (t : Fin 3) :
    KempeSeparatedChains.Certificate (state t.castSucc) (repairPair t).1 (repairPair t).2 where
  vertices := repairChain t
  root := repairRoot t
  root_mem := (repair_checked t).1
  connected := (repair_checked t).2.1
  active := (repair_checked t).2.2.1
  closed := (repair_checked t).2.2.2.1

theorem repair_eq (t : Fin 3) : (repairCertificate t).swap = state t.succ := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact ((repair_checked t).2.2.2.2 x).symm

noncomputable def repairStep (t : Fin 3) : Step (state t.castSucc) (state t.succ) :=
  repair_eq t ▸ (repairCertificate t).step

noncomputable def repairHistory : History (state 0) (state 3) :=
  .cons (repairStep 0) (.cons (repairStep 1) (.cons (repairStep 2) (.refl _)))

theorem repair_length : repairHistory.length = 3 := rfl

def finalCore : Fin 8 → Color := ![c0,c2,c0,c3,c3,c1,c2,c0]

theorem final_valid : ValidCore (fun j => state 3 (ports j)) finalCore := by
  unfold ValidCore
  decide +kernel

/-- Full adjacency of the exterior glued to the original eight-vertex core. -/
def wholeEdges : List (Fin 31 × Fin 31) :=
  exteriorEdges.map (fun e => (e.1.castLE (by decide), e.2.castLE (by decide))) ++
    StripResponseSummary.edges.map (fun e => (e.1.natAdd 23,e.2.natAdd 23)) ++
    (List.finRange 8).flatMap (fun i => (attachments i).map
      (fun j => (i.natAdd 23,j.castLE (by decide))))

def whole : SimpleGraph (Fin 31) where
  Adj u v := (u,v) ∈ wholeEdges ∨ (v,u) ∈ wholeEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel whole.Adj := by unfold whole; infer_instance

/-- The source embedding fixes the ordered ports and retains every core edge. -/
def sourceVertex (v : Fin 19) : Fin 31 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 31)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 23) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    whole.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel

theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 31,
    whole.Adj (i.natAdd 23) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (TriangleStripAnchors.vertex0099 i) j ∧
        sourceVertex j = v := by decide +kernel

/-- The all-phase lower bound applies to arbitrary colourings of the actual
source with any omitted core vertices. -/
theorem source_phase_requires_two (a b : Color) (D : exterior.Coloring Color)
    (history : Relation.ReflTransGen (KempePairHistory.Step a b) (state 0) D)
    (h : Finset (Fin 8))
    (k : (TriangleStripAnchors.input0099.graph.induce {v | Live h v}).Coloring Color)
    (boundary : ∀ i, k ⟨port i, live_port h i⟩ = D (ports i)) : 2 ≤ h.card := by
  obtain ⟨f,hf⟩ := validExcept_of_source (fun i => D (ports i)) h k boundary
  exact any_pair_requires_two a b D history hf

def finalValues (v : Fin 31) : Color :=
  Fin.addCases (m := 23) (n := 8) (motive := fun _ => Color) (fun x => state 3 x) finalCore v

theorem whole_valid : ∀ u v, whole.Adj u v → finalValues u ≠ finalValues v := by decide +kernel

def finalColouring : whole.Coloring Color := .mk finalValues (fun h => whole_valid _ _ h)

theorem final_exterior (v : Fin 23) : finalColouring (v.castAdd 8) = state 3 v := by
  change Fin.addCases (m := 23) (n := 8) (motive := fun _ => Color)
    (fun x => state 3 x) finalCore (v.castAdd 8) = _
  simp

/-- The repair has actual physical steps and reconstructs a proper colouring
on every vertex of the glued graph. -/
theorem reconstructed : Nonempty (History (state 0) (state 3)) ∧
    ∃ k : whole.Coloring Color, ∀ v : Fin 23, k (v.castAdd 8) = state 3 v :=
  ⟨⟨repairHistory⟩, finalColouring, final_exterior⟩

end FourColor.StripPhaseObstruction
