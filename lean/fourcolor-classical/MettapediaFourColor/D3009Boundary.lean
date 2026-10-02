import MettapediaFourColor.D3009Wheel

/-!
# Completing the thirteen-port wheel boundary

All outer vertices are read from complete actual neighbour stars. Opposite
readings of each shared corner agree by triangular closure. The source graph
maps with all core rotations and degrees preserved; no core capture occurs
when the wheel is induced. The final triangle and four-cycle argument
excludes identifications between distinct outer ports.
-/

namespace FourColor.D3009Boundary

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open D3009Wheel ExceptionalCoreOrientation ExceptionalOverlap

set_option maxRecDepth 32768

def firstNeighbor : Fin 8 → Fin 8 := ![1,7,3,1,2,4,5,6]
theorem first_edge : ∀ i, core.Adj i (firstNeighbor i) := by decide +kernel
theorem first_spoke : ∀ i,
    spoke i ⟨0, (star_specs i).1⟩ = firstNeighbor i := by decide +kernel
theorem degree_pos : ∀ i : Fin 8, 0 < degree i := by decide +kernel
theorem center_adj : ∀ i : Fin 8, i ≠ 0 → core.Adj 0 i := by decide +kernel

theorem seam_last : ∀ i : Fin 8, i ≠ 0 →
    spoke (firstNeighbor i)
      ⟨(star (firstNeighbor i)).length - 1, by
        have := (star_specs (firstNeighbor i)).1; omega⟩ = i := by decide +kernel

def shift : Fin 8 → ℕ := ![0,1,2,2,1,2,2,2]
def fullRow (i : Fin 8) : List (Fin 21) :=
  (input.internalStar (i.natAdd 13)).rotate (shift i)
def fullSpoke (i : Fin 8) (p : Fin (degree i)) : Fin 21 := (fullRow i).getD p.val 0
def nextPos (i : Fin 8) (p : Fin (degree i)) : Fin (degree i) :=
  ⟨(p.val + 1) % degree i, Nat.mod_lt _ (degree_pos i)⟩

theorem fullRow_length : ∀ i, (fullRow i).length = degree i := by decide +kernel
theorem fullSpoke_core : ∀ (i : Fin 8) (p : Fin (star i).length),
    fullSpoke i ⟨p.val, lt_of_lt_of_le p.isLt (star_specs i).2.1⟩ =
      (spoke i p).natAdd 13 := by decide +kernel

def owner : Fin 13 → Fin 8 × ℕ :=
  ![(2,3),(2,4),(3,3),(3,4),(1,3),(7,3),(7,4),
    (6,3),(6,4),(5,3),(5,4),(4,3),(4,4)]

theorem owner_bounds : ∀ b : Fin 13,
    (star (owner b).1).length ≤ (owner b).2 ∧ (owner b).2 < degree (owner b).1 := by
  decide +kernel

theorem ring_cases : ∀ (i : Fin 8) (p : Fin (degree i)), (star i).length ≤ p.val →
    ∃ b : Fin 13, fullSpoke i p = b.castAdd 8 ∧
      (owner b = (i,p.val) ∨ (i ≠ 0 ∧ p.val + 1 = degree i ∧
        owner b = (firstNeighbor i, (star (firstNeighbor i)).length))) := by decide +kernel

theorem edge_reading : ∀ a b : Fin 21, input.graph.Adj a b →
    ∃ (i : Fin 8) (p : Fin (degree i)),
      (a = i.natAdd 13 ∧ b = fullSpoke i p) ∨
      (b = i.natAdd 13 ∧ a = fullSpoke i p) ∨
      (a = fullSpoke i p ∧ b = fullSpoke i (nextPos i p)) ∨
      (b = fullSpoke i p ∧ a = fullSpoke i (nextPos i p)) := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  (r : Reading rotation)

def base (i : Fin 8) : G.Dart :=
  ⟨(r.map i, r.map (firstNeighbor i)), r.map.map_adj (first_edge i)⟩

def around (i : Fin 8) (n : ℕ) : G.Dart := (rotation.vertexRotation ^ n) (base r i)

theorem around_fst (i : Fin 8) (n : ℕ) : (around r i n).fst = r.map i :=
  FacialStarCompletion.pow_fst rotation (base r i) n

theorem around_step (i : Fin 8) (n : ℕ) :
    rotation.vertexRotation (around r i n) = around r i (n + 1) := by
  simp only [around, pow_succ', Equiv.Perm.mul_apply]

theorem around_core (tri : Triangular rotation) (i : Fin 8) (p : Fin (star i).length) :
    (around r i p.val).snd = r.map (spoke i p) := by
  have hd : ∀ n (hn : n < (star i).length), around r i n =
      (⟨(r.map i, r.map (spoke i ⟨n, hn⟩)),
        r.map.map_adj ((star_specs i).2.2 _ |>.mpr ⟨⟨n, hn⟩, rfl⟩)⟩ : G.Dart) := by
    intro n
    induction n with
    | zero => intro hn; simp only [around, pow_zero, Equiv.Perm.one_apply, base, first_spoke]
    | succ n ih =>
      intro hn
      rw [← around_step, ih (by omega)]
      obtain ⟨_, _, eq⟩ := reading_turns rotation r tri i ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl
      exact eq
  exact congrArg (fun d : G.Dart => d.snd) (hd p.val p.isLt)

def vertex (v : Fin 21) : V :=
  if h : v.val < 13 then (around r (owner ⟨v.val, h⟩).1 (owner ⟨v.val, h⟩).2).snd
  else r.map ⟨v.val - 13, by omega⟩

theorem vertex_core (i : Fin 8) : vertex r (i.natAdd 13) = r.map i := by
  simp [vertex, Fin.natAdd]

theorem vertex_ring (p : Fin 13) :
    vertex r (p.castAdd 8) = (around r (owner p).1 (owner p).2).snd := by
  simp [vertex, p.isLt]

/-- The common centre retains every core observation within one edge. -/
theorem core_near (i : Fin 8) :
    r.map i ∈ LocalCoverageAssembly.closedBall G (r.map 0) 1 := by
  by_cases hi : i = 0
  · subst i
    exact LocalCoverageAssembly.centre_mem G _ _
  · let p : G.Walk (r.map 0) (r.map i) :=
      .cons (r.map.map_adj (center_adj i hi)) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le

/-- The complete joint boundary, including possible identifications, lies
within radius two of the same retained centre. -/
theorem vertex_near (v : Fin 21) :
    vertex r v ∈ LocalCoverageAssembly.closedBall G (r.map 0) 2 := by
  by_cases hv : v.val < 13
  · let q : Fin 13 := ⟨v.val, hv⟩
    have ve : v = q.castAdd 8 := by apply Fin.ext; rfl
    rw [ve, vertex_ring]
    apply LocalCoverageAssembly.ball_recenter G (b := 1) (core_near r (owner q).1)
    let p : G.Walk (r.map (owner q).1) (around r (owner q).1 (owner q).2).snd :=
      .cons (by simpa only [around_fst] using (around r (owner q).1 (owner q).2).adj) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le
  · let i : Fin 8 := ⟨v.val - 13, by omega⟩
    have ve : v = i.natAdd 13 := by apply Fin.ext; dsimp [i]; omega
    rw [ve, vertex_core]
    exact LocalCoverageAssembly.ball_mono G (by decide : 1 ≤ 2) (core_near r i)

variable [Finite V]

theorem around_period (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 8) :
    around r i (degree i) = around r i 0 := by
  have h := FacialStarCompletion.pow_degree rotation cyclic (base r i)
  change (rotation.vertexRotation ^ G.degree (r.map i)) (base r i) = base r i at h
  rw [r.degree_eq] at h
  exact h

theorem around_previous (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 8) :
    around r i (degree i - 1) = rotation.vertexRotation.symm (base r i) := by
  have h := FacialStarCompletion.pow_pred rotation cyclic (base r i)
  change (rotation.vertexRotation ^ (G.degree (r.map i) - 1)) _ = _ at h
  rw [r.degree_eq] at h
  exact h

/-- One seam law supplies all seven shared exterior-corner identities. -/
theorem outer_seam (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) (noncenter : i ≠ 0) :
    (around r i (degree i - 1)).snd =
      (around r (firstNeighbor i) (star (firstNeighbor i)).length).snd := by
  let j := firstNeighbor i
  have hn := (star_specs j).1
  have hd : (base r i).symm = around r j ((star j).length - 1) := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact (around_fst r j _).symm
    · have h := around_core r tri j ⟨(star j).length - 1, by omega⟩
      rw [seam_last i noncenter] at h
      exact h.symm
  rw [around_previous r cyclic, FacialStarCompletion.across_edge rotation tri, hd,
    around_step, Nat.sub_add_cancel hn]

theorem row_agrees (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) (p : Fin (degree i)) :
    vertex r (fullSpoke i p) = (around r i p.val).snd := by
  by_cases hp : p.val < (star i).length
  · rw [fullSpoke_core i ⟨p.val,hp⟩, vertex_core]
    exact (around_core r tri i ⟨p.val,hp⟩).symm
  obtain ⟨b,hb,own | ⟨nc,last,seam⟩⟩ := ring_cases i p (by omega)
  · rw [hb, vertex_ring, own]
  · rw [hb, vertex_ring, seam]
    have hp : p.val = degree i - 1 := by omega
    rw [hp]
    exact (outer_seam r tri cyclic i nc).symm

theorem around_next (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) (p : Fin (degree i)) :
    rotation.vertexRotation (around r i p.val) = around r i (nextPos i p).val := by
  rw [around_step]
  by_cases h : p.val + 1 < degree i
  · simp only [nextPos, Nat.mod_eq_of_lt h]
  · have he : p.val + 1 = degree i := by omega
    simp only [nextPos, he, Nat.mod_self]
    exact around_period r cyclic i

/-- All source edges, including the complete boundary cycle, have one joint
ambient reading. Equality of shared ports was proved before this map is built. -/
def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    input.graph →g G where
  toFun := vertex r
  map_rel' := by
    intro a b h
    obtain ⟨i,p,h⟩ := edge_reading a b h
    have center : G.Adj (vertex r (i.natAdd 13)) (vertex r (fullSpoke i p)) := by
      rw [vertex_core, row_agrees r tri cyclic]
      simpa only [around_fst] using (around r i p.val).adj
    have ring : G.Adj (vertex r (fullSpoke i p)) (vertex r (fullSpoke i (nextPos i p))) := by
      rw [row_agrees r tri cyclic, row_agrees r tri cyclic]
      have h := consecutive_adjacent rotation tri (around r i p.val)
      rwa [around_next r cyclic] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact center
    · exact center.symm
    · exact ring
    · exact ring.symm

/-- All full cyclic source steps are actual ambient corners. -/
theorem full_turn (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) (p : Fin (degree i)) :
    Corner rotation (vertex r (i.natAdd 13)) (vertex r (fullSpoke i p))
      (vertex r (fullSpoke i (nextPos i p))) := by
  have adj (q : Fin (degree i)) :
      G.Adj (vertex r (i.natAdd 13)) (vertex r (fullSpoke i q)) := by
    rw [vertex_core, row_agrees r tri cyclic]
    simpa only [around_fst] using (around r i q.val).adj
  have dart_eq (q : Fin (degree i)) :
      (⟨(vertex r (i.natAdd 13), vertex r (fullSpoke i q)), adj q⟩ : G.Dart) =
        around r i q.val := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((vertex_core r i).trans (around_fst r i q.val).symm)
      (row_agrees r tri cyclic i q)
  refine ⟨adj p, adj (nextPos i p), ?_⟩
  exact (congrArg rotation.vertexRotation (dart_eq p)).trans
    ((around_next r cyclic i p).trans (dart_eq (nextPos i p)).symm)

/-- No incident edge can escape the completed interface. -/
theorem star_covers (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) {v : V} (adj : G.Adj (r.map i) v) :
    ∃ p : Fin (degree i), vertex r (fullSpoke i p) = v := by
  let d : G.Dart := ⟨(r.map i, v), adj⟩
  obtain ⟨n, hn, he⟩ := FacialStarCompletion.covers rotation cyclic (base r i) d rfl
  change n < G.degree (r.map i) at hn
  rw [r.degree_eq] at hn
  exact ⟨⟨n, hn⟩, (row_agrees r tri cyclic i ⟨n, hn⟩).trans
    (congrArg (fun e : G.Dart => e.snd) he)⟩

theorem around_injective (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 8) :
    Function.Injective (fun p : Fin (degree i) => (around r i p.val).snd) :=
  WheelNeighborhood.neighbor_injective rotation (base r i) cyclic
    (r.degree_eq i) (degree_pos i)

/-- An exterior port cannot fold back into an induced core. This permits
identifications between different ring ports while excluding core capture. -/
theorem ring_outside_core (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j)
    (p : Fin 13) (j : Fin 8) : vertex r (p.castAdd 8) ≠ r.map j := by
  intro eq
  rw [vertex_ring] at eq
  let i := (owner p).1
  let n := (owner p).2
  obtain ⟨lo, hi⟩ := owner_bounds p
  have adj : G.Adj (r.map i) (r.map j) := by
    have h := (around r i n).adj
    rw [around_fst, eq] at h
    exact h
  obtain ⟨q, hq⟩ := (star_specs i).2.2 j |>.mp (reflect i j adj)
  have he : (around r i n).snd = (around r i q.val).snd := by
    rw [around_core r tri i q, hq]
    exact eq
  have indices : (⟨n, hi⟩ : Fin (degree i)) =
      ⟨q.val, lt_of_lt_of_le q.isLt (star_specs i).2.1⟩ :=
    around_injective r cyclic i he
  have hval := congrArg Fin.val indices
  have hqbound := q.isLt
  change n = q.val at hval
  change (star i).length ≤ n at lo
  omega


theorem owner_strict : ∀ p : Fin 13,
    (owner p).1 ≠ 0 ∧ (owner p).2 + 1 < degree (owner p).1 := by decide +kernel

theorem owner_injective : Function.Injective owner := by decide +kernel

theorem owner_neighbors : ∀ p q : Fin 13,
    core.Adj (owner p).1 (owner q).1 →
      (owner q).1 = firstNeighbor (owner p).1 ∨
      (owner p).1 = firstNeighbor (owner q).1 := by decide +kernel

theorem center_core : ∀ p : Fin (degree 0),
    ∃ j : Fin 8, fullSpoke 0 p = j.natAdd 13 := by decide +kernel

/-- An owned outer position excludes the final shared seam position. Thus it
cannot also be adjacent to the next rim vertex when all triangles are facial. -/
theorem owner_not_adj_next (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b) (p : Fin 13) :
    ¬ G.Adj (r.map (firstNeighbor (owner p).1)) (vertex r (p.castAdd 8)) := by
  let i := (owner p).1
  let n : Fin (degree i) := ⟨(owner p).2, (owner_bounds p).2⟩
  have pos := degree_pos i
  have adj : G.Adj (r.map i) (vertex r (p.castAdd 8)) := by
    rw [vertex_ring]
    simpa only [around_fst] using (around r i n.val).adj
  intro edge
  rcases facial _ _ _ (base r i).adj edge adj.symm with h | h
  · rw [vertex_ring] at h
    have step := (WheelNeighborhood.corner_iff rotation (base r i) cyclic
      (r.degree_eq i) pos (⟨0,pos⟩ : Fin (degree i)) n).mp h
    have eq := congrArg Fin.val step
    have small : 1 < degree i := by have := owner_bounds p; have := owner_strict p; dsimp [i]; omega
    simp only [WheelNeighborhood.next, Nat.zero_add, Nat.mod_eq_of_lt small] at eq
    have lo := (owner_bounds p).1
    have len : (star i).length = 3 := by
      have h := (owner_strict p).1
      have fact : ∀ j : Fin 8, j ≠ 0 → (star j).length = 3 := by decide +kernel
      exact fact i h
    change (owner p).2 = 1 at eq
    rw [len] at lo
    omega
  · rw [vertex_ring] at h
    have step := (WheelNeighborhood.corner_iff rotation (base r i) cyclic
      (r.degree_eq i) pos n (⟨0,pos⟩ : Fin (degree i))).mp h
    have eq := congrArg Fin.val step
    have small := (owner_strict p).2
    simp only [WheelNeighborhood.next, n, i, Nat.mod_eq_of_lt small] at eq
    change 0 = (owner p).2 + 1 at eq
    omega

/-- The source centre has no neighbour outside its completed core. -/
theorem center_not_adj_boundary (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j) (p : Fin 13) :
    ¬ G.Adj (r.map 0) (vertex r (p.castAdd 8)) := by
  intro adj
  obtain ⟨q,hq⟩ := star_covers r tri cyclic 0 adj
  obtain ⟨j,hj⟩ := center_core q
  rw [hj,vertex_core] at hq
  exact ring_outside_core r tri cyclic reflect p j hq.symm

/-- Four-cycle chords and facial triangles exclude all remaining outer-port
collisions. The proof uses the shared owners, not separate marginal views. -/
theorem boundary_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (core_inj : Function.Injective r.map)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b)
    (chord : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a ≠ c → b ≠ d → G.Adj a c ∨ G.Adj b d) :
    Function.Injective (fun p : Fin 13 => vertex r (p.castAdd 8)) := by
  intro p q eq
  change vertex r (p.castAdd 8) = vertex r (q.castAdd 8) at eq
  have adj (b : Fin 13) : G.Adj (r.map (owner b).1) (vertex r (b.castAdd 8)) := by
    rw [vertex_ring]
    simpa only [around_fst] using (around r (owner b).1 (owner b).2).adj
  by_cases same : (owner p).1 = (owner q).1
  · have values : (owner p).2 = (owner q).2 := by
      rw [vertex_ring,vertex_ring,← same] at eq
      have he : (⟨(owner p).2,(owner_bounds p).2⟩ : Fin (degree (owner p).1)) =
          ⟨(owner q).2,by rw [same]; exact (owner_bounds q).2⟩ :=
        around_injective r cyclic (owner p).1 eq
      exact congrArg Fin.val he
    exact owner_injective (Prod.ext same values)
  · have cp := r.map.map_adj (center_adj _ (owner_strict p).1)
    have cq := r.map.map_adj (center_adj _ (owner_strict q).1)
    have aq : G.Adj (vertex r (p.castAdd 8)) (r.map (owner q).1) := by
      rw [eq]; exact (adj q).symm
    rcases chord _ _ _ _ cp (adj p) aq cq.symm
        (ring_outside_core r tri cyclic reflect p 0).symm (core_inj.ne same) with h | h
    · exact (center_not_adj_boundary r tri cyclic reflect p h).elim
    · rcases owner_neighbors p q (reflect _ _ h) with h | h
      · have bad := adj q
        rw [← eq,h] at bad
        exact (owner_not_adj_next r cyclic facial p bad).elim
      · have bad := adj p
        rw [eq,h] at bad
        exact (owner_not_adj_next r cyclic facial q bad).elim

theorem vertex_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (core_inj : Function.Injective r.map)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b)
    (chord : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a ≠ c → b ≠ d → G.Adj a c ∨ G.Adj b d) : Function.Injective (vertex r) := by
  have split (v : Fin 21) : (∃ p : Fin 13, v = p.castAdd 8) ∨
      ∃ i : Fin 8, v = i.natAdd 13 := by
    by_cases h : v.val < 13
    · exact Or.inl ⟨⟨v.val,h⟩,by apply Fin.ext; rfl⟩
    · refine Or.inr ⟨⟨v.val-13,by omega⟩,?_⟩
      apply Fin.ext; simp only [Fin.val_natAdd]; omega
  intro a b eq
  rcases split a with ⟨p,rfl⟩ | ⟨i,rfl⟩ <;> rcases split b with ⟨q,rfl⟩ | ⟨j,rfl⟩
  · exact congrArg (Fin.castAdd 8)
      (boundary_injective r tri cyclic core_inj reflect facial chord eq)
  · rw [vertex_core] at eq
    exact (ring_outside_core r tri cyclic reflect p j eq).elim
  · rw [vertex_core] at eq
    exact (ring_outside_core r tri cyclic reflect q i eq.symm).elim
  · rw [vertex_core,vertex_core] at eq
    exact congrArg (fun i : Fin 8 => i.natAdd 13) (core_inj eq)

/-- Complete source graph, ordered interior stars and distinct actual vertices.
This geometric contract does not assert a colouring repair. -/
structure Occurrence (rotation : Data G) where
  hom : input.graph →g G
  degree_eq : ∀ i : Fin 8, G.degree (hom (i.natAdd 13)) = degree i
  turn : ∀ (i : Fin 8) (p : Fin (degree i)),
    Corner rotation (hom (i.natAdd 13)) (hom (fullSpoke i p))
      (hom (fullSpoke i (nextPos i p)))
  injective : Function.Injective hom
  near : ∀ v, hom v ∈ LocalCoverageAssembly.closedBall G (hom 13) 2

end FourColor.D3009Boundary
