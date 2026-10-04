import MettapediaFourColor.StripSourceExtension

/-!
# A sharp three-hole bound and coupled restoration in D0099

For every boundary assignment, deleting core vertices 0, 2 and 5 leaves
an explicitly colourable path. One proper boundary forces a hole in each
of three disjoint pieces, so two holes do not always suffice. Restoration
retains the common choices at the edge between missing vertices 2 and 5.
This concerns fixed-boundary partial colourings, not Kempe reducibility.
-/

namespace FourColor.StripPartialColouring

open Color TriangleStripAnchors StripResponseSummary StripSourceExtension

def ValidExcept (b : Boundary) (holes : Finset (Fin 8)) (f : Fin 8 → Color) : Prop :=
  (∀ v, v ∉ holes → unary b v (f v)) ∧
    ∀ e ∈ edges, e.1 ∉ holes → e.2 ∉ holes → f e.1 ≠ f e.2

def holes : Finset (Fin 8) := {0, 2, 5}

def avoid (a b c : Color) : Color :=
  if c0 ≠ a ∧ c0 ≠ b ∧ c0 ≠ c then c0 else
  if c1 ≠ a ∧ c1 ≠ b ∧ c1 ≠ c then c1 else
  if c2 ≠ a ∧ c2 ≠ b ∧ c2 ≠ c then c2 else c3

theorem avoid_spec : ∀ a b c, avoid a b c ≠ a ∧ avoid a b c ≠ b ∧ avoid a b c ≠ c :=
  by decide +kernel

/-- Colour the path 7--6--4--1--3, leaving its three omitted vertices arbitrary. -/
def spine (b : Boundary) : Fin 8 → Color :=
  let a7 := avoid (b 0) (b 1) (b 10)
  let a6 := avoid (b 9) (b 10) a7
  let a4 := avoid (b 8) (b 9) a6
  let a3 := avoid (b 4) (b 5) (b 6)
  let a1 := avoid (b 8) a3 a4
  ![c0,a1,c0,a3,a4,c0,a6,a7]

private theorem path_valid (b : Boundary) (a1 a3 a4 a6 a7 : Color)
    (h1 : a1 ≠ b 8 ∧ a1 ≠ a3 ∧ a1 ≠ a4)
    (h3 : a3 ≠ b 4 ∧ a3 ≠ b 5 ∧ a3 ≠ b 6)
    (h4 : a4 ≠ b 8 ∧ a4 ≠ b 9 ∧ a4 ≠ a6)
    (h6 : a6 ≠ b 9 ∧ a6 ≠ b 10 ∧ a6 ≠ a7)
    (h7 : a7 ≠ b 0 ∧ a7 ≠ b 1 ∧ a7 ≠ b 10) :
    ValidExcept b holes ![c0,a1,c0,a3,a4,c0,a6,a7] := by
  constructor
  · intro v hv
    fin_cases v <;> simp_all [holes, unary, attachments]
  · intro e he
    simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [holes]

/-- Five vertices have compatible colours for every assignment on the boundary. -/
theorem spine_valid (b : Boundary) : ValidExcept b holes (spine b) := by
  exact path_valid b _ _ _ _ _ (avoid_spec _ _ _) (avoid_spec _ _ _)
    (avoid_spec _ _ _) (avoid_spec _ _ _) (avoid_spec _ _ _)

def Live (h : Finset (Fin 8)) (v : Fin 19) : Prop :=
  Fin.addCases (motive := fun _ => Prop)
    (fun _ : Fin 11 => True) (fun v : Fin 8 => v ∉ h) v

@[simp] theorem live_port (h : Finset (Fin 8)) (i : Fin 11) : Live h (port i) := by
  change Fin.addCases (fun _ : Fin 11 => True) (fun v : Fin 8 => v ∉ h) (i.castAdd 8)
  simp

@[simp] theorem live_core (h : Finset (Fin 8)) (i : Fin 8) :
    Live h (vertex0099 i) ↔ i ∉ h := by
  change Fin.addCases (fun _ : Fin 11 => True) (fun v : Fin 8 => v ∉ h) (i.natAdd 11) ↔ _
  simp

/-- All actual source edges among retained vertices are checked. -/
theorem partial_valid (b : Boundary) (h : Finset (Fin 8)) (f : Fin 8 → Color)
    (hb : ProperBoundary b) (hf : ValidExcept b h f) :
    ∀ u v, Live h u → Live h v → input0099.graph.Adj u v →
      completeColour b f u ≠ completeColour b f v := by
  intro u
  refine Fin.addCases (m := 11) (n := 8)
    (motive := fun u => ∀ v, Live h u → Live h v → input0099.graph.Adj u v →
      completeColour b f u ≠ completeColour b f v) (fun i => ?_) (fun i => ?_) u
  · intro v
    refine Fin.addCases (m := 11) (n := 8)
      (motive := fun v => Live h (port i) → Live h v → input0099.graph.Adj (port i) v →
        completeColour b f (port i) ≠ completeColour b f v) (fun j => ?_) (fun j => ?_) v
    · intro _ _ edge
      change completeColour b f (port i) ≠ completeColour b f (port j)
      simpa only [colour_port] using hb i j edge
    · intro _ hj edge
      change completeColour b f (port i) ≠ completeColour b f (vertex0099 j)
      simpa only [colour_port, colour_core] using
        (hf.1 j ((live_core h j).mp hj) i ((attachments_complete j i).mp edge.symm)).symm
  · intro v
    refine Fin.addCases (m := 11) (n := 8)
      (motive := fun v => Live h (vertex0099 i) → Live h v →
        input0099.graph.Adj (vertex0099 i) v →
        completeColour b f (vertex0099 i) ≠ completeColour b f v)
      (fun j => ?_) (fun j => ?_) v
    · intro hi _ edge
      change completeColour b f (vertex0099 i) ≠ completeColour b f (port j)
      simpa only [colour_port, colour_core] using
        hf.1 i ((live_core h i).mp hi) j ((attachments_complete i j).mp edge)
    · intro hi hj edge
      change completeColour b f (vertex0099 i) ≠ completeColour b f (vertex0099 j)
      rw [colour_core, colour_core]
      have hi := (live_core h i).mp hi
      have hj := (live_core h j).mp hj
      rcases (edges_complete i j).mp edge with he | he
      · exact hf.2 (i,j) he hi hj
      · exact (hf.2 (j,i) he hj hi).symm

def sourceSpine (b : Boundary) (hb : ProperBoundary b) :
    (input0099.graph.induce {v | Live holes v}).Coloring Color :=
  .mk (fun v => completeColour b (spine b) v.val)
    (fun {u v} edge => partial_valid b holes (spine b) hb (spine_valid b)
      u.val v.val u.property v.property edge)

theorem sourceSpine_boundary (b : Boundary) (hb : ProperBoundary b) (i : Fin 11) :
    sourceSpine b hb ⟨port i, live_port holes i⟩ = b i := colour_port _ _ _

/-- An arbitrary colouring of the retained source gives the same core contract. -/
theorem validExcept_of_source (b : Boundary) (h : Finset (Fin 8))
    (k : (input0099.graph.induce {v | Live h v}).Coloring Color)
    (hb : ∀ i, k ⟨port i, live_port h i⟩ = b i) :
    ∃ f, ValidExcept b h f := by
  let f (i : Fin 8) := if hi : i ∉ h then k ⟨vertex0099 i, (live_core h i).mpr hi⟩ else c0
  refine ⟨f, ?_, ?_⟩
  · intro v hv i hi
    have edge := k.valid (show (input0099.graph.induce {v | Live h v}).Adj
      ⟨vertex0099 v, (live_core h v).mpr hv⟩ ⟨port i, live_port h i⟩ from
        (attachments_complete v i).mpr hi)
    simpa only [f, dite_eq_left hv, hb] using edge
  · intro e he hu hv
    have edge := k.valid (show (input0099.graph.induce {v | Live h v}).Adj
      ⟨vertex0099 e.1, (live_core h e.1).mpr hu⟩
      ⟨vertex0099 e.2, (live_core h e.2).mpr hv⟩ from
        (edges_complete e.1 e.2).mpr (Or.inl he))
    simpa only [f, dite_eq_left hu, dite_eq_left hv] using edge

/-- The missing vertices share their choices; in particular a2 and a5 must differ. -/
def Completion (b : Boundary) (f : Fin 8 → Color) (a0 a2 a5 : Color) : Prop :=
  unary b 0 a0 ∧ unary b 2 a2 ∧ unary b 5 a5 ∧
  a0 ≠ f 1 ∧ a0 ≠ f 3 ∧
  a2 ≠ f 1 ∧ a2 ≠ f 3 ∧ a2 ≠ f 4 ∧ a2 ≠ f 6 ∧ a2 ≠ a5 ∧
  a5 ≠ f 6 ∧ a5 ≠ f 7

def fill (f : Fin 8 → Color) (a0 a2 a5 : Color) : Fin 8 → Color :=
  ![a0,f 1,a2,f 3,f 4,a5,f 6,f 7]

theorem fill_iff (b : Boundary) (f : Fin 8 → Color) (a0 a2 a5 : Color) :
    ValidCore b (fill f a0 a2 a5) ↔
      ValidExcept b holes f ∧ Completion b f a0 a2 a5 := by
  simp [ValidCore, ValidExcept, Completion, fill, holes, edges,
    Fin.forall_fin_succ, ne_comm]
  tauto

theorem reconstruct (b : Boundary) (hb : ProperBoundary b) (f : Fin 8 → Color)
    (hf : ValidExcept b holes f) {a0 a2 a5 : Color} (hc : Completion b f a0 a2 a5) :
    KempeBoundarySplit.GraphTrace input0099.graph input0099.boundary
      (trace (List.ofFn b)) :=
  graphTrace b hb ((terminal_iff b).mpr ⟨fill f a0 a2 a5, (fill_iff b f a0 a2 a5).mpr ⟨hf,hc⟩⟩)

/-- A proper boundary with three vertex-disjoint obstructions. -/
def testBoundary : Boundary := ![c0,c1,c0,c2,c3,c2,c0,c3,c2,c3,c2]

theorem example_proper : ProperBoundary testBoundary := by decide +kernel

theorem example_lists : ∀ v a, unary testBoundary v a ↔
    a ∈ (![ [c1], [c0,c1,c3], [c0,c1], [c1], [c0,c1], [c3], [c0,c1], [c3]]
      : Fin 8 → List Color) v := by decide +kernel

private theorem two_colours (a b c : Color)
    (ha : a = c0 ∨ a = c1) (hb : b = c0 ∨ b = c1) (hc : c = c0 ∨ c = c1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> simp_all

/-- Every partial colouring must omit a vertex from both forced edges and
from the two-colour triangle, even after arbitrary interior recolouring. -/
theorem three_obstructions {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (hf : ValidExcept testBoundary h f) :
    (0 ∈ h ∨ 3 ∈ h) ∧ (2 ∈ h ∨ 4 ∈ h ∨ 6 ∈ h) ∧ (5 ∈ h ∨ 7 ∈ h) := by
  have allowed v (hv : v ∉ h) := (example_lists v (f v)).mp (hf.1 v hv)
  have edge (u v : Fin 8) (he : (u,v) ∈ edges) (hu : u ∉ h) (hv : v ∉ h) :=
    hf.2 (u,v) he hu hv
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    have h0 := allowed 0 hn.1
    have h3 := allowed 3 hn.2
    have h03 := edge 0 3 (by decide) hn.1 hn.2
    simp_all
  · by_contra hn
    push Not at hn
    have h2 := allowed 2 hn.1
    have h4 := allowed 4 hn.2.1
    have h6 := allowed 6 hn.2.2
    exact two_colours (f 2) (f 4) (f 6) (by simpa using h2) (by simpa using h4)
      (by simpa using h6) (edge 2 4 (by decide) hn.1 hn.2.1)
      (edge 2 6 (by decide) hn.1 hn.2.2) (edge 4 6 (by decide) hn.2.1 hn.2.2)
  · by_contra hn
    push Not at hn
    have h5 := allowed 5 hn.1
    have h7 := allowed 7 hn.2
    have h57 := edge 5 7 (by decide) hn.1 hn.2
    simp_all

private theorem card_three {h : Finset (Fin 8)} {x y z : Fin 8}
    (hx : x ∈ h) (hy : y ∈ h) (hz : z ∈ h)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : 3 ≤ h.card := by
  have hs : ({x,y,z} : Finset (Fin 8)) ⊆ h := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  simpa [hxy, hxz, hyz] using Finset.card_le_card hs

theorem three_holes_necessary {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (hf : ValidExcept testBoundary h f) : 3 ≤ h.card := by
  obtain ⟨h03,h246,h57⟩ := three_obstructions hf
  obtain ⟨x,hx,hxh⟩ : ∃ x : Fin 8, (x = 0 ∨ x = 3) ∧ x ∈ h := by
    rcases h03 with h0 | h3
    · exact ⟨0, Or.inl rfl, h0⟩
    · exact ⟨3, Or.inr rfl, h3⟩
  obtain ⟨y,hy,hyh⟩ : ∃ y : Fin 8, (y = 2 ∨ y = 4 ∨ y = 6) ∧ y ∈ h := by
    rcases h246 with h2 | h4 | h6
    · exact ⟨2, Or.inl rfl, h2⟩
    · exact ⟨4, Or.inr (Or.inl rfl), h4⟩
    · exact ⟨6, Or.inr (Or.inr rfl), h6⟩
  obtain ⟨z,hz,hzh⟩ : ∃ z : Fin 8, (z = 5 ∨ z = 7) ∧ z ∈ h := by
    rcases h57 with h5 | h7
    · exact ⟨5, Or.inl rfl, h5⟩
    · exact ⟨7, Or.inr rfl, h7⟩
  apply card_three hxh hyh hzh
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> decide
  · rcases hx with rfl | rfl <;> rcases hz with rfl | rfl <;> decide
  · rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl <;> decide

/-- The lower bound applies to every actual source partial colouring fixing
this boundary, not just to the displayed greedy construction. -/
theorem source_three_holes (h : Finset (Fin 8))
    (k : (input0099.graph.induce {v | Live h v}).Coloring Color)
    (hb : ∀ i, k ⟨port i, live_port h i⟩ = testBoundary i) : 3 ≤ h.card := by
  obtain ⟨f,hf⟩ := validExcept_of_source testBoundary h k hb
  exact three_holes_necessary hf

/-- The universal upper bound is attained by an actual proper boundary. -/
theorem sharp_three_holes :
    (∀ b, ∃ h : Finset (Fin 8), h.card = 3 ∧ ∃ f, ValidExcept b h f) ∧
    (∃ b, ProperBoundary b ∧ ∀ h : Finset (Fin 8),
      (∃ f, ValidExcept b h f) → 3 ≤ h.card) := by
  exact ⟨fun b => ⟨holes, by decide, spine b, spine_valid b⟩,
    testBoundary, example_proper, fun _ ⟨_,hf⟩ => three_holes_necessary hf⟩

end FourColor.StripPartialColouring
