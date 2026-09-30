import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Vertex-to-edge colouring transport for dual-and-truncate maps

The expanded vertices are the source darts. At a source dart `d`, its three
neighbours are `alpha d`, `phi d`, and `phi.symm d`, with that cyclic order.
Cross edges retain the source edge identity; polygon edges are indexed by
the source darts. This is a literal rotation system, including parallel
edges when present, rather than an adjacency-only encoding.

A proper source vertex colouring by the three nonzero Klein colours gives
an actual target edge colouring. If the source edge has endpoint colours
`a` and `b`, the three colours at its expanded endpoint are `a+b`, `b`, `a`.
The source colouring is an explicit input: this changes the constraint
type and does not assert that every source has such a colouring.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateColoring

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] (RS : RotationSystem V E)

/-- The retained source witness uses precisely the three nonzero colours. -/
structure ThreeVertexColoring where
  colour : V → Color
  nonzero : ∀ v, colour v ≠ 0
  proper : ∀ d, colour (RS.vertOf d) ≠ colour (RS.vertOf (RS.alpha d))

abbrev Dart := RS.D × Fin 3
abbrev Edge := E ⊕ RS.D

/-- Slot zero crosses a source edge; the other slots follow a source face. -/
def flip (x : Dart RS) : Dart RS :=
  if x.2 = 0 then (RS.alpha x.1, 0)
  else if x.2 = 1 then (RS.phi x.1, 2)
  else (RS.phi.symm x.1, 1)

theorem flip_flip (x : Dart RS) : flip RS (flip RS x) = x := by
  rcases x with ⟨d, i⟩
  fin_cases i <;> simp [-RotationSystem.phi_apply, flip, RS.alpha_involutive]

def alpha : Equiv.Perm (Dart RS) where
  toFun := flip RS
  invFun := flip RS
  left_inv := flip_flip RS
  right_inv := flip_flip RS

def rho : Equiv.Perm (Dart RS) where
  toFun x := (x.1, x.2 + 1)
  invFun x := (x.1, x.2 - 1)
  left_inv := by rintro ⟨d, i⟩; simp
  right_inv := by rintro ⟨d, i⟩; simp

def edgeOf (x : Dart RS) : Edge RS :=
  if x.2 = 0 then .inl (RS.edgeOf x.1)
  else if x.2 = 1 then .inr x.1
  else .inr (RS.phi.symm x.1)

theorem edge_flip (x : Dart RS) : edgeOf RS (flip RS x) = edgeOf RS x := by
  rcases x with ⟨d, i⟩
  fin_cases i <;> simp [-RotationSystem.phi_apply, flip, edgeOf, RS.edge_alpha]

theorem cross_fiber (d : RS.D) :
    Finset.univ.filter (fun x : Dart RS => edgeOf RS x = .inl (RS.edgeOf d)) =
      {(d, 0), (RS.alpha d, 0)} := by
  apply Finset.ext
  intro x
  rcases x with ⟨y, i⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  fin_cases i <;> simp [edgeOf]
  constructor
  · exact RS.edge_fiber_two_cases rfl
  · rintro (rfl | rfl) <;> simp [RS.edge_alpha]

theorem polygon_fiber (d : RS.D) :
    Finset.univ.filter (fun x : Dart RS => edgeOf RS x = .inr d) =
      {(d, 1), (RS.phi d, 2)} := by
  apply Finset.ext
  intro x
  rcases x with ⟨y, i⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  fin_cases i <;> simp [-RotationSystem.phi_apply, edgeOf, Equiv.symm_apply_eq]

theorem phi_fixfree (d : RS.D) : RS.phi d ≠ d := by
  intro h
  apply RS.no_self_loops d
  exact (congrArg RS.vertOf h).symm.trans (RS.vert_phi_eq_vert_alpha d)

theorem phi_symm_fixfree (d : RS.D) : RS.phi.symm d ≠ d := by
  intro h
  apply phi_fixfree RS d
  have := congrArg RS.phi h
  simpa using this.symm

/-- The literal dual-and-truncate rotation has one vertex for each source dart. -/
abbrev rotation : RotationSystem RS.D (Edge RS) where
  D := Dart RS
  edgeOf := edgeOf RS
  vertOf := Prod.fst
  alpha := alpha RS
  rho := rho RS
  alpha_involutive := flip_flip RS
  alpha_fixfree := by
    rintro ⟨d, i⟩
    fin_cases i <;> simp [alpha, flip, RS.alpha_fixfree]
  edge_alpha := edge_flip RS
  edge_fiber_two := by
    intro e
    rcases e with e | d
    · obtain ⟨d, hd⟩ := RS.dartsOn_nonempty e
      have he : RS.edgeOf d = e := RS.mem_dartsOn.mp hd
      rw [← he, cross_fiber]
      simp [(RS.alpha_fixfree d).symm]
    · rw [polygon_fiber]
      simp
  vert_rho := by rintro ⟨d, i⟩; rfl
  outer := (RS.outer, 0)
  no_self_loops := by
    rintro ⟨d, i⟩
    fin_cases i
    · exact (RS.alpha_fixfree d).symm
    · exact (phi_fixfree RS d).symm
    · exact (phi_symm_fixfree RS d).symm

theorem cubic : (rotation RS).IsCubic := by
  intro d
  have h : (rotation RS).dartsAt d =
      ({(d, 0), (d, 1), (d, 2)} : Finset (Dart RS)) := by
    apply Finset.ext
    intro x
    rcases x with ⟨y, i⟩
    fin_cases i <;> simp [RotationSystem.dartsAt, rotation]
  rw [h]
  simp

/-- The construction triples the vertex count for a cubic source. -/
theorem vertex_count (h : RS.IsCubic) :
    Fintype.card RS.D = 3 * Fintype.card V :=
  RS.card_darts_eq_three_times_card_vertices h

theorem source_strictly_smaller (h : RS.IsCubic) :
    Fintype.card V < Fintype.card RS.D := by
  let : Nonempty V := ⟨RS.vertOf RS.outer⟩
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  rw [vertex_count RS h]
  omega

/-- Cross-edge colours are independent of which source dart names the edge. -/
def crossColour (c : V → Color) (e : E) : Color :=
  let d := (RS.dartsOn_nonempty e).choose
  c (RS.vertOf d) + c (RS.vertOf (RS.alpha d))

theorem crossColour_edge (c : V → Color) (d : RS.D) :
    crossColour RS c (RS.edgeOf d) =
      c (RS.vertOf d) + c (RS.vertOf (RS.alpha d)) := by
  let y := (RS.dartsOn_nonempty (RS.edgeOf d)).choose
  have hy : RS.edgeOf y = RS.edgeOf d :=
    RS.mem_dartsOn.mp (RS.dartsOn_nonempty (RS.edgeOf d)).choose_spec
  change c (RS.vertOf y) + c (RS.vertOf (RS.alpha y)) = _
  rcases RS.edge_fiber_two_cases rfl hy with heq | heq
  · simp [← heq]
  · simp [heq, RS.alpha_involutive, add_comm]

def edgeColour (c : V → Color) : Edge RS → Color
  | .inl e => crossColour RS c e
  | .inr d => c (RS.vertOf (RS.alpha d))

theorem vert_alpha_phi_symm (d : RS.D) :
    RS.vertOf (RS.alpha (RS.phi.symm d)) = RS.vertOf d := by
  simpa using (RS.vert_phi_eq_vert_alpha (RS.phi.symm d)).symm

theorem star_colour_zero (c : V → Color) (d : RS.D) :
    edgeColour RS c ((rotation RS).edgeOf (d, 0)) =
      c (RS.vertOf d) + c (RS.vertOf (RS.alpha d)) := by
  simp [edgeOf, edgeColour, crossColour_edge]

theorem star_colour_one (c : V → Color) (d : RS.D) :
    edgeColour RS c ((rotation RS).edgeOf (d, 1)) =
      c (RS.vertOf (RS.alpha d)) := by
  simp [edgeOf, edgeColour]

theorem star_colour_two (c : V → Color) (d : RS.D) :
    edgeColour RS c ((rotation RS).edgeOf (d, 2)) = c (RS.vertOf d) := by
  simp [edgeOf, edgeColour, vert_alpha_phi_symm]

theorem star_colour_distinct (c : ThreeVertexColoring RS) (d : RS.D)
    (i j : Fin 3) (hij : i ≠ j) :
    edgeColour RS c.colour ((rotation RS).edgeOf (d, i)) ≠
      edgeColour RS c.colour ((rotation RS).edgeOf (d, j)) := by
  fin_cases i <;> fin_cases j <;>
    simp [-RotationSystem.phi_apply, edgeOf, edgeColour,
      crossColour_edge, vert_alpha_phi_symm] <;>
    first
    | exact (hij rfl).elim
    | exact c.nonzero _
    | exact add_ne_right_of_ne_zero (c.nonzero (RS.vertOf d))
    | exact add_ne_left_of_ne_zero (c.nonzero (RS.vertOf (RS.alpha d)))
    | exact (add_ne_right_of_ne_zero (c.nonzero (RS.vertOf d))).symm
    | exact (add_ne_left_of_ne_zero (c.nonzero (RS.vertOf (RS.alpha d)))).symm
    | exact c.proper d
    | exact (c.proper d).symm

/-- The local law reconstructs a genuine proper edge-colouring witness. -/
def colouring (c : ThreeVertexColoring RS) : (rotation RS).EdgeColoring Color where
  toFun := edgeColour RS c.colour
  map_rel' := by
    intro e f h
    obtain ⟨hef, v, he, hf⟩ := h
    obtain ⟨⟨d, i⟩, hde, hdv⟩ := (rotation RS).mem_endpoints_iff.mp he
    obtain ⟨⟨y, j⟩, hyf, hyv⟩ := (rotation RS).mem_endpoints_iff.mp hf
    have hd : d = v := hdv
    have hy : y = v := hyv
    subst d
    subst y
    have hde : (rotation RS).edgeOf (v, i) = e := (rotation RS).mem_dartsOn.mp hde
    have hyf : (rotation RS).edgeOf (v, j) = f := (rotation RS).mem_dartsOn.mp hyf
    rw [← hde, ← hyf]
    apply star_colour_distinct RS c v i j
    intro hij
    exact hef (hde.symm.trans (hij ▸ hyf))

theorem colouring_nonzero (c : ThreeVertexColoring RS) :
    (rotation RS).IsTaitEdgeColoring (colouring RS c) := by
  rintro (e | d)
  · obtain ⟨d, hd⟩ := RS.dartsOn_nonempty e
    have he : RS.edgeOf d = e := RS.mem_dartsOn.mp hd
    change crossColour RS c.colour e ≠ 0
    rw [← he, crossColour_edge]
    exact add_ne_zero_of_ne (c.proper d)
  · exact c.nonzero (RS.vertOf (RS.alpha d))

/-- Actual colouring existence is transported, without assuming source existence. -/
theorem tait_of_three_vertex_colouring (h : Nonempty (ThreeVertexColoring RS)) :
    ∃ c : (rotation RS).EdgeColoring Color, (rotation RS).IsTaitEdgeColoring c := by
  obtain ⟨c⟩ := h
  exact ⟨colouring RS c, colouring_nonzero RS c⟩

end
end Mettapedia.GraphTheory.FourColor.DualTruncateColoring
