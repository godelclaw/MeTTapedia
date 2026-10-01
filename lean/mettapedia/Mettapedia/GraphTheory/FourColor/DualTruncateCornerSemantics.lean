import Mettapedia.GraphTheory.FourColor.DualTruncateColoring

/-!
# Exact corner semantics for dual-and-truncate colourings

Keep one polygon-corner colour per source dart. At every expanded vertex,
the cross-edge colour is forced by the other two colours. Equality at its
two endpoints is the retained joint balance equation. Eliminating those
cross-edge variables gives an equivalence of actual colouring witnesses,
without requiring the corners of a source vertex to share one colour.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateCornerSemantics

open DualTruncateColoring

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E)

/-- The two retained polygon colours at one actual expanded vertex. -/
def corner (c : Edge RS → Color) (d : RS.D) : Color :=
  c (.inr (RS.phi.symm d))

/-- Properness of the three actual edge colours at one target vertex. -/
def Star (c : Edge RS → Color) (d : RS.D) : Prop :=
  (∀ i : Fin 3, c ((rotation RS).edgeOf (d,i)) ≠ 0) ∧
  Function.Injective (fun i : Fin 3 => c ((rotation RS).edgeOf (d,i)))

@[simp] theorem corner_phi (c : Edge RS → Color) (d : RS.D) :
    corner RS c (RS.phi d) = c (.inr d) := by
  simp [-RotationSystem.phi_apply, corner]

theorem corner_star_two (c : Edge RS → Color) (d : RS.D) :
    c ((rotation RS).edgeOf (d,2)) = corner RS c d := rfl

private theorem third_sum (x a b : Color) (hx : x ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) :
    x = a+b := by
  revert x a b
  decide +kernel

theorem cross_of_star {c : Edge RS → Color} {d : RS.D} (h : Star RS c d) :
    c (.inl (RS.edgeOf d)) = corner RS c d + corner RS c (RS.phi d) := by
  rw [corner_phi]
  apply third_sum
  · exact h.1 0
  · exact h.1 2
  · exact h.1 1
  · exact fun he => (by decide : (0 : Fin 3) ≠ 2) (h.2 he)
  · exact fun he => (by decide : (0 : Fin 3) ≠ 1) (h.2 he)
  · exact fun he => (by decide : (2 : Fin 3) ≠ 1) (h.2 he)

theorem star_of_tait (c : (rotation RS).EdgeColoring Color)
    (hc : (rotation RS).IsTaitEdgeColoring c) (d : RS.D) : Star RS c d := by
  refine ⟨fun i => hc _, ?_⟩
  intro i j he
  by_contra hij
  have hedge : (rotation RS).edgeOf (d,i) ≠ (rotation RS).edgeOf (d,j) := by
    intro h
    apply hij
    exact congrArg Prod.snd ((rotation RS).edgeOf_injOn_dartsAt d
      (by simp [RotationSystem.dartsAt, rotation])
      (by simp [RotationSystem.dartsAt, rotation]) h)
  have hadj : (rotation RS).edgeAdjacencyGraph.Adj
      ((rotation RS).edgeOf (d,i)) ((rotation RS).edgeOf (d,j)) :=
    ⟨hedge, d,
      (rotation RS).mem_endpoints_iff.mpr ⟨(d,i), (rotation RS).mem_dartsOn.mpr rfl, rfl⟩,
      (rotation RS).mem_endpoints_iff.mpr ⟨(d,j), (rotation RS).mem_dartsOn.mpr rfl, rfl⟩⟩
  exact c.valid hadj he

/-- Cross-endpoint agreement is retained rather than checked separately. -/
def Balanced (q : RS.D → Color) (d : RS.D) : Prop :=
  q d + q (RS.phi d) = q (RS.alpha d) + q (RS.phi (RS.alpha d))

def Valid (q : RS.D → Color) : Prop :=
  (∀ d, q d ≠ 0) ∧ (∀ d, q d ≠ q (RS.phi d)) ∧ ∀ d, Balanced RS q d

theorem corners_balanced_of_stars {c : Edge RS → Color} {d : RS.D}
    (hd : Star RS c d) (ha : Star RS c (RS.alpha d)) :
    Balanced RS (corner RS c) d := by
  unfold Balanced
  rw [← cross_of_star RS hd, ← cross_of_star RS ha, RS.edge_alpha]

theorem corners_valid (c : (rotation RS).EdgeColoring Color)
    (hc : (rotation RS).IsTaitEdgeColoring c) : Valid RS (corner RS c) := by
  refine ⟨fun d => hc _, ?_, ?_⟩
  · intro d h
    have hs := star_of_tait RS c hc d
    have he : c ((rotation RS).edgeOf (d,2)) = c ((rotation RS).edgeOf (d,1)) := by
      rw [corner_star_two RS c d]
      change corner RS c d = c (.inr d)
      rw [← corner_phi RS c d]
      exact h
    exact (by decide : (2 : Fin 3) ≠ 1) (hs.2 he)
  · intro d
    exact corners_balanced_of_stars RS (star_of_tait RS c hc d)
      (star_of_tait RS c hc (RS.alpha d))

def cross (q : RS.D → Color) (e : E) : Color :=
  let d := (RS.dartsOn_nonempty e).choose
  q d + q (RS.phi d)

theorem cross_edge (q : RS.D → Color) (d : RS.D) (h : Balanced RS q d) :
    cross RS q (RS.edgeOf d) = q d + q (RS.phi d) := by
  let y := (RS.dartsOn_nonempty (RS.edgeOf d)).choose
  have hy : RS.edgeOf y = RS.edgeOf d :=
    RS.mem_dartsOn.mp (RS.dartsOn_nonempty (RS.edgeOf d)).choose_spec
  change q y + q (RS.phi y) = _
  rcases RS.edge_fiber_two_cases rfl hy with he | he
  · rw [he]
  · rw [he]
    exact h.symm

def edgeColours (q : RS.D → Color) : Edge RS → Color
  | .inl e => cross RS q e
  | .inr d => q (RS.phi d)

@[simp] theorem edge_star_one (q : RS.D → Color) (d : RS.D) :
    edgeColours RS q ((rotation RS).edgeOf (d,1)) = q (RS.phi d) := rfl

@[simp] theorem edge_star_two (q : RS.D → Color) (d : RS.D) :
    edgeColours RS q ((rotation RS).edgeOf (d,2)) = q d := by
  simp [edgeColours, edgeOf]

theorem edge_star_zero (q : RS.D → Color) (d : RS.D) (h : Balanced RS q d) :
    edgeColours RS q ((rotation RS).edgeOf (d,0)) = q d + q (RS.phi d) :=
  cross_edge RS q d h

theorem edgeColours_star {q : RS.D → Color} {d : RS.D}
    (hd : q d ≠ 0) (hp : q (RS.phi d) ≠ 0)
    (hne : q d ≠ q (RS.phi d)) (hb : Balanced RS q d) :
    Star RS (edgeColours RS q) d := by
  have he : (fun i : Fin 3 => edgeColours RS q ((rotation RS).edgeOf (d,i))) =
      (fun i => if i = 0 then q d + q (RS.phi d) else if i = 1 then q (RS.phi d) else q d) := by
    funext i
    fin_cases i
    · exact edge_star_zero RS q d hb
    · exact edge_star_one RS q d
    · exact edge_star_two RS q d
  change (∀ i, (fun i : Fin 3 => edgeColours RS q ((rotation RS).edgeOf (d,i))) i ≠ 0) ∧
    Function.Injective (fun i : Fin 3 => edgeColours RS q ((rotation RS).edgeOf (d,i)))
  rw [he]
  have good (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
      (∀ i : Fin 3, (if i = 0 then a+b else if i = 1 then b else a) ≠ 0) ∧
      Function.Injective (fun i : Fin 3 => if i = 0 then a+b else if i = 1 then b else a) := by
    revert a b
    decide +kernel
  exact good _ _ hd hp hne

def colouring (q : RS.D → Color) (h : Valid RS q) : (rotation RS).EdgeColoring Color where
  toFun := edgeColours RS q
  map_rel' := by
    intro e f hadj
    obtain ⟨hef,v,he,hf⟩ := hadj
    obtain ⟨⟨d,i⟩,hde,hdv⟩ := (rotation RS).mem_endpoints_iff.mp he
    obtain ⟨⟨y,j⟩,hyf,hyv⟩ := (rotation RS).mem_endpoints_iff.mp hf
    have hd : d = v := hdv
    have hy : y = v := hyv
    subst d
    subst y
    have hde := (rotation RS).mem_dartsOn.mp hde
    have hyf := (rotation RS).mem_dartsOn.mp hyf
    rw [← hde, ← hyf]
    intro hc
    have hij := (edgeColours_star RS (h.1 v) (h.1 (RS.phi v))
      (h.2.1 v) (h.2.2 v)).2 hc
    exact hef (hde.symm.trans (hij ▸ hyf))

theorem colouring_tait (q : RS.D → Color) (h : Valid RS q) :
    (rotation RS).IsTaitEdgeColoring (colouring RS q h) := by
  rintro (e | d)
  · obtain ⟨d,hd⟩ := RS.dartsOn_nonempty e
    have he := RS.mem_dartsOn.mp hd
    change cross RS q e ≠ 0
    rw [← he, cross_edge RS q d (h.2.2 d)]
    exact add_ne_zero_of_ne (h.2.1 d)
  · exact h.1 (RS.phi d)

@[simp] theorem corner_edgeColours (q : RS.D → Color) :
    corner RS (edgeColours RS q) = q := by
  funext d
  simp [corner, edgeColours]

theorem edgeColours_corners (c : (rotation RS).EdgeColoring Color)
    (hc : (rotation RS).IsTaitEdgeColoring c) :
    edgeColours RS (corner RS c) = c := by
  funext e
  rcases e with e | d
  · let y := (RS.dartsOn_nonempty e).choose
    have hy := RS.mem_dartsOn.mp (RS.dartsOn_nonempty e).choose_spec
    change corner RS c y + corner RS c (RS.phi y) = c (.inl e)
    rw [← cross_of_star RS (star_of_tait RS c hc y), hy]
  · simp only [edgeColours, corner_phi]

/-- This is an equivalence of actual witnesses, so it also preserves counts. -/
def colouringEquiv :
    {c : (rotation RS).EdgeColoring Color // (rotation RS).IsTaitEdgeColoring c} ≃
      {q : RS.D → Color // Valid RS q} where
  toFun c := ⟨corner RS c.val, corners_valid RS c.val c.property⟩
  invFun q := ⟨colouring RS q.val q.property, colouring_tait RS q.val q.property⟩
  left_inv c := by
    apply Subtype.ext
    apply DFunLike.ext
    intro e
    exact congrFun (edgeColours_corners RS c.val c.property) e
  right_inv q := by
    apply Subtype.ext
    exact corner_edgeColours RS q.val

end
end Mettapedia.GraphTheory.FourColor.DualTruncateCornerSemantics
