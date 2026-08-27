import Mathlib.Logic.Relation

/-!
# Boundary-essential gluing

Two connected sides with `k ≥ 2` ordered boundary half-edges, glued port to port,
give a connected and bridgeless graph — provided each side is *boundary-essential*,
meaning that deleting any of its bridges leaves a boundary half-edge on both sides
of the cut.

The argument is pure path surgery.  For an old edge `e` of one side: if it is not
a bridge there, a path already bypasses it.  If it is, its two sides carry ports
`p` and `q`; travel inside one component to `p`, cross the seam, traverse the other
side, and cross back at `q`.  For a seam edge, pick a second port and use the two
sides' connectivity.  That is why `k ≥ 2` is needed and why it is exactly enough.

Multigraph language is used deliberately: gluing can create parallel edges, and a
simple-graph carrier would silently identify two distinct seam edges.  Edges are
presented by their two endpoints, so loops and parallel edges are both
representable, and reachability is the reflexive-transitive closure of the
adjacency through the permitted edges — which makes every step of the surgery a
`trans`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundaryEssentialGluing

/-- A multigraph presented by the two endpoints of each edge. -/
structure Multigraph (Vtx Edg : Type*) where
  fst : Edg → Vtx
  snd : Edg → Vtx

namespace Multigraph

variable {Vtx Edg : Type*}

/-- One step across an edge that is not forbidden. -/
def StepAvoiding (g : Multigraph Vtx Edg) (avoid : Edg → Prop) (u v : Vtx) : Prop :=
  ∃ e : Edg, ¬ avoid e ∧
    ((g.fst e = u ∧ g.snd e = v) ∨ (g.fst e = v ∧ g.snd e = u))

/-- One step across any edge. -/
def Step (g : Multigraph Vtx Edg) : Vtx → Vtx → Prop :=
  g.StepAvoiding fun _ => False

/-- Reachability. -/
def Reach (g : Multigraph Vtx Edg) : Vtx → Vtx → Prop :=
  Relation.ReflTransGen g.Step

/-- Reachability avoiding one edge. -/
def ReachAvoiding (g : Multigraph Vtx Edg) (e₀ : Edg) : Vtx → Vtx → Prop :=
  Relation.ReflTransGen (g.StepAvoiding (· = e₀))

/-- Connectedness. -/
def Connected (g : Multigraph Vtx Edg) : Prop := ∀ u v, g.Reach u v

/-- An edge is a bridge when its endpoints part without it. -/
def IsBridge (g : Multigraph Vtx Edg) (e : Edg) : Prop :=
  ¬ g.ReachAvoiding e (g.fst e) (g.snd e)

/-- No edge is a bridge. -/
def Bridgeless (g : Multigraph Vtx Edg) : Prop := ∀ e, ¬ g.IsBridge e

theorem stepAvoiding_symm {g : Multigraph Vtx Edg} {avoid : Edg → Prop} {u v : Vtx}
    (h : g.StepAvoiding avoid u v) : g.StepAvoiding avoid v u := by
  obtain ⟨e, hne, hends⟩ := h
  exact ⟨e, hne, hends.symm.imp (fun h => h) (fun h => h)⟩

theorem reflTransGen_symm {g : Multigraph Vtx Edg} {avoid : Edg → Prop} {u v : Vtx}
    (h : Relation.ReflTransGen (g.StepAvoiding avoid) u v) :
    Relation.ReflTransGen (g.StepAvoiding avoid) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (stepAvoiding_symm hstep)) ih

theorem reachAvoiding_symm {g : Multigraph Vtx Edg} {e₀ : Edg} {u v : Vtx}
    (h : g.ReachAvoiding e₀ u v) : g.ReachAvoiding e₀ v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (stepAvoiding_symm hstep)) ih

theorem reach_symm {g : Multigraph Vtx Edg} {u v : Vtx} (h : g.Reach u v) : g.Reach v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (stepAvoiding_symm hstep)) ih

end Multigraph

open Multigraph

/-! ## The glued graph -/

variable {VH VK EH EK P : Type*}

/-- Gluing two sides port to port.  Vertices are the disjoint union, so a seam
edge never becomes a loop; edges are the two old edge sets together with one seam
edge per port, so two distinct ports never collapse to one edge. -/
def glue (H : Multigraph VH EH) (K : Multigraph VK EK)
    (pH : P → VH) (pK : P → VK) : Multigraph (VH ⊕ VK) (EH ⊕ EK ⊕ P) where
  fst
    | Sum.inl e => Sum.inl (H.fst e)
    | Sum.inr (Sum.inl e) => Sum.inr (K.fst e)
    | Sum.inr (Sum.inr p) => Sum.inl (pH p)
  snd
    | Sum.inl e => Sum.inl (H.snd e)
    | Sum.inr (Sum.inl e) => Sum.inr (K.snd e)
    | Sum.inr (Sum.inr p) => Sum.inr (pK p)

/-- A side is boundary-essential when deleting any of its bridges leaves a port
on both sides of the cut. -/
def BoundaryEssential (H : Multigraph VH EH) (pH : P → VH) : Prop :=
  ∀ e : EH, H.IsBridge e →
    (∃ p : P, H.ReachAvoiding e (H.fst e) (pH p)) ∧
      (∃ p : P, H.ReachAvoiding e (H.snd e) (pH p))

/-! ## Transporting each side into the glue -/

variable {H : Multigraph VH EH} {K : Multigraph VK EK} {pH : P → VH} {pK : P → VK}

/-- A permitted step of the first side is a permitted step of the glue. -/
theorem glue_step_inl {avoidH : EH → Prop} {avoidG : EH ⊕ EK ⊕ P → Prop}
    (hcompat : ∀ e, avoidG (Sum.inl e) → avoidH e) {u v : VH}
    (h : H.StepAvoiding avoidH u v) :
    (glue H K pH pK).StepAvoiding avoidG (Sum.inl u) (Sum.inl v) := by
  obtain ⟨e, hne, hends⟩ := h
  refine ⟨Sum.inl e, fun hcon => hne (hcompat e hcon), ?_⟩
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by simp [glue, h1], by simp [glue, h2]⟩
  · exact Or.inr ⟨by simp [glue, h1], by simp [glue, h2]⟩

/-- A permitted step of the second side is a permitted step of the glue. -/
theorem glue_step_inr {avoidK : EK → Prop} {avoidG : EH ⊕ EK ⊕ P → Prop}
    (hcompat : ∀ e, avoidG (Sum.inr (Sum.inl e)) → avoidK e) {u v : VK}
    (h : K.StepAvoiding avoidK u v) :
    (glue H K pH pK).StepAvoiding avoidG (Sum.inr u) (Sum.inr v) := by
  obtain ⟨e, hne, hends⟩ := h
  refine ⟨Sum.inr (Sum.inl e), fun hcon => hne (hcompat e hcon), ?_⟩
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by simp [glue, h1], by simp [glue, h2]⟩
  · exact Or.inr ⟨by simp [glue, h1], by simp [glue, h2]⟩

theorem glue_reach_inl {avoidH : EH → Prop} {avoidG : EH ⊕ EK ⊕ P → Prop}
    (hcompat : ∀ e, avoidG (Sum.inl e) → avoidH e) {u v : VH}
    (h : Relation.ReflTransGen (H.StepAvoiding avoidH) u v) :
    Relation.ReflTransGen ((glue H K pH pK).StepAvoiding avoidG)
      (Sum.inl u) (Sum.inl v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (glue_step_inl (K := K) (pK := pK) hcompat hstep)

theorem glue_reach_inr {avoidK : EK → Prop} {avoidG : EH ⊕ EK ⊕ P → Prop}
    (hcompat : ∀ e, avoidG (Sum.inr (Sum.inl e)) → avoidK e) {u v : VK}
    (h : Relation.ReflTransGen (K.StepAvoiding avoidK) u v) :
    Relation.ReflTransGen ((glue H K pH pK).StepAvoiding avoidG)
      (Sum.inr u) (Sum.inr v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (glue_step_inr (H := H) (pH := pH) hcompat hstep)

/-- Crossing the seam at a port that is not forbidden. -/
theorem glue_step_seam {avoidG : EH ⊕ EK ⊕ P → Prop} (p : P)
    (hne : ¬ avoidG (Sum.inr (Sum.inr p))) :
    (glue H K pH pK).StepAvoiding avoidG (Sum.inl (pH p)) (Sum.inr (pK p)) :=
  ⟨Sum.inr (Sum.inr p), hne, Or.inl ⟨rfl, rfl⟩⟩

/-! ## The gluing lemma -/

/-- **Gluing two connected boundary-essential sides is connected.** -/
theorem glue_connected (hH : H.Connected) (hK : K.Connected) (p₀ : P) :
    (glue H K pH pK).Connected := by
  have hcompatH : ∀ e : EH, (fun _ : EH ⊕ EK ⊕ P => False) (Sum.inl e) →
      (fun _ : EH => False) e := fun _ h => h
  have hcompatK : ∀ e : EK, (fun _ : EH ⊕ EK ⊕ P => False) (Sum.inr (Sum.inl e)) →
      (fun _ : EK => False) e := fun _ h => h
  have hcross : (glue H K pH pK).Reach (Sum.inl (pH p₀)) (Sum.inr (pK p₀)) :=
    Relation.ReflTransGen.single (glue_step_seam p₀ (fun h => h))
  intro u v
  rcases u with u | u <;> rcases v with v | v
  · exact glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK) hcompatH (hH u v)
  · exact ((glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK) hcompatH (hH u (pH p₀))).trans
      hcross).trans (glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK) hcompatK (hK (pK p₀) v))
  · refine (((glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK) hcompatK (hK u (pK p₀))).trans
      (Multigraph.reach_symm hcross)).trans
      (glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK) hcompatH (hH (pH p₀) v)))
  · exact glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK) hcompatK (hK u v)

/-- **Gluing two connected boundary-essential sides is bridgeless.**

Three cases, exactly as in the manuscript.  An old edge that is not a bridge of
its own side is bypassed there.  An old bridge has ports on both sides of its
cut, so the detour leaves through one, crosses, traverses the other side, and
returns through the other port.  A seam edge is bypassed using a second port,
which is where `k ≥ 2` is used. -/
theorem glue_bridgeless (hH : H.Connected) (hK : K.Connected)
    (hHess : BoundaryEssential H pH) (hKess : BoundaryEssential K pK)
    {p₀ q₀ : P} (hpq : p₀ ≠ q₀) :
    (glue H K pH pK).Bridgeless := by
  have hfalseH : ∀ (A : EH ⊕ EK ⊕ P → Prop) (e : EH),
      (∀ x, A x ↔ x = Sum.inr (Sum.inr p₀)) → A (Sum.inl e) → False := by
    intro A e hA h; simpa using (hA _).1 h
  intro edge hbridge
  apply hbridge
  rcases edge with e₀ | e₀ | p
  · -- an old edge of the first side
    by_cases hbr : H.IsBridge e₀
    · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hHess e₀ hbr
      have hcompatH : ∀ e : EH, (Sum.inl e : EH ⊕ EK ⊕ P) = Sum.inl e₀ → e = e₀ := by
        intro e h; simpa using h
      have hcompatK : ∀ e : EK, (Sum.inr (Sum.inl e) : EH ⊕ EK ⊕ P) = Sum.inl e₀ →
          False := by intro e h; simp at h
      have hleft := glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK)
        (avoidG := (· = Sum.inl e₀)) hcompatH hp
      have hright := glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK)
        (avoidG := (· = Sum.inl e₀)) hcompatH hq
      have hmid := glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK)
        (avoidG := (· = Sum.inl e₀)) hcompatK (hK (pK p) (pK q))
      have hseamP : (glue H K pH pK).StepAvoiding (· = Sum.inl e₀)
          (Sum.inl (pH p)) (Sum.inr (pK p)) :=
        glue_step_seam p (by simp)
      have hseamQ : (glue H K pH pK).StepAvoiding (· = Sum.inl e₀)
          (Sum.inl (pH q)) (Sum.inr (pK q)) :=
        glue_step_seam q (by simp)
      exact ((((hleft.tail hseamP).trans hmid).trans
        (Relation.ReflTransGen.single (Multigraph.stepAvoiding_symm hseamQ))).trans
        (Multigraph.reflTransGen_symm hright))
    · have hnb : H.ReachAvoiding e₀ (H.fst e₀) (H.snd e₀) := by
        simpa [Multigraph.IsBridge] using hbr
      have hcompatH : ∀ e : EH, (Sum.inl e : EH ⊕ EK ⊕ P) = Sum.inl e₀ → e = e₀ := by
        intro e h; simpa using h
      exact glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK) (avoidG := (· = Sum.inl e₀)) hcompatH hnb
  · -- an old edge of the second side
    by_cases hbr : K.IsBridge e₀
    · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hKess e₀ hbr
      have hcompatK : ∀ e : EK,
          (Sum.inr (Sum.inl e) : EH ⊕ EK ⊕ P) = Sum.inr (Sum.inl e₀) → e = e₀ := by
        intro e h; simpa using h
      have hcompatH : ∀ e : EH,
          (Sum.inl e : EH ⊕ EK ⊕ P) = Sum.inr (Sum.inl e₀) → False := by
        intro e h; simp at h
      have hleft := glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK)
        (avoidG := (· = Sum.inr (Sum.inl e₀))) hcompatK hp
      have hright := glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK)
        (avoidG := (· = Sum.inr (Sum.inl e₀))) hcompatK hq
      have hmid := glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK)
        (avoidG := (· = Sum.inr (Sum.inl e₀))) hcompatH (hH (pH p) (pH q))
      have hseamP : (glue H K pH pK).StepAvoiding (· = Sum.inr (Sum.inl e₀))
          (Sum.inl (pH p)) (Sum.inr (pK p)) :=
        glue_step_seam p (by simp)
      have hseamQ : (glue H K pH pK).StepAvoiding (· = Sum.inr (Sum.inl e₀))
          (Sum.inl (pH q)) (Sum.inr (pK q)) :=
        glue_step_seam q (by simp)
      exact (((hleft.tail (Multigraph.stepAvoiding_symm hseamP)).trans hmid).trans
        (Relation.ReflTransGen.single hseamQ)).trans
        (Multigraph.reflTransGen_symm hright)
    · have hnb : K.ReachAvoiding e₀ (K.fst e₀) (K.snd e₀) := by
        simpa [Multigraph.IsBridge] using hbr
      have hcompatK : ∀ e : EK,
          (Sum.inr (Sum.inl e) : EH ⊕ EK ⊕ P) = Sum.inr (Sum.inl e₀) → e = e₀ := by
        intro e h; simpa using h
      exact glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK)
        (avoidG := (· = Sum.inr (Sum.inl e₀))) hcompatK hnb
  · -- a seam edge, bypassed through a second port
    obtain ⟨r, hrp⟩ : ∃ r : P, r ≠ p := by
      by_cases hcase : p₀ = p
      · exact ⟨q₀, fun h => hpq (hcase.trans h.symm)⟩
      · exact ⟨p₀, hcase⟩
    have hcompatH : ∀ e : EH,
        (Sum.inl e : EH ⊕ EK ⊕ P) = Sum.inr (Sum.inr p) → False := by
      intro e h; simp at h
    have hcompatK : ∀ e : EK,
        (Sum.inr (Sum.inl e) : EH ⊕ EK ⊕ P) = Sum.inr (Sum.inr p) → False := by
      intro e h; simp at h
    have hHpath := glue_reach_inl (H := H) (K := K) (pH := pH) (pK := pK)
      (avoidG := (· = Sum.inr (Sum.inr p))) hcompatH (hH (pH p) (pH r))
    have hKpath := glue_reach_inr (H := H) (K := K) (pH := pH) (pK := pK)
      (avoidG := (· = Sum.inr (Sum.inr p))) hcompatK (hK (pK r) (pK p))
    have hseamR : (glue H K pH pK).StepAvoiding (· = Sum.inr (Sum.inr p))
        (Sum.inl (pH r)) (Sum.inr (pK r)) :=
      glue_step_seam r (by simpa using hrp)
    exact (hHpath.tail hseamR).trans hKpath

/-! ## A saturated side of a bridgeless graph is boundary-essential

The side is taken inside the ambient graph rather than as a separate object: a
vertex predicate picks it out, an edge is *internal* when both its endpoints lie
in it, and side reachability only uses internal edges.  Saturation says every
ambient edge leaving the side is represented by a port at its inside endpoint.

The argument is a single induction.  If deleting an internal bridge left a
component with no port, then every ambient step out of that component would have
to use either the deleted edge or an edge leaving the side -- and the latter
would put a port in the component.  So the component is ambiently separated by
one edge, contradicting bridgelessness. -/

section Saturated

variable {Vtx Edg : Type*} (G : Multigraph Vtx Edg) (side : Vtx → Prop)

/-- An edge lies inside the side when both its endpoints do. -/
def Internal (e : Edg) : Prop := side (G.fst e) ∧ side (G.snd e)

/-- Reachability inside the side, avoiding one internal edge. -/
def SideReachAvoiding (e₀ : Edg) : Vtx → Vtx → Prop :=
  Relation.ReflTransGen (G.StepAvoiding fun e => e = e₀ ∨ ¬ Internal G side e)

variable {G side}

/-- Side reachability never leaves the side. -/
theorem side_of_sideReachAvoiding {e₀ : Edg} {u v : Vtx} (hu : side u)
    (h : SideReachAvoiding G side e₀ u v) : side v := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih =>
      obtain ⟨f, hnf, hends⟩ := hstep
      have hint : Internal G side f :=
        Classical.byContradiction fun hcon => hnf (Or.inr hcon)
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 ▸ hint.2
      · exact h1 ▸ hint.1

/-- **A saturated side of a bridgeless graph is boundary-essential.**

`hsat` is saturation, `hbridgeless` is ambient bridgelessness, and the ports are
given by their attachment vertices. -/
theorem boundaryEssential_of_saturated {P : Type*} (portVertex : P → Vtx)
    (hbridgeless : G.Bridgeless)
    (hsat : ∀ e : Edg, ¬ Internal G side e →
      (side (G.fst e) → ∃ p : P, portVertex p = G.fst e) ∧
        (side (G.snd e) → ∃ p : P, portVertex p = G.snd e))
    (e₀ : Edg) (hint : Internal G side e₀)
    (hside : ¬ SideReachAvoiding G side e₀ (G.fst e₀) (G.snd e₀)) :
    ∃ p : P, SideReachAvoiding G side e₀ (G.fst e₀) (portVertex p) := by
  refine Classical.byContradiction fun hexists => ?_
  have hnoport : ∀ p : P, ¬ SideReachAvoiding G side e₀ (G.fst e₀) (portVertex p) :=
    fun p hp => hexists ⟨p, hp⟩
  -- with no port in the component, every ambient detour stays inside it
  have hstay : ∀ x : Vtx, G.ReachAvoiding e₀ (G.fst e₀) x →
      SideReachAvoiding G side e₀ (G.fst e₀) x := by
    intro x hx
    induction hx with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
        obtain ⟨f, hnf, hends⟩ := hstep
        by_cases hfint : Internal G side f
        · exact ih.tail ⟨f, by
            intro hcon
            rcases hcon with hcon | hcon
            · exact hnf hcon
            · exact hcon hfint, hends⟩
        · exfalso
          have hy : side _ := side_of_sideReachAvoiding hint.1 ih
          rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · obtain ⟨p, hp⟩ := (hsat f hfint).1 (h1 ▸ hy)
            exact hnoport p (hp ▸ h1 ▸ ih)
          · obtain ⟨p, hp⟩ := (hsat f hfint).2 (h2 ▸ hy)
            exact hnoport p (hp ▸ h2 ▸ ih)
  exact hside (hstay _ (Classical.byContradiction fun hcon => hbridgeless e₀ hcon))

end Saturated

end GoertzelV24BoundaryEssentialGluing

end Mettapedia.GraphTheory.FourColor

