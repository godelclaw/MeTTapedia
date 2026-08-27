import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryEssentialGluing
import Mathlib.Logic.Equiv.Defs

/-!
# Transporting connectivity and bridgelessness along a multigraph isomorphism

The gluing lemmas are proved on one presentation of the glued graph; the
rotation-system composite is another presentation of the same graph, with its
edges named by dart orbits.  Moving the lemmas across needs only that the two
presentations agree on which vertices each edge joins — and since an edge's
endpoints are an unordered pair, agreement is allowed to swap them.

An *isomorphism* here is a bijection on vertices and a bijection on edges under
which every edge's endpoint pair corresponds, in either order.  Under such a map
a permitted step corresponds to a permitted step, so reachability, connectivity
and bridgelessness all correspond.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MultigraphTransport

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24BoundaryEssentialGluing.Multigraph

variable {V E V' E' : Type*}

/-- A multigraph isomorphism: bijections on vertices and edges preserving each
edge's unordered endpoint pair. -/
structure Iso (g : Multigraph V E) (g' : Multigraph V' E') where
  vert : V ≃ V'
  edge : E ≃ E'
  ends : ∀ e : E,
    (g'.fst (edge e) = vert (g.fst e) ∧ g'.snd (edge e) = vert (g.snd e)) ∨
      (g'.fst (edge e) = vert (g.snd e) ∧ g'.snd (edge e) = vert (g.fst e))

namespace Iso

variable {g : Multigraph V E} {g' : Multigraph V' E'}

/-- The inverse isomorphism. -/
def symm (φ : Iso g g') : Iso g' g where
  vert := φ.vert.symm
  edge := φ.edge.symm
  ends := by
    intro e'
    have h := φ.ends (φ.edge.symm e')
    rw [Equiv.apply_symm_apply] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(Equiv.eq_symm_apply _).2 h1.symm, (Equiv.eq_symm_apply _).2 h2.symm⟩
    · exact Or.inr ⟨(Equiv.eq_symm_apply _).2 h2.symm, (Equiv.eq_symm_apply _).2 h1.symm⟩

/-- A permitted step transports forward, with the avoided edge transported. -/
theorem stepAvoiding_map (φ : Iso g g') {avoid : E → Prop} {u v : V}
    (h : g.StepAvoiding avoid u v) :
    g'.StepAvoiding (fun e' => avoid (φ.edge.symm e')) (φ.vert u) (φ.vert v) := by
  obtain ⟨e, hne, hends⟩ := h
  refine ⟨φ.edge e, by simpa using hne, ?_⟩
  rcases φ.ends e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact Or.inl ⟨by rw [h1, hu], by rw [h2, hv]⟩
  · exact Or.inr ⟨by rw [h1, hu], by rw [h2, hv]⟩
  · exact Or.inr ⟨by rw [h1, hv], by rw [h2, hu]⟩
  · exact Or.inl ⟨by rw [h1, hv], by rw [h2, hu]⟩

theorem reflTransGen_map (φ : Iso g g') {avoid : E → Prop} {u v : V}
    (h : Relation.ReflTransGen (g.StepAvoiding avoid) u v) :
    Relation.ReflTransGen (g'.StepAvoiding (fun e' => avoid (φ.edge.symm e')))
      (φ.vert u) (φ.vert v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (φ.stepAvoiding_map hstep)

/-- **Connectivity transports.** -/
theorem connected_of (φ : Iso g g') (h : g.Connected) : g'.Connected := by
  intro u' v'
  have := φ.reflTransGen_map (avoid := fun _ => False)
    (h (φ.vert.symm u') (φ.vert.symm v'))
  simpa [Multigraph.Reach, Multigraph.Step] using this

/-- **Bridgelessness transports.** -/
theorem bridgeless_of (φ : Iso g g') (h : g.Bridgeless) : g'.Bridgeless := by
  intro e' hbr
  apply hbr
  have hreach : g.ReachAvoiding (φ.edge.symm e')
      (g.fst (φ.edge.symm e')) (g.snd (φ.edge.symm e')) :=
    Classical.byContradiction (h (φ.edge.symm e'))
  have hmap := φ.reflTransGen_map (avoid := (· = φ.edge.symm e')) hreach
  have hpred : (fun x : E' => φ.edge.symm x = φ.edge.symm e') = (· = e') := by
    funext x
    exact propext φ.edge.symm.injective.eq_iff
  rw [hpred] at hmap
  have hends := φ.ends (φ.edge.symm e')
  rw [Equiv.apply_symm_apply] at hends
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hmap
  · rw [h1, h2]; exact Multigraph.reachAvoiding_symm hmap

end Iso

end GoertzelV24MultigraphTransport

end Mettapedia.GraphTheory.FourColor
