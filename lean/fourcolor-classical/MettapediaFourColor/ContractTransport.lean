import MettapediaFourColor.HypermapTransport
import FourColor.Coloring

/-!
# Exact transport of contract colourings

Relabelling carries the entire contracted edge set and the actual face
assignment together. The contract is an observation on genuine darts, not
an independently chosen boundary colouring.
-/

namespace FourColor.Hypermap

variable {D D' : Type*} (G : Hypermap D) (e : D ≃ D')

theorem insertE_relabel (cc : List D) :
    (G.relabel e).insertE (cc.map e) = (G.insertE cc).map e := by
  induction cc with
  | nil => rfl
  | cons d cc ih => simp only [List.map_cons, insertE, relabel_edge, ih]

theorem ccColoring_relabel (cc : List D) (k : D' → Color) :
    (G.relabel e).CcColoring (cc.map e) k ↔ G.CcColoring cc (k ∘ e) := by
  have mem (d : D) :
      e d ∈ (G.relabel e).insertE (cc.map e) ↔ d ∈ G.insertE cc := by
    rw [insertE_relabel]
    simp
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro d
      simpa only [relabel_edge, mem, Function.comp_apply] using h.edge (e d)
    · intro d
      simpa only [relabel_face, Function.comp_apply] using h.face (e d)
  · intro h
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨d, rfl⟩ := e.surjective z
      simpa only [relabel_edge, mem, Function.comp_apply] using h.edge d
    · intro z
      obtain ⟨d, rfl⟩ := e.surjective z
      simpa only [relabel_face, Function.comp_apply] using h.face d

/-- Push the supplied witness forward, preserving the contracted edge list. -/
theorem ccColoring_push (cc : List D) (k : D → Color) (h : G.CcColoring cc k) :
    (G.relabel e).CcColoring (cc.map e) (k ∘ e.symm) := by
  apply (ccColoring_relabel G e cc _).mpr
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

end FourColor.Hypermap
