import Mettapedia.GraphTheory.FourColor.OrderedPathExtension
import Mettapedia.GraphTheory.FourColor.EdgeColouringGluing

/-!
# Uniqueness of reconstruction across a short exposed path

Once the retained endpoint profiles omit unique colours, a proper
extension fixes both end-edge colours. For a path of at most two edges,
these are all the new edges, so restriction determines the entire
extension. This concerns colouring witnesses, independently of whether
recolouring histories on the smaller graph lift to the larger graph.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedEdgePath

open GoertzelV24ForkInterfaceSupport

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {inc : E → Finset V} {S : Finset E} (p : Path inc S)

/-- Properness forces each new end edge to carry the old missing colour. -/
theorem Path.end_colours_of_extension
    (A : Finset E) (hAS : Disjoint A S) (a d : E → Fin 3) (r s : Fin 3)
    (hr : ∀ q, q ∉ profile inc A a p.first ↔ q = r)
    (hs : ∀ q, q ∉ profile inc A a p.last ↔ q = s)
    (hd : Proper inc (A ∪ S) d) (hda : ∀ x ∈ A, d x = a x) :
    d p.firstEdge = r ∧ d p.lastEdge = s := by
  have hglue : EdgeColouringGluing.glue A d d = d := by
    funext x
    simp [EdgeColouringGluing.glue]
  have hcompat := ((EdgeColouringGluing.glue_proper_iff inc A S hAS d d).mp
    (hglue.symm ▸ hd)).2.2
  rw [EdgeColouringGluing.profile_congr inc A d a hda] at hcompat
  constructor
  · apply (hr _).mp
    have h := hcompat p.first
    rw [p.profile_first] at h
    exact Finset.disjoint_singleton_right.mp h
  · apply (hs _).mp
    have h := hcompat p.last
    rw [p.profile_last] at h
    exact Finset.disjoint_singleton_right.mp h

/-- For a one- or two-edge exposed path, there is at most one extension
on the retained union. Values outside the union remain irrelevant. -/
theorem Path.extension_unique_of_length_le_two (hshort : p.length ≤ 2)
    (A : Finset E) (hAS : Disjoint A S) (a d e : E → Fin 3) (r s : Fin 3)
    (hr : ∀ q, q ∉ profile inc A a p.first ↔ q = r)
    (hs : ∀ q, q ∉ profile inc A a p.last ↔ q = s)
    (hd : Proper inc (A ∪ S) d) (he : Proper inc (A ∪ S) e)
    (hda : ∀ x ∈ A, d x = a x) (hea : ∀ x ∈ A, e x = a x) :
    ∀ x ∈ A ∪ S, d x = e x := by
  have hendsD := p.end_colours_of_extension A hAS a d r s hr hs hd hda
  have hendsE := p.end_colours_of_extension A hAS a e r s hr hs he hea
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (hda x hx).trans (hea x hx).symm
  · obtain ⟨i, hi⟩ := p.edge.surjective ⟨x, hx⟩
    have hix : (p.edge i).val = x := congrArg Subtype.val hi
    by_cases hi0 : i.val = 0
    · have hiz : i = ⟨0, p.positive⟩ := Fin.ext hi0
      rw [← hix, hiz]
      exact hendsD.1.trans hendsE.1.symm
    · have hil : i = ⟨p.length - 1, by have := p.positive; omega⟩ :=
        Fin.ext (by change i.val = p.length - 1; have := i.isLt; omega)
      rw [← hix, hil]
      exact hendsD.2.trans hendsE.2.symm

end Mettapedia.GraphTheory.FourColor.OrderedEdgePath
