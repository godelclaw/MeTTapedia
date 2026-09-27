import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkInterfaceSupport
import Mathlib.Data.Fin.Basic

/-!
# Proper colourings of an ordered simple edge path

The path retains its original vertex and edge identifiers. Its edge list
is a bijection with the chosen edge set, and the endpoint equation records
all incidence. Proper colouring of that piece is exactly inequality of
consecutive edge colours.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedEdgePath

open GoertzelV24ForkInterfaceSupport

variable {V E : Type*} [DecidableEq V]

/-- A nonempty simple path on a specified edge set, with no repeated vertices. -/
structure Path (inc : E → Finset V) (S : Finset E) where
  length : ℕ
  positive : 0 < length
  vertex : Fin (length + 1) → V
  vertex_injective : Function.Injective vertex
  edge : Fin length ≃ S
  endpoints : ∀ i, inc (edge i).val = {vertex i.castSucc, vertex i.succ}

variable {inc : E → Finset V} {S : Finset E}

def Path.first (p : Path inc S) : V := p.vertex 0

def Path.last (p : Path inc S) : V := p.vertex (Fin.last p.length)

def Path.firstEdge (p : Path inc S) : E := (p.edge ⟨0, p.positive⟩).val

def Path.lastEdge (p : Path inc S) : E :=
  (p.edge ⟨p.length - 1, by have := p.positive; omega⟩).val

theorem Path.first_ne_last (p : Path inc S) : p.first ≠ p.last := by
  intro h
  have hh := congrArg Fin.val (p.vertex_injective h)
  simp only [Fin.val_zero, Fin.val_last] at hh
  have := p.positive
  omega

def Path.Consecutive (p : Path inc S) (c : E → Fin 3) : Prop :=
  ∀ i j : Fin p.length, i.val + 1 = j.val → c (p.edge i).val ≠ c (p.edge j).val

/-- The path's two end colours must avoid the colours already present. -/
def Path.EndpointCompatible (p : Path inc S) (A : Finset E) (a c : E → Fin 3) : Prop :=
  c p.firstEdge ∉ profile inc A a p.first ∧ c p.lastEdge ∉ profile inc A a p.last

/-- No nonconsecutive pair creates an extra colouring constraint. -/
theorem Path.proper_iff (p : Path inc S) (c : E → Fin 3) :
    Proper inc S c ↔ p.Consecutive c := by
  constructor
  · intro h i j hij
    apply h _ (p.edge i).property _ (p.edge j).property
    · intro he
      have hh := congrArg Fin.val (p.edge.injective (Subtype.ext he))
      omega
    · refine ⟨p.vertex i.succ, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [p.endpoints]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rw [p.endpoints]
        have hh : i.succ = j.castSucc := Fin.ext hij
        rw [hh]
        exact Finset.mem_insert_self _ _
  · intro h e he f hf hef hmeet
    obtain ⟨i, hi⟩ := p.edge.surjective ⟨e, he⟩
    obtain ⟨j, hj⟩ := p.edge.surjective ⟨f, hf⟩
    have hei : (p.edge i).val = e := congrArg Subtype.val hi
    have hfj : (p.edge j).val = f := congrArg Subtype.val hj
    obtain ⟨v, hv⟩ := hmeet
    obtain ⟨hve, hvf⟩ := Finset.mem_inter.mp hv
    rw [← hei, p.endpoints, Finset.mem_insert, Finset.mem_singleton] at hve
    rw [← hfj, p.endpoints, Finset.mem_insert, Finset.mem_singleton] at hvf
    rcases hve with hve | hve <;> rcases hvf with hvf | hvf
    · have hh := congrArg Fin.val (p.vertex_injective (hve.symm.trans hvf))
      have hij : i = j := Fin.ext hh
      exact (hef (hei.symm.trans (hij ▸ hfj))).elim
    · have hh := congrArg Fin.val (p.vertex_injective (hvf.symm.trans hve))
      have hc := h j i hh
      simpa only [hei, hfj] using hc.symm
    · have hh := congrArg Fin.val (p.vertex_injective (hve.symm.trans hvf))
      have hc := h i j hh
      simpa only [hei, hfj] using hc
    · have hh := congrArg Fin.val (p.vertex_injective (hve.symm.trans hvf))
      have hij : i = j := Fin.ext (by simpa using hh)
      exact (hef (hei.symm.trans (hij ▸ hfj))).elim

theorem Path.first_incident_iff (p : Path inc S) (i : Fin p.length) :
    p.first ∈ inc (p.edge i).val ↔ i.val = 0 := by
  rw [p.endpoints, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · have hh := congrArg Fin.val (p.vertex_injective h)
      simpa only [Fin.val_zero, Fin.val_castSucc] using hh.symm
    · have hh := congrArg Fin.val (p.vertex_injective h)
      simp only [Fin.val_zero, Fin.val_succ] at hh
      omega
  · intro h
    left
    apply congrArg p.vertex
    exact Fin.ext h.symm

theorem Path.last_incident_iff (p : Path inc S) (i : Fin p.length) :
    p.last ∈ inc (p.edge i).val ↔ i.val + 1 = p.length := by
  rw [p.endpoints, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · have hh := congrArg Fin.val (p.vertex_injective h)
      simp only [Fin.val_last, Fin.val_castSucc] at hh
      omega
    · have hh := congrArg Fin.val (p.vertex_injective h)
      exact hh.symm
  · intro h
    right
    apply congrArg p.vertex
    exact Fin.ext h.symm

theorem Path.firstEdge_mem (p : Path inc S) : p.firstEdge ∈ S :=
  (p.edge ⟨0, p.positive⟩).property

theorem Path.lastEdge_mem (p : Path inc S) : p.lastEdge ∈ S :=
  (p.edge ⟨p.length - 1, by have := p.positive; omega⟩).property

theorem Path.firstEdge_incident (p : Path inc S) : p.first ∈ inc p.firstEdge :=
  (p.first_incident_iff ⟨0, p.positive⟩).mpr rfl

theorem Path.lastEdge_incident (p : Path inc S) : p.last ∈ inc p.lastEdge :=
  (p.last_incident_iff ⟨p.length - 1, by have := p.positive; omega⟩).mpr
    (by dsimp only; have := p.positive; omega)

theorem Path.eq_firstEdge (p : Path inc S) {x : E} (hx : x ∈ S) (hv : p.first ∈ inc x) :
    x = p.firstEdge := by
  obtain ⟨i, hi⟩ := p.edge.surjective ⟨x, hx⟩
  have he : (p.edge i).val = x := congrArg Subtype.val hi
  have hiz := (p.first_incident_iff i).mp (he.symm ▸ hv)
  have hi0 : i = ⟨0, p.positive⟩ := Fin.ext hiz
  rw [← he, hi0]
  rfl

theorem Path.eq_lastEdge (p : Path inc S) {x : E} (hx : x ∈ S) (hv : p.last ∈ inc x) :
    x = p.lastEdge := by
  obtain ⟨i, hi⟩ := p.edge.surjective ⟨x, hx⟩
  have he : (p.edge i).val = x := congrArg Subtype.val hi
  have hin := (p.last_incident_iff i).mp (he.symm ▸ hv)
  have hi0 : i = ⟨p.length - 1, by have := p.positive; omega⟩ := Fin.ext (by dsimp only; omega)
  rw [← he, hi0]
  rfl

theorem Path.profile_first (p : Path inc S) (c : E → Fin 3) :
    profile inc S c p.first = {c p.firstEdge} := by
  ext colour
  simp only [profile, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨x, ⟨hx, hv⟩, hxc⟩
    rw [p.eq_firstEdge hx hv] at hxc
    exact hxc.symm
  · intro hc
    exact ⟨p.firstEdge, ⟨p.firstEdge_mem, p.firstEdge_incident⟩, hc.symm⟩

theorem Path.profile_last (p : Path inc S) (c : E → Fin 3) :
    profile inc S c p.last = {c p.lastEdge} := by
  ext colour
  simp only [profile, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨x, ⟨hx, hv⟩, hxc⟩
    rw [p.eq_lastEdge hx hv] at hxc
    exact hxc.symm
  · intro hc
    exact ⟨p.lastEdge, ⟨p.lastEdge_mem, p.lastEdge_incident⟩, hc.symm⟩

end Mettapedia.GraphTheory.FourColor.OrderedEdgePath
