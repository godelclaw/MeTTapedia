import Mathlib.Data.Finset.Basic

namespace Mettapedia.GraphTheory.FourColor.Curriculum

variable {V E : Type*}

/-- Two edges are adjacent when they are distinct and share an incident vertex. -/
def edgeAdjByIncidence (incident : V → Finset E) (e e' : E) : Prop :=
  e ≠ e' ∧ ∃ v, e ∈ incident v ∧ e' ∈ incident v

/-- The shared-vertex part of edge adjacency. -/
def hasSharedVertex (incident : V → Finset E) (e e' : E) : Prop :=
  ∃ v, e ∈ incident v ∧ e' ∈ incident v

/-- Edge adjacency is equivalent to distinctness plus shared-vertex incidence. -/
theorem edgeAdjByIncidence_iff (incident : V → Finset E) (e e' : E) :
    edgeAdjByIncidence incident e e' ↔ e ≠ e' ∧ hasSharedVertex incident e e' := by
  rfl

/-- The shared-vertex relation is symmetric. -/
theorem hasSharedVertex_comm (incident : V → Finset E) (e e' : E) :
    hasSharedVertex incident e e' ↔ hasSharedVertex incident e' e := by
  constructor
  · intro ⟨v, he, he'⟩
    exact ⟨v, he', he⟩
  · intro ⟨v, he', he⟩
    exact ⟨v, he, he'⟩

/-- Edge adjacency by incidence is symmetric. -/
theorem edgeAdjByIncidence_comm (incident : V → Finset E) (e e' : E) :
    edgeAdjByIncidence incident e e' ↔ edgeAdjByIncidence incident e' e := by
  constructor
  · intro ⟨hne, v, he, he'⟩
    exact ⟨hne.symm, v, he', he⟩
  · intro ⟨hne, v, he', he⟩
    exact ⟨hne.symm, v, he, he'⟩

/-- No edge is incidence-adjacent to itself. -/
theorem not_edgeAdjByIncidence_self (incident : V → Finset E) (e : E) :
    ¬ edgeAdjByIncidence incident e e := by
  intro h
  exact h.1 rfl

/-- Any listed incidence witnesses that an edge shares a vertex with itself. -/
theorem hasSharedVertex_self_of_mem (incident : V → Finset E) (e : E) (v : V)
    (h : e ∈ incident v) :
    hasSharedVertex incident e e := by
  exact ⟨v, h, h⟩

end Mettapedia.GraphTheory.FourColor.Curriculum
