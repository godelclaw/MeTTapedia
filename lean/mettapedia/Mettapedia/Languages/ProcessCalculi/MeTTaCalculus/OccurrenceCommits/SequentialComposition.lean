import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommitPreconditions

/-!
# Conditional composition of two matched occurrence commits

The initial condition is compiled by `CommitPrecondition.sequential`. The net
update below removes intermediate outputs that are consumed again, and retains
original occurrences consumed and then restored under the same identifier.

Both constructions are finite data. Their correspondence is proved against
the existing sequential store semantics, including intermediate freshness.
The condition must travel with the net update: its effects alone do not specify
where the sequence is admitted. These are ground matched instances; enumerating
overlaps of rule schemas is a separate construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

namespace Commit

/-- Initial occurrences required by either application, excluding the first output. -/
def sequentialInput (c d : Commit O R) : Finset O :=
  c.taken ∪ c.kept ∪ ((d.taken ∪ d.kept) \ c.made)

/-- Initial occurrences consumed somewhere in the sequence. -/
def sequentialTaken (c d : Commit O R) : Finset O :=
  c.taken ∪ (d.taken \ c.made)

/-- Outputs still present after both applications. -/
def sequentialMade (c d : Commit O R) : Finset O :=
  (c.made \ d.taken) ∪ d.made

/-- The net update. The full admission condition is
`CommitPrecondition.sequential label c d`, not just this update's enabling test. -/
def compose (c d : Commit O R) : Commit O R where
  taken := c.sequentialTaken d \ c.sequentialMade d
  kept := c.sequentialInput d \ (c.sequentialTaken d \ c.sequentialMade d)
  made := c.sequentialMade d \ c.sequentialTaken d
  queries := []

theorem compose_enabled {label : O → R} {store : Finset O} {c d : Commit O R}
    (first : Enabled label store c) (second : Enabled label (fire store c) d) :
    Enabled label store (c.compose d) := by
  have required (o : O) (member : o ∈ c.sequentialInput d) : o ∈ store := by
    simp only [sequentialInput, Finset.mem_union, Finset.mem_sdiff] at member
    have ct := first.taken_subset (x := o)
    have ck := first.kept_subset (x := o)
    have dt := second.taken_subset (x := o)
    have dk := second.kept_subset (x := o)
    simp only [mem_fire] at dt dk
    grind
  refine ⟨?_, ?_, ?_, ?_, by simp [compose]⟩
  · intro o member
    apply required o
    simp only [compose, sequentialTaken, sequentialInput, Finset.mem_sdiff,
      Finset.mem_union] at member ⊢
    grind
  · intro o member
    exact required o (Finset.mem_sdiff.mp member).1
  · apply Finset.disjoint_left.mpr
    intro o taken kept
    exact (Finset.mem_sdiff.mp kept).2 taken
  · apply Finset.disjoint_left.mpr
    intro o made present
    have cFresh : o ∈ c.made → o ∉ store := fun h => Finset.disjoint_left.mp first.fresh h
    have dFresh : o ∈ d.made → o ∉ fire store c := fun h => Finset.disjoint_left.mp second.fresh h
    simp only [mem_fire] at dFresh
    simp only [compose, sequentialMade, sequentialTaken, Finset.mem_sdiff,
      Finset.mem_union] at made
    grind

/-- The computed net update reaches precisely the sequential final store. -/
theorem compose_fire {label : O → R} {store : Finset O} {c d : Commit O R}
    (first : Enabled label store c) (second : Enabled label (fire store c) d) :
    fire store (c.compose d) = fire (fire store c) d := by
  ext o
  have ct := first.taken_subset (x := o)
  have dt := second.taken_subset (x := o)
  have cFresh : o ∈ c.made → o ∉ store := fun h => Finset.disjoint_left.mp first.fresh h
  have dFresh : o ∈ d.made → o ∉ fire store c := fun h => Finset.disjoint_left.mp second.fresh h
  simp only [mem_fire] at dt dFresh
  simp only [mem_fire, compose, sequentialTaken, sequentialMade, Finset.mem_sdiff,
    Finset.mem_union]
  grind

/-- Synthesis and decomposition for the conditional ground composite. -/
theorem composition_exact (label : O → R) (store result : Finset O) (c d : Commit O R) :
    ((CommitPrecondition.sequential label c d).Holds label store ∧
      result = fire store (c.compose d)) ↔
      ∃ middle, Enabled label store c ∧ middle = fire store c ∧
        Enabled label middle d ∧ result = fire middle d := by
  rw [CommitPrecondition.sequential_holds_iff]
  constructor
  · rintro ⟨⟨first, second⟩, resultEq⟩
    exact ⟨fire store c, first, rfl, second, resultEq.trans (compose_fire first second)⟩
  · rintro ⟨middle, first, rfl, second, resultEq⟩
    exact ⟨⟨first, second⟩, resultEq.trans (compose_fire first second).symm⟩

/-- Associativity at the final occurrence-store observation of an admitted
three-step execution. Each grouping retains its own transported conditions. -/
theorem compose_assoc_fire {label : O → R} {store : Finset O} {a b c : Commit O R}
    (first : Enabled label store a) (second : Enabled label (fire store a) b)
    (third : Enabled label (fire (fire store a) b) c) :
    fire store ((a.compose b).compose c) = fire store (a.compose (b.compose c)) := by
  have ab := compose_enabled first second
  have cAfter : Enabled label (fire store (a.compose b)) c := by
    rwa [compose_fire first second]
  rw [compose_fire ab cAfter, compose_fire first second]
  rw [compose_fire first (compose_enabled second third), compose_fire second third]

/-- Independent enabled commits admit either compiled order and agree at the
occurrence-store observation. Query independence remains a real hypothesis. -/
theorem compose_comm_fire {label : O → R} {store : Finset O} {c d : Commit O R}
    (first : Enabled label store c) (second : Enabled label store d)
    (independent : Independent label c d) :
    fire store (c.compose d) = fire store (d.compose c) := by
  have orders := (independent_iff_both_orders first second).mp independent
  rw [compose_fire first orders.1, compose_fire second orders.2]
  exact fire_comm first second

end Commit

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
