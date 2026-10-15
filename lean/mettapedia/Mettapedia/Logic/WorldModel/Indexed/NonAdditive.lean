import Mettapedia.Logic.WorldModel.Indexed.SourceExample

/-!
# Non-additive dynamics: negative controls

Morphisms of world models are additive state maps, and revision adds records.
Two kinds of dynamics fall outside this:

* **Deletion.** Deleting one record is not additive
  (`deleteRecord_not_additive`), does not commute with revision
  (`delete_revise_order`), is no revision (`deleteRecord_not_revision`), and the
  deleted reading of a world is not a world model: its extraction is not
  additive (`deletedAnswer_not_profileHom`).  On a single count, deleting then
  querying is querying then subtracting one (`count_delete`), and truncated
  subtraction is not additive (`truncatedSub_not_additive`).
* **Rewriting.** A step of a multiset rewriting language that replaces one
  record by another is no revision (`rewriteStep_not_revision`): revision only
  adds (`revision_inflationary`), while the step consumes
  (`rewriteStep_consumes`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WorldModel.Indexed.NonAdditive

open Sources

variable {α : Type} [DecidableEq α]

/-- Delete one occurrence of a record. -/
def deleteRecord (r : α) (m : Multiset α) : Multiset α := m.erase r

/-- Deletion is not additive. -/
theorem deleteRecord_not_additive (r : α) :
    ¬ ∀ m m' : Multiset α, deleteRecord r (m + m') = deleteRecord r m + deleteRecord r m' := by
  intro h
  have := congrArg Multiset.card (h {r} {r})
  simp [deleteRecord] at this

/-- Revising then deleting is not deleting then revising. -/
theorem delete_revise_order (r : α) :
    deleteRecord r (0 + {r}) ≠ deleteRecord r 0 + {r} := by
  simp [deleteRecord]

/-- Deletion is no revision. -/
theorem deleteRecord_not_revision (r : α) :
    ¬ ∃ d : Multiset α, ∀ m, deleteRecord r m = m + d := by
  rintro ⟨d, hd⟩
  have h0 := hd 0
  simp only [deleteRecord, Multiset.erase_zero, zero_add] at h0
  have h1 := hd {r}
  rw [← h0] at h1
  simp [deleteRecord] at h1

/-- Deleting then counting is counting then subtracting one. -/
theorem count_delete (r : α) (m : Multiset α) :
    (deleteRecord r m).count r = m.count r - 1 :=
  Multiset.count_erase_self r m

/-- Truncated subtraction of one is not additive. -/
theorem truncatedSub_not_additive : ¬ ∀ x y : ℕ, (x + y) - 1 = (x - 1) + (y - 1) := by
  intro h
  have := h 1 1
  omega

section Sources

variable {Src : Type} [DecidableEq Src]

/-- The deleted reading of a world is not a world model: no additive map
reproduces "delete a positive record of `a`, then answer". -/
theorem deletedAnswer_not_profileHom (a : Src) :
    ¬ ∃ F : Records Src →+ (Question {a} → ℕ),
      ∀ m, F m = answer {a} (deleteRecord (a, true) m) := by
  rintro ⟨F, hF⟩
  have hsum := hF ({(a, true)} + {(a, true)})
  rw [map_add, hF, deleteRecord] at hsum
  have := congrFun hsum (.perSource a (Finset.mem_singleton_self a) true)
  simp [answer, answerFun, deleteRecord] at this

end Sources

/-! ## Rewriting is not revision -/

/-- One step of a multiset rewriting rule: replace one `r` by `r'` when an `r`
is present. -/
def rewriteStep (r r' : α) (m : Multiset α) : Multiset α :=
  if r ∈ m then m.erase r + {r'} else m

omit [DecidableEq α] in
/-- Revision only adds. -/
theorem revision_inflationary (m d : Multiset α) : m ≤ m + d :=
  Multiset.le_add_right m d

/-- The rewrite step consumes its redex. -/
theorem rewriteStep_consumes {r r' : α} (h : r ≠ r') : ¬ ({r} : Multiset α) ≤ rewriteStep r r' {r} := by
  simp [rewriteStep, h]

/-- A rewriting step is no revision. -/
theorem rewriteStep_not_revision {r r' : α} (h : r ≠ r') :
    ¬ ∃ d : Multiset α, ∀ m, rewriteStep r r' m = m + d := by
  rintro ⟨d, hd⟩
  have := hd {r}
  exact rewriteStep_consumes h (this ▸ revision_inflationary {r} d)

end Mettapedia.Logic.WorldModel.Indexed.NonAdditive
