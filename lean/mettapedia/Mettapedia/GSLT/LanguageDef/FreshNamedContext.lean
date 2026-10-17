import Mettapedia.GSLT.LanguageDef.NamedFreeContext

/-!
# Fresh printed names preserve intrinsic context positions

The finite context and name lookup are the existing binding-signature owners.
Printing a position and looking up its name returns that exact position when
names are distinct. Prepending names that avoid an old reference preserves its
position under weakening. The executable admission predicate checks distinct
names and the reserved free-name inventory; it does not assume a lookup result.

These are context-level naming laws. They do not establish a C macro expander,
C namespaces, expression evaluation counts, or a native printing correspondence.
-/

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding

set_option autoImplicit false

theorem nameAt_mem_names (entries : List (String × TypeExpr))
    {sort : TypeExpr} (position : Var (contextSorts entries) sort) :
    nameAt entries position ∈ entries.map Prod.fst := by
  exact List.mem_map.mpr ⟨_, position_pair_mem entries sort position, rfl⟩

/-- A printed name resolves to its original occurrence, not merely to a
position of the same sort carrying an equal spelling. -/
theorem lookup_nameAt_of_nodup : ∀ (entries : List (String × TypeExpr)),
    (entries.map Prod.fst).Nodup → ∀ {sort : TypeExpr}
      (position : Var (contextSorts entries) sort),
      lookupPosition? entries (nameAt entries position) sort = some position := by
  intro entries
  induction entries with
  | nil => intro distinct sort position; nomatch position
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro distinct sort position
      have parts : headName ∉ tail.map Prod.fst ∧ (tail.map Prod.fst).Nodup := by
        simpa using distinct
      cases position with
      | zero => simp [nameAt, lookupPosition?]; rfl
      | succ old =>
          have different : headName ≠ nameAt tail old := by
            intro same
            exact parts.1 (same ▸ nameAt_mem_names tail old)
          simp [nameAt, lookupPosition?, different, ih parts.2 old]; rfl

/-- Weaken a position through an actual finite frame of new named entries. -/
def prependPosition : (frame entries : List (String × TypeExpr)) →
    {sort : TypeExpr} → Var (contextSorts entries) sort →
      Var (contextSorts (frame ++ entries)) sort
  | [], _, _, position => position
  | _ :: rest, entries, _, position => .succ (prependPosition rest entries position)

@[simp] theorem nameAt_prependPosition (frame entries : List (String × TypeExpr))
    {sort : TypeExpr} (position : Var (contextSorts entries) sort) :
    nameAt (frame ++ entries) (prependPosition frame entries position) = nameAt entries position := by
  induction frame with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨name, type⟩
      exact ih

theorem lookup_fresh_prefix (frame entries : List (String × TypeExpr))
    (name : String) (sort : TypeExpr) (fresh : name ∉ frame.map Prod.fst) :
    lookupPosition? (frame ++ entries) name sort =
      (lookupPosition? entries name sort).map (prependPosition frame entries) := by
  induction frame with
  | nil => simp [prependPosition]
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      have parts : name ≠ headName ∧ name ∉ tail.map Prod.fst := by
        simpa using fresh
      simp [lookupPosition?, Ne.symm parts.1, ih parts.2, prependPosition]
      cases lookupPosition? entries name sort <;> rfl

/-- An inserted frame cannot capture an old named reference if its printed
names avoid that reference. No condition on unrelated spellings is needed. -/
theorem fresh_prefix_preserves_position (frame entries : List (String × TypeExpr))
    (distinct : (entries.map Prod.fst).Nodup) {sort : TypeExpr}
    (position : Var (contextSorts entries) sort)
    (fresh : nameAt entries position ∉ frame.map Prod.fst) :
    lookupPosition? (frame ++ entries) (nameAt entries position) sort =
      some (prependPosition frame entries position) := by
  rw [lookup_fresh_prefix frame entries _ _ fresh, lookup_nameAt_of_nodup entries distinct position]
  rfl

/-- Check printed binder names independently of resolving any reference. -/
def admitNames (entries : List (String × TypeExpr)) (reserved : List String) : Bool :=
  decide ((entries.map Prod.fst).Nodup ∧ ∀ name ∈ entries.map Prod.fst, name ∉ reserved)

theorem admitted_printed_position (entries : List (String × TypeExpr)) (reserved : List String)
    (admitted : admitNames entries reserved = true) {sort : TypeExpr}
    (position : Var (contextSorts entries) sort) :
    lookupPosition? entries (nameAt entries position) sort = some position := by
  have checked : (entries.map Prod.fst).Nodup ∧ ∀ name ∈ entries.map Prod.fst, name ∉ reserved := by
    simpa [admitNames] using admitted
  exact lookup_nameAt_of_nodup entries checked.1 position

theorem admitted_name_avoids_free (entries : List (String × TypeExpr)) (reserved : List String)
    (admitted : admitNames entries reserved = true) {sort : TypeExpr}
    (position : Var (contextSorts entries) sort) : nameAt entries position ∉ reserved := by
  have checked : (entries.map Prod.fst).Nodup ∧ ∀ name ∈ entries.map Prod.fst, name ∉ reserved := by
    simpa [admitNames] using admitted
  exact checked.2 _ (nameAt_mem_names entries position)

example : admitNames [("cesta_local_0", .base "Expr")] ["value"] = true := by decide +kernel
example : admitNames [("value", .base "Expr")] ["value"] = false := by decide +kernel
example : admitNames [("same", .base "Expr"), ("same", .base "Expr")] [] = false := by decide +kernel

/-- Without freshness, an old reference resolves to the newly inserted binder. -/
example : lookupPosition? [("value", .base "Expr"), ("value", .base "Expr")]
    "value" (.base "Expr") = some Var.zero := by
  simp [lookupPosition?]; rfl

/-- A fresh spelling leaves the original reference at its weakened position. -/
example : lookupPosition? [("cesta_local_0", .base "Expr"), ("value", .base "Expr")]
    "value" (.base "Expr") = some (Var.succ Var.zero) := by
  simp [lookupPosition?]; rfl

#print axioms lookup_nameAt_of_nodup
#print axioms fresh_prefix_preserves_position
#print axioms admitted_printed_position
#print axioms admitted_name_avoids_free

end Mettapedia.GSLT.LanguageDef.NamedFreeContext
