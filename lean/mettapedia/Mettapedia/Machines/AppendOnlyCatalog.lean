import Mathlib.Data.List.Infix

/-!
# A notified append and a retained occurrence catalog

A space prefix and its source-plan catalog may advance together when one
actual row was appended and its plan was recorded. The full reader below
checks each occurrence against the catalog; the incremental reader appends
the supplied record. Equal rows remain separate records and may retain
different plans. A native prefix epoch and revision counter must separately
justify the hypotheses used here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AppendOnlyCatalog

variable {Row Plan : Type}

/-- Full ordered alignment checks every source occurrence against a catalog
record, retaining the record's previously captured plan. -/
def align [DecidableEq Row] : List Row → List (Row × Plan) → Option (List (Row × Plan))
  | [], [] => some []
  | row :: rows, record :: records =>
      if row = record.1 then
        (align rows records).map (record :: ·)
      else none
  | _, _ => none

def project (records : List (Row × Plan)) : List Row := records.map Prod.fst

/-- Alignment returns the original records, rather than reconstructing plans. -/
theorem align_projection [DecidableEq Row] (records : List (Row × Plan)) :
    align (project records) records = some records := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      change align (record.1 :: project records) (record :: records) = _
      simp [align, ih]

/-- Prefix authority plus the measured length and last row determine the
actual one-row extension. A length and last row alone do not. -/
theorem certified_single_append [DecidableEq Row] (before after : List Row) (row : Row)
    (isPrefix : before <+: after) (length : after.length = before.length + 1)
    (last : after.getLast? = some row) : after = before ++ [row] := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  have size : suffix.length = 1 := by simp at length; omega
  cases suffix with
  | nil => simp at size
  | cons first rest =>
      cases rest with
      | nil => simpa using last
      | cons second rest => simp at size

/-- A full alignment after a certified append agrees with retaining all old
records and adding the notified occurrence once. -/
theorem notified_append_matches_alignment [DecidableEq Row]
    (before after : List Row) (records : List (Row × Plan)) (row : Row) (plan : Plan)
    (catalog : project records = before) (isPrefix : before <+: after)
    (length : after.length = before.length + 1) (last : after.getLast? = some row) :
    align after (records ++ [(row, plan)]) = some (records ++ [(row, plan)]) := by
  rw [certified_single_append before after row isPrefix length last, ← catalog]
  simpa [project] using align_projection (records ++ [(row, plan)])

/-- A revision accompanies the rows that were actually inspected. -/
structure VersionedRows (Row : Type) where
  revision : Nat
  rows : List Row

def appendRow (state : VersionedRows Row) (row : Row) : VersionedRows Row :=
  ⟨state.revision + 1, state.rows ++ [row]⟩

def tokenCurrent (captured : Nat) (state : VersionedRows Row) : Bool :=
  decide (captured = state.revision)

/-- A later write makes the captured revision stale. Keeping that captured
token cannot silently certify rows added after the observation. -/
theorem captured_token_rejects_later_append (observed : VersionedRows Row) (row : Row) :
    tokenCurrent observed.revision (appendRow observed row) = false := by
  simp [tokenCurrent, appendRow]

/-- Reading a new revision after the write would accept a catalog that has
not incorporated the new occurrence. -/
theorem reread_token_can_label_incomplete_catalog (observed : VersionedRows Row) (row : Row) :
    tokenCurrent (appendRow observed row).revision (appendRow observed row) = true ∧
      observed.rows ≠ (appendRow observed row).rows := by
  constructor
  · simp [tokenCurrent]
  · intro equal
    have sizes := congrArg List.length equal
    simp [appendRow] at sizes

namespace Callability

variable {Head : Type} [DecidableEq Head]

/-- `none` represents an equation whose variable head admits any name. -/
def accepts (head : Head) : Option Head → Bool
  | none => true
  | some named => decide (named = head)

def viewAdmits (rows : List (Option Head)) (head : Head) : Bool :=
  rows.any (accepts head)

def programAdmits (predeclared : List (Option Head))
    (spaces : List (List (Option Head))) (head : Head) : Bool :=
  predeclared.any (accepts head) || spaces.any (fun rows => rows.any (accepts head))

/-- A one-space program without predeclarations reads precisely its view. -/
theorem one_space_agrees (rows : List (Option Head)) (head : Head) :
    programAdmits [] [rows] head = viewAdmits rows head := by
  simp [programAdmits, viewAdmits]

/-- A cached prefix can be extended by inspecting only the new rows. -/
theorem append_extends_view (before after : List (Option Head)) (head : Head) :
    viewAdmits (before ++ after) head = (viewAdmits before head || viewAdmits after head) := by
  simp [viewAdmits]

inductive Role where
  | data | call
  deriving DecidableEq

def role (rows : List (Option Head)) (head : Head) : Role :=
  if viewAdmits rows head then .call else .data

/-- A later definition changes only the plan made in its later view; the
earlier view still gives the data interpretation. -/
theorem later_definition_changes_new_role (before after : List (Option Head)) (head : Head)
    (absent : viewAdmits before head = false) (present : viewAdmits after head = true) :
    role before head = .data ∧ role (before ++ after) head = .call := by
  simp [role, absent, append_extends_view, present]

end Callability

namespace Controls

/-- The records remain separate even when their payloads agree. -/
theorem duplicate_rows_keep_both_plans :
    align [1, 1] [(1, 7), (1, 9)] = some [(1, 7), (1, 9)] := by decide

/-- Length and last row can agree after a rewrite; they do not prove prefix. -/
theorem rewritten_prefix_is_not_append :
    ([1, 2] : List Nat).length + 1 = ([3, 2, 4] : List Nat).length ∧
      ([3, 2, 4] : List Nat).getLast? = some 4 ∧
      ¬ ([1, 2] : List Nat) <+: [3, 2, 4] := by decide

theorem predeclared_head_is_not_a_live_row :
    Callability.viewAdmits ([] : List (Option Nat)) 7 = false ∧
      Callability.programAdmits [some 7] [[]] 7 = true := by decide

theorem another_space_is_not_the_local_view :
    Callability.viewAdmits ([] : List (Option Nat)) 7 = false ∧
      Callability.programAdmits [] [[], [some 7]] 7 = true := by decide

theorem wildcard_head_admits_new_names :
    Callability.viewAdmits ([none] : List (Option Nat)) 100 = true := by decide

end Controls
end Mettapedia.Machines.AppendOnlyCatalog
