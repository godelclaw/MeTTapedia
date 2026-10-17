import Mettapedia.Languages.MeTTa.EquationKernel.Judgment

/-!
# Certificates of equation application, checked without search

A certificate is a list of rows. Each row names one kernel rule and refers to
earlier rows by position, so a derivation used twice is written once. The
checker computes every row's claim from its data and the claims of the rows
it cites: it applies the supplied substitution, compares atoms, walks the
supplied path and counts equal copies in the program. It never matches,
unifies or enumerates alternatives. The certificate supplies every choice:
the stored copy, the position and the substitution.

The checker (`check`) holds its table newest first, as the MeTTa checker
does, so recording a row's claim is one cons; `check_eq_checkReference`
relates it to the reference replay `checkRows`, which appends. A reference
`k` rows back walks past `k` newer claims, and a citation counts copies by
scanning the program: no cost bound beyond that is claimed here.

* `check_exact`: acceptance is exactly validity of every row for the
  independently stated row rules (`Row.Valid`).
* `check_sound` and `exists_check_of_reaches`: some certificate is accepted
  exactly when the claim is reachable.
* `check_seq`, `check_congr`, `check_both`: sequential composition,
  composition in a context, and one shared derivation used twice.
* `replay_append`, `check_trace_iff`: a linear trace of steps is a special
  certificate; replay composes along concatenation.
* `exists_trace_iff_reaches`: reflexivity and step rows already reach every
  reachable claim; congruence and transitivity add sharing and composition.
* `check_perm`: acceptance depends on the program only through the counts of
  its atoms, so reordering the space changes nothing.
* `accepted_citations_length`: equal stored copies of an equation are
  separate citations; accepted citations of one step are as many as the
  stored atoms that license it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom Atomspace)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Var Subst subst vars)

/-- A claim `source →* target`. -/
abbrev Claim := Atom × Atom

/-- One row names one kernel rule. References are positions of earlier rows. -/
inductive Row where
  | refl (atom : Atom)
  | step (prior : Nat) (citation : Citation) (path : List Nat) (bindings : Bindings)
  | congr (left : List Atom) (inner : Nat) (right : List Atom)
  | trans (first second : Nat)
  deriving DecidableEq, Repr

structure Certificate where
  rows : List Row
  root : Nat
  deriving DecidableEq, Repr

/-! ## The checker -/

/-- The claim of one row, computed from the claims of the earlier rows. -/
def Row.claim? (program : List Atom) (table : List Claim) : Row → Option Claim
  | .refl atom => some (atom, atom)
  | .step prior citation path bindings =>
      match table[prior]?, equationSides citation.equation with
      | some (source, current), some (left, right) =>
          if citation.copy < program.count citation.equation ∧
              subatom? current path = some (subst bindings.toSubst left) then
            (replaceAt? current path (subst bindings.toSubst right)).map (source, ·)
          else none
      | _, _ => none
  | .congr left inner right =>
      (table[inner]?).map fun claim =>
        (.expression (left ++ claim.1 :: right), .expression (left ++ claim.2 :: right))
  | .trans first second =>
      match table[first]?, table[second]? with
      | some (source, middle), some (middle', target) =>
          if middle = middle' then some (source, target) else none
      | _, _ => none

/-- `Row.claim?` with an arbitrary lookup of earlier claims. -/
def Row.claimBy? (program : List Atom) (lookup : Nat → Option Claim) : Row → Option Claim
  | .refl atom => some (atom, atom)
  | .step prior citation path bindings =>
      match lookup prior, equationSides citation.equation with
      | some (source, current), some (left, right) =>
          if citation.copy < program.count citation.equation ∧
              subatom? current path = some (subst bindings.toSubst left) then
            (replaceAt? current path (subst bindings.toSubst right)).map (source, ·)
          else none
      | _, _ => none
  | .congr left inner right =>
      (lookup inner).map fun claim =>
        (.expression (left ++ claim.1 :: right), .expression (left ++ claim.2 :: right))
  | .trans first second =>
      match lookup first, lookup second with
      | some (source, middle), some (middle', target) =>
          if middle = middle' then some (source, target) else none
      | _, _ => none

theorem Row.claim?_eq_claimBy (program : List Atom) (table : List Claim) (row : Row) :
    row.claim? program table = row.claimBy? program (fun index => table[index]?) := by
  cases row <;> rfl

theorem Row.claimBy?_congr (program : List Atom) {lookup other : Nat → Option Claim}
    (same : ∀ index, lookup index = other index) (row : Row) :
    row.claimBy? program lookup = row.claimBy? program other := by
  rw [show lookup = other from funext same]

/-- The reference replay: check rows in order, appending each computed claim
to the table. It states what the checker computes; the checker below runs it
with the table held newest first. -/
def checkRows (program : List Atom) : List Claim → List Row → Option (List Claim)
  | table, [] => some table
  | table, row :: rows =>
      match row.claim? program table with
      | some claim => checkRows program (table ++ [claim]) rows
      | none => none

/-- Lookup in a table held newest first with its length. -/
def revLookup (reversed : List Claim) (count index : Nat) : Option Claim :=
  if index < count then reversed[count - 1 - index]? else none

/-- The checker's loop. The table is held newest first, as the MeTTa checker
holds it: recording a claim is one cons, a reference to the previous row is
found at the head, and a reference `k` rows back walks past `k` newer claims. -/
def checkRowsRev (program : List Atom) : List Claim → Nat → List Row → Option (List Claim × Nat)
  | reversed, count, [] => some (reversed, count)
  | reversed, count, row :: rows =>
      match row.claimBy? program (revLookup reversed count) with
      | some claim => checkRowsRev program (claim :: reversed) (count + 1) rows
      | none => none

def check (program : List Atom) (certificate : Certificate) (claim : Claim) : Bool :=
  match checkRowsRev program [] 0 certificate.rows with
  | some (reversed, count) => decide (revLookup reversed count certificate.root = some claim)
  | none => false

theorem revLookup_reverse (table : List Claim) (index : Nat) :
    revLookup table.reverse table.length index = table[index]? := by
  unfold revLookup
  split_ifs with below
  · rw [List.getElem?_reverse (by omega)]
    congr 1
    omega
  · exact (List.getElem?_eq_none (Nat.le_of_not_lt below)).symm

theorem checkRowsRev_eq (program : List Atom) :
    ∀ (rows : List Row) (table : List Claim),
      checkRowsRev program table.reverse table.length rows =
        (checkRows program table rows).map fun final => (final.reverse, final.length)
  | [], table => rfl
  | row :: rows, table => by
      have lookups : row.claimBy? program (revLookup table.reverse table.length) = row.claim? program table := by
        rw [Row.claim?_eq_claimBy]
        exact Row.claimBy?_congr program (revLookup_reverse table) row
      simp only [checkRowsRev, checkRows, lookups]
      cases row.claim? program table with
      | none => rfl
      | some claim =>
          have := checkRowsRev_eq program rows (table ++ [claim])
          simpa using this

/-- The checker in terms of the reference replay. -/
def checkReference (program : List Atom) (certificate : Certificate) (claim : Claim) : Bool :=
  match checkRows program [] certificate.rows with
  | some table => decide (table[certificate.root]? = some claim)
  | none => false

theorem check_eq_checkReference (program : List Atom) (certificate : Certificate) (claim : Claim) :
    check program certificate claim = checkReference program certificate claim := by
  have run := checkRowsRev_eq program certificate.rows []
  simp only [List.reverse_nil, List.length_nil] at run
  unfold check checkReference
  rw [run]
  cases checkRows program [] certificate.rows with
  | none => rfl
  | some table =>
      simp only [Option.map_some]
      rw [show revLookup table.reverse table.length certificate.root = table[certificate.root]? from
        revLookup_reverse table certificate.root]

/-! ## The independent row rules -/

/-- What a row asserts, stated without the checker. -/
inductive Row.Valid (program : List Atom) (table : List Claim) : Row → Claim → Prop
  | refl (atom : Atom) : Row.Valid program table (.refl atom) (atom, atom)
  | step {prior : Nat} {citation : Citation} {path : List Nat} {bindings : Bindings}
      {source current left right next : Atom} :
      table[prior]? = some (source, current) →
      citation.equation = Atom.equality left right →
      citation.Valid (spaceOf program) →
      subatom? current path = some (subst bindings.toSubst left) →
      replaceAt? current path (subst bindings.toSubst right) = some next →
      Row.Valid program table (.step prior citation path bindings) (source, next)
  | congr {left right : List Atom} {inner : Nat} {source target : Atom} :
      table[inner]? = some (source, target) →
      Row.Valid program table (.congr left inner right)
        (.expression (left ++ source :: right), .expression (left ++ target :: right))
  | trans {first second : Nat} {source middle target : Atom} :
      table[first]? = some (source, middle) →
      table[second]? = some (middle, target) →
      Row.Valid program table (.trans first second) (source, target)

inductive RowsValid (program : List Atom) : List Claim → List Row → List Claim → Prop
  | nil (table : List Claim) : RowsValid program table [] table
  | cons {table final : List Claim} {row : Row} {claim : Claim} {rows : List Row} :
      Row.Valid program table row claim →
      RowsValid program (table ++ [claim]) rows final →
      RowsValid program table (row :: rows) final

def Certificate.Valid (program : List Atom) (certificate : Certificate) (claim : Claim) : Prop :=
  ∃ table, RowsValid program [] certificate.rows table ∧ table[certificate.root]? = some claim

/-! ## Exactness -/

theorem Row.claim?_exact (program : List Atom) (table : List Claim) (row : Row) (claim : Claim) :
    row.claim? program table = some claim ↔ Row.Valid program table row claim := by
  cases row with
  | refl atom =>
      simp only [Row.claim?, Option.some.injEq]
      constructor
      · rintro rfl
        exact .refl atom
      · intro valid
        cases valid
        rfl
  | step prior citation path bindings =>
      constructor
      · intro computed
        simp only [Row.claim?] at computed
        split at computed
        · rename_i source current left right atPrior sides
          split_ifs at computed with conditions
          obtain ⟨next, replaced, rfl⟩ := Option.map_eq_some_iff.mp computed
          exact .step atPrior (equationSides_eq_some.mp sides)
            (Citation.valid_spaceOf.mpr conditions.1) conditions.2 replaced
        · cases computed
      · intro valid
        cases valid with
        | step atPrior equation cited found replaced =>
            rename_i source current left right next
            have sides : equationSides citation.equation = some (left, right) :=
              equationSides_eq_some.mpr equation
            simp only [Row.claim?, atPrior, sides]
            rw [if_pos ⟨Citation.valid_spaceOf.mp cited, found⟩, replaced]
            rfl
  | congr left inner right =>
      simp only [Row.claim?]
      constructor
      · intro computed
        obtain ⟨⟨source, target⟩, found, rfl⟩ := Option.map_eq_some_iff.mp computed
        exact .congr found
      · intro valid
        cases valid with
        | congr found => simp only [found, Option.map_some]
  | trans first second =>
      constructor
      · intro computed
        simp only [Row.claim?] at computed
        split at computed
        · rename_i source middle middle' target atFirst atSecond
          split_ifs at computed with same
          cases computed
          subst same
          exact .trans atFirst atSecond
        · cases computed
      · intro valid
        cases valid with
        | trans atFirst atSecond =>
            simp only [Row.claim?, atFirst, atSecond, if_true]

theorem checkRows_exact (program : List Atom) (table : List Claim) (rows : List Row)
    (final : List Claim) :
    checkRows program table rows = some final ↔ RowsValid program table rows final := by
  induction rows generalizing table with
  | nil =>
      simp only [checkRows, Option.some.injEq]
      constructor
      · rintro rfl
        exact .nil table
      · intro valid
        cases valid
        rfl
  | cons row rows ih =>
      constructor
      · intro checked
        simp only [checkRows] at checked
        split at checked
        · rename_i claim computed
          exact .cons ((Row.claim?_exact _ _ _ _).mp computed) ((ih _).mp checked)
        · cases checked
      · intro valid
        cases valid with
        | cons rowValid rest =>
            rename_i claim
            simp only [checkRows, (Row.claim?_exact _ _ _ _).mpr rowValid]
            exact (ih _).mpr rest

theorem check_exact (program : List Atom) (certificate : Certificate) (claim : Claim) :
    check program certificate claim = true ↔ certificate.Valid program claim := by
  rw [check_eq_checkReference]
  unfold checkReference Certificate.Valid
  constructor
  · intro accepted
    split at accepted
    · rename_i table checked
      exact ⟨table, (checkRows_exact _ _ _ _).mp checked, of_decide_eq_true accepted⟩
    · cases accepted
  · rintro ⟨table, valid, rooted⟩
    rw [(checkRows_exact _ _ _ _).mpr valid]
    exact decide_eq_true rooted

/-! ## Soundness -/

theorem Row.Valid.derives {program : List Atom} {table : List Claim} {row : Row}
    {claim : Claim} (valid : Row.Valid program table row claim)
    (earlier : ∀ entry ∈ table, Derives (spaceOf program) entry.1 entry.2) :
    Derives (spaceOf program) claim.1 claim.2 := by
  cases valid with
  | refl atom => exact .refl atom
  | step atPrior equation cited found replaced =>
      have prior := earlier _ (List.mem_of_getElem? atPrior)
      have stored := cited.mem
      rw [equation] at stored
      exact .step _ _ prior stored found replaced
  | congr found => exact .congr _ _ (earlier _ (List.mem_of_getElem? found))
  | trans atFirst atSecond =>
      have first := earlier _ (List.mem_of_getElem? atFirst)
      have second := earlier _ (List.mem_of_getElem? atSecond)
      exact .trans first second

theorem RowsValid.derives {program : List Atom} {table final : List Claim} {rows : List Row}
    (valid : RowsValid program table rows final)
    (earlier : ∀ entry ∈ table, Derives (spaceOf program) entry.1 entry.2) :
    ∀ entry ∈ final, Derives (spaceOf program) entry.1 entry.2 := by
  induction valid with
  | nil => exact earlier
  | cons rowValid _ ih =>
      apply ih
      intro entry member
      rcases List.mem_append.mp member with old | new
      · exact earlier entry old
      · rw [List.mem_singleton.mp new]
        exact rowValid.derives earlier

theorem Certificate.Valid.derives {program : List Atom} {certificate : Certificate}
    {source target : Atom} (valid : certificate.Valid program (source, target)) :
    Derives (spaceOf program) source target := by
  obtain ⟨table, rows, rooted⟩ := valid
  exact rows.derives (by simp) _ (List.mem_of_getElem? rooted)

theorem check_sound {program : List Atom} {certificate : Certificate} {source target : Atom}
    (accepted : check program certificate (source, target) = true) :
    Reaches (spaceOf program) source target :=
  ((check_exact _ _ _).mp accepted).derives.reaches

/-! ## Coverage -/

/-- The bindings of a substitution on the variables it is asked about. -/
def bindingsOn (σ : Subst) (names : List Var) : Bindings :=
  names.filterMap fun name => (σ name).map (name, ·)

theorem lookup_bindingsOn_absent (σ : Subst) (names : List Var) (name : Var)
    (absent : name ∉ names) : (bindingsOn σ names).toSubst name = none := by
  induction names with
  | nil => rfl
  | cons head rest ih =>
      have different : name ≠ head := fun same => absent (same ▸ List.mem_cons_self ..)
      have later : name ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      unfold bindingsOn Bindings.toSubst at ih ⊢
      cases bound : σ head with
      | none => simpa [List.filterMap_cons, bound] using ih later
      | some value =>
          have skip : (name == head) = false := by simpa using different
          simp only [List.filterMap_cons, bound, Option.map_some, List.lookup, skip]
          exact ih later

theorem lookup_bindingsOn (σ : Subst) (names : List Var) (name : Var) (member : name ∈ names) :
    (bindingsOn σ names).toSubst name = σ name := by
  induction names with
  | nil => cases member
  | cons head rest ih =>
      by_cases same : name = head
      · subst same
        unfold bindingsOn Bindings.toSubst
        cases bound : σ name with
        | none =>
            simp only [List.filterMap_cons, bound]
            by_cases later : name ∈ rest
            · exact (ih later).trans bound
            · exact lookup_bindingsOn_absent σ rest name later
        | some value => simp [bound]
      · have later : name ∈ rest := by
          rcases List.mem_cons.mp member with here | there
          · exact absurd here same
          · exact there
        unfold bindingsOn Bindings.toSubst at ih ⊢
        cases bound : σ head with
        | none => simpa [List.filterMap_cons, bound] using ih later
        | some value =>
            have skip : (name == head) = false := by simpa using same
            simp only [List.filterMap_cons, bound, Option.map_some, List.lookup, skip]
            exact ih later

theorem subst_bindingsOn (σ : Subst) (left right : Atom) :
    subst (bindingsOn σ (vars left ++ vars right)).toSubst left = subst σ left ∧
      subst (bindingsOn σ (vars left ++ vars right)).toSubst right = subst σ right :=
  ⟨SubstitutionAlgebra.subst_congr_on_vars _ _ _
      (fun name member => lookup_bindingsOn σ _ name (List.mem_append_left _ member)),
    SubstitutionAlgebra.subst_congr_on_vars _ _ _
      (fun name member => lookup_bindingsOn σ _ name (List.mem_append_right _ member))⟩

theorem RowsValid.append {program : List Atom} {table middle final : List Claim}
    {front back : List Row}
    (frontValid : RowsValid program table front middle)
    (backValid : RowsValid program middle back final) :
    RowsValid program table (front ++ back) final := by
  induction frontValid with
  | nil => exact backValid
  | cons rowValid _ ih => exact .cons rowValid (ih backValid)

/-- Checked rows only extend the table. -/
theorem RowsValid.extends {program : List Atom} {table final : List Claim} {rows : List Row}
    (valid : RowsValid program table rows final) :
    ∃ claims, final = table ++ claims ∧ claims.length = rows.length := by
  induction valid with
  | nil => exact ⟨[], by simp, rfl⟩
  | @cons _ _ _ claim _ _ _ ih =>
      obtain ⟨claims, same, length⟩ := ih
      exact ⟨claim :: claims, by simp [same], by simp [length]⟩

theorem getElem?_last {table claims : List Claim} {claim : Claim}
    (last : claims.getLast? = some claim) :
    (table ++ claims)[table.length + claims.length - 1]? = some claim := by
  have positive : 0 < claims.length := by
    cases claims with
    | nil => cases last
    | cons _ _ => simp
  rw [List.getElem?_append_right (by omega)]
  have shift : table.length + claims.length - 1 - table.length = claims.length - 1 := by omega
  rw [shift, ← List.getLast?_eq_getElem?]
  exact last

/-- Every derivation is written by rows that extend any table. The rows
record the derivation's own choices; nothing is searched. -/
theorem exists_rows_of_derives {program : List Atom} {source target : Atom}
    (derived : Derives (spaceOf program) source target) (table : List Claim) :
    ∃ rows claims, RowsValid program table rows (table ++ claims) ∧
      claims.getLast? = some (source, target) := by
  induction derived generalizing table with
  | refl atom =>
      exact ⟨[.refl atom], [(atom, atom)], .cons (.refl atom) (.nil _), rfl⟩
  | @step source current next left right path σ _ stored found replaced ih =>
      obtain ⟨rows, claims, valid, last⟩ := ih table
      obtain ⟨sameLeft, sameRight⟩ := subst_bindingsOn σ left right
      let row := Row.step (table.length + claims.length - 1) ⟨Atom.equality left right, 0⟩ path
        (bindingsOn σ (vars left ++ vars right))
      have stepValid : Row.Valid program (table ++ claims) row (source, next) :=
        .step (getElem?_last last) rfl (Citation.exists_valid stored)
          (sameLeft ▸ found) (sameRight ▸ replaced)
      refine ⟨rows ++ [row], claims ++ [(source, next)], ?_, by simp⟩
      rw [← List.append_assoc]
      exact valid.append (.cons stepValid (.nil _))
  | @congr source target left right _ ih =>
      obtain ⟨rows, claims, valid, last⟩ := ih table
      let row := Row.congr left (table.length + claims.length - 1) right
      have congrValid : Row.Valid program (table ++ claims) row
          (.expression (left ++ source :: right), .expression (left ++ target :: right)) :=
        .congr (getElem?_last last)
      refine ⟨rows ++ [row], claims ++ [(.expression (left ++ source :: right),
        .expression (left ++ target :: right))], ?_, by simp⟩
      rw [← List.append_assoc]
      exact valid.append (.cons congrValid (.nil _))
  | @trans first middle last _ _ firstIh secondIh =>
      obtain ⟨front, frontClaims, frontValid, frontLast⟩ := firstIh table
      obtain ⟨back, backClaims, backValid, backLast⟩ := secondIh (table ++ frontClaims)
      have firstAt : (table ++ frontClaims ++ backClaims)[table.length + frontClaims.length - 1]? =
          some (first, middle) := by
        have positive : 0 < frontClaims.length := by
          cases frontClaims with
          | nil => cases frontLast
          | cons _ _ => simp
        rw [List.getElem?_append_left (by simp; omega)]
        exact getElem?_last frontLast
      have secondAt := getElem?_last (table := table ++ frontClaims) backLast
      let row := Row.trans (table.length + frontClaims.length - 1)
        ((table ++ frontClaims).length + backClaims.length - 1)
      have transValid : Row.Valid program (table ++ frontClaims ++ backClaims) row (first, last) :=
        .trans firstAt secondAt
      refine ⟨front ++ back ++ [row], frontClaims ++ backClaims ++ [(first, last)], ?_, by simp⟩
      have joined := (frontValid.append backValid).append (.cons transValid (.nil _))
      simpa only [List.append_assoc] using joined

/-- Coverage: every reachable claim has an accepted certificate. -/
theorem exists_check_of_reaches {program : List Atom} {source target : Atom}
    (reaches : Reaches (spaceOf program) source target) :
    ∃ certificate, check program certificate (source, target) = true := by
  obtain ⟨rows, claims, valid, last⟩ := exists_rows_of_derives (Derives.of_reaches reaches) []
  refine ⟨⟨rows, claims.length - 1⟩, (check_exact _ _ _).mpr ⟨_, valid, ?_⟩⟩
  simpa using getElem?_last (table := []) last

theorem exists_check_iff_reaches (program : List Atom) (source target : Atom) :
    (∃ certificate, check program certificate (source, target) = true) ↔
      Reaches (spaceOf program) source target :=
  ⟨fun ⟨_, accepted⟩ => check_sound accepted, exists_check_of_reaches⟩

/-! ## Composition -/

/-- Move every reference past a prefix of rows. -/
def Row.shift (offset : Nat) : Row → Row
  | .refl atom => .refl atom
  | .step prior citation path bindings => .step (prior + offset) citation path bindings
  | .congr left inner right => .congr left (inner + offset) right
  | .trans first second => .trans (first + offset) (second + offset)

theorem getElem?_shift (before table : List Claim) (position : Nat) :
    (before ++ table)[position + before.length]? = table[position]? := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]

theorem Row.Valid.shift {program : List Atom} {table : List Claim} {row : Row} {claim : Claim}
    (valid : Row.Valid program table row claim) (before : List Claim) :
    Row.Valid program (before ++ table) (row.shift before.length) claim := by
  cases valid with
  | refl atom => exact .refl atom
  | step atPrior equation cited found replaced =>
      exact .step ((getElem?_shift _ _ _).trans atPrior) equation cited found replaced
  | congr found => exact .congr ((getElem?_shift _ _ _).trans found)
  | trans atFirst atSecond =>
      exact .trans ((getElem?_shift _ _ _).trans atFirst) ((getElem?_shift _ _ _).trans atSecond)

theorem RowsValid.shift {program : List Atom} {table final : List Claim} {rows : List Row}
    (valid : RowsValid program table rows final) (before : List Claim) :
    RowsValid program (before ++ table) (rows.map (Row.shift before.length)) (before ++ final) := by
  induction valid with
  | nil => exact .nil _
  | cons rowValid _ ih =>
      refine .cons (rowValid.shift before) ?_
      simpa only [List.append_assoc] using ih

theorem Certificate.Valid.table {program : List Atom} {certificate : Certificate} {claim : Claim}
    (valid : certificate.Valid program claim) :
    ∃ table, RowsValid program [] certificate.rows table ∧
      table.length = certificate.rows.length ∧ table[certificate.root]? = some claim := by
  obtain ⟨table, rows, rooted⟩ := valid
  obtain ⟨claims, same, length⟩ := rows.extends
  subst same
  exact ⟨_, rows, by simpa using length, rooted⟩

/-- Sequential composition: the second certificate follows the first and a
transitivity row joins their roots. -/
def Certificate.seq (first second : Certificate) : Certificate :=
  ⟨first.rows ++ second.rows.map (Row.shift first.rows.length) ++
      [.trans first.root (second.root + first.rows.length)],
    first.rows.length + second.rows.length⟩

theorem check_seq {program : List Atom} {first second : Certificate} {source middle target : Atom}
    (firstAccepted : check program first (source, middle) = true)
    (secondAccepted : check program second (middle, target) = true) :
    check program (first.seq second) (source, target) = true := by
  obtain ⟨firstTable, firstRows, firstLength, firstRoot⟩ :=
    ((check_exact _ _ _).mp firstAccepted).table
  obtain ⟨secondTable, secondRows, secondLength, secondRoot⟩ :=
    ((check_exact _ _ _).mp secondAccepted).table
  have shifted := secondRows.shift firstTable
  simp only [List.append_nil] at shifted
  have firstAt : (firstTable ++ secondTable)[first.root]? = some (source, middle) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp firstRoot).1]
    exact firstRoot
  have secondAt : (firstTable ++ secondTable)[second.root + first.rows.length]? =
      some (middle, target) := by
    rw [← firstLength, getElem?_shift]
    exact secondRoot
  refine (check_exact _ _ _).mpr ⟨firstTable ++ secondTable ++ [(source, target)], ?_, ?_⟩
  · have joined := (firstRows.append shifted).append (.cons (.trans firstAt secondAt) (.nil _))
    simpa only [Certificate.seq, firstLength, List.append_assoc] using joined
  · rw [List.getElem?_append_right (by simp [Certificate.seq, firstLength, secondLength])]
    simp [Certificate.seq, firstLength, secondLength]

/-- Composition in a context: one argument of an expression is rewritten. -/
def Certificate.congr (left : List Atom) (inner : Certificate) (right : List Atom) : Certificate :=
  ⟨inner.rows ++ [.congr left inner.root right], inner.rows.length⟩

theorem check_congr {program : List Atom} {inner : Certificate} {source target : Atom}
    (left right : List Atom) (accepted : check program inner (source, target) = true) :
    check program (Certificate.congr left inner right)
      (.expression (left ++ source :: right), .expression (left ++ target :: right)) = true := by
  obtain ⟨table, rows, length, rooted⟩ := ((check_exact _ _ _).mp accepted).table
  refine (check_exact _ _ _).mpr ⟨_, rows.append (.cons (.congr rooted) (.nil _)), ?_⟩
  simp only [Certificate.congr]
  rw [← length, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- One derivation shared by two arguments: `(head a a) →* (head b b)` with
the derivation of `a →* b` written once and cited twice. -/
def Certificate.both (head : Atom) (inner : Certificate) (source target : Atom) : Certificate :=
  ⟨inner.rows ++ [.congr [head] inner.root [source], .congr [head, target] inner.root [],
      .trans inner.rows.length (inner.rows.length + 1)],
    inner.rows.length + 2⟩

theorem check_both {program : List Atom} {inner : Certificate} {source target : Atom}
    (head : Atom) (accepted : check program inner (source, target) = true) :
    check program (Certificate.both head inner source target)
      (.expression [head, source, source], .expression [head, target, target]) = true := by
  obtain ⟨table, rows, length, rooted⟩ := ((check_exact _ _ _).mp accepted).table
  let firstClaim : Claim := (.expression [head, source, source], .expression [head, target, source])
  let secondClaim : Claim := (.expression [head, target, source], .expression [head, target, target])
  have first : Row.Valid program table (.congr [head] inner.root [source]) firstClaim := .congr rooted
  have rootedLater : (table ++ [firstClaim])[inner.root]? = some (source, target) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp rooted).1]
    exact rooted
  have second : Row.Valid program (table ++ [firstClaim]) (.congr [head, target] inner.root [])
      secondClaim := by
    simpa using (Row.Valid.congr (program := program) (left := [head, target]) (right := [])
      rootedLater)
  have atFirstRow : (table ++ [firstClaim] ++ [secondClaim])[inner.rows.length]? = some firstClaim := by
    rw [← length, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have atSecondRow : (table ++ [firstClaim] ++ [secondClaim])[inner.rows.length + 1]? =
      some secondClaim := by
    rw [← length, List.append_assoc, List.getElem?_append_right (by omega)]
    simp
  have third : Row.Valid program (table ++ [firstClaim] ++ [secondClaim])
      (.trans inner.rows.length (inner.rows.length + 1))
      (.expression [head, source, source], .expression [head, target, target]) :=
    .trans atFirstRow atSecondRow
  refine (check_exact _ _ _).mpr ⟨_, rows.append (.cons first (.cons second (.cons third
    (.nil _)))), ?_⟩
  simp only [Certificate.both]
  rw [← length]
  simp

theorem both_rows_length (head : Atom) (inner : Certificate) (source target : Atom) :
    (Certificate.both head inner source target).rows.length = inner.rows.length + 3 := by
  simp [Certificate.both]

/-! ## Linear traces -/

/-- One step of a linear trace: a stored copy, a position and bindings. -/
structure StepData where
  citation : Citation
  path : List Nat
  bindings : Bindings
  deriving DecidableEq, Repr

def StepData.apply? (program : List Atom) (current : Atom) (step : StepData) : Option Atom :=
  match equationSides step.citation.equation with
  | some (left, right) =>
      if step.citation.copy < program.count step.citation.equation ∧
          subatom? current step.path = some (subst step.bindings.toSubst left) then
        replaceAt? current step.path (subst step.bindings.toSubst right)
      else none
  | none => none

def replay (program : List Atom) (source : Atom) : List StepData → Option Atom
  | [] => some source
  | step :: steps => (step.apply? program source).bind fun next => replay program next steps

/-- Replay composes along concatenation, joining at the literal middle atom. -/
theorem replay_append (program : List Atom) (source : Atom) (front back : List StepData) :
    replay program source (front ++ back) =
      (replay program source front).bind fun middle => replay program middle back := by
  induction front generalizing source with
  | nil => rfl
  | cons step steps ih =>
      simp only [List.cons_append, replay]
      cases step.apply? program source with
      | none => rfl
      | some next => exact ih next

def traceSteps (start : Nat) : List StepData → List Row
  | [] => []
  | step :: steps => .step start step.citation step.path step.bindings :: traceSteps (start + 1) steps

/-- A trace as a certificate: a reflexivity row, then each step extends the
previous row's claim. -/
def traceCertificate (source : Atom) (steps : List StepData) : Certificate :=
  ⟨.refl source :: traceSteps 0 steps, steps.length⟩

theorem claim?_traceStep {program : List Atom} {table : List Claim} {start : Nat}
    {source current : Atom} (atStart : table[start]? = some (source, current)) (step : StepData) :
    (Row.step start step.citation step.path step.bindings).claim? program table =
      (step.apply? program current).map (source, ·) := by
  cases sides : equationSides step.citation.equation with
  | none => simp [Row.claim?, StepData.apply?, atStart, sides]
  | some pair =>
      rcases pair with ⟨left, right⟩
      simp only [Row.claim?, StepData.apply?, atStart, sides]
      split_ifs <;> simp

theorem checkRows_traceSteps (program : List Atom) (steps : List StepData) :
    ∀ (table : List Claim) (start : Nat) (source current : Atom),
      table.length = start + 1 → table[start]? = some (source, current) →
        (checkRows program table (traceSteps start steps)).bind
            (fun final => final[start + steps.length]?) =
          (replay program current steps).map (source, ·) := by
  induction steps with
  | nil =>
      intro table start source current _ atStart
      simp [checkRows, traceSteps, replay, atStart]
  | cons step steps ih =>
      intro table start source current length atStart
      simp only [traceSteps, checkRows, claim?_traceStep atStart, replay]
      cases step.apply? program current with
      | none => rfl
      | some next =>
          simp only [Option.map_some, Option.bind_some]
          have extended := ih (table ++ [(source, next)]) (start + 1) source next
            (by simp [length]) (by simp [← length])
          simpa [Nat.add_assoc, Nat.add_comm 1] using extended

theorem check_trace_iff (program : List Atom) (source target : Atom) (steps : List StepData) :
    check program (traceCertificate source steps) (source, target) = true ↔
      replay program source steps = some target := by
  have traced := checkRows_traceSteps program steps [(source, source)] 0 source source rfl rfl
  rw [check_eq_checkReference]
  unfold checkReference traceCertificate
  simp only [checkRows, Row.claim?, List.nil_append, Nat.zero_add] at traced ⊢
  cases checked : checkRows program [(source, source)] (traceSteps 0 steps) with
  | none =>
      rw [checked] at traced
      simp only [Option.bind_none] at traced
      constructor
      · intro impossible
        cases impossible
      · intro replayed
        rw [replayed] at traced
        cases traced
  | some final =>
      rw [checked] at traced
      simp only [Option.bind_some] at traced
      show decide (final[steps.length]? = some (source, target)) = true ↔ _
      rw [traced]
      cases replay program source steps with
      | none => simp
      | some reached => simp

/-- Reflexivity and step rows suffice: every reachable claim has a linear
trace. Congruence and transitivity rows add sharing and composition, not
reachable claims. -/
theorem exists_trace_iff_reaches (program : List Atom) (source target : Atom) :
    (∃ steps, replay program source steps = some target) ↔ Reaches (spaceOf program) source target := by
  constructor
  · rintro ⟨steps, replayed⟩
    exact check_sound ((check_trace_iff program source target steps).mpr replayed)
  · intro reaches
    induction reaches with
    | refl => exact ⟨[], rfl⟩
    | @tail middle last _ step ih =>
        obtain ⟨steps, replayed⟩ := ih
        obtain ⟨left, right, path, σ, stored, found, replaced⟩ := step.exists_path
        obtain ⟨sameLeft, sameRight⟩ := subst_bindingsOn σ left right
        refine ⟨steps ++ [⟨⟨Atom.equality left right, 0⟩, path, bindingsOn σ (vars left ++ vars right)⟩], ?_⟩
        rw [replay_append, replayed]
        have cited : 0 < program.count (Atom.equality left right) :=
          Citation.valid_spaceOf.mp (Citation.exists_valid stored)
        simp only [Option.bind_some, replay, StepData.apply?, equationSides_equality, sameLeft, sameRight,
          found, replaced, cited, and_self, if_true, Option.bind_some]

/-! ## Reordering the space -/

theorem Row.claim?_perm {program other : List Atom} (permuted : program.Perm other)
    (table : List Claim) (row : Row) : row.claim? program table = row.claim? other table := by
  cases row <;> simp only [Row.claim?, permuted.count_eq]

theorem checkRows_perm {program other : List Atom} (permuted : program.Perm other)
    (table : List Claim) (rows : List Row) :
    checkRows program table rows = checkRows other table rows := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rows ih =>
      simp only [checkRows, Row.claim?_perm permuted]
      cases row.claim? other table with
      | none => rfl
      | some claim => exact ih _

/-- The verdict depends on the program only through the counts of its atoms. -/
theorem check_perm {program other : List Atom} (permuted : program.Perm other)
    (certificate : Certificate) (claim : Claim) :
    check program certificate claim = check other certificate claim := by
  rw [check_eq_checkReference, check_eq_checkReference]
  simp only [checkReference, checkRows_perm permuted]

/-! ## Equal stored copies are separate citations -/

/-- Whether an equation atom licenses one step from `source` to `target` at a
position with given bindings. -/
def licenses (source target : Atom) (path : List Nat) (bindings : Bindings) (equation : Atom) :
    Bool :=
  match equationSides equation with
  | some (left, right) =>
      decide (subatom? source path = some (subst bindings.toSubst left) ∧
        replaceAt? source path (subst bindings.toSubst right) = some target)
  | none => false

theorem check_one_step_iff (program : List Atom) (source target : Atom) (citation : Citation)
    (path : List Nat) (bindings : Bindings) :
    check program (traceCertificate source [⟨citation, path, bindings⟩]) (source, target) = true ↔
      citation ∈ occurrences program ∧
        licenses source target path bindings citation.equation = true := by
  rw [check_trace_iff, mem_occurrences]
  simp only [replay, StepData.apply?, licenses]
  cases equationSides citation.equation with
  | none => simp
  | some sides =>
      rcases sides with ⟨left, right⟩
      by_cases cited : citation.copy < program.count citation.equation <;>
        by_cases found : subatom? source path = some (subst bindings.toSubst left) <;>
        simp [cited, found]

/-- The accepted citations of one step are as many as the program's atoms
that license it: two equal stored equations give two accepted citations. -/
theorem accepted_citations_length (program : List Atom) (source target : Atom)
    (path : List Nat) (bindings : Bindings) :
    ((occurrences program).filter fun citation =>
        check program (traceCertificate source [⟨citation, path, bindings⟩]) (source, target)).length =
      (program.filter (licenses source target path bindings)).length := by
  rw [← occurrences_filter_length program (licenses source target path bindings)]
  congr 1
  apply List.filter_congr
  intro citation member
  have accepted := check_one_step_iff program source target citation path bindings
  have inOccurrences : citation ∈ occurrences program := member
  cases licensed : licenses source target path bindings citation.equation <;>
    cases checked : check program (traceCertificate source [⟨citation, path, bindings⟩])
      (source, target) <;> simp_all

end Mettapedia.Languages.MeTTa.EquationKernel
