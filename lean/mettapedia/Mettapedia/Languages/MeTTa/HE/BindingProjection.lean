import Mettapedia.Languages.MeTTa.HE.BindingResolutionReadSupport
import Mathlib.Data.Finset.Card

/-!
# Support-preserving projection of HE assignments

Projection filters assignment entries in their original order and retains the
ordered equality authority. A finite list of binding applications supplies its
transitive read support, including unsuccessful lookups. Projecting to that
support preserves the exact list of applications, with repeated observations
and correlations between variables intact.

The applications retain their original fuel. These laws do not discover the
roots of a native continuation, model closure execution or resource finalizers,
or authorize projection of equality relations. Assignment-count bounds are
separate from the byte size of assignment values and retained authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.BindingProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open BindingResolutionReadSupport

/-- Filter assignments by admitted names without changing order or authority. -/
def project (keep : List String) (bindings : Bindings) : Bindings :=
  { bindings with assignments := bindings.assignments.filter (fun entry => keep.contains entry.1) }

@[simp] theorem project_equalities (keep : List String) (bindings : Bindings) :
    (project keep bindings).equalities = bindings.equalities := rfl

private theorem lookup_filter (keep : List String) (key : String) :
    ∀ entries : List (String × Atom),
      (entries.filter (fun entry => keep.contains entry.1)).lookup key =
        if key ∈ keep then entries.lookup key else none := by
  intro entries
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      by_cases included : name ∈ keep
      · have admitted : keep.contains name = true := by simpa using included
        by_cases same : key = name
        · subst key
          simp only [List.filter_cons, admitted, ↓reduceIte,
            List.lookup_cons, BEq.rfl, if_pos included]
        · have distinct : (key == name) = false := by simpa using same
          simpa only [List.filter_cons, admitted, ↓reduceIte,
            List.lookup_cons, distinct] using ih
      · have refused : keep.contains name = false := by simpa using included
        by_cases same : key = name
        · subst key
          simpa only [List.filter_cons, refused, Bool.false_eq_true, ↓reduceIte,
            List.lookup_cons, BEq.rfl, if_neg included] using ih
        · have distinct : (key == name) = false := by simpa using same
          simpa only [List.filter_cons, refused, Bool.false_eq_true, ↓reduceIte,
            List.lookup_cons, distinct] using ih

/-- Retained lookups keep their full value; omitted names have no assignment. -/
theorem lookup_project (keep : List String) (bindings : Bindings) (key : String) :
    (project keep bindings).lookup key =
      if key ∈ keep then bindings.lookup key else none :=
  lookup_filter keep key bindings.assignments

theorem lookup_project_kept (keep : List String) (bindings : Bindings) (key : String)
    (member : key ∈ keep) :
    (project keep bindings).lookup key = bindings.lookup key := by
  simp [lookup_project, member]

/-- The projection is a subsequence, so it cannot invent or reorder entries. -/
theorem assignments_sublist (keep : List String) (bindings : Bindings) :
    (project keep bindings).assignments.Sublist bindings.assignments :=
  List.filter_sublist

theorem assignment_count_le (keep : List String) (bindings : Bindings) :
    (project keep bindings).assignments.length ≤ bindings.assignments.length :=
  (assignments_sublist keep bindings).length_le

/-- With unique assignment names, retained entries are bounded by the number
of retained names. Values and equality authority are not charged as entries. -/
theorem assignment_count_le_names (keep : List String) (bindings : Bindings)
    (unique : (bindings.assignments.map Prod.fst).Nodup) :
    (project keep bindings).assignments.length ≤ keep.toFinset.card := by
  let names := (project keep bindings).assignments.map Prod.fst
  have subsequence : names.Sublist (bindings.assignments.map Prod.fst) :=
    (assignments_sublist keep bindings).map Prod.fst
  have noDuplicates : names.Nodup := List.Nodup.sublist subsequence unique
  have contained : names.toFinset ⊆ keep.toFinset := by
    intro key member
    obtain ⟨entry, retained, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact List.mem_toFinset.mpr (by
      simpa using (List.mem_filter.mp retained).2)
  calc
    (project keep bindings).assignments.length = names.length := by simp [names]
    _ = names.toFinset.card := (List.toFinset_card_of_nodup noDuplicates).symm
    _ ≤ keep.toFinset.card := Finset.card_le_card contained

/-- Two projections retain exactly the intersection of their admitted names. -/
theorem project_project (first second : List String) (bindings : Bindings) :
    project second (project first bindings) =
      project (first.filter second.contains) bindings := by
  unfold project
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro entry member
  simp [List.mem_filter, Bool.and_comm]

theorem project_idempotent (keep : List String) (bindings : Bindings) :
    project keep (project keep bindings) = project keep bindings := by
  unfold project
  congr 1
  simp [List.filter_filter]

/-- The equality-aware public resolver is unchanged when its reads are kept. -/
theorem resolveFull_project (keep : List String) (bindings : Bindings)
    (root : String) (fuel : Nat)
    (retained : ∀ key ∈ support bindings root fuel, key ∈ keep) :
    (project keep bindings).resolveFull root fuel = bindings.resolveFull root fuel := by
  apply resolveFull_eq_of_reads (first := bindings) (second := project keep bindings) rfl root fuel
  apply (Mettapedia.Machines.ReadOnlyQuery.agrees_samples_iff _ _ _).mpr
  intro key member
  exact lookup_project_kept keep bindings key (retained key member)

/-- Application preserves aliases, absent reads and correlated occurrences. -/
theorem applyFull_project (keep : List String) (bindings : Bindings)
    (atom : Atom) (fuel : Nat)
    (retained : ∀ key ∈ applySupport bindings fuel atom, key ∈ keep) :
    (project keep bindings).applyFull atom fuel = bindings.applyFull atom fuel := by
  apply applyFull_eq_of_support (first := bindings) (second := project keep bindings) rfl fuel atom
  intro key member
  exact lookup_project_kept keep bindings key (retained key member)

abbrev Applications := List (Atom × Nat)

/-- All assignment reads of the declared applications, not just root names. -/
def applicationSupport (bindings : Bindings) (applications : Applications) : List String :=
  applications.flatMap fun request => applySupport bindings request.2 request.1

def observe (bindings : Bindings) (applications : Applications) : List Atom :=
  applications.map fun request => bindings.applyFull request.1 request.2

def forApplications (bindings : Bindings) (applications : Applications) : Bindings :=
  project (applicationSupport bindings applications) bindings

/-- Capture for the whole retained continuation also preserves any ordered
subsequence of its observations. Looking only at the currently executing
application does not establish this condition for pending siblings. -/
theorem observe_forApplications_sublist (bindings : Bindings)
    (retained selected : Applications) (included : selected.Sublist retained) :
    observe (forApplications bindings retained) selected =
      observe bindings selected := by
  apply List.map_congr_left
  intro request member
  apply applyFull_project
  intro key dependency
  exact List.mem_flatMap.mpr ⟨request, included.subset member, dependency⟩

/-- Actual computed projection preserves the complete ordered observation. -/
theorem observe_forApplications (bindings : Bindings) (applications : Applications) :
    observe (forApplications bindings applications) applications =
      observe bindings applications :=
  observe_forApplications_sublist bindings applications applications (.refl _)

/-- A pending suffix keeps its bindings while an earlier application is
observed. This is one captured support union, not one projection per child.
Order and repeated observations remain part of each side. -/
theorem observe_forApplications_append (bindings : Bindings)
    (current pending : Applications) :
    observe (forApplications bindings (current ++ pending)) current =
        observe bindings current ∧
      observe (forApplications bindings (current ++ pending)) pending =
        observe bindings pending := by
  constructor
  · exact observe_forApplications_sublist bindings _ _ (List.sublist_append_left _ _)
  · exact observe_forApplications_sublist bindings _ _ (List.sublist_append_right _ _)

namespace Controls

def aliasStore : Bindings :=
  ⟨[("x", .var "y"), ("y", .symbol "7"), ("unused", .symbol "Other")], []⟩

def aliasApplications : Applications := [(.var "x", 7), (.var "x", 7)]

theorem alias_reachable_assignment_kept :
    (forApplications aliasStore aliasApplications).assignments =
      [("x", .var "y"), ("y", .symbol "7")] ∧
      observe (forApplications aliasStore aliasApplications) aliasApplications =
        [.symbol "7", .symbol "7"] := by decide

theorem root_names_alone_lose_meaning :
    observe (project ["x"] aliasStore) aliasApplications ≠ observe aliasStore aliasApplications := by decide

/-- The current ground field reads no assignment, but its pending sibling
still reads an alias chain. Child-local support cannot replace parent support. -/
theorem child_support_does_not_cover_pending_sibling :
    observe (forApplications aliasStore [(.symbol "Head", 7)]) aliasApplications =
        [.var "x", .var "x"] ∧
      observe (forApplications aliasStore [(.symbol "Head", 7)]) aliasApplications ≠
        observe aliasStore aliasApplications := by decide

/-- A later, wider projection cannot reconstruct a binding already discarded.
The continuation must retain the authority before returning from its child. -/
theorem reprojecting_cannot_restore_pending_sibling :
    observe (forApplications
        (forApplications aliasStore [(.symbol "Head", 7)]) aliasApplications)
        aliasApplications ≠ observe aliasStore aliasApplications := by decide

def duplicateNames : Bindings :=
  ⟨[("x", .symbol "First"), ("x", .symbol "Second")], []⟩

theorem duplicate_names_need_the_count_premise :
    (project ["x"] duplicateNames).assignments.length = 2 ∧
      (["x"] : List String).toFinset.card = 1 := by decide

/-- Projection for an exhausted application does not license a later
application with a larger fuel budget and additional reads. -/
theorem increased_fuel_needs_a_new_support :
    observe (forApplications aliasStore [(.var "x", 1)]) [(.var "x", 1)] =
      observe aliasStore [(.var "x", 1)] ∧
      observe (forApplications aliasStore [(.var "x", 1)]) [(.var "x", 7)] ≠
        observe aliasStore [(.var "x", 7)] := by decide

theorem absent_assignment_is_a_dependency :
    "unbound" ∈ applicationSupport aliasStore [(.var "unbound", 7)] ∧
      (forApplications aliasStore [(.var "unbound", 7)]).lookup "unbound" = none := by decide

def firstBranch : Bindings :=
  ⟨[("x", .expression [.symbol "Pair", .var "y", .var "y"]),
    ("y", .symbol "A"), ("unused", .symbol "Other")], []⟩

def secondBranch : Bindings := firstBranch.assign "y" (.symbol "B")

theorem correlated_branches_stay_distinct :
    observe (forApplications firstBranch aliasApplications) aliasApplications =
      [.expression [.symbol "Pair", .symbol "A", .symbol "A"],
       .expression [.symbol "Pair", .symbol "A", .symbol "A"]] ∧
      observe (forApplications secondBranch aliasApplications) aliasApplications =
      [.expression [.symbol "Pair", .symbol "B", .symbol "B"],
       .expression [.symbol "Pair", .symbol "B", .symbol "B"]] := by decide

def equalityAlias : Bindings := aliasStore.addEquality "z" "x"

theorem equality_authority_kept :
    (forApplications equalityAlias [(.var "z", 7)]).equalities = [("z", "x")] ∧
      observe (forApplications equalityAlias [(.var "z", 7)]) [(.var "z", 7)] =
        [.symbol "7"] := by decide

end Controls

end Mettapedia.Languages.MeTTa.HE.BindingProjection
