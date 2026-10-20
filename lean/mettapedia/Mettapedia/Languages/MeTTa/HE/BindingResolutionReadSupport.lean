import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.EqualityClosure
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Assignment read support for equality-aware HE resolution

The public HE resolver follows assignments through ordered equality classes.
Its finite support includes the class lookups, the variables inspected by its
resolvability guard, and the recursively inspected assignment values. Absent
lookups are dependencies too. The support conservatively records every member
of an inspected equality class, even if its first value stops the search.

Equality authority is retained separately: reusing an assignment certificate
requires the ordered classes to agree. Identical relation rows are one sufficient
condition; appending a previously stored edge is another. The result theorem
preserves the actual `resolveFull`, including fuel exhaustion and cycle rejection.
The same holds of `applyFull`, the application of bindings to an atom that the
HE evaluator performs: its support is the support of each variable occurrence.
It makes no claim about an interpreter, mutable C storage, or pointer lifetime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.BindingResolutionReadSupport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (vars)

open Mettapedia.Machines

/-- The assignment lookups that govern the resolvability scan of a value.
The scan tests the assignment of each variable itself, and only when that
variable's equality class is trivial; it never reads another class member. -/
def guardSupport (atom : Atom) : List String := vars atom

/-- Finite transitive support for the actual equality-aware recursive resolver.
Fuel bounds recursive discovery and visited classes stop dependency cycles.
The support may also inspect a value that the resolver's guard leaves unchanged. -/
def atomSupport (bindings : Bindings) : Nat → List String → Atom → List String
  | 0, _, _ => []
  | remaining + 1, visited, .var key =>
      let cls := bindings.eqClassOrdered key
      if cls.any visited.contains then []
      else cls ++ match cls.findSome? bindings.lookup with
        | none => []
        | some value =>
            guardSupport value ++
              atomSupport bindings remaining (cls ++ visited) value
  | remaining + 1, visited, .expression atoms =>
      atoms.flatMap (atomSupport bindings remaining visited)
  | _ + 1, _, _ => []

/-- The public entry checks class assignments even when recursive fuel is zero. -/
def support (bindings : Bindings) (key : String) (fuel : Nat) : List String :=
  bindings.eqClassOrdered key ++ atomSupport bindings fuel [] (.var key)

/-- Complete assignment values sampled at every supporting coordinate. -/
def reads (bindings : Bindings) (key : String) (fuel : Nat) :
    ReadOnlyQuery.Reads String (Option Atom) :=
  ReadOnlyQuery.samples bindings.lookup (support bindings key fuel)

private theorem classes_eq {first second : Bindings}
    (equalities : second.equalities = first.equalities) (key : String) :
    second.eqClassOrdered key = first.eqClassOrdered key := by
  simp only [Bindings.eqClassOrdered, Bindings.eqVarsInOrder, Bindings.eqClass,
    equalities]

private theorem representative_eq {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key)
    (key : String) :
    second.eqRepresentative key = first.eqRepresentative key := by
  simp only [Bindings.eqRepresentative, classes]

private theorem findSome_eq (first second : Bindings) (keys : List String)
    (agree : ∀ key ∈ keys, second.lookup key = first.lookup key) :
    keys.findSome? second.lookup = keys.findSome? first.lookup := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.findSome?_cons, agree key (by simp)]
      cases first.lookup key with
      | none => exact ih (fun key member => agree key (by simp [member]))
      | some value => rfl

private theorem vars_expression (atoms : List Atom) :
    vars (.expression atoms) = atoms.flatMap vars := by
  simp only [vars]
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp [vars.varsList, ih]

/-- Resolution cannot discover an isolated name that occurs neither in the
operand nor in any stored assignment value. Equality classes and assignment
values are checked separately, including absent class lookups. -/
theorem atomSupport_avoids (bindings : Bindings) (name : String)
    (classes : ∀ root, root ≠ name → name ∉ bindings.eqClassOrdered root)
    (values : ∀ key value, bindings.lookup key = some value → name ∉ vars value) :
    ∀ fuel visited atom, name ∉ vars atom →
      name ∉ atomSupport bindings fuel visited atom := by
  intro fuel
  induction fuel with
  | zero => intro visited atom absent; simp [atomSupport]
  | succ fuel ih =>
      intro visited atom absent
      cases atom with
      | symbol | grounded => simp [atomSupport]
      | expression atoms =>
          simp only [atomSupport, List.mem_flatMap]
          rintro ⟨child, member, occurs⟩
          apply ih visited child _ occurs
          intro childOccurs
          exact absent (by
            rw [vars_expression]
            exact List.mem_flatMap.mpr ⟨child, member, childOccurs⟩)
      | var root =>
          have different : root ≠ name := by simpa [vars, eq_comm] using absent
          simp only [atomSupport]
          split
          · simp
          · simp only [List.mem_append, not_or]
            refine ⟨classes root different, ?_⟩
            cases found : (bindings.eqClassOrdered root).findSome? bindings.lookup with
            | none => simp
            | some value =>
                obtain ⟨key, _member, lookup⟩ := List.exists_of_findSome?_eq_some found
                have valueAbsent := values key value lookup
                simp only [guardSupport, List.mem_append, not_or]
                exact ⟨valueAbsent,
                  ih (bindings.eqClassOrdered root ++ visited) value valueAbsent⟩

private theorem guardAux_eq {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key) :
    ∀ fuel atom,
      (∀ key ∈ vars atom, second.lookup key = first.lookup key) →
      second.hasResolvableVarAux fuel atom = first.hasResolvableVarAux fuel atom := by
  intro fuel
  induction fuel with
  | zero => intro atom agree; rfl
  | succ remaining ih =>
      intro atom agree
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | var key =>
          simp only [Bindings.hasResolvableVarAux, classes,
            Bindings.isBound, agree key (by simp [vars])]
      | expression atoms =>
          simp only [Bindings.hasResolvableVarAux]
          induction atoms with
          | nil => rfl
          | cons atom rest tail =>
              have headAgree : ∀ key ∈ vars atom,
                  second.lookup key = first.lookup key := by
                intro key member
                apply agree key
                simp only [vars_expression, List.mem_flatMap]
                exact ⟨atom, by simp, member⟩
              have tailAgree : ∀ key ∈ vars (.expression rest),
                  second.lookup key = first.lookup key := by
                intro key member
                apply agree key
                simp only [vars_expression, List.mem_flatMap] at member ⊢
                rcases member with ⟨child, contained, read⟩
                exact ⟨child, List.mem_cons_of_mem atom contained, read⟩
              simp only [List.any_cons, ih atom headAgree, tail tailAgree]

private theorem guard_eq {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key) (atom : Atom)
    (agree : ∀ key ∈ vars atom, second.lookup key = first.lookup key) :
    second.hasResolvableVar atom = first.hasResolvableVar atom := by
  unfold Bindings.hasResolvableVar
  exact guardAux_eq classes _ atom agree

/-- Agreement on transitive assignment reads preserves the actual recursive
resolution, including the original fuel and visited-path rejection. -/
theorem resolveAtomFullAux_eq_of_ordered_classes {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key) :
    ∀ fuel visited atom,
      (∀ key ∈ atomSupport first fuel visited atom,
        second.lookup key = first.lookup key) →
      second.resolveAtomFullAux fuel visited atom =
        first.resolveAtomFullAux fuel visited atom := by
  intro fuel
  induction fuel with
  | zero => intro visited atom agree; rfl
  | succ remaining ih =>
      intro visited atom agree
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | expression atoms =>
          simp only [Bindings.resolveAtomFullAux]
          have children : ∀ atom ∈ atoms,
              second.resolveAtomFullAux remaining visited atom =
                first.resolveAtomFullAux remaining visited atom := by
            intro atom member
            exact ih visited atom (fun key contained =>
              agree key (by
                simp only [atomSupport, List.mem_flatMap]
                exact ⟨atom, member, contained⟩))
          have mapped : atoms.mapM (second.resolveAtomFullAux remaining visited) =
              atoms.mapM (first.resolveAtomFullAux remaining visited) := by
            clear agree
            induction atoms with
            | nil => rfl
            | cons atom rest tail =>
                simp only [List.mapM_cons, children atom (by simp)]
                rw [tail (fun atom member => children atom (by simp [member]))]
          rw [mapped]
      | var root =>
          simp only [Bindings.resolveAtomFullAux, classes]
          by_cases visitedClass : (first.eqClassOrdered root).any visited.contains = true
          · simp only [visitedClass, ↓reduceIte]
          · have classAgree : ∀ key ∈ (first.eqClassOrdered root), second.lookup key = first.lookup key := by
              intro key member
              apply agree key
              simp only [atomSupport, visitedClass, Bool.false_eq_true, ↓reduceIte, List.mem_append]
              exact Or.inl member
            have found := findSome_eq first second (first.eqClassOrdered root) classAgree
            rw [found]
            cases valueFound : (first.eqClassOrdered root).findSome? first.lookup with
            | none => simp only [representative_eq classes]
            | some value =>
                have nextAgree : ∀ key ∈
                    atomSupport first remaining ((first.eqClassOrdered root) ++ visited) value,
                    second.lookup key = first.lookup key := by
                  intro key member
                  apply agree key
                  simp only [atomSupport, visitedClass, Bool.false_eq_true, ↓reduceIte, valueFound,
                    List.mem_append]
                  exact Or.inr (Or.inr member)
                have guardAgree : ∀ key ∈ guardSupport value,
                    second.lookup key = first.lookup key := by
                  intro key member
                  apply agree key
                  simp only [atomSupport, visitedClass, Bool.false_eq_true, ↓reduceIte, valueFound,
                    List.mem_append]
                  exact Or.inr (Or.inl member)
                have scanned := guard_eq classes value guardAgree
                have continued := ih ((first.eqClassOrdered root) ++ visited) value nextAgree
                cases value <;> simp only [scanned, continued,
                  representative_eq classes]

/-- Identical equality rows instantiate ordered-class agreement. -/
theorem resolveAtomFullAux_eq_of_support {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (fuel : Nat) (visited : List String) (atom : Atom)
    (agree : ∀ key ∈ atomSupport first fuel visited atom,
      second.lookup key = first.lookup key) :
    second.resolveAtomFullAux fuel visited atom = first.resolveAtomFullAux fuel visited atom :=
  resolveAtomFullAux_eq_of_ordered_classes (classes_eq equalities) fuel visited atom agree

/-- A valid read certificate licenses reuse of the public HE resolution.
The equality relations remain a separate governing authority. -/
theorem resolveFull_eq_of_ordered_classes {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key)
    (key : String) (fuel : Nat)
    (agree : ReadOnlyQuery.Agrees second.lookup (reads first key fuel)) :
    second.resolveFull key fuel = first.resolveFull key fuel := by
  have lookups := (ReadOnlyQuery.agrees_samples_iff first.lookup second.lookup
    (support first key fuel)).mp agree
  have classAgree : ∀ observed ∈ first.eqClassOrdered key,
      second.lookup observed = first.lookup observed :=
    fun observed member => lookups observed (List.mem_append_left _ member)
  have atomAgree : ∀ observed ∈ atomSupport first fuel [] (.var key),
      second.lookup observed = first.lookup observed :=
    fun observed member => lookups observed (List.mem_append_right _ member)
  simp only [Bindings.resolveFull, classes,
    findSome_eq first second _ classAgree,
    resolveAtomFullAux_eq_of_ordered_classes classes fuel [] (.var key) atomAgree]

/-- Exact retained equality rows give the original read-certificate interface. -/
theorem resolveFull_eq_of_reads {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (key : String) (fuel : Nat)
    (agree : ReadOnlyQuery.Agrees second.lookup (reads first key fuel)) :
    second.resolveFull key fuel = first.resolveFull key fuel :=
  resolveFull_eq_of_ordered_classes (classes_eq equalities) key fuel agree

theorem resolveFull_eq_of_checkReads {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (key : String) (fuel : Nat)
    (valid : ReadOnlyQuery.checkReads second.lookup (reads first key fuel) = true) :
    second.resolveFull key fuel = first.resolveFull key fuel :=
  resolveFull_eq_of_reads equalities key fuel ((ReadOnlyQuery.checkReads_iff _ _).mp valid)

/-- Assignment lookups read when bindings are applied to an atom: the support
of each variable occurrence, at the fuel the application gives it. -/
def applySupport (bindings : Bindings) : Nat → Atom → List String
  | 0, _ => []
  | remaining + 1, .var key => support bindings key remaining
  | remaining + 1, .expression atoms => atoms.flatMap (applySupport bindings remaining)
  | _ + 1, _ => []

/-- Complete assignment values sampled at every coordinate an application
reads. -/
def applyReads (bindings : Bindings) (atom : Atom) (fuel : Nat) :
    ReadOnlyQuery.Reads String (Option Atom) :=
  ReadOnlyQuery.samples bindings.lookup (applySupport bindings fuel atom)

/-- Agreement on the support of an application preserves the application,
including every variable left in place by an exhausted or rejected
resolution. -/
theorem applyFull_eq_of_ordered_classes {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key) :
    ∀ fuel atom,
      (∀ key ∈ applySupport first fuel atom, second.lookup key = first.lookup key) →
      second.applyFull atom fuel = first.applyFull atom fuel := by
  intro fuel
  induction fuel with
  | zero => intro atom agree; rfl
  | succ remaining ih =>
      intro atom agree
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | var key =>
          have resolved := resolveFull_eq_of_ordered_classes classes key remaining
            ((ReadOnlyQuery.agrees_samples_iff _ _ _).mpr agree)
          simp only [Bindings.applyFull, resolved]
      | expression atoms =>
          simp only [Bindings.applyFull]
          congr 1
          apply List.map_congr_left
          intro child member
          exact ih child (fun key contained => agree key (by
            simp only [applySupport, List.mem_flatMap]
            exact ⟨child, member, contained⟩))

/-- The original row-preserving interface follows from ordered-class agreement. -/
theorem applyFull_eq_of_support {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (fuel : Nat) (atom : Atom)
    (agree : ∀ key ∈ applySupport first fuel atom, second.lookup key = first.lookup key) :
    second.applyFull atom fuel = first.applyFull atom fuel :=
  applyFull_eq_of_ordered_classes (classes_eq equalities) fuel atom agree

/-- A valid read certificate licenses reuse of an application of bindings. -/
theorem applyFull_eq_of_reads {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (atom : Atom) (fuel : Nat)
    (agree : ReadOnlyQuery.Agrees second.lookup (applyReads first atom fuel)) :
    second.applyFull atom fuel = first.applyFull atom fuel :=
  applyFull_eq_of_support equalities fuel atom
    ((ReadOnlyQuery.agrees_samples_iff _ _ _).mp agree)

/-- A duplicate stored equality preserves the full resolver at every depth,
including cycle rejection and depth exhaustion. The stored record itself grows. -/
theorem resolveFull_addEquality_of_mem {bindings : Bindings} {left right : String}
    (stored : (left, right) ∈ bindings.equalities) (key : String) (fuel : Nat) :
    (bindings.addEquality left right).resolveFull key fuel = bindings.resolveFull key fuel := by
  apply resolveFull_eq_of_ordered_classes
    (EqualityClosure.eqClassOrdered_addEquality_of_mem stored) key fuel
  exact (ReadOnlyQuery.agrees_samples_iff _ _ _).mpr (fun _ _ => rfl)

/-- All variable occurrences in a future atom retain their joint readout after
an already-stored edge is appended. No name is renamed independently. -/
theorem applyFull_addEquality_of_mem {bindings : Bindings} {left right : String}
    (stored : (left, right) ∈ bindings.equalities) (atom : Atom) (fuel : Nat) :
    (bindings.addEquality left right).applyFull atom fuel = bindings.applyFull atom fuel :=
  applyFull_eq_of_ordered_classes
    (EqualityClosure.eqClassOrdered_addEquality_of_mem stored) fuel atom (fun _ _ => rfl)

private theorem lookup_map_of_key_preserved (transform : String × Atom → String × Atom)
    (changed key : String) (different : key ≠ changed)
    (keys : ∀ entry, (transform entry).1 = entry.1)
    (values : ∀ entry, entry.1 ≠ changed → (transform entry).2 = entry.2) :
    ∀ assignments : List (String × Atom),
      (assignments.map transform).lookup key = assignments.lookup key
  | [] => rfl
  | (name, old) :: rest => by
      have tail := lookup_map_of_key_preserved transform changed key different keys values rest
      have shape : transform (name, old) = (name, (transform (name, old)).2) :=
        Prod.ext (keys _) rfl
      rw [List.map_cons, shape, List.lookup_cons, List.lookup_cons, tail]
      cases hit : key == name with
      | false => rfl
      | true =>
          have equal : key = name := by simpa using hit
          simp only [values (name, old) (equal ▸ different)]

/-- An assignment changes the lookup of its own variable only, whether that
variable was unassigned or already assigned. -/
theorem lookup_assign_of_ne (bindings : Bindings) (changed : String) (value : Atom)
    (key : String) (different : key ≠ changed) :
    (bindings.assign changed value).lookup key = bindings.lookup key := by
  by_cases bound : bindings.isBound changed = true
  · simp only [Bindings.assign, Bindings.lookup, bound, if_true]
    refine lookup_map_of_key_preserved _ changed key different ?_ ?_ bindings.assignments
    · rintro ⟨name, old⟩
      by_cases same : (name == changed) = true <;> simp [same]
    · rintro ⟨name, old⟩ other
      have distinct : (name == changed) = false := by simpa using other
      simp [distinct]
  · simp only [Bindings.assign, Bindings.lookup, bound, Bool.false_eq_true, if_false,
      List.lookup_append]
    cases bindings.assignments.lookup key with
    | some found => rfl
    | none => simp [different]

/-- An assignment outside the transitive support preserves the public
resolution, whether it binds a fresh variable or rebinds an assigned one. -/
theorem resolveFull_assign_unrelated (bindings : Bindings)
    (root changed : String) (value : Atom) (fuel : Nat)
    (outside : changed ∉ support bindings root fuel) :
    (bindings.assign changed value).resolveFull root fuel =
      bindings.resolveFull root fuel := by
  apply resolveFull_eq_of_reads (first := bindings)
    (second := bindings.assign changed value) rfl root fuel
  apply (ReadOnlyQuery.agrees_samples_iff _ _ _).mpr
  intro key member
  exact lookup_assign_of_ne bindings changed value key fun same => outside (same ▸ member)

/-- An assignment outside the support of an application preserves the
application. -/
theorem applyFull_assign_unrelated (bindings : Bindings)
    (atom : Atom) (changed : String) (value : Atom) (fuel : Nat)
    (outside : changed ∉ applySupport bindings fuel atom) :
    (bindings.assign changed value).applyFull atom fuel = bindings.applyFull atom fuel :=
  applyFull_eq_of_support (first := bindings) (second := bindings.assign changed value) rfl
    fuel atom fun key member =>
      lookup_assign_of_ne bindings changed value key fun same => outside (same ▸ member)

/-- Array-trace stability transports the certificate into the real HE
resolver when the two assignment lookup maps realize the trace endpoints.
Equality relations are a separate retained authority. -/
theorem resolveFull_eq_of_untouched_trace {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (initial : String → Option Atom)
    (writes : Nat → Option
      (Mettapedia.Logic.ArrayInvariants.UpdateTrace.Write String (Option Atom)))
    (start finish : Nat)
    (firstLookup : first.lookup =
      Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes start)
    (secondLookup : second.lookup =
      Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes finish)
    (root : String) (fuel : Nat) (ordered : start ≤ finish)
    (untouched : ∀ key ∈ support first root fuel, ∀ i,
      start ≤ i → i < finish →
        ¬ Mettapedia.Logic.ArrayInvariants.UpdateTrace.Updates writes i key) :
    second.resolveFull root fuel = first.resolveFull root fuel := by
  apply resolveFull_eq_of_reads equalities
  have valid : ReadOnlyQuery.Agrees
      (Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes start)
      (reads first root fuel) := by
    rw [← firstLookup]
    exact (ReadOnlyQuery.agrees_samples_iff _ _ _).mpr (fun _ _ => rfl)
  have retained := ReadOnlyQuery.trace_preserves_reads initial writes start finish
    (reads first root fuel) valid ordered (by
      intro observed member
      simp only [reads, ReadOnlyQuery.samples, List.mem_map] at member
      rcases member with ⟨key, contained, rfl⟩
      exact untouched key contained)
  rw [secondLookup]
  exact retained


/-- Structural depth bounds may differ between two records. Agreement of the
actual ordered classes and lookups still preserves their complete readout. -/
theorem complete_applyFull_eq_of_ordered_classes {first second : Bindings}
    (classes : ∀ key, second.eqClassOrdered key = first.eqClassOrdered key)
    (lookups : ∀ key, second.lookup key = first.lookup key) (atom : Atom) :
    second.applyFull atom (second.resolutionFuel atom) =
      first.applyFull atom (first.resolutionFuel atom) := by
  let firstDepth := first.resolutionFuel atom
  let secondDepth := second.resolutionFuel atom
  have firstStable := first.applyFullCovered_stable atom firstDepth secondDepth
    (first.applyFullCovered_resolutionFuel atom)
  have secondStable := second.applyFullCovered_stable atom secondDepth firstDepth
    (second.applyFullCovered_resolutionFuel atom)
  have sameDepth := applyFull_eq_of_ordered_classes classes (firstDepth + secondDepth) atom
    (fun key _ => lookups key)
  rw [Nat.add_comm secondDepth] at secondStable
  exact secondStable.symm.trans (sameDepth.trans firstStable)


namespace Controls

def openAlias : Bindings :=
  { assignments := [("x", .var "y")], equalities := [] }

def firstBranch : Bindings := openAlias.assign "y" (.symbol "A")

/-- Restoring the open checkpoint and writing the other branch's value. -/
def secondBranch : Bindings := openAlias.assign "y" (.symbol "B")

theorem transitive_read_resolves :
    firstBranch.resolveFull "x" 6 = some (.symbol "A") ∧
      "y" ∈ support firstBranch "x" 6 := by
  decide

theorem unrelated_assignment_preserves :
    (firstBranch.assign "z" (.symbol "Other")).resolveFull "x" 6 =
      firstBranch.resolveFull "x" 6 := by
  exact resolveFull_assign_unrelated firstBranch "x" "z" (.symbol "Other") 6 (by decide)

/-- Rebinding an unrelated variable that already has a value preserves the
resolution too. -/
theorem unrelated_rebinding_preserves :
    ((firstBranch.assign "z" (.symbol "Other")).assign "z" (.symbol "Again")).resolveFull "x" 6 =
      firstBranch.resolveFull "x" 6 := by
  rw [resolveFull_assign_unrelated _ "x" "z" (.symbol "Again") 6 (by decide)]
  exact unrelated_assignment_preserves

/-- Root-cell agreement misses the assignment actually followed by the resolver. -/
theorem root_only_certificate_is_insufficient :
    ReadOnlyQuery.checkReads secondBranch.lookup
        (ReadOnlyQuery.samples firstBranch.lookup ["x"]) = true ∧
      secondBranch.resolveFull "x" 6 ≠ firstBranch.resolveFull "x" 6 := by
  decide

/-- The unbound target is observed even when the guard skips recursion. -/
theorem formerly_absent_assignment_invalidates :
    openAlias.lookup "y" = none ∧
      "y" ∈ support openAlias "x" 6 ∧
      ReadOnlyQuery.checkReads firstBranch.lookup (reads openAlias "x" 6) = false ∧
      firstBranch.resolveFull "x" 6 ≠ openAlias.resolveFull "x" 6 := by
  decide

theorem restored_alias_rebinding_invalidates :
    firstBranch.lookup "x" = secondBranch.lookup "x" ∧
      ReadOnlyQuery.checkReads secondBranch.lookup (reads firstBranch "x" 6) = false ∧
      firstBranch.resolveFull "x" 6 = some (.symbol "A") ∧
      secondBranch.resolveFull "x" 6 = some (.symbol "B") := by
  decide

def equalitySource : Bindings :=
  { assignments := [("z", .symbol "B")], equalities := [] }

/-- Assignment reads alone do not protect a changed equality-class authority. -/
theorem equality_authority_must_be_retained :
    ReadOnlyQuery.checkReads (equalitySource.addEquality "z" "x").lookup
        (reads equalitySource "x" 6) = true ∧
      (equalitySource.addEquality "z" "x").resolveFull "x" 6 = some (.symbol "B") ∧
      equalitySource.resolveFull "x" 6 = none := by
  decide

def equalityAlias : Bindings := firstBranch.addEquality "z" "x"

/-- Reusing the class reads preserves resolution through the equality alias. -/
theorem equality_aware_resolution_preserves :
    equalityAlias.resolveFull "z" 6 = some (.symbol "A") ∧
      (equalityAlias.assign "other" (.symbol "Other")).resolveFull "z" 6 =
        equalityAlias.resolveFull "z" 6 := by
  constructor
  · decide
  · exact resolveFull_assign_unrelated equalityAlias "z" "other" (.symbol "Other") 6
      (by decide)

def compound : Bindings :=
  { assignments := [("x", .expression [.symbol "Pair", .var "y", .var "y"]),
      ("y", .symbol "A")], equalities := [] }

theorem correlated_compound_resolution :
    compound.resolveFull "x" 6 =
      some (.expression [.symbol "Pair", .symbol "A", .symbol "A"]) ∧
      (compound.assign "z" (.symbol "Other")).resolveFull "x" 6 =
        compound.resolveFull "x" 6 := by
  constructor
  · decide
  · exact resolveFull_assign_unrelated compound "x" "z" (.symbol "Other") 6
      (by decide)

def cyclic : Bindings :=
  { assignments := [("x", .var "y"), ("y", .var "x")], equalities := [] }

theorem rejection_is_preserved :
    cyclic.resolveFull "x" 6 = none ∧
      (cyclic.assign "z" (.symbol "Other")).resolveFull "x" 6 = none ∧
      firstBranch.resolveFull "x" 0 = none := by
  decide

def pairOfAlias : Atom := .expression [.symbol "Pair", .var "x", .var "w"]

/-- An application reads the support of each of its variables, including a
variable with no assignment. -/
theorem application_reads_each_variable :
    firstBranch.applyFull pairOfAlias 7 =
        .expression [.symbol "Pair", .symbol "A", .var "w"] ∧
      "y" ∈ applySupport firstBranch 7 pairOfAlias ∧
      "w" ∈ applySupport firstBranch 7 pairOfAlias := by
  decide

theorem unrelated_assignment_preserves_application :
    (firstBranch.assign "z" (.symbol "Other")).applyFull pairOfAlias 7 =
      firstBranch.applyFull pairOfAlias 7 :=
  applyFull_assign_unrelated firstBranch pairOfAlias "z" (.symbol "Other") 7 (by decide)

/-- Binding a variable the application left in place invalidates its
certificate, and so does rebinding the target of an alias. -/
theorem changed_dependency_invalidates_application :
    ReadOnlyQuery.checkReads (firstBranch.assign "w" (.symbol "C")).lookup
        (applyReads firstBranch pairOfAlias 7) = false ∧
      (firstBranch.assign "w" (.symbol "C")).applyFull pairOfAlias 7 ≠
        firstBranch.applyFull pairOfAlias 7 ∧
      ReadOnlyQuery.checkReads secondBranch.lookup
        (applyReads firstBranch pairOfAlias 7) = false ∧
      secondBranch.applyFull pairOfAlias 7 ≠ firstBranch.applyFull pairOfAlias 7 := by
  decide

/-- Reconciliation may repeat a stored relation without changing the joint
readout or its shared residual name; the actual record still retains both edges. -/
theorem duplicate_edge_preserves_open_compound :
    let source : Bindings := ⟨[("value", .expression [.symbol "Pair", .var "b", .var "b"])],
      [("a", "b")]⟩
    let changed := source.addEquality "a" "b"
    (∀ fuel, changed.applyFull (.var "value") fuel = source.applyFull (.var "value") fuel) ∧
      changed.applyFull (.var "value") 12 = .expression [.symbol "Pair", .var "a", .var "a"] ∧
      changed.equalities.length = 2 := by
  refine ⟨fun fuel => applyFull_addEquality_of_mem (by decide) _ fuel, ?_, rfl⟩
  decide +kernel

/-- A repeated edge preserves rejection as well; it cannot repair a cyclic
assignment dependency. -/
theorem duplicate_edge_preserves_cyclic_refusal :
    let source : Bindings := ⟨[("a", .expression [.symbol "F", .var "b"])], [("a", "b")]⟩
    (source.addEquality "a" "b").resolveFull "a" 12 = none ∧
      source.resolveFull "a" 12 = none := by
  decide +kernel

/-- Mere equality-edge permutation is too weak for string-visible readout:
changing first appearance changes the common residual variable. -/
theorem edge_permutation_changes_joint_residual :
    let first : Bindings := ⟨[], [("a", "b"), ("c", "b")]⟩
    let second : Bindings := ⟨[], [("c", "b"), ("a", "b")]⟩
    List.Perm first.equalities second.equalities ∧
      first.applyFull (.expression [.var "b", .var "b"]) 6 =
        .expression [.var "a", .var "a"] ∧
      second.applyFull (.expression [.var "b", .var "b"]) 6 =
        .expression [.var "c", .var "c"] := by
  refine ⟨List.Perm.swap _ _ [], ?_, ?_⟩ <;> decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.HE.BindingResolutionReadSupport

/-! ## Complete readout at the resolution depth -/

namespace Mettapedia.Languages.MeTTa.HE.Bindings
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Two covered depths select the same complete equality-aware readout. -/
theorem applyFull_resolutionFuel_eq_of_covered (bindings : Bindings) (atom : Atom) (depth : Nat)
    (covered : bindings.applyFullCovered atom depth=true) :
    bindings.applyFull atom (bindings.resolutionFuel atom)=bindings.applyFull atom depth := by
  have first:=bindings.applyFullCovered_stable atom depth (bindings.resolutionFuel atom) covered
  have second:=bindings.applyFullCovered_stable atom (bindings.resolutionFuel atom) depth
    (bindings.applyFullCovered_resolutionFuel atom)
  rw [Nat.add_comm depth] at first
  exact second.symm.trans first

/-- The complete readout of a whole retained tuple is the tuple of complete
component readouts, despite their different structural depth bounds. -/
theorem applyFull_resolutionFuel_expression (bindings : Bindings) (atoms : List Atom) :
    bindings.applyFull (.expression atoms) (bindings.resolutionFuel (.expression atoms))=
      .expression (atoms.map fun atom=>bindings.applyFull atom (bindings.resolutionFuel atom)) := by
  let rest:=bindings.boundVars.toFinset.card*(bindings.resolutionValueDepth+1)+
    atomScanFuel.atomListScanFuel atoms+3
  have depth : bindings.resolutionFuel (.expression atoms)=rest+1 := by
    simp only [resolutionFuel,atomScanFuel,rest]
    omega
  rw [depth,Bindings.applyFull]
  congr 1
  apply List.map_congr_left
  intro atom member
  apply (bindings.applyFull_resolutionFuel_eq_of_covered atom rest ?_).symm
  apply bindings.queryRank_covers
  have smaller:=atomScanFuel_mem atoms atom member
  simp only [atomScanFuel] at smaller
  simp only [queryRank,rest]
  omega

end Mettapedia.Languages.MeTTa.HE.Bindings
