import Mettapedia.Logic.LP.Core

/-!
# Standardizing Logic-Program Clauses Apart

This module supplies the variable-renaming substrate required by executable
SLD resolution.  A source clause is copied into a typed activation scope before
unification; two different scopes therefore cannot share a variable, even when
the source clauses use the same variable names.

The construction is deliberately below any evaluator or language frontend:
it operates directly on the shared `Logic.LP` terms, atoms, and clauses.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed., 1987
- Apt, *From Logic Programming to Prolog*, 1997
- ISO/IEC 13211-1:1995, *Information technology — Programming languages — Prolog*
-/

namespace Mettapedia.Logic.LP

/-! ## Rebinding the variable carrier -/

/-- Replace only the variable carrier of a signature.  All program symbols and
their arities remain definitionally unchanged. -/
@[reducible] def LPSignature.withVars (σ : LPSignature) (V : Type*) : LPSignature where
  constants := σ.constants
  vars := V
  relationSymbols := σ.relationSymbols
  relationArity := σ.relationArity
  functionSymbols := σ.functionSymbols
  functionArity := σ.functionArity

/-- Rename every variable in a term, possibly into a different variable
carrier.  Constants, function symbols, and argument positions are preserved. -/
def Term.renameVars {σ : LPSignature} {V : Type*} (ρ : σ.vars → V) :
    Term σ → Term (σ.withVars V)
  | .var v => .var (ρ v)
  | .const c => .const c
  | .app f ts => .app f (fun i => (ts i).renameVars ρ)

/-- Rename every variable in an atom. -/
def Atom.renameVars {σ : LPSignature} {V : Type*} (ρ : σ.vars → V)
    (a : Atom σ) : Atom (σ.withVars V) where
  symbol := a.symbol
  args := fun i => (a.args i).renameVars ρ

/-- Rename every variable in a clause with one shared renaming.  Using one
renaming for the head and body preserves repeated-variable sharing. -/
def Clause.renameVars {σ : LPSignature} {V : Type*} (ρ : σ.vars → V)
    (c : Clause σ) : Clause (σ.withVars V) where
  head := c.head.renameVars ρ
  body := c.body.map (·.renameVars ρ)

/-- Rename every clause in a program. -/
def Program.renameVars {σ : LPSignature} {V : Type*} (ρ : σ.vars → V)
    (prog : Program σ) : Program (σ.withVars V) :=
  prog.map (·.renameVars ρ)

@[simp] theorem Term.renameVars_var {σ : LPSignature} {V : Type*}
    (ρ : σ.vars → V) (v : σ.vars) :
    (Term.var v).renameVars ρ = .var (ρ v) := rfl

@[simp] theorem Term.renameVars_const {σ : LPSignature} {V : Type*}
    (ρ : σ.vars → V) (c : σ.constants) :
    (Term.const c).renameVars ρ = .const c := rfl

@[simp] theorem Term.renameVars_app {σ : LPSignature} {V : Type*}
    (ρ : σ.vars → V) (f : σ.functionSymbols)
    (ts : Fin (σ.functionArity f) → Term σ) :
    (Term.app f ts).renameVars ρ = .app f (fun i => (ts i).renameVars ρ) := rfl

/-! ## Typed activation scopes -/

/-- A runtime logic variable is its source-level identity paired with the
activation that copied it. -/
@[ext]
structure ScopedVar (V : Type*) where
  /-- Identity assigned to the clause or query activation.  The resolver must
  allocate distinct identities to simultaneously live activations. -/
  scope : Nat
  /-- Variable identity in the source clause or query. -/
  name : V
deriving DecidableEq

/-- The runtime signature used by standardized-apart resolution. -/
abbrev LPSignature.scoped (σ : LPSignature) : LPSignature :=
  σ.withVars (ScopedVar σ.vars)

/-- Inject a source variable into one activation scope. -/
def ScopedVar.at (scope : Nat) (name : V) : ScopedVar V := ⟨scope, name⟩

/-- Copy a source term into one activation scope. -/
def Term.atScope {σ : LPSignature} (scope : Nat) (t : Term σ) : Term σ.scoped :=
  t.renameVars (ScopedVar.at scope)

/-- Copy a source atom into one activation scope. -/
def Atom.atScope {σ : LPSignature} (scope : Nat) (a : Atom σ) : Atom σ.scoped :=
  a.renameVars (ScopedVar.at scope)

/-- Copy a source clause into one activation scope. -/
def Clause.atScope {σ : LPSignature} (scope : Nat) (c : Clause σ) : Clause σ.scoped :=
  c.renameVars (ScopedVar.at scope)

/-- Copy a source query into one activation scope. -/
def queryAtScope {σ : LPSignature} (scope : Nat) (goals : List (Atom σ)) :
    List (Atom σ.scoped) :=
  goals.map (·.atScope scope)

@[simp] theorem ScopedVar.at_scope (scope : Nat) (name : V) :
    (ScopedVar.at scope name).scope = scope := rfl

@[simp] theorem ScopedVar.at_name (scope : Nat) (name : V) :
    (ScopedVar.at scope name).name = name := rfl

theorem ScopedVar.at_injective (scope : Nat) :
    Function.Injective (ScopedVar.at (V := V) scope) := by
  intro left right h
  exact congrArg ScopedVar.name h

/-- Different activation scopes have disjoint variable images. -/
theorem ScopedVar.at_ne_at_of_scope_ne {leftScope rightScope : Nat}
    (hScope : leftScope ≠ rightScope) (left right : V) :
    ScopedVar.at leftScope left ≠ ScopedVar.at rightScope right := by
  intro h
  exact hScope (congrArg ScopedVar.scope h)

/-! ## Every copied variable records its activation -/

theorem Term.mem_freeVars_renameVars {σ : LPSignature} {V : Type*}
    [DecidableEq σ.vars] [DecidableEq V]
    (ρ : σ.vars → V) (t : Term σ) (v : V) :
    v ∈ (t.renameVars ρ).freeVars ↔ ∃ source ∈ t.freeVars, ρ source = v := by
  induction t with
  | var source => simp [Term.freeVars, eq_comm]
  | const c => simp [Term.renameVars, Term.freeVars]
  | app f ts ih =>
      simp only [Term.renameVars, Term.freeVars, Finset.mem_biUnion,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hv⟩
        obtain ⟨source, hsource, rfl⟩ := (ih i).mp hv
        exact ⟨source, ⟨i, hsource⟩, rfl⟩
      · rintro ⟨source, ⟨i, hsource⟩, rfl⟩
        exact ⟨i, (ih i).mpr ⟨source, hsource, rfl⟩⟩

/-- Every free variable of a scoped term belongs to the requested activation. -/
theorem Term.scope_eq_of_mem_freeVars_atScope {σ : LPSignature}
    [DecidableEq σ.vars] (scope : Nat) (t : Term σ) (v : ScopedVar σ.vars)
    (hv : v ∈ (t.atScope scope).freeVars) :
    v.scope = scope := by
  obtain ⟨source, _, hsource⟩ :=
    (Term.mem_freeVars_renameVars (ScopedVar.at scope) t v).mp hv
  rw [← hsource]
  rfl

/-- Every free variable of a scoped atom belongs to the requested activation. -/
theorem Atom.scope_eq_of_mem_freeVars_atScope {σ : LPSignature}
    [DecidableEq σ.vars] (scope : Nat) (a : Atom σ) (v : ScopedVar σ.vars)
    (hv : v ∈ (a.atScope scope).freeVars) :
    v.scope = scope := by
  simp only [Atom.atScope, Atom.renameVars, Atom.freeVars,
    Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
  obtain ⟨i, hi⟩ := hv
  exact Term.scope_eq_of_mem_freeVars_atScope scope (a.args i) v hi

private theorem Atom.mem_foldl_freeVars_iff {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (init : Finset σ.vars) (atoms : List (Atom σ)) :
    v ∈ atoms.foldl (fun acc atom => acc ∪ atom.freeVars) init ↔
      v ∈ init ∨ ∃ atom ∈ atoms, v ∈ atom.freeVars := by
  induction atoms generalizing init with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.foldl_cons, ih, Finset.mem_union]
      aesop

theorem Atom.mem_freeVarsOfList_iff {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (atoms : List (Atom σ)) :
    v ∈ Atom.freeVarsOfList atoms ↔ ∃ atom ∈ atoms, v ∈ atom.freeVars := by
  rw [Atom.freeVarsOfList, Atom.mem_foldl_freeVars_iff]
  simp

/-- Every free variable of a scoped clause belongs to its activation. -/
theorem Clause.scope_eq_of_mem_freeVars_atScope {σ : LPSignature}
    [DecidableEq σ.vars] (scope : Nat) (clause : Clause σ)
    (v : ScopedVar σ.vars) (hv : v ∈ (clause.atScope scope).freeVars) :
    v.scope = scope := by
  rcases Finset.mem_union.mp hv with hhead | hbody
  · exact Atom.scope_eq_of_mem_freeVars_atScope scope clause.head v hhead
  · rw [Atom.mem_freeVarsOfList_iff] at hbody
    obtain ⟨atom, hatom, hv⟩ := hbody
    simp only [Clause.atScope, Clause.renameVars, List.mem_map] at hatom
    obtain ⟨source, hsource, rfl⟩ := hatom
    exact Atom.scope_eq_of_mem_freeVars_atScope scope source v hv

/-- Copies made for different activations have disjoint free-variable sets.
This is the core standardization-apart property. -/
theorem Clause.freeVars_atScope_disjoint {σ : LPSignature}
    [DecidableEq σ.vars] (left right : Clause σ) {leftScope rightScope : Nat}
    (hScope : leftScope ≠ rightScope) :
    Disjoint (left.atScope leftScope).freeVars (right.atScope rightScope).freeVars := by
  rw [Finset.disjoint_left]
  intro v hleft hright
  have hl := Clause.scope_eq_of_mem_freeVars_atScope leftScope left v hleft
  have hr := Clause.scope_eq_of_mem_freeVars_atScope rightScope right v hright
  exact hScope (hl.symm.trans hr)

/-! ## Non-degenerate regression witnesses -/

/-- Reusing the same source variable in two activations produces distinct runtime
variables.  This is the minimal counterexample to unscoped clause reuse. -/
theorem same_source_variable_distinct_across_scopes (name : V) {left right : Nat}
    (h : left ≠ right) :
    ScopedVar.at left name ≠ ScopedVar.at right name :=
  ScopedVar.at_ne_at_of_scope_ne h name name

end Mettapedia.Logic.LP
