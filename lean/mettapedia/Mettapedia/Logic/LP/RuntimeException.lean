import Mettapedia.Logic.LP.RuntimeFiniteReadback
import Mettapedia.Logic.LP.RuntimeMaterialize

/-!
# Durable finite exception terms for the canonical runtime

SWI-Prolog duplicates a thrown term before unwinding so rollback cannot leave
the exception pointing into reclaimed stack storage.  The canonical Lean
runtime uses the same separation: capture reads the current finite heap graph
into an immutable `Term`; installation freshens every surviving variable above
the live activation supply and materializes it back into the restored heap.

Rational exception graphs are reported by finite readback and remain an
explicit later boundary.  They are never truncated or mistaken for finite
terms.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeException

open RuntimeTerm RuntimeMaterialize RuntimeReadback

/-- An exception payload detached from the mutable heap that produced it. -/
structure Packet (σ : LPSignature) where
  term : Term σ.scoped

/-- Capture the throw-time instantiation of one heap root. -/
def capture {σ : LPSignature} (heap : Heap σ.scoped) (root : Addr) :
    Except ReadbackError (Packet σ) :=
  Packet.mk <$> RuntimeReadback.Heap.readTerm heap root

/-- The first scope strictly above every variable scope in a finite term. -/
def scopeCeiling {σ : LPSignature} : Term σ.scoped → Nat
  | .var identity => identity.scope + 1
  | .const _ => 0
  | .app symbol arguments =>
      ∑ index : Fin (σ.functionArity symbol),
        scopeCeiling (arguments index)

/-- Rename one captured variable into a fresh interval beginning at `base`.
The old scope remains part of the new identity, so variables from distinct
activations cannot collapse merely because their source names agree. -/
def freshIdentity {σ : LPSignature} (base : Nat)
    (identity : ScopedVar σ.vars) :
    ScopedVar σ.vars := {
  scope := base + identity.scope
  name := identity.name
}

@[simp]
theorem freshIdentity_scope {σ : LPSignature} (base : Nat)
    (identity : ScopedVar σ.vars) :
    (freshIdentity base identity).scope = base + identity.scope := rfl

@[simp]
theorem freshIdentity_name {σ : LPSignature} (base : Nat)
    (identity : ScopedVar σ.vars) :
    (freshIdentity base identity).name = identity.name := rfl

theorem freshIdentity_injective {σ : LPSignature} (base : Nat) :
    Function.Injective (freshIdentity (σ := σ) base) := by
  intro left right equal
  apply ScopedVar.ext
  · simpa [freshIdentity] using congrArg ScopedVar.scope equal
  · simpa [freshIdentity] using congrArg ScopedVar.name equal

/-- A captured term freshened relative to the persistent activation supply. -/
def freshenTerm {σ : LPSignature} (base : Nat) :
    Term σ.scoped → Term σ.scoped
  | .var identity => .var (freshIdentity base identity)
  | .const symbol => .const symbol
  | .app symbol arguments =>
      .app symbol fun index => freshenTerm base (arguments index)

/-- `scopeCeiling` is strictly above every variable scope in the captured
finite term. -/
theorem scope_lt_scopeCeiling {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (term : Term σ.scoped) (identity : ScopedVar σ.vars)
    (hMem : identity ∈ term.freeVars) :
    identity.scope < scopeCeiling term := by
  induction term with
  | var source =>
      rw [Term.freeVars, Finset.mem_singleton] at hMem
      subst identity
      exact Nat.lt_succ_self source.scope
  | const symbol => simp [Term.freeVars] at hMem
  | app symbol arguments inductionHypotheses =>
      simp only [Term.freeVars, Finset.mem_biUnion,
        Finset.mem_univ, true_and] at hMem
      obtain ⟨index, hChild⟩ := hMem
      have hLe : scopeCeiling (arguments index) ≤
          ∑ child, scopeCeiling (arguments child) := by
        simpa using (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun child => scopeCeiling (arguments child))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ index))
      exact lt_of_lt_of_le (inductionHypotheses index hChild)
        (by simpa [scopeCeiling] using hLe)

/-- Freshened packet variables occupy the half-open interval reserved above
the current persistent scope supply. -/
theorem freshenTerm_scope_range {σ : LPSignature}
    [DecidableEq σ.scoped.vars]
    (base : Nat) (term : Term σ.scoped) (identity : ScopedVar σ.vars)
    (hMem : identity ∈ (freshenTerm base term).freeVars) :
    base ≤ identity.scope ∧ identity.scope < base + scopeCeiling term := by
  induction term with
  | var source =>
      have hEq : identity = freshIdentity base source := by
        simpa [freshenTerm, Term.freeVars] using
          Finset.mem_singleton.mp hMem
      subst hEq
      simp [freshIdentity, scopeCeiling]
  | const symbol => simp [freshenTerm, Term.freeVars] at hMem
  | app symbol arguments inductionHypotheses =>
      simp only [freshenTerm, Term.freeVars, Finset.mem_biUnion,
        Finset.mem_univ, true_and] at hMem
      obtain ⟨index, hChild⟩ := hMem
      obtain ⟨hBase, hUpper⟩ := inductionHypotheses index hChild
      have hLe : scopeCeiling (arguments index) ≤
          ∑ child, scopeCeiling (arguments child) := by
        simpa using (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun child => scopeCeiling (arguments child))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ index))
      exact ⟨hBase, lt_of_lt_of_le hUpper
        (Nat.add_le_add_left (by simpa [scopeCeiling] using hLe) base)⟩

/-- A captured term freshened relative to the persistent activation supply. -/
def Packet.freshTerm (packet : Packet σ) (base : Nat) : Term σ.scoped :=
  freshenTerm base packet.term

/-- Checked result of installing one detached exception packet. -/
structure Installed (σ : LPSignature) where
  memory : Memory σ.scoped
  root : Addr
  nextScope : Nat

/-- Materialize a detached exception into restored memory with fresh variable
identities.  The caller threads `nextScope` persistently across backtracking. -/
def Packet.install [DecidableEq σ.scoped.vars] (packet : Packet σ)
    (memory : Memory σ.scoped) (nextScope : Nat) :
    Except MemoryError (Installed σ) := do
  let result ← materializeTerm memory (packet.freshTerm nextScope)
  pure {
    memory := result.memory
    root := result.root
    nextScope := nextScope + scopeCeiling packet.term
  }

theorem Packet.install_nextScope_mono [DecidableEq σ.scoped.vars]
    {packet : Packet σ} {memory : Memory σ.scoped} {nextScope : Nat}
    {installed : Installed σ}
    (hInstall : packet.install memory nextScope = .ok installed) :
    nextScope ≤ installed.nextScope := by
  simp only [Packet.install] at hInstall
  cases hResult : materializeTerm memory (packet.freshTerm nextScope) with
  | error error => simp [hResult] at hInstall
  | ok result =>
    simp [hResult] at hInstall
    cases hInstall
    exact Nat.le_add_right nextScope (scopeCeiling packet.term)

theorem Packet.install_trail_exact [DecidableEq σ.scoped.vars]
    {packet : Packet σ} {memory : Memory σ.scoped} {nextScope : Nat}
    {installed : Installed σ}
    (hInstall : packet.install memory nextScope = .ok installed) :
    installed.memory.trail = memory.trail := by
  simp only [Packet.install] at hInstall
  cases hResult : materializeTerm memory (packet.freshTerm nextScope) with
  | error error => simp [hResult] at hInstall
  | ok result =>
    simp [hResult] at hInstall
    cases hInstall
    exact materializeTerm_trail_exact hResult

end RuntimeException
end Mettapedia.Logic.LP
