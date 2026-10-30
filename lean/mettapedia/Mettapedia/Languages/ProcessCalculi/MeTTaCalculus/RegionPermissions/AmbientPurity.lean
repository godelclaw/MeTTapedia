import Mathlib.Tactic
import Mettapedia.Logic.LP.FiniteDependencyClosure

/-!
# An effect gate kept as an ambient flag: what it guarantees, and what each entry point must keep

The weights evaluator decides whether a call may have an effect from its dynamic context. Each
running computation has a **driver**; drivers are linked to the driver whose authority they borrow;
each driver carries a `pure` flag. An effectful call is refused when some driver on the chain is
pure. Entry points (resumption of a retained task, a forced shared row, a worker job, a host
callback) **install** a stored flag on the driver they run under, replacing its flag for the
duration, and may start a new chain.

This module models that gate on a chain of flags, current driver first.

* **The gate is sound relative to an invariant** (`gate_sound`): if every pure caller in the
  computation's *logical* ancestry is matched by some pure driver on the *physical* chain
  (`Covers`), an effect admitted by the gate has no pure logical caller.
* **Installing a flag can create authority** (`install_creates_authority`): a chain refused by the
  gate is admitted after one entry point installs `false` on its only pure driver.
* **A resumption on a fresh chain loses its caller's prohibition** unless its stored flag carries
  it (`fresh_chain_needs_stored_flag`): the physical chain is the stored flag alone, while the
  logical caller is pure.

So the gate's soundness is not local to the call site: it is a global invariant that every place
which installs or copies a flag must keep (`Covers` after the entry). Capabilities make the same
guarantee local: a computation that was never given an effect capability cannot perform the effect,
wherever and whenever it runs (`InteractionTypes.Facets`, `AuthorityRun.authority_mono`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.AmbientPurity

/-- **The gate**: an effectful call runs only when no driver on the chain is pure. -/
def admits (chain : List Bool) (effectful : Bool) : Bool :=
  !effectful || chain.all (fun pure => !pure)

/-- The physical chain covers the logical ancestry when a pure logical caller implies a pure
driver on the chain. -/
def Covers (physical logical : List Bool) : Prop := logical.any id = true → physical.any id = true

/-- An entry point installs a stored flag on the current driver. -/
def install (stored : Bool) : List Bool → List Bool
  | [] => [stored]
  | _ :: rest => stored :: rest

theorem admits_effect_iff (chain : List Bool) : admits chain true = true ↔ chain.any id = false := by
  induction chain with
  | nil => simp [admits]
  | cons p rest ih =>
      cases p <;> simp_all [admits]

/-- **The gate is sound relative to the cover invariant.** -/
theorem gate_sound {physical logical : List Bool} (covers : Covers physical logical)
    (admitted : admits physical true = true) : logical.any id = false := by
  rw [admits_effect_iff] at admitted
  cases h : logical.any id with
  | false => rfl
  | true => rw [covers h] at admitted; exact absurd admitted (by decide)

/-- **Installing a flag can create authority**: the chain `[true]` refuses an effect; after an
entry point installs `false` on it, the same chain admits it. -/
theorem install_creates_authority :
    admits [true] true = false ∧ admits (install false [true]) true = true := by
  decide

/-- **A resumption on a fresh chain needs its stored flag**: if the logical caller is pure and the
resumed computation runs on a chain holding only its stored flag, the gate admits an effect exactly
when that flag is `false`, so the cover invariant holds exactly when the stored flag is `true`. -/
theorem fresh_chain_needs_stored_flag (stored : Bool) :
    (admits [stored] true = true ↔ stored = false) ∧ (Covers [stored] [false, true] ↔ stored = true) := by
  cases stored <;> simp [admits, Covers]

/-- An entry point that installs the **logical caller's purity, joined with its own**, keeps the
cover invariant for a computation whose logical ancestry is that caller's. -/
theorem install_join_covers (callerPure ownPure : Bool) (rest logical : List Bool)
    (covers : Covers rest logical) :
    Covers (install (callerPure || ownPure) (false :: rest)) (callerPure :: logical) := by
  intro pure
  cases callerPure with
  | true => simp [install]
  | false =>
      have : logical.any id = true := by simpa using pure
      have := covers this
      cases ownPure <;> simp [install, this]

/-- Purity at an observation boundary, distinguishing a restriction owned by
the observation from one borrowed from its current caller. -/
structure BoundaryPurity where
  owned : Bool
  borrowed : Bool
  deriving DecidableEq, Repr

/-- The flag needed for effect admission forgets which boundary supplied it. -/
def BoundaryPurity.combined (p : BoundaryPurity) : Bool := p.owned || p.borrowed

/-- A caller's prohibition cannot be converted into a catchable local fault.
When both prohibit the effect, the caller's restriction still applies. -/
inductive BoundaryDecision where
  | admitted
  | ownedRefusal
  | callerRefusal
  deriving DecidableEq, Repr

def BoundaryPurity.decision (p : BoundaryPurity) : BoundaryDecision :=
  if p.borrowed then .callerRefusal else if p.owned then .ownedRefusal else .admitted

/-- Resumption retains the owned policy but consults its present caller. -/
def BoundaryPurity.resume (p : BoundaryPurity) (currentCaller : Bool) : BoundaryPurity :=
  { p with borrowed := currentCaller }

theorem BoundaryPurity.admits_iff (p : BoundaryPurity) :
    admits [p.owned, p.borrowed] true = true ↔ p.decision = .admitted := by
  cases p with
  | mk owned borrowed => cases owned <;> cases borrowed <;>
      simp [admits, BoundaryPurity.decision]

/-- No classifier using only the combined flag can tell a local refusal from
an otherwise identical caller refusal. -/
theorem boundary_decision_not_from_combined :
    ¬ ∃ classify : Bool → BoundaryDecision,
      ∀ p : BoundaryPurity, classify p.combined = p.decision := by
  rintro ⟨classify, correct⟩
  have localCase : classify true = .ownedRefusal := by
    simpa [BoundaryPurity.combined, BoundaryPurity.decision] using
      correct ⟨true, false⟩
  have callerCase : classify true = .callerRefusal := by
    simpa [BoundaryPurity.combined, BoundaryPurity.decision] using
      correct ⟨false, true⟩
  rw [localCase] at callerCase
  cases callerCase

/-- The ordered owners of the prohibitions in a logical scope chain. Keeping
the chain also distinguishes nested callers, not just local from external. -/
def refusingScopes {Scope : Type} (chain : List (Scope × Bool)) : List Scope :=
  chain.filterMap fun (scope, pure) => if pure then some scope else none

theorem refusingScopes_append {Scope : Type} (left right : List (Scope × Bool)) :
    refusingScopes (left ++ right) = refusingScopes left ++ refusingScopes right := by
  simp [refusingScopes]

/-- The existing gate admits an effect exactly when the provenance list has
no denying scope. The list retains information that the gate discards. -/
theorem admits_iff_no_refusingScopes {Scope : Type} (chain : List (Scope × Bool)) :
    admits (chain.map Prod.snd) true = true ↔ refusingScopes chain = [] := by
  induction chain with
  | nil => simp [admits, refusingScopes]
  | cons entry rest ih =>
      rcases entry with ⟨scope, pure⟩
      cases pure with
      | false => simp_all [admits, refusingScopes]
      | true => simp [admits, refusingScopes]

/-- Refusing scopes reachable through a finite authority graph. The carrier
is explicit: completeness requires it to contain every relevant parent. This
closure does not prescribe the native walk's treatment of cycles. -/
def refusingGraph {Scope : Type} [DecidableEq Scope]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool) : Finset Scope :=
  (Mettapedia.Logic.LP.FiniteDependencyClosure.within parents carrier roots).filter
    fun scope => pure scope = true

@[simp] theorem mem_refusingGraph {Scope : Type} [DecidableEq Scope]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool) (scope : Scope) :
    scope ∈ refusingGraph parents carrier roots pure ↔
      scope ∈ Mettapedia.Logic.LP.FiniteDependencyClosure.within parents carrier roots ∧
        pure scope = true := by
  simp [refusingGraph]

/-- A pure root cannot disappear from the graph's refusal set. -/
theorem root_mem_refusingGraph {Scope : Type} [DecidableEq Scope]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool) (contained : roots ⊆ carrier)
    {scope : Scope} (root : scope ∈ roots) (restricted : pure scope = true) :
    scope ∈ refusingGraph parents carrier roots pure := by
  rw [mem_refusingGraph]
  exact ⟨Mettapedia.Logic.LP.FiniteDependencyClosure.roots_subset_within
    parents carrier roots contained root, restricted⟩

/-- Every pure parent of a reachable scope is retained, provided the finite
carrier is closed under parent edges. -/
theorem parent_mem_refusingGraph {Scope : Type} [DecidableEq Scope]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool)
    (closed : ∀ scope ∈ carrier, parents scope ⊆ carrier)
    {child parent : Scope}
    (reachable : child ∈ Mettapedia.Logic.LP.FiniteDependencyClosure.within parents carrier roots)
    (edge : parent ∈ parents child) (restricted : pure parent = true) :
    parent ∈ refusingGraph parents carrier roots pure := by
  rw [mem_refusingGraph]
  exact ⟨Mettapedia.Logic.LP.FiniteDependencyClosure.within_closed
    parents carrier roots closed reachable edge, restricted⟩

/-- With complete parent coverage, the collected refusals do not depend on
which closed finite carrier was used for the traversal. -/
theorem refusingGraph_independent {Scope : Type} [DecidableEq Scope]
    (parents : Scope → Finset Scope) (left right roots : Finset Scope)
    (pure : Scope → Bool) (leftContains : roots ⊆ left) (rightContains : roots ⊆ right)
    (leftClosed : ∀ scope ∈ left, parents scope ⊆ left)
    (rightClosed : ∀ scope ∈ right, parents scope ⊆ right) :
    refusingGraph parents left roots pure = refusingGraph parents right roots pure := by
  unfold refusingGraph
  rw [Mettapedia.Logic.LP.FiniteDependencyClosure.within_independent
    parents left right roots leftContains rightContains leftClosed rightClosed]

/-- Two distinct denying scopes cannot be faithfully represented by one
scope identity. -/
theorem refusingGraph_not_singleton {Scope : Type} [DecidableEq Scope]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool) {left right : Scope}
    (leftDenied : left ∈ refusingGraph parents carrier roots pure)
    (rightDenied : right ∈ refusingGraph parents carrier roots pure)
    (distinct : left ≠ right) :
    ¬ ∃ chosen, refusingGraph parents carrier roots pure = {chosen} := by
  rintro ⟨chosen, only⟩
  have leftEq : left = chosen := Finset.mem_singleton.mp (only ▸ leftDenied)
  have rightEq : right = chosen := Finset.mem_singleton.mp (only ▸ rightDenied)
  exact distinct (leftEq.trans rightEq.symm)

/-- Several scope occurrences may belong to the same owner. Collect exactly
the owners of reachable denying scopes, identifying such aliases. -/
def refusingOwners {Scope Owner : Type} [DecidableEq Scope] [DecidableEq Owner]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool) (owner : Scope → Owner) : Finset Owner :=
  (refusingGraph parents carrier roots pure).image owner

@[simp] theorem mem_refusingOwners {Scope Owner : Type} [DecidableEq Scope] [DecidableEq Owner]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool) (owner : Scope → Owner) (target : Owner) :
    target ∈ refusingOwners parents carrier roots pure owner ↔
      ∃ scope ∈ refusingGraph parents carrier roots pure, owner scope = target := by
  exact Finset.mem_image

/-- If two denying scopes have different owners, a single owner identifier
cannot retain the obligations of both. -/
theorem refusingOwners_not_singleton {Scope Owner : Type}
    [DecidableEq Scope] [DecidableEq Owner]
    (parents : Scope → Finset Scope) (carrier roots : Finset Scope)
    (pure : Scope → Bool) (owner : Scope → Owner) {left right : Scope}
    (leftDenied : left ∈ refusingGraph parents carrier roots pure)
    (rightDenied : right ∈ refusingGraph parents carrier roots pure)
    (distinct : owner left ≠ owner right) :
    ¬ ∃ chosen, refusingOwners parents carrier roots pure owner = {chosen} := by
  rintro ⟨chosen, only⟩
  have leftMem : owner left ∈ refusingOwners parents carrier roots pure owner :=
    Finset.mem_image.mpr ⟨left, leftDenied, rfl⟩
  have rightMem : owner right ∈ refusingOwners parents carrier roots pure owner :=
    Finset.mem_image.mpr ⟨right, rightDenied, rfl⟩
  have leftEq : owner left = chosen := Finset.mem_singleton.mp (only ▸ leftMem)
  have rightEq : owner right = chosen := Finset.mem_singleton.mp (only ▸ rightMem)
  exact distinct (leftEq.trans rightEq.symm)

/-- A boundary may own one refusal while other owners' refusals continue
across it. The set does not prescribe an ordering of their observations. -/
structure RefusalCut (Owner : Type) where
  owned : Bool
  remaining : Finset Owner
  deriving DecidableEq

def cutRefusals {Owner : Type} [DecidableEq Owner]
    (boundary : Owner) (owners : Finset Owner) : RefusalCut Owner :=
  ⟨decide (boundary ∈ owners), owners.erase boundary⟩

def RefusalCut.reassemble {Owner : Type} [DecidableEq Owner]
    (boundary : Owner) (cut : RefusalCut Owner) : Finset Owner :=
  if cut.owned then insert boundary cut.remaining else cut.remaining

/-- The cut preserves the complete set of denying owners. -/
theorem reassemble_cutRefusals {Owner : Type} [DecidableEq Owner]
    (boundary : Owner) (owners : Finset Owner) :
    (cutRefusals boundary owners).reassemble boundary = owners := by
  by_cases member : boundary ∈ owners
  · simp [cutRefusals, RefusalCut.reassemble, member]
  · simp [cutRefusals, RefusalCut.reassemble, member]

/-- Every other owner's refusal crosses this boundary unchanged. -/
theorem mem_cutRefusals_remaining {Owner : Type} [DecidableEq Owner]
    (boundary other : Owner) (owners : Finset Owner) (distinct : other ≠ boundary) :
    other ∈ (cutRefusals boundary owners).remaining ↔ other ∈ owners := by
  simp [cutRefusals, distinct]

@[simp] theorem BoundaryPurity.resume_owned (p : BoundaryPurity) (currentCaller : Bool) :
    (p.resume currentCaller).owned = p.owned := rfl

@[simp] theorem BoundaryPurity.resume_borrowed (p : BoundaryPurity) (currentCaller : Bool) :
    (p.resume currentCaller).borrowed = currentCaller := rfl

namespace Controls

/-- A pure driver on the chain covers a pure logical caller; a chain without one does not. -/
theorem covers_controls : Covers [true] [true] ∧ ¬ Covers [false] [true] := by
  refine ⟨fun _ => rfl, fun covers => ?_⟩
  have := covers rfl
  revert this
  decide

/-- The gate refuses an effect under a pure driver and admits it under none. -/
theorem admits_controls : admits [true] true = false ∧ admits [false] true = true := by decide

/-- Equal admission flags may have different refusal owners, and an active
caller restriction takes precedence when both boundaries prohibit the effect. -/
theorem boundary_owner_controls :
    (BoundaryPurity.mk true false).combined = (BoundaryPurity.mk false true).combined ∧
    (BoundaryPurity.mk true false).decision = .ownedRefusal ∧
    (BoundaryPurity.mk false true).decision = .callerRefusal ∧
    (BoundaryPurity.mk true true).decision = .callerRefusal := by decide

/-- A later caller may add or remove its own restriction without changing the
retained observation's owned restriction. -/
theorem boundary_resume_controls :
    ((BoundaryPurity.mk false false).resume true).decision = .callerRefusal ∧
    (((BoundaryPurity.mk false false).resume true).resume false).decision = .admitted ∧
    ((BoundaryPurity.mk true true).resume false).decision = .ownedRefusal := by decide

/-- Two active prohibitions remain separately attributable across a nested
chain; an unrestrictive intervening scope is not an additional refusal. -/
theorem refusingScopes_controls :
    refusingScopes [(1, true), (2, false), (3, true)] = [1, 3] ∧
    admits [true, false, true] true = false ∧
    refusingScopes [(1, false), (2, false)] = ([] : List Nat) := by decide

private def branchParents (scope : Fin 3) : Finset (Fin 3) :=
  if scope = 0 then {1, 2} else ∅

private def branchPure (scope : Fin 3) : Bool := scope == 1 || scope == 2

/-- Two incomparable parents both deny; the unrestricted root cannot replace
either one. -/
theorem branching_refusal_controls :
    refusingGraph branchParents Finset.univ {0} branchPure = {1, 2} ∧
    refusingOwners branchParents Finset.univ {0} branchPure id = {1, 2} ∧
    branchPure 0 = false ∧ branchParents 1 = ∅ ∧ branchParents 2 = ∅ ∧
    ¬ ∃ chosen, refusingGraph branchParents Finset.univ {0} branchPure = {chosen} := by
  decide

/-- Distinct denying scopes may legitimately name one common owner; the
owner set then contains that owner once. -/
theorem branching_shared_owner_control :
    refusingGraph branchParents Finset.univ {0} branchPure = {1, 2} ∧
    refusingOwners branchParents Finset.univ {0} branchPure (fun _ => (0 : Fin 3)) = {0} := by
  decide

/-- Dropping one parent from the captured carrier loses its denial; the
carrier-closure premise is therefore observable, not just a size bound. -/
theorem truncated_authority_carrier_control :
    refusingGraph branchParents {0, 1} {0} branchPure = {1} ∧
    (2 : Fin 3) ∉ refusingGraph branchParents {0, 1} {0} branchPure ∧
    ¬ (∀ scope ∈ ({0, 1} : Finset (Fin 3)), branchParents scope ⊆ {0, 1}) := by
  decide

/-- Owning a local refusal does not erase either of two other owners' claims;
a purely external refusal has no local owner to consume. -/
theorem refusal_cut_controls :
    cutRefusals (0 : Fin 3) {0, 1, 2} = ⟨true, {1, 2}⟩ ∧
    cutRefusals (0 : Fin 3) {1, 2} = ⟨false, {1, 2}⟩ ∧
    cutRefusals (0 : Fin 3) {0} = ⟨true, ∅⟩ := by decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.AmbientPurity
