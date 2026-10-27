import Mathlib.Tactic

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

namespace Controls

/-- A pure driver on the chain covers a pure logical caller; a chain without one does not. -/
theorem covers_controls : Covers [true] [true] ∧ ¬ Covers [false] [true] := by
  refine ⟨fun _ => rfl, fun covers => ?_⟩
  have := covers rfl
  revert this
  decide

/-- The gate refuses an effect under a pure driver and admits it under none. -/
theorem admits_controls : admits [true] true = false ∧ admits [false] true = true := by decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.AmbientPurity
