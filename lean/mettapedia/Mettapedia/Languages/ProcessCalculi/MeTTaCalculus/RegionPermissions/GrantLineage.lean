import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.ServiceGrants

/-!
# The space service's grant table refines the delegation core

The space service keeps, per store, a table of grants: each has an identity, a parent (none for a
root the store's owner issued), a grantee, a policy (rights and ticket requirements), a delegable
flag, a revoked flag and a form (the shape of what it may add, inherited by its children). A
grant gives authority while it is **live**: it is not revoked, and it is a root, or its parent is
live and delegable, its policy is an accepted child of the parent's, and its form is the parent's
(`Live`, the service's `grant_authority` walk). The holder of a live delegable grant may delegate
a child to any account, and a grant can be revoked (`Step`).

## The abstraction

A grant **offers** a usage of its store: a right with a ticket when its closed policy holds the
right, a right without a ticket when the right is ticketless (`Offers`). The delegation core of
`Machines.Kernel.Delegation` is read with principals as subjects and (form, usage) pairs as
objects. A core state **abstracts** a table (`Abstracts`) when every live grant's grantee holds a
capability to each usage the grant offers, with the grant flag when the grant is delegable, and
every account may grant to every account (the service lets a delegable grant be delegated to any
account). The roots of a table are the genesis (`genesis`).

## The refinement

* **A child's usages are copies of its parent's** exactly when the child keeps the parent's
  requirements (`keepsRequirements_iff_offers`).
* **Every step of the service is matched by passes of the core** that keep the abstraction, for any
  edge rule that keeps closed requirements (`abstracts_step`), and hence along every run
  (`refines`). The service's rule now is such a rule (`serviceEdge_sound`).
* **Authority is confined**: every usage a live grant offers is in the core's `CanHold` of the
  genesis (`live_canHold`), so it is offered by a root of the same form, delegably when the grant is
  delegable (`usage_from_root`). Per-store rate control survives delegation.
* **Exactly those rules refine.** An edge rule that accepts a child dropping a requirement admits a
  run whose live usages no core run from the genesis can hold (`not_refines_of_escape`); the
  service's earlier rule is one (`Controls.native_not_refines`).

## Where the abstraction is not exact

The core passes a copy of a capability without its grant flag to any subject its holder may grant
to, while the service never delegates from a grant that is not delegable. With every account
grant-connected, the core's `CanHold` lets a non-delegable root's usage reach another account
(`Controls.core_spreads_nondelegable`) that no run of the service reaches
(`Controls.service_keeps_nondelegable`). The refinement is sound, not exact: making the core's pass
condition a parameter (the holder may grant to the recipient, or the source capability carries the
grant flag) would make the service an exact instance.

Revocation is matched by no core step: the core state keeps the capabilities of revoked grants,
which only over-approximates. The service's own revocation (a revoked grant, and every grant below
it, is no longer live) is `Live` itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.GrantLineage

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.ServiceGrants
open Mettapedia.Machines.Kernel
open ServiceRight

/-! ## Usages -/

/-- A usage of a store: a right, used without a ticket (`true`) or with one (`false`). -/
abbrev Usage := ServiceRight × Bool

/-- **What a policy offers**: a right with a ticket when it holds the right, without one when the
right is ticketless. -/
def Offers (p : Policy) (u : Usage) : Prop :=
  if u.2 then u.1 ∈ ticketless p else u.1 ∈ effective p.rights

instance (p : Policy) (u : Usage) : Decidable (Offers p u) := by
  unfold Offers; split <;> infer_instance

/-- **A child's usages are copies of its parent's exactly when it keeps the parent's
requirements.** -/
theorem keepsRequirements_iff_offers {parent child : Policy} :
    KeepsRequirements parent child ↔ ∀ u, Offers child u → Offers parent u := by
  constructor
  · intro edge u offered
    obtain ⟨r, free⟩ := u
    cases free with
    | false => simpa [Offers] using edge.1 (by simpa [Offers] using offered)
    | true => simpa [Offers] using keepsRequirements_ticketless edge (by simpa [Offers] using offered)
  · intro within
    refine ⟨fun r eff => by simpa [Offers] using within (r, false) (by simpa [Offers] using eff),
      fun r member => ?_⟩
    obtain ⟨required, eff⟩ := Finset.mem_inter.mp member
    by_contra notRequired
    have free : Offers child (r, true) := by
      simpa [Offers, ticketless] using ⟨eff, notRequired⟩
    have := within (r, true) free
    simp only [Offers, if_true, ticketless, Finset.mem_sdiff] at this
    exact this.2 required

/-- Every usage. -/
def allUsages : List Usage :=
  [observe, read, append, write].flatMap fun r => [(r, false), (r, true)]

theorem mem_allUsages (u : Usage) : u ∈ allUsages := by
  obtain ⟨r, b⟩ := u
  cases r <;> cases b <;> decide

/-! ## The grant table -/

/-- A grant of the table. -/
structure Grant (P F : Type) where
  id : ℕ
  parent : Option ℕ
  grantee : P
  policy : Policy
  delegable : Bool
  revoked : Bool
  form : F

/-- The table of one store, and the next identity. -/
structure Table (P F : Type) where
  grants : List (Grant P F)
  next : ℕ

variable {P F : Type} [DecidableEq P] [DecidableEq F]
variable (edge : Policy → Policy → Prop) (accounts : List P)

/-- **A live grant**: not revoked, and a root, or the accepted child of a live delegable parent,
with the parent's form. -/
inductive Live (T : List (Grant P F)) : Grant P F → Prop
  | root {g : Grant P F} (member : g ∈ T) (isRoot : g.parent = none) (live : g.revoked = false) :
      Live T g
  | child {g p : Grant P F} (member : g ∈ T) (parentMember : p ∈ T) (link : g.parent = some p.id)
      (parentLive : Live T p) (parentDelegable : p.delegable = true) (accepted : edge p.policy g.policy)
      (sameForm : g.form = p.form) (live : g.revoked = false) : Live T g

/-- Revoke the grant with identity `gid`. -/
def revokeAt (gid : ℕ) (g : Grant P F) : Grant P F :=
  if g.id = gid then { g with revoked := true } else g

omit [DecidableEq P] [DecidableEq F] in
@[simp] theorem revokeAt_id (gid : ℕ) (g : Grant P F) : (revokeAt gid g).id = g.id := by
  unfold revokeAt; split <;> rfl

omit [DecidableEq P] [DecidableEq F] in
@[simp] theorem revokeAt_parent (gid : ℕ) (g : Grant P F) : (revokeAt gid g).parent = g.parent := by
  unfold revokeAt; split <;> rfl

omit [DecidableEq P] [DecidableEq F] in
@[simp] theorem revokeAt_grantee (gid : ℕ) (g : Grant P F) :
    (revokeAt gid g).grantee = g.grantee := by
  unfold revokeAt; split <;> rfl

/-- **One step of the service**: the holder of a live delegable grant delegates a child to a
registered account, under the edge rule; or a grant is revoked. -/
inductive Step : Table P F → Table P F → Prop
  | delegate {T : Table P F} {p : Grant P F} (recipient : P) (policy : Policy) (delegable : Bool)
      (member : p ∈ T.grants) (live : Live edge T.grants p) (parentDelegable : p.delegable = true)
      (accepted : edge p.policy policy) (registered : recipient ∈ accounts) :
      Step T ⟨⟨T.next, some p.id, recipient, policy, delegable, false, p.form⟩ :: T.grants, T.next + 1⟩
  | revoke {T : Table P F} (gid : ℕ) : Step T ⟨T.grants.map (revokeAt gid), T.next⟩

/-- The invariant of reachable tables: identities below the next one, parents below their children,
grantees registered. -/
structure WellFormed (T : Table P F) : Prop where
  id_lt : ∀ g ∈ T.grants, g.id < T.next
  parent_lt : ∀ g ∈ T.grants, ∀ q, g.parent = some q → q < g.id
  grantee_mem : ∀ g ∈ T.grants, g.grantee ∈ accounts

/-! ## The delegation core, read for the service -/

/-- The core's state for the service: principals hold capabilities to (form, usage) pairs. -/
abbrev Core (P F : Type) := Delegation.State P (F × Usage)

/-- **A core state abstracts a table**: every live grant's grantee holds each usage the grant
offers, with the grant flag when the grant is delegable; and every account may grant to every
account. -/
structure Abstracts (T : Table P F) (st : Core P F) : Prop where
  uses : ∀ g ∈ T.grants, Live edge T.grants g → ∀ u, Offers (close g.policy) u →
    Delegation.Holds st g.grantee (.obj (g.form, u)) g.delegable
  mayGrant : ∀ a ∈ accounts, ∀ b ∈ accounts, Delegation.Holds st a (.subj b) true

/-- The capabilities of a root: one per usage it offers. -/
def usageCaps (g : Grant P F) : List (Delegation.Cap P (F × Usage)) :=
  (allUsages.filter fun u => decide (Offers (close g.policy) u)).map fun u =>
    ⟨0, g.grantee, .obj (g.form, u), g.delegable, []⟩

/-- Every account may grant to every account. -/
def directory : List (Delegation.Cap P (F × Usage)) :=
  accounts.flatMap fun a => accounts.map fun b => ⟨0, a, .subj b, true, []⟩

/-- **The genesis**: the roots' capabilities and the directory. -/
def genesis (roots : List (Grant P F)) : Core P F :=
  ⟨roots.flatMap usageCaps ++ directory accounts, 1⟩

variable {edge accounts}

/-! ## Liveness across steps -/

omit [DecidableEq P] [DecidableEq F] in
/-- A grant of the table stays live, or not, when a fresh child is added. -/
theorem live_of_live_cons {T : Table P F} (wf : WellFormed accounts T) {c : Grant P F}
    (fresh : c.id = T.next) :
    ∀ {g : Grant P F}, Live edge (c :: T.grants) g → g ∈ T.grants → Live edge T.grants g := by
  intro g live
  induction live with
  | root member isRoot revoked => exact fun inT => .root inT isRoot revoked
  | @child g p member parentMember link parentLive parentDelegable accepted sameForm revoked ih =>
      intro inT
      have parentInT : p ∈ T.grants := by
        rcases List.mem_cons.mp parentMember with rfl | inT'
        · have := wf.parent_lt g inT _ link
          have := wf.id_lt g inT
          omega
        · exact inT'
      exact .child inT parentInT link (ih parentInT) parentDelegable accepted sameForm revoked

omit [DecidableEq P] [DecidableEq F] in
/-- Adding a grant keeps every live grant live. -/
theorem live_cons_of_live {T : List (Grant P F)} {c : Grant P F} :
    ∀ {g : Grant P F}, Live edge T g → Live edge (c :: T) g := by
  intro g live
  induction live with
  | root member isRoot revoked => exact .root (List.mem_cons_of_mem _ member) isRoot revoked
  | child member parentMember link _ parentDelegable accepted sameForm revoked ih =>
      exact .child (List.mem_cons_of_mem _ member) (List.mem_cons_of_mem _ parentMember) link ih
        parentDelegable accepted sameForm revoked

omit [DecidableEq P] [DecidableEq F] in
/-- **Revocation only removes liveness**: a grant live after a revocation was live before. -/
theorem live_of_live_revoke {T : List (Grant P F)} {gid : ℕ} :
    ∀ {g : Grant P F}, Live edge (T.map (revokeAt gid)) g → g ∈ T ∧ Live edge T g := by
  intro g live
  induction live with
  | @root g member isRoot revoked =>
      obtain ⟨g₀, inT, rfl⟩ := List.mem_map.mp member
      by_cases same : g₀.id = gid
      · simp [revokeAt, same] at revoked
      · have unchanged : revokeAt gid g₀ = g₀ := by simp [revokeAt, same]
        rw [unchanged] at isRoot revoked ⊢
        exact ⟨inT, .root inT isRoot revoked⟩
  | @child g p member parentMember link parentLive parentDelegable accepted sameForm revoked ih =>
      obtain ⟨g₀, inT, rfl⟩ := List.mem_map.mp member
      by_cases same : g₀.id = gid
      · simp [revokeAt, same] at revoked
      · have unchanged : revokeAt gid g₀ = g₀ := by simp [revokeAt, same]
        rw [unchanged] at link sameForm revoked accepted ⊢
        obtain ⟨parentInT, parentLive₀⟩ := ih
        exact ⟨inT, .child inT parentInT link parentLive₀ parentDelegable accepted sameForm revoked⟩

omit [DecidableEq P] [DecidableEq F] in
/-- **A revoked grant is not live.** -/
theorem not_live_of_revoked {T : List (Grant P F)} {g : Grant P F} (revoked : g.revoked = true) :
    ¬ Live edge T g := by
  intro live
  cases live with
  | root _ _ notRevoked => rw [revoked] at notRevoked; cases notRevoked
  | child _ _ _ _ _ _ _ notRevoked => rw [revoked] at notRevoked; cases notRevoked

/-! ## The refinement -/

omit [DecidableEq F] [DecidableEq P] in
/-- A holding with the grant flag covers any flag. -/
theorem holds_of_holds_true {st : Core P F} {a : P} {x : Delegation.Target P (F × Usage)}
    (h : Delegation.Holds st a x true) (g : Bool) : Delegation.Holds st a x g := by
  obtain ⟨c, member, holder, target, grant⟩ := h
  exact ⟨c, member, holder, target, fun _ => grant rfl⟩

omit [DecidableEq P] [DecidableEq F] in
theorem passes_append {ops ops' : List (Delegation.Op P (F × Usage))}
    (h : Delegation.Passes ops) (h' : Delegation.Passes ops') : Delegation.Passes (ops ++ ops') := by
  intro op member
  rcases List.mem_append.mp member with m | m
  · exact h op m
  · exact h' op m

/-- **Passing each usage of a list gives the recipient each of them**, when the holder holds each
with the grant flag and may grant to the recipient. -/
theorem holds_after_passes {a b : P} {f : F} {d : Bool} :
    ∀ (us : List Usage) (st : Core P F), (∀ u ∈ us, Delegation.Holds st a (.obj (f, u)) true) →
      Delegation.Holds st a (.subj b) true →
      ∀ u ∈ us, Delegation.Holds (Delegation.run st (us.map fun u => .pass a (.obj (f, u)) d b)) b
        (.obj (f, u)) d
  | [], _, _, _ => by simp
  | u :: us, st, held, grants => by
      intro w member
      have heldU : Delegation.Holds st a (.obj (f, u)) d := holds_of_holds_true (held u (by simp)) d
      simp only [List.map_cons, Delegation.run]
      have passesRest : Delegation.Passes (us.map fun u => .pass a (.obj (f, u)) d b) := by
        intro op m
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp m
        exact ⟨_, _, _, _, rfl⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact Delegation.holds_run_passes passesRest (Delegation.holds_new_pass heldU grants)
      · exact holds_after_passes us _ (fun v m => Delegation.holds_step_pass (held v (by simp [m])))
          (Delegation.holds_step_pass grants) w inRest

/-- **Every step of the service is matched by passes of the core that keep the abstraction**, for
an edge rule under which a child keeps its parent's closed requirements. -/
theorem abstracts_step (sound : ∀ p c, edge p c → KeepsRequirements (close p) (close c))
    {T T' : Table P F} {st : Core P F} (wf : WellFormed accounts T)
    (abs : Abstracts edge accounts T st) (step : Step edge accounts T T') :
    ∃ ops, Delegation.Passes ops ∧ Abstracts edge accounts T' (Delegation.run st ops) ∧
      WellFormed accounts T' := by
  cases step with
  | @delegate p recipient policy delegable member live parentDelegable accepted registered =>
      let us := allUsages.filter fun u => decide (Offers (close policy) u)
      let ops := us.map fun u => Delegation.Op.pass p.grantee (.obj (p.form, u)) delegable recipient
      have passes : Delegation.Passes ops := by
        intro op m
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp m
        exact ⟨_, _, _, _, rfl⟩
      have parentHolds : ∀ u ∈ us, Delegation.Holds st p.grantee (.obj (p.form, u)) true := by
        intro u m
        have offered : Offers (close policy) u := by simpa [us] using (List.mem_filter.mp m).2
        have := abs.uses p member live u
          ((keepsRequirements_iff_offers.mp (sound _ _ accepted)) u offered)
        rwa [parentDelegable] at this
      have grants := abs.mayGrant _ (wf.grantee_mem p member) _ registered
      have childHolds := holds_after_passes (d := delegable) us st parentHolds grants
      refine ⟨ops, passes, ⟨fun g inT' liveG u offered => ?_, fun a ha b hb =>
        Delegation.holds_run_passes passes (abs.mayGrant a ha b hb)⟩, ⟨?_, ?_, ?_⟩⟩
      · rcases List.mem_cons.mp inT' with rfl | inT
        · exact childHolds u (List.mem_filter.mpr ⟨mem_allUsages u, by simpa using offered⟩)
        · exact Delegation.holds_run_passes passes
            (abs.uses g inT (live_of_live_cons wf rfl liveG inT) u offered)
      · intro g m
        rcases List.mem_cons.mp m with rfl | inT
        · simp
        · have := wf.id_lt g inT
          simp only
          omega
      · intro g m q link
        rcases List.mem_cons.mp m with rfl | inT
        · simp only [Option.some.injEq] at link
          subst link
          exact wf.id_lt p member
        · exact wf.parent_lt g inT q link
      · intro g m
        rcases List.mem_cons.mp m with rfl | inT
        · exact registered
        · exact wf.grantee_mem g inT
  | revoke gid =>
      refine ⟨[], fun _ h => absurd h List.not_mem_nil, ⟨fun g inT' liveG u offered => ?_,
        abs.mayGrant⟩, ⟨?_, ?_, ?_⟩⟩
      · obtain ⟨inT, live₀⟩ := live_of_live_revoke liveG
        exact abs.uses g inT live₀ u offered
      · intro g m
        obtain ⟨g₀, inT, rfl⟩ := List.mem_map.mp m
        rw [revokeAt_id]
        exact wf.id_lt g₀ inT
      · intro g m q link
        obtain ⟨g₀, inT, rfl⟩ := List.mem_map.mp m
        rw [revokeAt_parent] at link
        rw [revokeAt_id]
        exact wf.parent_lt g₀ inT q link
      · intro g m
        obtain ⟨g₀, inT, rfl⟩ := List.mem_map.mp m
        rw [revokeAt_grantee]
        exact wf.grantee_mem g₀ inT

/-- **The grant table refines the delegation core**: along every run of the service, some run of
passes of the core from the abstracting state keeps the abstraction. -/
theorem refines (sound : ∀ p c, edge p c → KeepsRequirements (close p) (close c))
    {T T' : Table P F} {st : Core P F} (wf : WellFormed accounts T)
    (abs : Abstracts edge accounts T st) (run : Relation.ReflTransGen (Step edge accounts) T T') :
    ∃ ops, Delegation.Passes ops ∧ Abstracts edge accounts T' (Delegation.run st ops) ∧
      WellFormed accounts T' := by
  induction run with
  | refl => exact ⟨[], fun _ h => absurd h List.not_mem_nil, abs, wf⟩
  | tail _ step ih =>
      obtain ⟨ops, passes, abs', wf'⟩ := ih
      obtain ⟨ops', passes', abs'', wf''⟩ := abstracts_step sound wf' abs' step
      exact ⟨ops ++ ops', passes_append passes passes',
        by rw [Delegation.run_append]; exact abs'', wf''⟩

/-! ## Confinement -/

omit [DecidableEq P] [DecidableEq F] in
/-- **The genesis abstracts its roots.** -/
theorem abstracts_genesis {roots : List (Grant P F)} (next : ℕ) :
    Abstracts edge accounts ⟨roots, next⟩ (genesis accounts roots) where
  uses g member _ u offered :=
    ⟨⟨0, g.grantee, .obj (g.form, u), g.delegable, []⟩,
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨g, member, List.mem_map.mpr
        ⟨u, List.mem_filter.mpr ⟨mem_allUsages u, by simpa using offered⟩, rfl⟩⟩),
      rfl, rfl, fun h => h⟩
  mayGrant a ha b hb :=
    ⟨⟨0, a, .subj b, true, []⟩, List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha,
      List.mem_map.mpr ⟨b, hb, rfl⟩⟩), rfl, rfl, fun _ => rfl⟩

/-- **Authority is confined**: every usage a live grant offers, along any run of the service from
its roots, is in the core's `CanHold` of the genesis. -/
theorem live_canHold (sound : ∀ p c, edge p c → KeepsRequirements (close p) (close c))
    {roots : List (Grant P F)} {next : ℕ} (wf : WellFormed accounts ⟨roots, next⟩)
    {T' : Table P F} (run : Relation.ReflTransGen (Step edge accounts) ⟨roots, next⟩ T') :
    ∀ g ∈ T'.grants, Live edge T'.grants g → ∀ u, Offers (close g.policy) u →
      Delegation.CanHold (genesis accounts roots) g.grantee (.obj (g.form, u)) g.delegable := by
  obtain ⟨ops, -, abs, -⟩ := refines sound wf (abstracts_genesis next) run
  intro g member live u offered
  exact Delegation.holds_confined _ ops (abs.uses g member live u offered)

omit [DecidableEq F] [DecidableEq P] in
/-- What the core can ever give, it held at the genesis: `CanHold` of a target is a holding of it by
some subject of the genesis. -/
theorem canHold_held {st₀ : Core P F} :
    ∀ {b : P} {x : Delegation.Target P (F × Usage)} {g : Bool}, Delegation.CanHold st₀ b x g →
      ∃ a, Delegation.Holds st₀ a x g := by
  intro b x g h
  induction h with
  | base held => exact ⟨_, held⟩
  | pass _ _ ih _ => exact ih

/-- **Every usage of a live grant is offered by a root of the same form**, delegably when the grant
is delegable. -/
theorem usage_from_root (sound : ∀ p c, edge p c → KeepsRequirements (close p) (close c))
    {roots : List (Grant P F)} {next : ℕ} (wf : WellFormed accounts ⟨roots, next⟩)
    {T' : Table P F} (run : Relation.ReflTransGen (Step edge accounts) ⟨roots, next⟩ T') :
    ∀ g ∈ T'.grants, Live edge T'.grants g → ∀ u, Offers (close g.policy) u →
      ∃ r ∈ roots, r.form = g.form ∧ Offers (close r.policy) u ∧
        (g.delegable = true → r.delegable = true) := by
  intro g member live u offered
  obtain ⟨a, c, inCaps, holder, target, grant⟩ :=
    canHold_held (live_canHold sound wf run g member live u offered)
  rcases List.mem_append.mp inCaps with fromRoot | fromDirectory
  · obtain ⟨r, inRoots, inUsages⟩ := List.mem_flatMap.mp fromRoot
    obtain ⟨v, inFilter, rfl⟩ := List.mem_map.mp inUsages
    simp only [Delegation.Target.obj.injEq, Prod.mk.injEq] at target
    obtain ⟨sameForm, rfl⟩ := target
    exact ⟨r, inRoots, sameForm, by simpa using (List.mem_filter.mp inFilter).2, grant⟩
  · obtain ⟨a', -, inMap⟩ := List.mem_flatMap.mp fromDirectory
    obtain ⟨b', -, rfl⟩ := List.mem_map.mp inMap
    simp at target

/-- **The service's rule now refines the delegation core.** -/
theorem serviceEdge_sound : ∀ p c, ServiceEdge p c → KeepsRequirements (close p) (close c) :=
  fun _ _ => serviceEdge_iff.mp

/-! ## Exactly the rules that keep requirements refine -/

/-- A root and the child it may delegate. -/
def rootGrant (owner : P) (p : Policy) (f : F) : Grant P F := ⟨0, none, owner, p, true, false, f⟩

/-- **A rule that lets a child drop a closed requirement does not refine the core**: the one-step
run that delegates such a child has a live grant offering a usage that no core run from the
genesis gives its grantee. -/
theorem not_refines_of_escape {owner recipient : P} (recipientIn : recipient ∈ accounts) {p c : Policy} (f : F) (accepted : edge p c)
    (escape : ¬ KeepsRequirements (close p) (close c)) (d : Bool) :
    Step edge accounts ⟨[rootGrant owner p f], 1⟩
        ⟨[⟨1, some 0, recipient, c, d, false, f⟩, rootGrant owner p f], 2⟩ ∧
      ¬ ∃ ops, Abstracts edge accounts ⟨[⟨1, some 0, recipient, c, d, false, f⟩, rootGrant owner p f], 2⟩
        (Delegation.run (genesis accounts [rootGrant owner p f]) ops) := by
  have rootLive : Live edge [rootGrant owner p f] (rootGrant owner p f) :=
    .root (List.mem_singleton_self _) rfl rfl
  refine ⟨.delegate (p := rootGrant owner p f) recipient c d (List.mem_singleton_self _) rootLive rfl
    accepted recipientIn, ?_⟩
  rintro ⟨ops, abs⟩
  obtain ⟨u, offeredChild, notParent⟩ : ∃ u, Offers (close c) u ∧ ¬ Offers (close p) u := by
    by_contra none
    exact escape (keepsRequirements_iff_offers.mpr fun u offered =>
      by_contra fun notParent => none ⟨u, offered, notParent⟩)
  have childLive : Live edge [⟨1, some 0, recipient, c, d, false, f⟩, rootGrant owner p f]
      ⟨1, some 0, recipient, c, d, false, f⟩ :=
    .child (p := rootGrant owner p f) List.mem_cons_self
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl (live_cons_of_live rootLive) rfl accepted
      rfl rfl
  have held := abs.uses _ (by simp) childLive u offeredChild
  obtain ⟨a, cap, inCaps, -, target, -⟩ :=
    canHold_held (Delegation.holds_confined _ ops held)
  rcases List.mem_append.mp inCaps with fromRoot | fromDirectory
  · obtain ⟨r, inRoots, inUsages⟩ := List.mem_flatMap.mp fromRoot
    simp only [List.mem_singleton] at inRoots
    subst inRoots
    obtain ⟨v, inFilter, rfl⟩ := List.mem_map.mp inUsages
    simp only [Delegation.Target.obj.injEq, Prod.mk.injEq] at target
    obtain ⟨-, rfl⟩ := target
    exact notParent (of_decide_eq_true (List.mem_filter.mp inFilter).2)
  · obtain ⟨a', -, inMap⟩ := List.mem_flatMap.mp fromDirectory
    obtain ⟨b', -, rfl⟩ := List.mem_map.mp inMap
    simp at target

/-! ## Controls -/

namespace Controls

/-- Two accounts. -/
inductive Account where
  | alice
  | bob
  deriving DecidableEq, Repr

open Account

/-- Both accounts are registered. -/
def registered : List Account := [alice, bob]

/-- **The service's earlier rule does not refine the core**: Alice's root needs a ticket per
append; the earlier rule accepts Bob's child that appends without one, and no core run from the
genesis gives Bob a ticketless append. -/
theorem native_not_refines :
    ¬ ∃ ops, Abstracts NativeEdge registered
      ⟨[⟨1, some 0, bob, freeChild, false, false, ()⟩, rootGrant alice ticketedRoot ()], 2⟩
      (Delegation.run (genesis registered [rootGrant alice ticketedRoot ()]) ops) :=
  (not_refines_of_escape (by decide) () nativeEdge_drops_requirement.1
    (fun keeps => nativeEdge_drops_requirement.2.2.2 (by
      have : close ticketedRoot = ticketedRoot := by decide
      have : close freeChild = freeChild := by decide
      simpa [*] using keeps)) false).2

/-- **The rule now accepts a child that keeps the requirement, and refines**: Bob's ticketed child
of Alice's ticketed root is a step, and every usage it offers is offered by the root. -/
theorem service_child_from_root :
    Step ServiceEdge registered ⟨[rootGrant alice ticketedRoot ()], 1⟩
        ⟨[⟨1, some 0, bob, ticketedRoot, false, false, ()⟩, rootGrant alice ticketedRoot ()], 2⟩ ∧
      ∀ u, Offers (close ticketedRoot) u → Offers (close ticketedRoot) u :=
  ⟨.delegate (p := rootGrant alice ticketedRoot ()) bob ticketedRoot false (List.mem_singleton_self _)
    (.root (List.mem_singleton_self _) rfl rfl) rfl (by decide) (by decide),
    fun _ h => h⟩

/-- The usage of reading without a ticket, of form `()`. -/
def freeRead : Unit × Usage := ((), (read, true))

/-- A root that reads without a ticket and is not delegable. -/
def readRoot : Grant Account Unit := ⟨0, none, alice, ⟨{read}, ∅⟩, false, false, ()⟩

/-- **The core over-approximates**: with every account grant-connected, Alice's non-delegable
read reaches Bob in the core's `CanHold`. -/
theorem core_spreads_nondelegable :
    Delegation.CanHold (genesis registered [readRoot]) bob (.obj freeRead) false := by
  have aliceHolds : Delegation.CanHold (genesis registered [readRoot]) alice (.obj freeRead) false :=
    .base ⟨⟨0, alice, .obj freeRead, false, []⟩, by decide, rfl, rfl, fun h => absurd h (by decide)⟩
  have aliceGrants : Delegation.CanHold (genesis registered [readRoot]) alice (.subj bob) true :=
    .base ⟨⟨0, alice, .subj bob, true, []⟩, by decide, rfl, rfl, fun _ => rfl⟩
  exact .pass aliceHolds aliceGrants

/-- **The service does not**: from Alice's non-delegable root, every reachable table holds only
Alice's grants, none delegable. -/
theorem service_keeps_nondelegable {T : Table Account Unit}
    (run : Relation.ReflTransGen (Step ServiceEdge registered) ⟨[readRoot], 1⟩ T) :
    ∀ g ∈ T.grants, g.grantee = alice ∧ g.delegable = false := by
  induction run with
  | refl => simp [readRoot]
  | tail _ step ih =>
      cases step with
      | delegate recipient policy delegable member _ parentDelegable =>
          rw [(ih _ member).2] at parentDelegable
          cases parentDelegable
      | revoke gid =>
          intro g m
          obtain ⟨g₀, inT, rfl⟩ := List.mem_map.mp m
          unfold revokeAt
          split <;> exact ih g₀ inT

/-! ### Usages, liveness, steps and well-formed tables -/

/-- **Usages**: the ticketed root offers an append with a ticket and none without; the free child
offers an append without one. -/
theorem offers_controls :
    Offers (close ticketedRoot) (append, false) ∧ ¬ Offers (close ticketedRoot) (append, true) ∧
      Offers (close freeChild) (append, true) := by
  decide

/-- Bob's ticketed child of Alice's root. -/
def bobsChild : Grant Account Unit := ⟨1, some 0, bob, ticketedRoot, false, false, ()⟩

/-- **Liveness**: Alice's root is live; revoked, it is not, and neither is Bob's child below it. -/
theorem live_controls :
    Live ServiceEdge [rootGrant alice ticketedRoot ()] (rootGrant alice ticketedRoot ()) ∧
      ¬ Live ServiceEdge [bobsChild, revokeAt 0 (rootGrant alice ticketedRoot ())]
        (revokeAt 0 (rootGrant alice ticketedRoot ())) ∧
      ¬ Live ServiceEdge [bobsChild, revokeAt 0 (rootGrant alice ticketedRoot ())] bobsChild := by
  have rootRevoked : (revokeAt 0 (rootGrant alice ticketedRoot ())).revoked = true := by
    simp [revokeAt, rootGrant]
  refine ⟨.root (List.mem_singleton_self _) rfl rfl, not_live_of_revoked rootRevoked,
    fun live => ?_⟩
  cases live with
  | root _ isRoot _ => simp [bobsChild] at isRoot
  | @child _ p _ parentMember link parentLive _ _ _ _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at parentMember
      rcases parentMember with rfl | rfl
      · simp [bobsChild] at link
      · exact not_live_of_revoked rootRevoked parentLive

/-- **Steps**: the rule now refuses to delegate the free child from Alice's ticketed root. -/
theorem free_child_not_a_step :
    ¬ Step ServiceEdge registered ⟨[rootGrant alice ticketedRoot ()], 1⟩
      ⟨[⟨1, some 0, bob, freeChild, false, false, ()⟩, rootGrant alice ticketedRoot ()], 2⟩ := by
  intro step
  generalize hT : (⟨[rootGrant alice ticketedRoot ()], 1⟩ : Table Account Unit) = T at step
  generalize hT' : (⟨[⟨1, some 0, bob, freeChild, false, false, ()⟩, rootGrant alice ticketedRoot ()],
    2⟩ : Table Account Unit) = T' at step
  cases step with
  | @delegate p recipient policy delegable member _ _ accepted _ =>
      subst hT
      have hpol : policy = freeChild := by
        have := congrArg (fun t : Table Account Unit => t.grants.head?.map Grant.policy) hT'
        simpa using this.symm
      simp only [List.mem_singleton] at member
      subst member hpol
      exact absurd accepted (by decide)
  | revoke gid =>
      subst hT
      have := congrArg Table.next hT'
      simp at this

/-- **Well-formed tables**: Alice's root below the next identity is; at a next identity no larger
than its own, it is not. -/
theorem wellFormed_controls :
    WellFormed registered (⟨[rootGrant alice ticketedRoot ()], 1⟩ : Table Account Unit) ∧
      ¬ WellFormed registered (⟨[rootGrant alice ticketedRoot ()], 0⟩ : Table Account Unit) := by
  refine ⟨⟨fun g m => ?_, fun g m q link => ?_, fun g m => ?_⟩, fun wf => ?_⟩
  · simp only [List.mem_singleton] at m; subst m; decide
  · simp only [List.mem_singleton] at m; subst m; simp [rootGrant] at link
  · simp only [List.mem_singleton] at m; subst m; decide
  · have := wf.id_lt _ (List.mem_singleton_self _)
    simp [rootGrant] at this

/-- **The refinement on one step, positive**: after Bob's ticketed child of Alice's ticketed root,
some run of passes from the genesis abstracts the table. -/
theorem service_child_abstracted :
    ∃ ops, Delegation.Passes ops ∧
      Abstracts ServiceEdge registered
        ⟨[⟨1, some 0, bob, ticketedRoot, false, false, ()⟩, rootGrant alice ticketedRoot ()], 2⟩
        (Delegation.run (genesis registered [rootGrant alice ticketedRoot ()]) ops) := by
  have wf : WellFormed registered (⟨[rootGrant alice ticketedRoot ()], 1⟩ : Table Account Unit) :=
    wellFormed_controls.1
  obtain ⟨ops, passes, abs, -⟩ := refines serviceEdge_sound wf (abstracts_genesis 1)
    (Relation.ReflTransGen.single service_child_from_root.1)
  exact ⟨ops, passes, abs⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.GrantLineage
