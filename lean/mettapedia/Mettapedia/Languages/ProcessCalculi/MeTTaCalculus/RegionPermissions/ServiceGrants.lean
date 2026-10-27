import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic
import Mettapedia.Machines.Kernel.Delegation

/-!
# Grant lineages in the space service: rights attenuate, restrictions must be inherited

The space service keeps, per store, immutable grants with a parent, a grantee, a set of rights, a
set of rights that need a one-shot ticket per use (its *ticket requirements*), and a delegable
flag. A holder of a delegable grant may delegate a child to any account. The service's earlier rule
accepted a child when its effective rights lie within the parent's and its ticket requirements lie
within the parent's (`NativeEdge`; `grant_edge_valid` and `delegate-grant` in the service source).
The draft's service now keeps closed requirements (`ServiceEdge`), below.

## Rights shrink along a lineage; requirements must not

A right that needs a ticket is a right with a restriction. Less authority means fewer rights *or
more restrictions*, so attenuation reverses the order on requirements: a child must keep every
requirement of its parent on the rights it holds (`KeepsRequirements`).

* With that rule, the rights usable without a ticket only shrink along a lineage
  (`keepsRequirements_ticketless`, `chain_ticketless`), so no descendant of a grant whose appends
  need tickets appends without one (`chain_no_free_append`), and the appends of the whole lineage
  are bounded by the tickets the owner issued (`appends_le_tickets`).
* With the service's rule, a child may drop the requirement (`nativeEdge_drops_requirement`): for
  every `m` there is a lineage, accepted by the service's rule, whose leaf makes `m` appends with no
  ticket at all although its root needs a ticket for each (`native_free_appends`). The holder of
  the root cannot append without tickets itself, but it can give an account it controls a child that
  can. This is the run observed on the service's own code.
* A ticket requirement on `append` beside a held `write` does not bind row additions: a write batch
  adds rows without a ticket (`write_bypasses_append_requirement`). Requirements must be closed
  along the implication of rights (`RequirementsClosed`, `closed_no_free_add`).

## The rule now: requirements kept and closed

The draft's service closes requirements along the implication of rights (`close`: a ticket per
append beside a held `write` is a ticket per write) and accepts a child exactly when its effective
rights lie within the parent's and the parent's closed requirements on the rights it holds are
among its own (`ServiceEdge`). That is `KeepsRequirements` between closed policies
(`serviceEdge_iff`), so the attenuation theorems hold for it:

* every grant of a lineage keeps the root's closed requirements (`serviceChain_keeps`), so checking
  the requirements of the grant a use goes through misses none of its ancestors';
* the ticketless rights only shrink (`serviceChain_ticketless`);
* no grant adds a row without a ticket, by append or by a write batch (`serviceChain_no_free_add`),
  and row additions are bounded by the tickets issued (`rowAdds_le_tickets`).

## The service's delegation discipline is not the delegation core's

`Machines.Kernel.Delegation` passes a capability only to a subject one holds a grant capability for
(`mayGrant`), and passes it even when the copied capability has no grant flag
(`Controls.core_passes_nongrant_copy`, `Controls.core_needs_subject_grant`). The service lets the
holder of a *delegable* grant delegate to *any* account and forbids delegating a non-delegable one.
Both have the shape "authority reaches only along passes from a genesis", but neither step
relation is an instance of the other; one delegation core for both would take the condition for a
pass as a parameter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.ServiceGrants

/-- The service's four rights. -/
inductive ServiceRight where
  | observe
  | read
  | append
  | write
  deriving DecidableEq, Repr

open ServiceRight

/-- What held rights let their holder do: `write` gives `read` and `append`, and `read` gives
`observe` (`effective_rights`). -/
def effective (rs : Finset ServiceRight) : Finset ServiceRight :=
  rs ∪ (if write ∈ rs then {read, append, observe} else ∅) ∪
    (if read ∈ rs then {observe} else ∅)

theorem subset_effective (rs : Finset ServiceRight) : rs ⊆ effective rs := by
  intro x member
  simp [effective, member]

/-- A grant's policy: its rights, and the rights that need a ticket for each use. -/
structure Policy where
  rights : Finset ServiceRight
  requires : Finset ServiceRight
  deriving DecidableEq

/-- The rights usable without a ticket. -/
def ticketless (p : Policy) : Finset ServiceRight := effective p.rights \ p.requires

/-- **The service's rule for a child grant**: effective rights within the parent's, ticket
requirements within the parent's. -/
def NativeEdge (parent child : Policy) : Prop :=
  effective child.rights ⊆ effective parent.rights ∧ child.requires ⊆ parent.requires

/-- **Attenuation that keeps restrictions**: effective rights within the parent's, and every
requirement of the parent on a right the child holds is a requirement of the child. -/
def KeepsRequirements (parent child : Policy) : Prop :=
  effective child.rights ⊆ effective parent.rights ∧
    parent.requires ∩ effective child.rights ⊆ child.requires

/-- **Kept requirements: the rights usable without a ticket only shrink.** -/
theorem keepsRequirements_ticketless {parent child : Policy}
    (edge : KeepsRequirements parent child) : ticketless child ⊆ ticketless parent := by
  intro x member
  obtain ⟨effChild, notRequired⟩ := Finset.mem_sdiff.mp member
  refine Finset.mem_sdiff.mpr ⟨edge.1 effChild, fun required => notRequired ?_⟩
  exact edge.2 (Finset.mem_inter.mpr ⟨required, effChild⟩)

theorem keepsRequirements_trans {a b c : Policy} (ab : KeepsRequirements a b)
    (bc : KeepsRequirements b c) : KeepsRequirements a c := by
  refine ⟨bc.1.trans ab.1, fun x member => ?_⟩
  obtain ⟨required, effC⟩ := Finset.mem_inter.mp member
  exact bc.2 (Finset.mem_inter.mpr ⟨ab.2 (Finset.mem_inter.mpr ⟨required, bc.1 effC⟩), effC⟩)

/-- Along a lineage that keeps requirements, every grant's ticketless rights lie within the root's. -/
theorem chain_ticketless {root : Policy} :
    ∀ {lineage : List Policy}, List.IsChain KeepsRequirements (root :: lineage) →
      ∀ g ∈ lineage, ticketless g ⊆ ticketless root
  | [], _ => by simp
  | g :: rest, chain => by
      rw [List.isChain_cons_cons] at chain
      intro x member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact keepsRequirements_ticketless chain.1
      · exact (chain_ticketless chain.2 x inRest).trans (keepsRequirements_ticketless chain.1)

/-- **No descendant of a grant whose appends need tickets appends without one**, when every edge
keeps requirements. -/
theorem chain_no_free_append {root : Policy} (needs : append ∈ root.requires)
    {lineage : List Policy} (chain : List.IsChain KeepsRequirements (root :: lineage)) :
    ∀ g ∈ lineage, append ∉ ticketless g := by
  intro g member free
  have := chain_ticketless chain g member free
  exact (Finset.mem_sdiff.mp this).2 needs

/-- One append through a grant: with a ticket, it needs the append right; without one, it needs the
right to be ticketless. -/
def Permitted (g : Policy) (ticket : Bool) : Prop :=
  if ticket then append ∈ effective g.rights else append ∈ ticketless g

/-- **Appends are bounded by tickets** when every edge keeps requirements: in any permitted
sequence of appends through grants of a lineage under a root whose appends need tickets, every
append spends a ticket, so there are at most as many appends as tickets issued. -/
theorem appends_le_tickets {root : Policy} (needs : append ∈ root.requires)
    {lineage : List Policy} (chain : List.IsChain KeepsRequirements (root :: lineage))
    (uses : List (Policy × Bool)) (inLineage : ∀ u ∈ uses, u.1 = root ∨ u.1 ∈ lineage)
    (permitted : ∀ u ∈ uses, Permitted u.1 u.2) {issued : Nat}
    (spent : (uses.filter (fun u => u.2)).length ≤ issued) : uses.length ≤ issued := by
  have allTicketed : uses.filter (fun u => u.2) = uses := by
    apply List.filter_eq_self.mpr
    intro u member
    cases ticket : u.2 with
    | true => rfl
    | false =>
        exfalso
        have free := permitted u member
        simp only [Permitted, ticket, Bool.false_eq_true, if_false] at free
        rcases inLineage u member with isRoot | inL
        · rw [isRoot] at free
          exact (Finset.mem_sdiff.mp free).2 needs
        · exact chain_no_free_append needs chain u.1 inL free
  rw [← allTicketed]
  exact spent

/-! ## The service's rule drops requirements -/

/-- The root: append, and every append needs a ticket. -/
def ticketedRoot : Policy := ⟨{append}, {append}⟩

/-- The child the service accepts: append, and no ticket needed. -/
def freeChild : Policy := ⟨{append}, ∅⟩

/-- **The service's rule lets a child drop a ticket requirement.** -/
theorem nativeEdge_drops_requirement :
    NativeEdge ticketedRoot freeChild ∧ append ∈ ticketless freeChild ∧
      append ∉ ticketless ticketedRoot ∧ ¬ KeepsRequirements ticketedRoot freeChild := by
  refine ⟨⟨subset_rfl, by simp [freeChild]⟩, by decide, by decide, ?_⟩
  rintro ⟨-, keeps⟩
  have : append ∈ ticketedRoot.requires ∩ effective freeChild.rights := by decide
  have := keeps this
  simp [freeChild] at this

/-- **Under the service's rule, appends are not bounded by tickets**: for every `m`, `m` appends
through the accepted child, none with a ticket, are each permitted, while the owner issued none. -/
theorem native_free_appends (m : Nat) :
    NativeEdge ticketedRoot freeChild ∧
      (∀ u ∈ List.replicate m (freeChild, false), Permitted u.1 u.2) ∧
      ((List.replicate m (freeChild, false)).filter (fun u => u.2)).length ≤ 0 ∧
      (List.replicate m (freeChild, false)).length = m := by
  refine ⟨nativeEdge_drops_requirement.1, ?_, ?_, List.length_replicate⟩
  · intro u member
    rw [List.eq_of_mem_replicate member]
    simp only [Permitted, Bool.false_eq_true, if_false]
    decide
  · simp

/-! ## A requirement on `append` beside `write` -/

/-- A row can be added without a ticket: by an append, or by a write batch's `add`. -/
def AddsRowFree (p : Policy) : Prop := append ∈ ticketless p ∨ write ∈ ticketless p

/-- **A write batch bypasses an append requirement**: with `write` held and only `append`
requiring tickets, a row is added without one. -/
theorem write_bypasses_append_requirement :
    append ∈ (⟨{write}, {append}⟩ : Policy).requires ∧ AddsRowFree ⟨{write}, {append}⟩ := by
  refine ⟨by decide, Or.inr ?_⟩
  decide

/-- Requirements closed along the implication of rights: requiring a ticket for `append` while
holding `write` requires one for `write`. -/
def RequirementsClosed (p : Policy) : Prop :=
  append ∈ p.requires → write ∈ effective p.rights → write ∈ p.requires

/-- **Closed requirements bind every row addition.** -/
theorem closed_no_free_add {p : Policy} (closed : RequirementsClosed p)
    (needs : append ∈ p.requires) : ¬ AddsRowFree p := by
  rintro (free | free)
  · exact (Finset.mem_sdiff.mp free).2 needs
  · obtain ⟨eff, notRequired⟩ := Finset.mem_sdiff.mp free
    exact notRequired (closed needs eff)

/-! ## The service's rule now: requirements kept, and closed along the implication of rights

The draft's service now closes a grant's requirements along the implication of rights before it
uses them (`requirement_closure`: a ticket per append beside a held `write` is a ticket per write
too), and accepts a child exactly when its effective rights lie within the parent's and every closed
requirement of the parent on a right the child holds is a closed requirement of the child
(`ServiceEdge`). That is the edge that keeps requirements, between closed policies
(`serviceEdge_iff`). -/

/-- **The closure of a policy's requirements**: requiring a ticket for each append while holding
`write` requires one for each write. -/
def close (p : Policy) : Policy :=
  ⟨p.rights, p.requires ∪ (if append ∈ p.requires ∧ write ∈ effective p.rights then {write} else ∅)⟩

@[simp] theorem close_rights (p : Policy) : (close p).rights = p.rights := rfl

theorem requires_subset_close (p : Policy) : p.requires ⊆ (close p).requires :=
  Finset.subset_union_left

/-- **A closed policy's requirements are closed.** -/
theorem close_closed (p : Policy) : RequirementsClosed (close p) := by
  intro needs eff
  simp only [close, Finset.mem_union] at needs eff ⊢
  rcases needs with needs | added
  · exact Or.inr (by simp [needs, eff])
  · by_cases h : append ∈ p.requires ∧ write ∈ effective p.rights
    · exact Or.inr (by simp [h])
    · simp [h] at added

/-- **The service's rule now**: effective rights within the parent's, and the parent's closed
requirements on the rights the child holds kept by the child's closed requirements. -/
def ServiceEdge (parent child : Policy) : Prop :=
  effective child.rights ⊆ effective parent.rights ∧
    (close parent).requires ∩ effective child.rights ⊆ (close child).requires

instance (parent child : Policy) : Decidable (ServiceEdge parent child) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The service's rule is the edge that keeps requirements, between closed policies.** -/
theorem serviceEdge_iff {parent child : Policy} :
    ServiceEdge parent child ↔ KeepsRequirements (close parent) (close child) := Iff.rfl

/-- **Along a lineage of the service's edges, every grant keeps the root's closed requirements.**
Applied from any ancestor, it says the leaf's closed requirements contain every closed requirement
of an ancestor on a right the leaf holds; so the service, which checks only the requirements of the
grant a use goes through, misses none. -/
theorem serviceChain_keeps {root : Policy} :
    ∀ {lineage : List Policy}, List.IsChain ServiceEdge (root :: lineage) →
      ∀ g ∈ lineage, KeepsRequirements (close root) (close g)
  | [], _ => by simp
  | g :: rest, chain => by
      rw [List.isChain_cons_cons] at chain
      intro x member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact serviceEdge_iff.mp chain.1
      · exact keepsRequirements_trans (serviceEdge_iff.mp chain.1) (serviceChain_keeps chain.2 x inRest)

/-- **Along a lineage of the service's edges, every grant's closed ticketless rights lie within
the root's.** -/
theorem serviceChain_ticketless {root : Policy} {lineage : List Policy}
    (chain : List.IsChain ServiceEdge (root :: lineage)) :
    ∀ g ∈ lineage, ticketless (close g) ⊆ ticketless (close root) :=
  fun g member => keepsRequirements_ticketless (serviceChain_keeps chain g member)

/-- **No grant of a lineage of the service's edges adds a row without a ticket**, by append or by a
write batch, when the root's appends need tickets. -/
theorem serviceChain_no_free_add {root : Policy} (needs : append ∈ root.requires)
    {lineage : List Policy} (chain : List.IsChain ServiceEdge (root :: lineage)) :
    ∀ g ∈ lineage, ¬ AddsRowFree (close g) := by
  intro g member free
  have closedRoot := close_closed root
  have rootNeeds : append ∈ (close root).requires := requires_subset_close root needs
  have within := serviceChain_ticketless chain g member
  rcases free with free | free
  · exact (Finset.mem_sdiff.mp (within free)).2 rootNeeds
  · obtain ⟨eff, notRequired⟩ := Finset.mem_sdiff.mp (within free)
    exact notRequired (closedRoot rootNeeds eff)

/-- One addition of a row through a grant: by append, or by a write batch; with a ticket it needs
the right, without one the right must be ticketless. -/
def AddPermitted (g : Policy) (byWrite ticket : Bool) : Prop :=
  if ticket then (if byWrite then write else append) ∈ effective g.rights
  else (if byWrite then write else append) ∈ ticketless g

/-- **Row additions are bounded by tickets** under the service's rule: in any permitted sequence of
row additions, by append or by write batch, through the closed grants of a lineage whose root's
appends need tickets, every addition spends a ticket. -/
theorem rowAdds_le_tickets {root : Policy} (needs : append ∈ root.requires)
    {lineage : List Policy} (chain : List.IsChain ServiceEdge (root :: lineage))
    (uses : List (Policy × Bool × Bool)) (inLineage : ∀ u ∈ uses, u.1 = root ∨ u.1 ∈ lineage)
    (permitted : ∀ u ∈ uses, AddPermitted (close u.1) u.2.1 u.2.2) {issued : Nat}
    (spent : (uses.filter (fun u => u.2.2)).length ≤ issued) : uses.length ≤ issued := by
  have allTicketed : uses.filter (fun u => u.2.2) = uses := by
    apply List.filter_eq_self.mpr
    intro u member
    cases ticket : u.2.2 with
    | true => rfl
    | false =>
        exfalso
        have free := permitted u member
        simp only [AddPermitted, ticket, Bool.false_eq_true, if_false] at free
        have noFree : ¬ AddsRowFree (close u.1) := by
          rcases inLineage u member with isRoot | inL
          · rw [isRoot]
            exact closed_no_free_add (close_closed root) (requires_subset_close root needs)
          · exact serviceChain_no_free_add needs chain u.1 inL
        cases byWrite : u.2.1 with
        | false => simp only [byWrite, Bool.false_eq_true, if_false] at free; exact noFree (Or.inl free)
        | true => simp only [byWrite, if_true] at free; exact noFree (Or.inr free)
  rw [← allTicketed]
  exact spent

/-! ## Controls: the delegation core's step is a different discipline -/

namespace Controls

open Mettapedia.Machines.Kernel

/-- Subject `true` holds a capability to object `0` without the grant flag, and may grant to
subject `false`. -/
def coreState : Delegation.State Bool ℕ :=
  ⟨[⟨0, true, .obj 0, false, []⟩, ⟨1, true, .subj false, true, []⟩], 2⟩

/-- **The core passes a copy of a capability that has no grant flag** to a subject its holder may
grant to; the service never delegates a non-delegable grant. -/
theorem core_passes_nongrant_copy :
    Delegation.Holds (Delegation.step coreState (.pass true (.obj 0) false false)) false
      (.obj 0) false := by
  refine ⟨⟨2, false, .obj 0, false, [0]⟩, ?_, rfl, rfl, fun h => absurd h (by decide)⟩
  simp [Delegation.step, Delegation.source, Delegation.mayGrant, coreState]

/-- Subject `true` holds a grant-flagged capability to object `0`, and may grant to nobody. -/
def isolatedState : Delegation.State Bool ℕ := ⟨[⟨0, true, .obj 0, true, []⟩], 1⟩

/-- **The core passes nothing without a grant capability to the recipient**; the service lets a
delegable grant be delegated to any account. -/
theorem core_needs_subject_grant :
    Delegation.step isolatedState (.pass true (.obj 0) true false) = isolatedState := by
  simp [Delegation.step, Delegation.source, Delegation.mayGrant, isolatedState]

/-! ### The predicates, one positive and one negative instance each -/

/-- A grant edge the service accepts and one it refuses: write cannot be delegated under append. -/
theorem nativeEdge_controls :
    NativeEdge ticketedRoot freeChild ∧ ¬ NativeEdge ticketedRoot ⟨{write}, ∅⟩ := by
  refine ⟨nativeEdge_drops_requirement.1, fun edge => ?_⟩
  have := edge.1 (show write ∈ effective ({write} : Finset ServiceRight) by decide)
  revert this
  decide

/-- A child that keeps the root's requirement keeps requirements; the free child does not. -/
theorem keepsRequirements_controls :
    KeepsRequirements ticketedRoot ticketedRoot ∧ ¬ KeepsRequirements ticketedRoot freeChild :=
  ⟨⟨subset_rfl, Finset.inter_subset_left⟩, nativeEdge_drops_requirement.2.2.2⟩

/-- A ticketless append is permitted through the free child and not through the ticketed root. -/
theorem permitted_controls : Permitted freeChild false ∧ ¬ Permitted ticketedRoot false := by
  refine ⟨by simp only [Permitted, Bool.false_eq_true, if_false]; decide, ?_⟩
  simp only [Permitted, Bool.false_eq_true, if_false]
  decide

/-- **Closing adds the write requirement exactly when `write` is held beside a requirement on
`append`.** -/
theorem close_controls :
    close ⟨{write}, {append}⟩ = ⟨{write}, {append, write}⟩ ∧
      close ticketedRoot = ticketedRoot := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The rule now refuses the free child, and accepts a child that adds a requirement.** -/
theorem serviceEdge_controls :
    ServiceEdge ticketedRoot ticketedRoot ∧ ¬ ServiceEdge ticketedRoot freeChild ∧
      ServiceEdge ⟨{read, append}, ∅⟩ ⟨{append}, {append}⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **A write batch beside an append requirement needs a ticket under the rule now**: the closed
policy adds no row without one, while the unclosed policy does
(`write_bypasses_append_requirement`). -/
theorem closed_write_batch_needs_ticket :
    ¬ AddsRowFree (close ⟨{write}, {append}⟩) ∧ AddsRowFree ⟨{write}, {append}⟩ :=
  ⟨closed_no_free_add (close_closed _) (requires_subset_close _ (by decide)),
    write_bypasses_append_requirement.2⟩

/-- **The lineage theorems apply**: the root needs a ticket per append beside `write`, its child
holds `write` with the same requirement, and neither adds a row without a ticket. -/
theorem service_lineage_instance :
    List.IsChain ServiceEdge [⟨{write}, {append}⟩, ⟨{write}, {append}⟩] ∧
      ∀ g ∈ [(⟨{write}, {append}⟩ : Policy)], ¬ AddsRowFree (close g) := by
  have chain : List.IsChain ServiceEdge [⟨{write}, {append}⟩, ⟨{write}, {append}⟩] := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    decide
  exact ⟨chain, serviceChain_no_free_add (by decide) chain⟩

/-- A ticketed append through the ticketed root is permitted; a ticketless write batch through the
closed write policy is not. -/
theorem addPermitted_controls :
    AddPermitted (close ticketedRoot) false true ∧
      ¬ AddPermitted (close ⟨{write}, {append}⟩) true false := by
  refine ⟨?_, ?_⟩
  · simp only [AddPermitted, if_true, Bool.false_eq_true, if_false]
    decide
  · simp only [AddPermitted, Bool.false_eq_true, if_false, if_true]
    decide

/-- Requiring tickets for `write` too closes the requirements; requiring them for `append` alone
beside `write` does not, and lets a row be added without a ticket. -/
theorem requirementsClosed_controls :
    RequirementsClosed ⟨{write}, {append, write}⟩ ∧ ¬ RequirementsClosed ⟨{write}, {append}⟩ ∧
      ¬ AddsRowFree ⟨{write}, {append, write}⟩ := by
  refine ⟨fun _ _ => by decide, fun closed => ?_, closed_no_free_add (fun _ _ => by decide) (by decide)⟩
  have := closed (by decide) (by decide)
  revert this
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.ServiceGrants
