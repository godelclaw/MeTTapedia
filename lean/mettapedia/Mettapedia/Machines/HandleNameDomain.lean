import Std

/-!
# Domain-relative names and native-handle authority

A transported handle contains numeric name and resource identifiers.  Its
spelling is decoded relative to the originating name domain, not whichever
domain a worker previously used.  A borrowed operation installs that domain
for decoding and restores the previous context afterward.

Decoding is not authority.  Acquisition additionally requires an owned
capability for the same domain, resource, decoded kind, and current registry
generation, together with a live entry.  Textually copied handles, wrong
owners, stale generations, and revoked entries therefore remain invalid even
when their names decode correctly.  Borrowing a domain does not create a
capability or resurrect an old one.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HandleNameDomain

universe u

variable {Domain : Type} [DecidableEq Domain]
variable {Result : Type}

/-- Numeric wire names have no domain-independent spelling. -/
structure WireHandle where
  name : Nat
  resource : Nat
  deriving DecidableEq, Repr

structure NameDomains (Domain : Type u) where
  spelling : Domain → Nat → Option String

structure DecodedHandle where
  kind : String
  resource : Nat
  deriving DecidableEq, Repr

def decode (domains : NameDomains Domain) (domain : Domain) (wire : WireHandle) :
    Option DecodedHandle :=
  (domains.spelling domain wire.name).map fun kind => ⟨kind, wire.resource⟩

/-- The worker context before and after one borrowed operation. -/
structure Context (Domain : Type u) where
  current : Domain
  deriving DecidableEq, Repr

/-- Run with the originating domain, returning the untouched previous context. -/
def withDomain (previous : Context Domain) (origin : Domain)
    (operation : Context Domain → Result) : Result × Context Domain :=
  (operation { previous with current := origin }, previous)

omit [DecidableEq Domain] in
theorem withDomain_restores (previous : Context Domain) (origin : Domain)
    (operation : Context Domain → Result) :
    (withDomain previous origin operation).2 = previous := rfl

omit [DecidableEq Domain] in
theorem withDomain_decodes_in_origin (domains : NameDomains Domain)
    (previous : Context Domain) (origin : Domain) (wire : WireHandle) :
    (withDomain previous origin fun context =>
      decode domains context.current wire).1 = decode domains origin wire := rfl

/-- Current registry entries are domain-relative as well as resource-relative. -/
structure Entry (Domain : Type u) where
  owner : Domain
  kind : String
  generation : Nat
  resource : Nat
  live : Bool
  deriving DecidableEq, Repr

structure Registry (Domain : Type u) where
  current : Domain → Nat → Option (Entry Domain)

/-- Authority is a separate, unforgeable input to this transition.  `none`
represents a merely textual copy, not an owned capability. -/
structure Capability (Domain : Type u) where
  owner : Domain
  kind : String
  resource : Nat
  generation : Nat
  deriving DecidableEq, Repr

def acquire (domains : NameDomains Domain) (registry : Registry Domain)
    (domain : Domain) (wire : WireHandle) (authority : Option (Capability Domain)) :
    Option Nat :=
  (decode domains domain wire).bind fun decoded =>
    authority.bind fun capability =>
      (registry.current domain wire.resource).bind fun entry =>
        if capability.owner = domain ∧ entry.owner = domain ∧
            capability.kind = decoded.kind ∧ entry.kind = decoded.kind ∧
            capability.resource = wire.resource ∧
            capability.generation = entry.generation ∧ entry.live = true then
          some entry.resource
        else none

/-- Any successful acquisition has a complete decoding, ownership, kind,
resource, generation, and liveness witness. -/
theorem acquire_sound (domains : NameDomains Domain) (registry : Registry Domain)
    (domain : Domain) (wire : WireHandle) (authority : Option (Capability Domain))
    {resource : Nat} (success : acquire domains registry domain wire authority = some resource) :
    ∃ decoded capability entry,
      decode domains domain wire = some decoded ∧
      authority = some capability ∧
      registry.current domain wire.resource = some entry ∧
      capability.owner = domain ∧ entry.owner = domain ∧
      capability.kind = decoded.kind ∧ entry.kind = decoded.kind ∧
      capability.resource = wire.resource ∧
      capability.generation = entry.generation ∧ entry.live = true ∧
      entry.resource = resource := by
  unfold acquire at success
  rw [Option.bind_eq_some_iff] at success
  obtain ⟨decoded, decodedFound, success⟩ := success
  rw [Option.bind_eq_some_iff] at success
  obtain ⟨capability, capabilityFound, success⟩ := success
  rw [Option.bind_eq_some_iff] at success
  obtain ⟨entry, entryFound, success⟩ := success
  split at success
  next valid =>
    cases success
    exact ⟨decoded, capability, entry, decodedFound, capabilityFound, entryFound,
      valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2.1,
      valid.2.2.2.2.2.1, valid.2.2.2.2.2.2, rfl⟩
  next invalid => contradiction

/-- Correct transport composes origin-relative decoding and authority checking
with exact restoration, whether acquisition succeeds or fails. -/
theorem transport_acquire_composes (domains : NameDomains Domain) (registry : Registry Domain)
    (previous : Context Domain) (origin : Domain) (wire : WireHandle)
    (authority : Option (Capability Domain)) :
    (withDomain previous origin fun context =>
      acquire domains registry context.current wire authority) =
        (acquire domains registry origin wire authority, previous) := rfl

/-- A domain borrow by itself supplies no owned capability. -/
theorem borrow_mints_no_authority (domains : NameDomains Domain) (registry : Registry Domain)
    (previous : Context Domain) (origin : Domain) (wire : WireHandle) :
    (withDomain previous origin fun context =>
      acquire domains registry context.current wire none).1 = none := by
  simp [withDomain, acquire]

namespace Controls

inductive TwoDomains where
  | left | right
  deriving DecidableEq, Repr

open TwoDomains

def domains : NameDomains TwoDomains where
  spelling domain name :=
    match domain, name with
    | .left, 7 => some "owned-resource"
    | .right, 7 => some "different-resource"
    | _, _ => none

/-- The same two numeric IDs have different meanings in the two domains. -/
def wire : WireHandle := ⟨7, 1⟩

def leftEntry : Entry TwoDomains := ⟨left, "owned-resource", 1, 42, true⟩
def rightEntry : Entry TwoDomains := ⟨right, "different-resource", 1, 99, true⟩

def registry : Registry TwoDomains where
  current domain resource :=
    match domain, resource with
    | .left, 1 => some leftEntry
    | .right, 1 => some rightEntry
    | _, _ => none

def leftCapability : Capability TwoDomains := ⟨left, "owned-resource", 1, 1⟩
def rightCapability : Capability TwoDomains := ⟨right, "different-resource", 1, 1⟩

theorem same_numeric_name_decodes_differently :
    decode domains left wire = some ⟨"owned-resource", 1⟩ ∧
      decode domains right wire = some ⟨"different-resource", 1⟩ := by
  exact ⟨rfl, rfl⟩

theorem correct_transport_preserves_interpretation_and_restores :
    (withDomain ⟨right⟩ left fun context =>
      acquire domains registry context.current wire (some leftCapability)) =
        (some 42, ⟨right⟩) := by
  rfl

theorem wrong_owner_refused_in_both_directions :
    acquire domains registry left wire (some rightCapability) = none ∧
      acquire domains registry right wire (some leftCapability) = none := by
  exact ⟨rfl, rfl⟩

/-- Correct text and a correct name domain are insufficient without ownership. -/
theorem copied_textual_handle_refused :
    acquire domains registry left wire none = none := by
  rfl

def revokedRegistry : Registry TwoDomains where
  current domain resource :=
    if domain = left ∧ resource = 1 then some { leftEntry with live := false } else none

theorem borrowing_does_not_resurrect_revoked_handle :
    (withDomain ⟨right⟩ left fun context =>
      acquire domains revokedRegistry context.current wire (some leftCapability)) =
        (none, ⟨right⟩) := by
  rfl

def advancedRegistry : Registry TwoDomains where
  current domain resource :=
    if domain = left ∧ resource = 1 then some { leftEntry with generation := 2 } else none

theorem stale_generation_refused_after_borrow :
    (withDomain ⟨right⟩ left fun context =>
      acquire domains advancedRegistry context.current wire (some leftCapability)) =
        (none, ⟨right⟩) := by
  rfl

theorem fresh_generation_after_stale_control_succeeds :
    acquire domains advancedRegistry left wire
      (some { leftCapability with generation := 2 }) = some 42 := by
  rfl

end Controls

#print axioms acquire_sound
#print axioms transport_acquire_composes
#print axioms borrow_mints_no_authority
#print axioms Controls.correct_transport_preserves_interpretation_and_restores
#print axioms Controls.wrong_owner_refused_in_both_directions
#print axioms Controls.copied_textual_handle_refused
#print axioms Controls.borrowing_does_not_resurrect_revoked_handle
#print axioms Controls.stale_generation_refused_after_borrow

end Mettapedia.Machines.HandleNameDomain
