import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold

/-!
# A sealing kernel must resolve its helpers in a closed environment

An LCF-style kernel seals the conclusions of its rules, and keeps the sealing
right private.  A rule may compute its conclusion by calling a helper.  In a
reflective rewriting language the helper is resolved in an equation space:
calling it returns the results of every equation for its name, as a bag.  If
that space is the live one, any program can add an equation for the helper,
and the genuine rule seals what the new equation returns.  No capability is
used and nothing but the kernel seals: the kernel's mint discipline holds
literally, and a forged theorem is minted anyway.

* **Late binding forges** (`late_bound_forgery`): for every claim there is a
  one-equation extension of a sound space under which the kernel's step mints
  it.
* **Three repairs** keep the kernel sound under every extension:
  - **a closed resolver** (`closed_sound`): the kernel resolves its helpers in
    the space captured when it was created;
  - **owned heads** (`owned_extension_resolve`, `owned_sound`): a module may add
    equations only for heads it owns or that nobody owns, and the kernel owns
    its helpers; late binding is then sound;
  - **certified installation** (`certified_sound`): the kernel may extend its
    own helpers when each new equation carries a proof that its result is
    derivable.  This is proof-carrying self-modification.

Reflection is the ability to add equations to a running program; authority is
which heads a module may extend.  The repair is that reflection be gated by
namespace authority, or that the kernel not reflect on the live space.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal.ClosedResolver

universe u v w x

/-- An equation `(head arg) = result`. -/
structure Equation (Head : Type u) (Arg : Type v) (Result : Type w) where
  head : Head
  arg : Arg
  result : Result

variable {Head : Type u} {Arg : Type v} {Result : Type w}
variable [DecidableEq Head] [DecidableEq Arg]

/-- Calling `head` on `arg` returns the results of every matching equation. -/
def resolve (space : Multiset (Equation Head Arg Result)) (head : Head) (arg : Arg) :
    Multiset Result :=
  (space.filter fun equation => equation.head = head ∧ equation.arg = arg).map Equation.result

theorem resolve_add (first second : Multiset (Equation Head Arg Result)) (head : Head) (arg : Arg) :
    resolve (first + second) head arg = resolve first head arg + resolve second head arg := by
  simp [resolve, Multiset.filter_add]

theorem resolve_singleton_self (head : Head) (arg : Arg) (result : Result) :
    resolve {⟨head, arg, result⟩} head arg = {result} := by
  rw [resolve, Multiset.filter_singleton, if_pos ⟨rfl, rfl⟩, Multiset.map_singleton]

/-- The kernel's step seals every claim its helper returns. -/
def step (space : Multiset (Equation Head Arg Result)) (helper : Head) (input : Arg) :
    Multiset Result :=
  resolve space helper input

/-- A space is sound for the helper when everything the helper returns is
derivable. -/
def Sound (derivable : Result → Prop) (space : Multiset (Equation Head Arg Result))
    (helper : Head) : Prop :=
  ∀ input, ∀ claim ∈ step space helper input, derivable claim

/-- **Late binding forges**: one added equation makes the genuine step mint any
claim at all. -/
theorem late_bound_forgery (space : Multiset (Equation Head Arg Result)) (helper : Head)
    (input : Arg) (claim : Result) :
    claim ∈ step (space + {⟨helper, input, claim⟩}) helper input := by
  rw [step, resolve_add, resolve_singleton_self]
  exact Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self claim))

/-- A forged claim makes the live kernel unsound. -/
theorem late_bound_unsound {derivable : Result → Prop} (space : Multiset (Equation Head Arg Result))
    (helper : Head) (input : Arg) {claim : Result} (forged : ¬ derivable claim) :
    ¬ Sound derivable (space + {⟨helper, input, claim⟩}) helper :=
  fun sound => forged (sound input claim (late_bound_forgery space helper input claim))

/-! ## Repair 1: a closed resolver -/

/-- The kernel's step in the space it captured, whatever the live space. -/
def closedStep (captured _live : Multiset (Equation Head Arg Result)) (helper : Head)
    (input : Arg) : Multiset Result :=
  step captured helper input

/-- **A closed resolver is sound under every extension.** -/
theorem closed_sound {derivable : Result → Prop} {captured : Multiset (Equation Head Arg Result)}
    {helper : Head} (sound : Sound derivable captured helper)
    (extension : Multiset (Equation Head Arg Result)) (input : Arg) :
    ∀ claim ∈ closedStep captured (captured + extension) helper input, derivable claim :=
  sound input

/-! ## Repair 2: owned heads -/

/-- An extension a module may add: only heads it owns or that nobody owns. -/
def Authorized {Module : Type x} (owner : Head → Option Module) (module : Module)
    (extension : Multiset (Equation Head Arg Result)) : Prop :=
  ∀ equation ∈ extension, owner equation.head = none ∨ owner equation.head = some module

/-- **An authorized extension by another module leaves the kernel's helper
unchanged.** -/
theorem owned_extension_resolve {Module : Type x} {owner : Head → Option Module}
    {kernel module : Module} (other : module ≠ kernel) {helper : Head}
    (owned : owner helper = some kernel) (space extension : Multiset (Equation Head Arg Result))
    (authorized : Authorized owner module extension) (input : Arg) :
    resolve (space + extension) helper input = resolve space helper input := by
  rw [resolve_add]
  have empty : resolve extension helper input = 0 := by
    rw [resolve, Multiset.map_eq_zero, Multiset.filter_eq_nil]
    intro equation member hit
    rcases authorized equation member with unowned | ownedByModule
    · rw [hit.1, owned] at unowned
      exact Option.some_ne_none _ unowned
    · rw [hit.1, owned, Option.some.injEq] at ownedByModule
      exact other ownedByModule.symm
  rw [empty]
  simp

/-- **With owned heads, late binding is sound** under every authorized
extension by another module. -/
theorem owned_sound {derivable : Result → Prop} {Module : Type x} {owner : Head → Option Module}
    {kernel module : Module} (other : module ≠ kernel) {helper : Head}
    (owned : owner helper = some kernel) {space : Multiset (Equation Head Arg Result)}
    (sound : Sound derivable space helper) (extension : Multiset (Equation Head Arg Result))
    (authorized : Authorized owner module extension) :
    Sound derivable (space + extension) helper := by
  intro input claim member
  rw [step, owned_extension_resolve other owned space extension authorized] at member
  exact sound input claim member

/-! ## Repair 3: certified installation -/

/-- Every new equation for the helper carries a proof that its result is
derivable. -/
def Certified (derivable : Result → Prop) (helper : Head)
    (extension : Multiset (Equation Head Arg Result)) : Prop :=
  ∀ equation ∈ extension, equation.head = helper → derivable equation.result

/-- **Proof-carrying self-modification is sound.** -/
theorem certified_sound {derivable : Result → Prop} {helper : Head}
    {space : Multiset (Equation Head Arg Result)} (sound : Sound derivable space helper)
    (extension : Multiset (Equation Head Arg Result))
    (certified : Certified derivable helper extension) :
    Sound derivable (space + extension) helper := by
  intro input claim member
  rw [step, resolve_add, Multiset.mem_add] at member
  rcases member with old | new
  · exact sound input claim old
  · obtain ⟨equation, filtered, rfl⟩ := Multiset.mem_map.1 new
    obtain ⟨member, hit⟩ := Multiset.mem_filter.1 filtered
    exact certified equation member hit.1

/-! ## Controls -/

namespace Controls

/-- Kernel claims: `A →* A` is derivable, `A →* forged` is not. -/
inductive Claim
  | reflA
  | forged
  deriving DecidableEq

/-- The derivable claims. -/
def derivable : Claim → Prop
  | .reflA => True
  | .forged => False

/-- The kernel's helper and a user's helper. -/
inductive HelperName
  | stepClaim
  | userHelper
  deriving DecidableEq

/-- The genuine space: the helper returns `A →* A`. -/
def genuine : Multiset (Equation HelperName Unit Claim) := {⟨.stepClaim, (), .reflA⟩}

theorem genuine_sound : Sound derivable genuine .stepClaim := by
  intro input claim member
  simp only [step, resolve, genuine] at member
  simp only [Multiset.filter_singleton] at member
  split_ifs at member
  · rw [Multiset.mem_map] at member
    obtain ⟨equation, inSingle, rfl⟩ := member
    rw [Multiset.mem_singleton] at inSingle
    subst inSingle
    trivial
  · simp at member

/-- **The forgery**: one equation for the kernel's helper mints `A →* forged`. -/
theorem forgery :
    Claim.forged ∈ step (genuine + {⟨.stepClaim, (), .forged⟩}) .stepClaim () ∧
      ¬ Sound derivable (genuine + {⟨.stepClaim, (), .forged⟩}) .stepClaim :=
  ⟨late_bound_forgery _ _ _ _, late_bound_unsound _ _ _ (fun h => h)⟩

/-- Owners: the kernel owns its helper. -/
def owner : HelperName → Option Bool
  | .stepClaim => some true
  | .userHelper => some false

/-- **The forging extension is not authorized for the user's module.** -/
theorem forgery_unauthorized :
    ¬ Authorized owner false ({⟨.stepClaim, (), .forged⟩} : Multiset (Equation HelperName Unit Claim)) := by
  intro authorized
  rcases authorized ⟨.stepClaim, (), .forged⟩ (Multiset.mem_singleton_self _) with
    unowned | ownedByUser
  · exact Option.some_ne_none _ unowned
  · exact Bool.noConfusion (Option.some.inj ownedByUser)

/-- The user may extend its own helper. -/
theorem user_extension_authorized :
    Authorized owner false
      ({⟨.userHelper, (), .forged⟩} : Multiset (Equation HelperName Unit Claim)) := by
  intro equation member
  rw [Multiset.mem_singleton] at member
  subst member
  exact Or.inr rfl

/-- The user's own helper may be extended, and the kernel stays sound. -/
theorem user_extension_sound :
    Sound derivable (genuine + {⟨.userHelper, (), .forged⟩}) .stepClaim :=
  owned_sound (owner := owner) (kernel := true) (module := false) (by decide) rfl genuine_sound _
    user_extension_authorized

/-- An installation for the kernel's own helper with a derivability proof. -/
theorem install_certified :
    Certified derivable .stepClaim
      ({⟨.stepClaim, (), .reflA⟩} : Multiset (Equation HelperName Unit Claim)) := by
  intro equation member _
  rw [Multiset.mem_singleton] at member
  subst member
  trivial

/-- **Certified self-modification keeps the kernel sound.** -/
theorem certified_install_sound :
    Sound derivable (genuine + {⟨.stepClaim, (), .reflA⟩}) .stepClaim :=
  certified_sound genuine_sound _ install_certified

/-- The forging equation carries no certificate. -/
theorem forgery_uncertified :
    ¬ Certified derivable .stepClaim
      ({⟨.stepClaim, (), .forged⟩} : Multiset (Equation HelperName Unit Claim)) :=
  fun certified => certified _ (Multiset.mem_singleton_self _) rfl

end Controls

end Mettapedia.Languages.MeTTa.Seal.ClosedResolver
