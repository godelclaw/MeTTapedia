import Mettapedia.Languages.MeTTa.Seal.Capability
import Mettapedia.Languages.MeTTa.Seal.Observation
import Mathlib.Data.List.Forall2

/-!
# Identity-bearing native seals over the existing capability calculus

This reference contract enriches the existing primitive values with a fresh
capsule identity. Its primitive actions are the original `Seal.Action`, not a
second authority language. Erasure forgets capsule identities and commutes with
every primitive execution. The existing rights and authentic-construction laws
therefore remain applicable. This is a one-way authority refinement: erasure
does not preserve the new identity observer.

One configuration is one allocation scope. Its counter is unbounded; no
operation resets it. Importing references from another native allocation scope
requires a separate owned-reference protocol. There is no second handle or
capability registry here, and no claim about native memory or foreign code.
Lean constructors and derived `Repr` are metatheory/debugging tools, not client
operations. A native client gets the opaque primitive and observer interfaces.

`D` is the retained data descriptor. A native realization must retain the term
and binding owners represented by that descriptor. Sealing does not evaluate,
substitute, freshen, or freeze a referenced mutable space/state. A proof kernel
must use stable logical judgments and validated context snapshots; an opaque
box alone does not make live solver bindings into a stable certified claim.

Equality, reference patterns and space removal share `Value.key`. Display
redacts identity. The wire codec checks a captured datum-admission predicate in
both directions. That predicate must reject embedded native/state/foreign
references; a theorem cannot inspect an arbitrary descriptor `D`. The wire
grammar itself has no capability, nonce or capsule constructors. The optional
operation policy is checked separately at each call.
Copyable seal facets are not linear cancel/consume rights. Key locks recognize
actual held local nonce references and an issuer policy, not passwords or
encryption. Surface misuse faults refine to primitive refusal but remain
distinct from an ordinary wrong-brand/non-box recognition miss.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal.NativeContract

variable {D : Type}

/-- Native values retain the original authority-bearing structure. Only a
capsule adds an allocation identity; its payload remains recursively retained. -/
inductive Value (D : Type) where
  | data (datum : D)
  | nonce (identity : Nat)
  | pair (left right : Value D)
  | cap (brand : Brand) (rights : Rights)
  | box (identity : Nat) (brand : Brand) (payload : Value D)
  deriving Repr

namespace Value

/-- Forgetting identity is for the authority proof, never native equality. -/
def erase : Value D → Seal.Val D
  | .data datum => .data datum
  | .nonce identity => .nonce identity
  | .pair left right => .pair left.erase right.erase
  | .cap brand rights => .cap brand rights
  | .box _ brand payload => .box brand payload.erase

/-- The common comparison key: capsule contents and brands are not compared. -/
inductive Key (D : Type) where
  | data (datum : D)
  | nonce (identity : Nat)
  | pair (left right : Key D)
  | cap (brand : Brand) (rights : Rights)
  | box (identity : Nat)
  deriving DecidableEq, Repr

def key : Value D → Key D
  | .data datum => .data datum
  | .nonce identity => .nonce identity
  | .pair left right => .pair left.key right.key
  | .cap brand rights => .cap brand rights
  | .box identity _ _ => .box identity

def Same (left right : Value D) : Prop := left.key = right.key

instance [DecidableEq D] (left right : Value D) : Decidable (left.Same right) :=
  inferInstanceAs (Decidable (left.key = right.key))

theorem same_equivalence : Equivalence (Same (D := D)) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

@[simp] theorem same_boxes (i j : Nat) (b c : Brand) (v w : Value D) :
    (box i b v).Same (box j c w) ↔ i = j := by simp [Same, key]

/-- Explicit substitution traverses ordinary structure and treats authority
leaves atomically. It never substitutes inside an unopened capsule. -/
def mapData (transform : D → D) : Value D → Value D
  | .data datum => .data (transform datum)
  | .pair left right => .pair (left.mapData transform) (right.mapData transform)
  | .nonce identity => .nonce identity
  | .cap brand rights => .cap brand rights
  | .box identity brand payload => .box identity brand payload

/-- All capsule identities are below the next allocation counter, including
identities retained inside unopened payloads. -/
def Bounded (limit : Nat) : Value D → Prop
  | .data _ => True
  | .nonce _ => True
  | .pair left right => left.Bounded limit ∧ right.Bounded limit
  | .cap _ _ => True
  | .box identity _ payload => identity < limit ∧ payload.Bounded limit

theorem Bounded.mono {value : Value D} {small large : Nat}
    (bound : value.Bounded small) (increase : small ≤ large) : value.Bounded large := by
  induction value with
  | data => trivial
  | nonce => trivial
  | cap => trivial
  | pair left right ihLeft ihRight => exact ⟨ihLeft bound.1, ihRight bound.2⟩
  | box identity brand payload ih => exact ⟨lt_of_lt_of_le bound.1 increase, ih bound.2⟩

/-- An actual capsule occurrence, including occurrences inside ordinary pairs
and unopened payloads. This is a derived relation, not an allocation registry. -/
inductive Contains (identity : Nat) (brand : Brand) (payload : Value D) : Value D → Prop where
  | here : Contains identity brand payload (.box identity brand payload)
  | left {first second : Value D} : Contains identity brand payload first →
      Contains identity brand payload (.pair first second)
  | right {first second : Value D} : Contains identity brand payload second →
      Contains identity brand payload (.pair first second)
  | inside {outer : Nat} {outerBrand : Brand} {body : Value D} :
      Contains identity brand payload body →
      Contains identity brand payload (.box outer outerBrand body)

theorem Contains.bound {identity limit : Nat} {brand : Brand} {payload value : Value D}
    (occurrence : Contains identity brand payload value) (bounded : value.Bounded limit) :
    identity < limit := by
  induction occurrence with
  | here => exact bounded.1
  | left _ ih => exact ih bounded.1
  | right _ ih => exact ih bounded.2
  | inside _ ih => exact ih bounded.2

theorem bounded_of_contains (value : Value D) (limit : Nat)
    (bounded : ∀ identity brand payload, Contains identity brand payload value → identity < limit) :
    value.Bounded limit := by
  induction value with
  | data => trivial
  | nonce => trivial
  | cap => trivial
  | pair left right ihLeft ihRight =>
      exact ⟨ihLeft (fun i b p occurrence => bounded i b p (.left occurrence)),
        ihRight (fun i b p occurrence => bounded i b p (.right occurrence))⟩
  | box identity brand payload ih =>
      exact ⟨bounded identity brand payload .here,
        ih (fun i b p occurrence => bounded i b p (.inside occurrence))⟩

end Value

structure Config (D : Type) where
  holds : Nat → List (Value D)
  nextBrand : Brand
  nextNonce : Nonce
  nextCapsule : Nat

namespace Config

def erase (c : Config D) : Seal.Config D :=
  ⟨fun principal => (c.holds principal).map Value.erase, c.nextBrand, c.nextNonce⟩

def held (c : Config D) (principal index : Nat) : Option (Value D) :=
  (c.holds principal)[index]?

def give (c : Config D) (receiver : Nat) (value : Value D) : Config D :=
  { c with holds := Function.update c.holds receiver (c.holds receiver ++ [value]) }

theorem erase_held (c : Config D) (principal index : Nat) :
    c.erase.held principal index = (c.held principal index).map Value.erase := by
  simp [erase, held, Seal.Config.held, List.getElem?_map]

theorem erase_give (c : Config D) (receiver : Nat) (value : Value D) :
    (c.give receiver value).erase = c.erase.give receiver value.erase := by
  unfold give erase Seal.Config.give
  congr 1
  funext principal
  by_cases same : principal = receiver
  · subst principal; simp
  · simp [same]

theorem held_give_last (c : Config D) (receiver : Nat) (value : Value D) :
    (c.give receiver value).held receiver (c.holds receiver).length = some value := by
  simp [give, held]

theorem held_give_stable {c : Config D} {receiver principal index : Nat} {value old : Value D}
    (found : c.held principal index = some old) :
    (c.give receiver value).held principal index = some old := by
  unfold give held at *
  by_cases same : principal = receiver
  · subst principal
    simp only [Function.update_self]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  · simpa [Function.update_of_ne same] using found

def Bounded (c : Config D) : Prop :=
  ∀ principal value, value ∈ c.holds principal → value.Bounded c.nextCapsule

def empty : Config D := ⟨fun _ => [], 0, 0, 0⟩

theorem empty_bounded : (empty : Config D).Bounded := by simp [Bounded, empty]

/-- This occurrence is retained somewhere in the actual holdings. -/
def Issued (c : Config D) (identity : Nat) (brand : Brand) (payload : Value D) : Prop :=
  ∃ principal value, value ∈ c.holds principal ∧ Value.Contains identity brand payload value

/-- An identity denotes one brand and payload throughout the retained graph.
This is stronger than the freshness bound on counters. -/
def Coherent (c : Config D) : Prop :=
  ∀ identity firstBrand secondBrand firstPayload secondPayload,
    c.Issued identity firstBrand firstPayload → c.Issued identity secondBrand secondPayload →
      firstBrand = secondBrand ∧ firstPayload = secondPayload

def WellFormed (c : Config D) : Prop := c.Bounded ∧ c.Coherent

theorem empty_wellFormed : (empty : Config D).WellFormed := by
  refine ⟨empty_bounded, ?_⟩
  rintro identity firstBrand secondBrand firstPayload secondPayload ⟨p, v, member, _⟩ _
  cases member

theorem issued_of_held {c : Config D} {principal index identity brand : Nat}
    {value payload : Value D} (held : c.held principal index = some value)
    (occurrence : Value.Contains identity brand payload value) : c.Issued identity brand payload :=
  ⟨principal, value, List.mem_of_getElem? held, occurrence⟩

theorem Issued.bound {c : Config D} (bounded : c.Bounded)
    {identity brand : Nat} {payload : Value D} (issued : c.Issued identity brand payload) :
    identity < c.nextCapsule := by
  obtain ⟨principal, value, member, occurrence⟩ := issued
  exact occurrence.bound (bounded principal value member)

theorem mem_give {c : Config D} {receiver principal : Nat} {value candidate : Value D} :
    candidate ∈ (c.give receiver value).holds principal ↔
      candidate ∈ c.holds principal ∨ (principal = receiver ∧ candidate = value) := by
  unfold give
  by_cases same : principal = receiver
  · subst principal; simp
  · simp [same]

theorem issued_give (c : Config D) (receiver : Nat) (value : Value D)
    (identity brand : Nat) (payload : Value D) :
    (c.give receiver value).Issued identity brand payload ↔
      c.Issued identity brand payload ∨ Value.Contains identity brand payload value := by
  constructor
  · rintro ⟨principal, candidate, held, occurrence⟩
    rcases mem_give.mp held with old | ⟨_, rfl⟩
    · exact Or.inl ⟨principal, candidate, old, occurrence⟩
    · exact Or.inr occurrence
  · rintro (⟨principal, candidate, member, occurrence⟩ | occurrence)
    · exact ⟨principal, candidate, mem_give.mpr (Or.inl member), occurrence⟩
    · exact ⟨receiver, value, mem_give.mpr (Or.inr ⟨rfl, rfl⟩), occurrence⟩

end Config

/-- Independent native execution of the existing primitive instruction syntax. -/
def output (c : Config D) (principal : Nat) : Seal.Action D → Option (Nat × Value D)
  | .newSeal => some (principal, .cap c.nextBrand Rights.both)
  | .newNonce => some (principal, .nonce c.nextNonce)
  | .make datum => some (principal, .data datum)
  | .pair left right => do
      let a ← c.held principal left
      let b ← c.held principal right
      some (principal, .pair a b)
  | .fst index => match c.held principal index with
      | some (.pair left _) => some (principal, left)
      | _ => none
  | .snd index => match c.held principal index with
      | some (.pair _ right) => some (principal, right)
      | _ => none
  | .attenuate index wanted => match c.held principal index with
      | some (.cap brand rights) => some (principal, .cap brand (rights.meet wanted))
      | _ => none
  | .sealBox capability content => match c.held principal capability, c.held principal content with
      | some (.cap brand rights), some payload =>
          if rights.sealRight = true then some (principal, .box c.nextCapsule brand payload) else none
      | _, _ => none
  | .unsealBox capability capsule => match c.held principal capability, c.held principal capsule with
      | some (.cap brand rights), some (.box _ actual payload) =>
          if rights.unsealRight = true ∧ brand = actual then some (principal, payload) else none
      | _, _ => none
  | .send index receiver => (c.held principal index).map fun value => (receiver, value)

def advance (c : Config D) : Seal.Action D → Config D
  | .newSeal => { c with nextBrand := c.nextBrand + 1 }
  | .newNonce => { c with nextNonce := c.nextNonce + 1 }
  | .sealBox _ _ => { c with nextCapsule := c.nextCapsule + 1 }
  | _ => c

def run (c : Config D) (principal : Nat) (action : Seal.Action D) : Option (Config D) :=
  (output c principal action).map fun (receiver, value) => (advance c action).give receiver value

theorem run_of_output {c : Config D} {principal receiver : Nat} {action : Seal.Action D}
    {value : Value D} (produced : output c principal action = some (receiver, value)) :
    run c principal action = some ((advance c action).give receiver value) := by
  simp [run, produced]

theorem advance_holds (c : Config D) (action : Seal.Action D) :
    (advance c action).holds = c.holds := by cases action <;> rfl

theorem advance_counter (c : Config D) (action : Seal.Action D) :
    c.nextCapsule ≤ (advance c action).nextCapsule := by cases action <;> simp [advance]

/-- Every retained capsule in a primitive output is an old occurrence or the
one freshly allocated root of this particular seal instruction. -/
theorem output_capsule_origin {c : Config D} {principal receiver identity brand : Nat}
    {action : Seal.Action D} {value payload : Value D}
    (produced : output c principal action = some (receiver, value))
    (occurrence : Value.Contains identity brand payload value) :
    c.Issued identity brand payload ∨
      ∃ capability content, action = .sealBox capability content ∧
        identity = c.nextCapsule ∧ value = .box identity brand payload := by
  cases action with
  | newSeal => cases Option.some.inj produced; cases occurrence
  | newNonce => cases Option.some.inj produced; cases occurrence
  | make datum => cases Option.some.inj produced; cases occurrence
  | pair first second =>
      cases a : c.held principal first with
      | none => simp [output, a] at produced
      | some left =>
          cases b : c.held principal second with
          | none => simp [output, a, b] at produced
          | some right =>
              simp only [output, a, b, bind, Option.bind, Option.some.injEq] at produced
              cases produced
              cases occurrence with
              | left child => exact Or.inl (Config.issued_of_held a child)
              | right child => exact Or.inl (Config.issued_of_held b child)
  | fst index =>
      cases held : c.held principal index with
      | none => simp [output, held] at produced
      | some original =>
          cases original <;> simp only [output, held] at produced
          all_goals try contradiction
          cases Option.some.inj produced
          exact Or.inl (Config.issued_of_held held (.left occurrence))
  | snd index =>
      cases held : c.held principal index with
      | none => simp [output, held] at produced
      | some original =>
          cases original <;> simp only [output, held] at produced
          all_goals try contradiction
          cases Option.some.inj produced
          exact Or.inl (Config.issued_of_held held (.right occurrence))
  | attenuate index wanted =>
      cases held : c.held principal index with
      | none => simp [output, held] at produced
      | some original =>
          cases original <;> simp only [output, held] at produced
          all_goals try contradiction
          cases Option.some.inj produced
          cases occurrence
  | sealBox capability content =>
      cases cap : c.held principal capability with
      | none => simp [output, cap] at produced
      | some facet =>
          cases facet <;> simp only [output, cap] at produced
          all_goals try contradiction
          cases body : c.held principal content with
          | none => simp [body] at produced
          | some retained =>
              simp only [body] at produced
              split_ifs at produced
              · cases Option.some.inj produced
                cases occurrence with
                | here => exact Or.inr ⟨capability, content, rfl, rfl, rfl⟩
                | inside child => exact Or.inl (Config.issued_of_held body child)
  | unsealBox capability capsule =>
      cases cap : c.held principal capability with
      | none => simp [output, cap] at produced
      | some facet =>
          cases facet <;> simp only [output, cap] at produced
          all_goals try contradiction
          cases boxed : c.held principal capsule with
          | none => simp [boxed] at produced
          | some original =>
              cases original <;> simp only [boxed] at produced
              all_goals try contradiction
              split_ifs at produced
              · cases Option.some.inj produced
                exact Or.inl (Config.issued_of_held boxed (.inside occurrence))
  | send index destination =>
      cases held : c.held principal index with
      | none => simp [output, held] at produced
      | some original =>
          simp only [output, held, Option.map_some, Option.some.injEq] at produced
          cases produced
          exact Or.inl (Config.issued_of_held held occurrence)

theorem output_bounded {c : Config D} (bounded : c.Bounded)
    {principal receiver : Nat} {action : Seal.Action D} {value : Value D}
    (produced : output c principal action = some (receiver, value)) :
    value.Bounded (advance c action).nextCapsule := by
  apply Value.bounded_of_contains
  intro identity brand payload occurrence
  rcases output_capsule_origin produced occurrence with old | fresh
  · exact lt_of_lt_of_le (old.bound bounded) (advance_counter c action)
  · obtain ⟨capability, content, rfl, rfl, _⟩ := fresh
    simp [advance]

theorem run_wellFormed {c next : Config D} (wellFormed : c.WellFormed)
    {principal : Nat} {action : Seal.Action D} (ran : run c principal action = some next) :
    next.WellFormed := by
  unfold run at ran
  obtain ⟨⟨receiver, value⟩, produced, rfl⟩ := Option.map_eq_some_iff.mp ran
  have oldIssued : ∀ i b p, (advance c action).Issued i b p ↔ c.Issued i b p := by
    intro i b p
    simp only [Config.Issued, advance_holds]
  refine ⟨?_, ?_⟩
  · intro owner candidate member
    rcases Config.mem_give.mp member with old | ⟨_, rfl⟩
    · have prior : candidate ∈ c.holds owner := by simpa only [advance_holds] using old
      exact (wellFormed.1 owner candidate prior).mono (advance_counter c action)
    · exact output_bounded wellFormed.1 produced
  · intro identity firstBrand secondBrand firstPayload secondPayload first second
    have origin : ∀ b p, ((advance c action).give receiver value).Issued identity b p →
        c.Issued identity b p ∨
          (identity = c.nextCapsule ∧ value = .box identity b p) := by
      intro b p issued
      rcases (Config.issued_give _ _ _ _ _ _).mp issued with old | new
      · exact Or.inl ((oldIssued _ _ _).mp old)
      · rcases output_capsule_origin produced new with old | fresh
        · exact Or.inl old
        · obtain ⟨_, _, _, identityAt, valueAt⟩ := fresh
          exact Or.inr ⟨identityAt, valueAt⟩
    rcases origin _ _ first with oldFirst | ⟨fresh, firstValue⟩
    · rcases origin _ _ second with oldSecond | ⟨fresh, _⟩
      · exact wellFormed.2 _ _ _ _ _ oldFirst oldSecond
      · exact False.elim (Nat.ne_of_lt (oldFirst.bound wellFormed.1) fresh)
    · rcases origin _ _ second with oldSecond | ⟨_, secondValue⟩
      · exact False.elim (Nat.ne_of_lt (oldSecond.bound wellFormed.1) fresh)
      · have equal := firstValue.symm.trans secondValue
        cases equal
        exact ⟨rfl, rfl⟩

theorem output_erases (c : Config D) (principal : Nat) (action : Seal.Action D) :
    (output c principal action).map (fun (receiver, value) => (receiver, value.erase)) =
      action.output c.erase principal := by
  cases action with
  | newSeal => rfl
  | newNonce => rfl
  | make => rfl
  | pair left right =>
      simp only [output, Seal.Action.output, Config.erase_held]
      cases c.held principal left <;> cases c.held principal right <;> rfl
  | fst index =>
      simp only [output, Seal.Action.output, Config.erase_held]
      cases c.held principal index with
      | none => rfl
      | some value => cases value <;> rfl
  | snd index =>
      simp only [output, Seal.Action.output, Config.erase_held]
      cases c.held principal index with
      | none => rfl
      | some value => cases value <;> rfl
  | attenuate index wanted =>
      simp only [output, Seal.Action.output, Config.erase_held]
      cases c.held principal index with
      | none => rfl
      | some value => cases value <;> rfl
  | sealBox capability content =>
      simp only [output, Seal.Action.output, Config.erase_held]
      cases c.held principal capability with
      | none => rfl
      | some value =>
          cases value <;> cases c.held principal content <;>
            simp [Value.erase]
  | unsealBox capability capsule =>
      simp only [output, Seal.Action.output, Config.erase_held]
      cases c.held principal capability with
      | none => rfl
      | some value =>
          cases value <;> cases c.held principal capsule with
          | none => rfl
          | some value => cases value <;> simp [Value.erase]
  | send index receiver =>
      simp only [output, Seal.Action.output, Config.erase_held]
      cases c.held principal index <;> rfl

theorem advance_erases (c : Config D) (action : Seal.Action D) :
    (advance c action).erase = action.advance c.erase := by cases action <;> rfl

theorem run_erases (c : Config D) (principal : Nat) (action : Seal.Action D) :
    (run c principal action).map Config.erase = action.run c.erase principal := by
  have outputs := output_erases c principal action
  cases found : output c principal action with
  | none => simp [found] at outputs; simp [run, found, Seal.Action.run, outputs]
  | some result =>
      rcases result with ⟨receiver, value⟩
      simp only [found, Option.map_some] at outputs
      simp [run, found, Seal.Action.run, ← outputs, Config.erase_give, advance_erases]

/-- Actual primitive output plus a separate current operation authorization.
The policy consumes the actual state and instruction, not a printed token. -/
def perform (allows : Nat → Seal.Action D → Seal.Config D → Bool)
    (c : Config D) (principal : Nat) (action : Seal.Action D) : Option (Config D) :=
  if allows principal action c.erase = true then run c principal action else none

theorem perform_original_step (allows : Nat → Seal.Action D → Seal.Config D → Bool)
    (c next : Config D) (principal : Nat) (action : Seal.Action D)
    (performed : perform allows c principal action = some next) :
    Seal.Step (fun p a state => allows p a state = true) c.erase next.erase := by
  unfold perform at performed
  split at performed
  · rename_i allowed
    refine ⟨principal, action, allowed, ?_⟩
    rw [← run_erases, performed]
    rfl
  · cases performed

/-- Native traces use the existing policy over the erased actual state. -/
def Step (policy : Seal.Policy D) (c next : Config D) : Prop :=
  ∃ principal action, policy principal action c.erase ∧ run c principal action = some next

abbrev Reach (policy : Seal.Policy D) := Relation.ReflTransGen (Step policy)

theorem Step.original {policy : Seal.Policy D} {c next : Config D} (step : Step policy c next) :
    Seal.Step policy c.erase next.erase := by
  obtain ⟨principal, action, allowed, ran⟩ := step
  refine ⟨principal, action, allowed, ?_⟩
  rw [← run_erases, ran]
  rfl

theorem Reach.original {policy : Seal.Policy D} {c next : Config D} (reached : Reach policy c next) :
    Seal.Reach policy c.erase next.erase := by
  induction reached with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.original

theorem Reach.wellFormed {policy : Seal.Policy D} {c next : Config D}
    (reached : Reach policy c next) (initial : c.WellFormed) : next.WellFormed := by
  induction reached with
  | refl => exact initial
  | tail _ step ih =>
      obtain ⟨principal, action, _, ran⟩ := step
      exact run_wellFormed ih ran

/-- No arbitrary malformed origin is accepted for identity substitutivity.
Starting empty, every reachable graph has coherent nested capsule identities. -/
theorem Reach.empty_coherent {policy : Seal.Policy D} {next : Config D}
    (reached : Reach policy Config.empty next) : next.Coherent :=
  (reached.wellFormed Config.empty_wellFormed).2

/-- Equality by capsule identity is substitutive for its actual brand/payload
on reached well-formed configurations, including retained nested occurrences. -/
theorem same_capsules_same_contents {c : Config D} (coherent : c.Coherent)
    {first second firstBrand secondBrand : Nat} {firstPayload secondPayload : Value D}
    (heldFirst : c.Issued first firstBrand firstPayload)
    (heldSecond : c.Issued second secondBrand secondPayload)
    (same : (Value.box first firstBrand firstPayload).Same (.box second secondBrand secondPayload)) :
    firstBrand = secondBrand ∧ firstPayload = secondPayload := by
  have identity := (Value.same_boxes _ _ _ _ _ _).mp same
  subst second
  exact coherent _ _ _ _ _ heldFirst heldSecond

/-- Identity enrichment neither grants a new sealing right nor upgrades a
copyable facet; this is the existing authority theorem on the actual run. -/
theorem no_new_right {policy : Seal.Policy D} {c next : Config D} {brand : Brand}
    (reached : Reach policy c next) (old : brand < c.nextBrand)
    {right : Rights → Bool} (selector : Seal.RightSel right)
    (held : next.erase.anyCap brand right) : c.erase.anyCap brand right := by
  exact Seal.anyCap_of_reach selector reached.original old held

section LCF

variable {J : Type} (rules : List J → J → Prop)

/-- Native capsule identities do not replace the kernel policy or its original
theory scope. This theorem uses precisely the original sealed-kernel invariant. -/
theorem lcf_original {kernel brand identity principal : Nat} {c next : Config J}
    {judgment : J} (initial : Seal.KernelStart rules kernel brand c.erase)
    (reached : Reach (Seal.kernelPolicy rules kernel brand) c next)
    (held : Value.box identity brand (.data judgment) ∈ next.holds principal) :
    Mettapedia.Logic.Derives rules judgment := by
  have sourceHeld : Seal.Val.box brand (.data judgment) ∈ next.erase.holds principal :=
    List.mem_map.mpr ⟨_, held, rfl⟩
  obtain ⟨actual, same, derived⟩ := Seal.lcf_sound rules initial reached.original sourceHeld
  cases same
  exact derived

end LCF

/-- The portable syntax has no authority constructors. A host data codec remains
responsible for the ordinary datum format; it cannot add these constructors. -/
inductive Wire (D : Type) where
  | data (datum : D)
  | pair (left right : Wire D)
  deriving DecidableEq, Repr

def decode (admitDatum : D → Bool) : Wire D → Option (Value D)
  | .data datum => if admitDatum datum = true then some (.data datum) else none
  | .pair left right => match decode admitDatum left, decode admitDatum right with
      | some a, some b => some (.pair a b)
      | _, _ => none

def serialize (admitDatum : D → Bool) : Value D → Option (Wire D)
  | .data datum => if admitDatum datum = true then some (.data datum) else none
  | .pair left right => match serialize admitDatum left, serialize admitDatum right with
      | some a, some b => some (.pair a b)
      | _, _ => none
  | .nonce _ => none
  | .cap _ _ => none
  | .box _ _ _ => none

def Portable (admitDatum : D → Bool) : Value D → Prop
  | .data datum => admitDatum datum = true
  | .pair left right => Portable admitDatum left ∧ Portable admitDatum right
  | _ => False

theorem decoded_portable (admitDatum : D → Bool) (wire : Wire D) (value : Value D)
    (decoded : decode admitDatum wire = some value) : Portable admitDatum value := by
  induction wire generalizing value with
  | data datum =>
      simp only [decode] at decoded
      split at decoded
      · rename_i admitted
        cases Option.some.inj decoded
        exact admitted
      · cases decoded
  | pair left right ihLeft ihRight =>
      cases first : decode admitDatum left with
      | none => simp [decode, first] at decoded
      | some a =>
          cases second : decode admitDatum right with
          | none => simp [decode, first, second] at decoded
          | some b =>
              simp only [decode, first, second, Option.some.injEq] at decoded
              cases decoded
              exact ⟨ihLeft _ first, ihRight _ second⟩

theorem decode_serialized (admitDatum : D → Bool) (value : Value D) (wire : Wire D)
    (encoded : serialize admitDatum value = some wire) : decode admitDatum wire = some value := by
  induction value generalizing wire with
  | data datum =>
      simp only [serialize] at encoded
      split at encoded
      · rename_i admitted
        cases Option.some.inj encoded
        simp [decode, admitted]
      · cases encoded
  | pair left right ihLeft ihRight =>
      cases first : serialize admitDatum left with
      | none => simp [serialize, first] at encoded
      | some a =>
          cases second : serialize admitDatum right with
          | none => simp [serialize, first, second] at encoded
          | some b =>
              simp only [serialize, first, second, Option.some.injEq] at encoded
              cases encoded
              simp [decode, ihLeft _ first, ihRight _ second]
  | nonce => cases encoded
  | cap => cases encoded
  | box => cases encoded

/-- This theorem concerns the explicit `Value` authority constructors. The
additional datum predicate is the host codec's separate embedded-reference
boundary, and is retained by `decoded_portable`. -/
theorem Portable.no_authority {admitDatum : D → Bool} {value : Value D}
    (portable : Portable admitDatum value) (brand : Brand) (right : Rights → Bool) :
    ¬ value.erase.hasCap brand right := by
  induction value with
  | data => simp [Value.erase]
  | pair left right ihLeft ihRight =>
      simp [Value.erase, ihLeft portable.1, ihRight portable.2]
  | nonce => cases portable
  | cap => cases portable
  | box => cases portable

/-- A nickname is public metadata. The print observer uses J's redaction and
does not publish capsule identity, nonce counters or facet brand numbers. -/
def display (printData : D → String) (nickname : Brand → String) : Value D → String
  | .data datum => printData datum
  | .nonce _ => "(Key)"
  | .pair left right => "(" ++ display printData nickname left ++ " " ++ display printData nickname right ++ ")"
  | .cap brand rights =>
      if rights.sealRight && rights.unsealRight then "(Seal " ++ nickname brand ++ ")"
      else if rights.sealRight then "(Sealer " ++ nickname brand ++ ")"
      else if rights.unsealRight then "(Unsealer " ++ nickname brand ++ ")"
      else "(SealFacet " ++ nickname brand ++ ")"
  | .box _ brand _ => "(Sealed " ++ nickname brand ++ ")"

/-- A bridge into J's opaque-handle observer. This is a mathematical view, not
a numeric-handle native API. Applying `Shown.erase` is the printing observer. -/
def capsuleView (nickname : Brand → String) : Value D → Option Seal.Shown
  | .box identity brand _ => some (.boxed (nickname brand) identity)
  | _ => none

theorem capsule_print_view (nickname : Brand → String) (identity brand : Nat) (payload : Value D) :
    (capsuleView nickname (.box identity brand payload)).map Seal.Shown.erase =
      some (.boxed (nickname brand) 0) := rfl

/-- The store keeps occurrence order. Removing a reference removes one matching
occurrence, using exactly the same relation as equality and reference matching. -/
def removeFirst [DecidableEq D] (needle : Value D) : List (Value D) → List (Value D)
  | [] => []
  | value :: rest => if value.Same needle then rest else value :: removeFirst needle rest

theorem removeFirst_keys [DecidableEq D] (needle : Value D) (values : List (Value D)) :
    (removeFirst needle values).map Value.key = (values.map Value.key).erase needle.key := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      by_cases same : value.Same needle
      · change value.key = needle.key at same
        simp [removeFirst, Value.Same, same]
      · change value.key ≠ needle.key at same
        simp [removeFirst, Value.Same, same, ih]

/-- A quoted atom retains its actual value, rather than reconstructing it from
display or wire data. This wrapper is a host contract, not a dialect evaluator. -/
structure Quoted (D : Type) where
  retained : Value D

def quote (value : Value D) : Quoted D := ⟨value⟩
def unquote (quoted : Quoted D) : Value D := quoted.retained

/-- Source patterns can name a held reference, not a written capsule identity.
Pair patterns cannot inspect the representation of an opaque leaf. -/
inductive Pattern (D : Type) where
  | bind (slot : Nat)
  | datum (value : D)
  | pair (left right : Pattern D)
  | reference (heldIndex : Nat)
  deriving Repr

def matchPattern [DecidableEq D] (c : Config D) (principal : Nat) :
    Pattern D → Value D → List (Nat × Value D) → Option (List (Nat × Value D))
  | .bind slot, value, bindings =>
      match bindings.lookup slot with
      | none => some (bindings ++ [(slot, value)])
      | some previous => if previous.Same value then some bindings else none
  | .datum expected, .data actual, bindings =>
      if expected = actual then some bindings else none
  | .pair first second, .pair left right, bindings => do
      let next ← matchPattern c principal first left bindings
      matchPattern c principal second right next
  | .reference index, value, bindings => do
      let held ← c.held principal index
      if held.Same value then some bindings else none
  | _, _, _ => none

theorem reference_uses_common_relation [DecidableEq D] (c : Config D) (principal index : Nat)
    (held value : Value D) (bindings : List (Nat × Value D))
    (found : c.held principal index = some held) :
    matchPattern c principal (.reference index) value bindings =
      if held.Same value then some bindings else none := by simp [matchPattern, found]

theorem pair_cannot_open_capsule [DecidableEq D] (c : Config D) (principal identity brand : Nat)
    (left right : Pattern D) (payload : Value D) (bindings : List (Nat × Value D)) :
    matchPattern c principal (.pair left right) (.box identity brand payload) bindings = none := rfl

inductive Fault where
  | wrongFacet
  | missingRight
  | denied
  deriving DecidableEq, Repr

inductive Reply (α : Type) where
  | value (result : α)
  | empty
  | fault (reason : Fault)
  deriving Repr

/-- The retained state is explicit even on a recognition miss or fault. -/
structure Call (D : Type) where
  state : Config D
  reply : Reply (Value D)

def execute (c : Config D) (principal : Nat) (action : Seal.Action D) : Call D :=
  match output c principal action with
  | none => ⟨c, .empty⟩
  | some (receiver, value) => ⟨(advance c action).give receiver value, .value value⟩

def Call.completed (call : Call D) : Option (Config D) :=
  match call.reply with
  | .value _ => some call.state
  | _ => none

theorem execute_run (c : Config D) (principal : Nat) (action : Seal.Action D) :
    (execute c principal action).completed = run c principal action := by
  cases produced : output c principal action with
  | none => simp [execute, run, Call.completed, produced]
  | some result =>
      rcases result with ⟨receiver, value⟩
      simp [execute, run, Call.completed, produced]

/-- `seal` takes the held payload as data and preserves all binding/owner
descriptors it contains. The wrong operation right is a misuse fault. -/
def sealCall (c : Config D) (principal capability payload : Nat) : Call D :=
  match c.held principal capability with
  | some (.cap _ rights) =>
      if rights.sealRight = true then execute c principal (.sealBox capability payload)
      else ⟨c, .fault .missingRight⟩
  | _ => ⟨c, .fault .wrongFacet⟩

/-- Wrong-brand and non-box recognition are empty results. An actual unseal
returns the retained payload verbatim, including its variable relationships. -/
def inspect (c : Config D) (principal capability capsule : Nat) : Call D :=
  match c.held principal capability with
  | some (.cap _ rights) =>
      if rights.unsealRight = true then execute c principal (.unsealBox capability capsule)
      else ⟨c, .fault .missingRight⟩
  | _ => ⟨c, .fault .wrongFacet⟩

theorem sealCall_run (c : Config D) (principal capability payload : Nat) :
    (sealCall c principal capability payload).completed = run c principal (.sealBox capability payload) := by
  cases held : c.held principal capability with
  | none => simp [sealCall, held, Call.completed, run, output]
  | some value =>
      cases value <;> simp only [sealCall, held]
      all_goals try solve | simp [Call.completed, run, output, held]
      rename_i brand rights
      by_cases allowed : rights.sealRight = true
      · simp [allowed, execute_run]
      · simp [allowed, Call.completed, run, output, held]
        cases c.held principal payload <;> simp [allowed]

theorem inspect_run (c : Config D) (principal capability capsule : Nat) :
    (inspect c principal capability capsule).completed = run c principal (.unsealBox capability capsule) := by
  cases held : c.held principal capability with
  | none => simp [inspect, held, Call.completed, run, output]
  | some value =>
      cases value <;> simp only [inspect, held]
      all_goals try solve | simp [Call.completed, run, output, held]
      rename_i brand rights
      by_cases allowed : rights.unsealRight = true
      · simp [allowed, execute_run]
      · simp [allowed, Call.completed, run, output, held]
        cases c.held principal capsule with
        | none => rfl
        | some value => cases value <;> simp [allowed]

theorem inspect_is_retained {c : Config D} {principal capability capsule identity brand : Nat}
    {rights : Rights} {payload : Value D}
    (heldCap : c.held principal capability = some (.cap brand rights))
    (heldBox : c.held principal capsule = some (.box identity brand payload))
    (right : rights.unsealRight = true) :
    inspect c principal capability capsule = ⟨c.give principal payload, .value payload⟩ := by
  simp [inspect, heldCap, right, execute, output, heldBox, advance]

theorem seal_is_fresh {c : Config D} (bounded : c.Bounded)
    {principal capability content brand : Nat} {rights : Rights} {payload : Value D}
    (heldCap : c.held principal capability = some (.cap brand rights))
    (heldData : c.held principal content = some payload) (right : rights.sealRight = true) :
    (sealCall c principal capability content).reply = .value (.box c.nextCapsule brand payload) ∧
    ∀ identity oldBrand oldPayload, c.Issued identity oldBrand oldPayload →
      ¬ (Value.box c.nextCapsule brand payload).Same (.box identity oldBrand oldPayload) := by
  refine ⟨?_, ?_⟩
  · simp [sealCall, heldCap, right, execute, output, heldData]
  · intro identity oldBrand oldPayload issued same
    have sameId := (Value.same_boxes _ _ _ _ _ _).mp same
    exact (Nat.ne_of_lt (issued.bound bounded)) sameId.symm

/-- Separate operation admission remains live even when a capability or proof
box persists. A held facet is necessary, and does not itself approve policy. -/
def invoke (allows : Nat → Seal.Action D → Seal.Config D → Bool)
    (c : Config D) (principal : Nat) (action : Seal.Action D) : Call D :=
  if allows principal action c.erase = true then
    match action with
    | .sealBox capability payload => sealCall c principal capability payload
    | .unsealBox capability capsule => inspect c principal capability capsule
    | _ => execute c principal action
  else ⟨c, .fault .denied⟩

theorem invoke_perform (allows : Nat → Seal.Action D → Seal.Config D → Bool)
    (c : Config D) (principal : Nat) (action : Seal.Action D) :
    (invoke allows c principal action).completed = perform allows c principal action := by
  unfold invoke perform
  split
  · cases action <;> simp only [sealCall_run, inspect_run, execute_run]
  · rfl

theorem invoke_original_step (allows : Nat → Seal.Action D → Seal.Config D → Bool)
    (c next : Config D) (principal : Nat) (action : Seal.Action D)
    (accepted : (invoke allows c principal action).completed = some next) :
    Seal.Step (fun p a state => allows p a state = true) c.erase next.erase :=
  perform_original_step allows c next principal action
    ((invoke_perform allows c principal action) ▸ accepted)

/-- A key-locked service keeps its unsealer private. `issuer`, `capability`
and `capsule` are trusted service parameters. The host-authenticated `caller`
offers a key from its own holdings; a guessed issuer slot is not an offer.
This inner recognizer performs no revocation check; use `invokeKeyed` for the
current policy boundary. An unsealer leaked outside the service bypasses it. -/
def inspectKeyed (c : Config D) (issuer capability capsule caller key : Nat) : Call D :=
  match c.held caller key with
  | some (.nonce actual) =>
      let opened := inspect c issuer capability capsule
      match opened.reply with
      | .value (.pair (.nonce expected) _) =>
          if actual = expected then execute opened.state issuer (.snd (c.holds issuer).length)
          else ⟨opened.state, .empty⟩
      | .value _ => ⟨opened.state, .empty⟩
      | .empty => opened
      | .fault _ => opened
  | _ => ⟨c, .empty⟩

theorem inspectKeyed_no_offer {c : Config D} {issuer capability capsule caller key : Nat}
    (absent : ∀ identity, c.held caller key ≠ some (.nonce identity)) :
    inspectKeyed c issuer capability capsule caller key = ⟨c, .empty⟩ := by
  cases found : c.held caller key with
  | none => simp [inspectKeyed, found]
  | some value =>
      cases value <;> simp only [inspectKeyed, found]
      rename_i identity
      exact False.elim (absent identity found)

theorem inspectKeyed_retained {c : Config D}
    {issuer capability capsule caller key identity brand nonce : Nat} {rights : Rights}
    {payload : Value D}
    (offered : c.held caller key = some (.nonce nonce))
    (heldCap : c.held issuer capability = some (.cap brand rights))
    (heldBox : c.held issuer capsule = some (.box identity brand (.pair (.nonce nonce) payload)))
    (right : rights.unsealRight = true) :
    inspectKeyed c issuer capability capsule caller key =
      ⟨(c.give issuer (.pair (.nonce nonce) payload)).give issuer payload, .value payload⟩ := by
  have opened := inspect_is_retained heldCap heldBox right
  simp [inspectKeyed, offered, opened, execute, output, Config.held_give_last, advance]

/-- Reuse the operation-admission hook, with the authenticated caller selecting
its captured policy family. The actual issuer, primitive request and current
source state are checked before opening. This is not a new permission algebra. -/
def invokeKeyed (allows : Nat → Nat → Seal.Action D → Seal.Config D → Bool)
    (c : Config D) (issuer capability capsule caller key : Nat) : Call D :=
  if allows caller issuer (.unsealBox capability capsule) c.erase = true then
    inspectKeyed c issuer capability capsule caller key
  else ⟨c, .fault .denied⟩

theorem invokeKeyed_denied (allows : Nat → Nat → Seal.Action D → Seal.Config D → Bool)
    (c : Config D) (issuer capability capsule caller key : Nat)
    (denied : allows caller issuer (.unsealBox capability capsule) c.erase ≠ true) :
    invokeKeyed allows c issuer capability capsule caller key = ⟨c, .fault .denied⟩ := by
  simp [invokeKeyed, denied]

theorem invokeKeyed_success_requires_current_policy
    (allows : Nat → Nat → Seal.Action D → Seal.Config D → Bool)
    (c : Config D) (issuer capability capsule caller key : Nat) (value : Value D)
    (returned : (invokeKeyed allows c issuer capability capsule caller key).reply = .value value) :
    allows caller issuer (.unsealBox capability capsule) c.erase = true ∧
      (inspectKeyed c issuer capability capsule caller key).reply = .value value := by
  unfold invokeKeyed at returned
  split at returned
  · rename_i accepted
    exact ⟨accepted, returned⟩
  · cases returned

def sealKeyed (c : Config D) (issuer capability payload key : Nat) : Call D :=
  match c.held issuer key with
  | some (.nonce _) =>
      let paired := execute c issuer (.pair key payload)
      match paired.reply with
      | .value _ => sealCall paired.state issuer capability (c.holds issuer).length
      | _ => paired
  | _ => ⟨c, .empty⟩

def program (principal : Nat) : List (Seal.Action D) → Config D → Option (Config D)
  | [], c => some c
  | action :: rest, c => do
      let next ← run c principal action
      program principal rest next

theorem program_original {principal : Nat} {actions : List (Seal.Action D)} {c next : Config D}
    (ran : program principal actions c = some next) : Reach (fun _ _ _ => True) c next := by
  induction actions generalizing c with
  | nil => cases Option.some.inj ran; exact .refl
  | cons action rest ih =>
      cases first : run c principal action with
      | none => simp [program, first] at ran
      | some middle =>
          have later : program principal rest middle = some next := by
            simpa [program, first] using ran
          exact (Relation.ReflTransGen.single ⟨principal, action, trivial, first⟩).trans (ih later)

/-- Surface creation sends the two attenuated facets to the recipient. Its
both-rights root remains with the private issuer, not in the surface result. -/
def newSealFor (c : Config D) (issuer recipient : Nat) : Option (Config D × Nat × Nat) := do
  if issuer = recipient then none else do
    let root := (c.holds issuer).length
    let next ← program issuer [.newSeal, .attenuate root Rights.sealOnly,
      .attenuate root Rights.unsealOnly, .send (root + 1) recipient,
      .send (root + 2) recipient] c
    let sealer := (c.holds recipient).length
    some (next, sealer, sealer + 1)

theorem newSealFor_wellFormed {c next : Config D} {issuer recipient sealer unsealer : Nat}
    (initial : c.WellFormed)
    (created : newSealFor c issuer recipient = some (next, sealer, unsealer)) : next.WellFormed := by
  unfold newSealFor at created
  split at created
  · cases created
  ·
    cases ran : program issuer [.newSeal, .attenuate (c.holds issuer).length Rights.sealOnly,
      .attenuate (c.holds issuer).length Rights.unsealOnly,
      .send ((c.holds issuer).length + 1) recipient,
      .send ((c.holds issuer).length + 2) recipient] c with
    | none => simp [ran] at created
    | some result =>
        simp only [ran, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at created
        obtain ⟨rfl, _, _⟩ := created
        exact (program_original ran).wellFormed initial

end Mettapedia.Languages.MeTTa.Seal.NativeContract
