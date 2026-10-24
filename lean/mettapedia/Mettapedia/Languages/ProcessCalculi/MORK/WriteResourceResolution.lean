import Mettapedia.Algebra.FocusedAccess
import Mathlib.Data.List.Lex

/-!
# The MORK kernel's write resources and their resolution

An executable `(exec loc (I sources…) (O sinks…))` of the MORK kernel reads a
snapshot of the space through its sources and writes through its sinks.  Before
matching, every sink requests a write resource (`WriteResourceRequest` in
`kernel/src/sinks.rs`): a region of the trie below a byte prefix, an ACT file
by name, or a solver instance by name.  This module states what the kernel does
with those requests and why it is sound, as read in `kernel/src/sinks.rs` and
`kernel/src/space.rs` at MORK commit `ed57c671`.  The kernel's order of effects
within a firing is modelled in
`Mettapedia.Languages.ProcessCalculi.MORK.MM2MainlineProviders`.

* **A sink writes inside its region** (`constPrefix_prefix_instantiate`): a
  template's request is the constant prefix of its encoding up to the first
  variable, and every instance of the template extends it.
* **Requests join** (`pjoin`, the kernel's `WriteResourceRequest::pjoin`): two
  trie regions join to the longest common prefix, the least region containing
  both (`Mettapedia.Algebra.FocusedAccess.cone_lcp_subset_iff`); a file or a
  solver joins only with itself; different kinds do not join.
  `Subsumes c r`, read as `c.pjoin(r) == Some(c)`, is cone containment for tries
  (`subsumes_trie_iff`).
* **Resolution** (`Resolves`): the kernel maps every request to the least
  request of the same executable that subsumes it (`prefix_subsumption_resources`
  in `kernel/src/space.rs`) and opens one exclusive write zipper per resolved
  request.  **Two resolutions are equal or apart** (`resolved_eq_or_apart`): equal
  requests share one zipper, and distinct trie resolutions are incomparable
  prefixes, so their cones are disjoint and the foci below them are independent
  (`resolved_independent`).  This is the condition under which the kernel's
  unchecked exclusive zippers (`write_zipper_at_exclusive_path_unchecked`) never
  overlap.
* **The kernel's order is lexicographic and still right** (`lexLeast_resolves`):
  the kernel compares trie requests by the byte order of their prefixes, not by
  inclusion.  The candidates it compares all subsume one request, so they are
  prefixes of one path and form a chain; on a chain a proper prefix is
  lexicographically smaller (`lt_of_strict_prefix`), so the least candidate is
  the shortest.

The kernel reads its sources from a snapshot clone of the space and runs one
executable at a time, so these regions license parallel *writing* within a
firing, not parallel firings: every source requests the whole trie.  The
commuting of whole firings is
`Mettapedia.Algebra.LocatedUpdates.Transaction.serial_eq_wave`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.WriteResourceResolution

open Mettapedia.Algebra.FocusedAccess

universe u v

/-! ## Templates and their regions -/

section Templates

variable {σ : Type u} {ν : Type v}

/-- Fill the variables of a template, a sequence of constant symbols and
variables. -/
def instantiate (fill : ν → List σ) : List (σ ⊕ ν) → List σ
  | [] => []
  | .inl symbol :: rest => symbol :: instantiate fill rest
  | .inr hole :: rest => fill hole ++ instantiate fill rest

/-- The constant prefix of a template: its symbols up to the first variable. -/
def constPrefix : List (σ ⊕ ν) → List σ
  | .inl symbol :: rest => symbol :: constPrefix rest
  | _ => []

/-- **Every instance of a template extends its constant prefix.** -/
theorem constPrefix_prefix_instantiate (fill : ν → List σ) :
    ∀ template : List (σ ⊕ ν), constPrefix template <+: instantiate fill template
  | [] => List.nil_prefix
  | .inl symbol :: rest => by
      simp only [constPrefix, instantiate, List.cons_prefix_cons, true_and]
      exact constPrefix_prefix_instantiate fill rest
  | .inr _ :: _ => List.nil_prefix

end Templates

/-! ## Requests -/

/-- A write resource requested by a sink. -/
inductive Request (σ : Type u) where
  | trie (pre : List σ)
  | act (name : String)
  | solver (name : String)
  deriving DecidableEq

variable {σ : Type u} [DecidableEq σ]

/-- The kernel's join of two write requests. -/
def pjoin : Request σ → Request σ → Option (Request σ)
  | .trie first, .trie second => some (.trie (lcp first second))
  | .act first, .act second => if first = second then some (.act first) else none
  | .solver first, .solver second => if first = second then some (.solver first) else none
  | _, _ => none

/-- `candidate` subsumes `request`: their join is the candidate. -/
def Subsumes (candidate request : Request σ) : Prop :=
  pjoin candidate request = some candidate

theorem lcp_eq_left_iff (first second : List σ) : lcp first second = first ↔ first <+: second := by
  constructor
  · intro same
    rw [← same]
    exact lcp_prefix_right first second
  · intro below
    have lower : first <+: lcp first second :=
      (prefix_lcp_iff first first second).mpr ⟨List.prefix_refl first, below⟩
    exact ((lcp_prefix_left first second).eq_of_length
      (Nat.le_antisymm (lcp_prefix_left first second).length_le lower.length_le))

/-- **For tries, subsumption is cone containment.** -/
theorem subsumes_trie_iff (candidate request : List σ) :
    Subsumes (.trie candidate) (.trie request) ↔ candidate <+: request := by
  simp only [Subsumes, pjoin, Option.some.injEq, Request.trie.injEq]
  exact lcp_eq_left_iff candidate request

theorem subsumes_act_iff (candidate request : String) :
    Subsumes (σ := σ) (.act candidate) (.act request) ↔ candidate = request := by
  simp only [Subsumes, pjoin]
  split_ifs <;> simp_all

theorem subsumes_solver_iff (candidate request : String) :
    Subsumes (σ := σ) (.solver candidate) (.solver request) ↔ candidate = request := by
  simp only [Subsumes, pjoin]
  split_ifs <;> simp_all

/-- Subsumption never crosses kinds. -/
theorem subsumes_trie_left {candidate : Request σ} {request : List σ}
    (subsumes : Subsumes candidate (.trie request)) : ∃ pre, candidate = .trie pre := by
  cases candidate with
  | trie pre => exact ⟨pre, rfl⟩
  | act name => simp [Subsumes, pjoin] at subsumes
  | solver name => simp [Subsumes, pjoin] at subsumes

theorem subsumes_act_right {candidate : Request σ} {name : String}
    (subsumes : Subsumes candidate (.act name)) : candidate = .act name := by
  cases candidate with
  | trie pre => exact absurd subsumes (by simp [Subsumes, pjoin])
  | act other => rw [(subsumes_act_iff other name).mp subsumes]
  | solver other => exact absurd subsumes (by simp [Subsumes, pjoin])

theorem subsumes_solver_right {candidate : Request σ} {name : String}
    (subsumes : Subsumes candidate (.solver name)) : candidate = .solver name := by
  cases candidate with
  | trie pre => exact absurd subsumes (by simp [Subsumes, pjoin])
  | act other => exact absurd subsumes (by simp [Subsumes, pjoin])
  | solver other => rw [(subsumes_solver_iff other name).mp subsumes]

theorem Subsumes.trans {first second third : Request σ} (firstSecond : Subsumes first second)
    (secondThird : Subsumes second third) : Subsumes first third := by
  cases third with
  | trie pre =>
      obtain ⟨middle, rfl⟩ := subsumes_trie_left secondThird
      obtain ⟨outer, rfl⟩ := subsumes_trie_left firstSecond
      rw [subsumes_trie_iff] at firstSecond secondThird ⊢
      exact firstSecond.trans secondThird
  | act name =>
      have secondEq := subsumes_act_right secondThird
      subst secondEq
      rwa [subsumes_act_right firstSecond]
  | solver name =>
      have secondEq := subsumes_solver_right secondThird
      subst secondEq
      rwa [subsumes_solver_right firstSecond]

/-- Two resolved requests never overlap. -/
def Apart : Request σ → Request σ → Prop
  | .trie first, .trie second => ¬ first <+: second ∧ ¬ second <+: first
  | .act first, .act second => first ≠ second
  | .solver first, .solver second => first ≠ second
  | _, _ => True

/-! ## Resolution -/

/-- What the kernel resolves a request to among the requests of one executable:
a request of the list that subsumes it and is subsumed by every request of the
list that subsumes it. -/
structure Resolves (requests : List (Request σ)) (request resolved : Request σ) : Prop where
  mem : resolved ∈ requests
  subsumes : Subsumes resolved request
  least : ∀ other ∈ requests, Subsumes other request → Subsumes resolved other

/-- **Two resolutions are equal or apart.** -/
theorem resolved_eq_or_apart {requests : List (Request σ)} {first second firstResolved secondResolved : Request σ}
    (firstResolves : Resolves requests first firstResolved)
    (secondResolves : Resolves requests second secondResolved) :
    firstResolved = secondResolved ∨ Apart firstResolved secondResolved := by
  cases firstResolved with
  | trie firstPre =>
      cases secondResolved with
      | trie secondPre =>
          by_cases forward : firstPre <+: secondPre
          · -- the first resolution also subsumes the second request
            left
            have reaches : Subsumes (.trie firstPre) second :=
              Subsumes.trans ((subsumes_trie_iff _ _).mpr forward) secondResolves.subsumes
            have back := secondResolves.least _ firstResolves.mem reaches
            rw [subsumes_trie_iff] at back
            rw [List.IsPrefix.eq_of_length forward
              (Nat.le_antisymm forward.length_le back.length_le)]
          · by_cases backward : secondPre <+: firstPre
            · left
              have reaches : Subsumes (.trie secondPre) first :=
                Subsumes.trans ((subsumes_trie_iff _ _).mpr backward) firstResolves.subsumes
              have back := firstResolves.least _ secondResolves.mem reaches
              rw [subsumes_trie_iff] at back
              rw [List.IsPrefix.eq_of_length back
                (Nat.le_antisymm back.length_le backward.length_le)]
            · exact Or.inr ⟨forward, backward⟩
      | act _ => exact Or.inr trivial
      | solver _ => exact Or.inr trivial
  | act firstName =>
      cases secondResolved with
      | act secondName =>
          by_cases same : firstName = secondName
          · exact Or.inl (by rw [same])
          · exact Or.inr same
      | trie _ => exact Or.inr trivial
      | solver _ => exact Or.inr trivial
  | solver firstName =>
      cases secondResolved with
      | solver secondName =>
          by_cases same : firstName = secondName
          · exact Or.inl (by rw [same])
          · exact Or.inr same
      | trie _ => exact Or.inr trivial
      | act _ => exact Or.inr trivial

/-- **Distinct trie resolutions have independent foci**: the exclusive write
zippers opened for them never see each other's writes. -/
theorem resolved_independent {V : Type v} [Nontrivial V] {requests : List (Request σ)}
    {first second : Request σ} {firstPre secondPre : List σ}
    (firstResolves : Resolves requests first (.trie firstPre))
    (secondResolves : Resolves requests second (.trie secondPre)) (different : firstPre ≠ secondPre) :
    Lens.Independent (below (V := V) firstPre) (below secondPre) := by
  rcases resolved_eq_or_apart firstResolves secondResolves with same | apart
  · cases same
    exact absurd rfl different
  · exact (independent_below_iff firstPre secondPre).mpr apart

/-- A sink writes inside the region of its resolution. -/
theorem instance_in_resolution {ν : Type v} {requests : List (Request σ)} {pre : List σ}
    (template : List (σ ⊕ ν)) (resolves : Resolves requests (.trie (constPrefix template)) (.trie pre))
    (fill : ν → List σ) : pre <+: instantiate fill template :=
  ((subsumes_trie_iff _ _).mp resolves.subsumes).trans (constPrefix_prefix_instantiate fill template)

/-! ## The kernel's byte order -/

section Order

variable [LinearOrder σ]

omit [DecidableEq σ] in
/-- A proper prefix is lexicographically smaller. -/
theorem lt_of_strict_prefix : ∀ {first second : List σ}, first <+: second → first ≠ second →
    first < second
  | [], [], _, different => absurd rfl different
  | [], _ :: _, _, _ => List.nil_lt_cons _ _
  | _ :: _, [], below, _ => by simp at below
  | a :: first, b :: second, below, different => by
      rw [List.cons_prefix_cons] at below
      obtain ⟨rfl, below⟩ := below
      have tails : first ≠ second := fun same => different (by rw [same])
      exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt_of_strict_prefix below tails⟩)

/-- **The lexicographically least subsuming trie request resolves the request.** -/
theorem lexLeast_resolves {requests : List (Request σ)} {request candidate : List σ}
    (mem : Request.trie candidate ∈ requests) (subsumes : candidate <+: request)
    (lexLeast : ∀ other : List σ, Request.trie other ∈ requests → other <+: request →
      candidate ≤ other) :
    Resolves requests (.trie request) (.trie candidate) := by
  refine ⟨mem, (subsumes_trie_iff _ _).mpr subsumes, ?_⟩
  intro other otherMem otherSubsumes
  obtain ⟨otherPre, rfl⟩ := subsumes_trie_left otherSubsumes
  rw [subsumes_trie_iff] at otherSubsumes ⊢
  rcases List.prefix_or_prefix_of_prefix subsumes otherSubsumes with below | above
  · exact below
  · by_cases same : otherPre = candidate
    · rw [same]
    · exact absurd (lexLeast otherPre otherMem otherSubsumes)
        (not_le.mpr (lt_of_strict_prefix above same))

end Order

/-! ## Controls -/

namespace Controls

/-- Two sibling regions are resolved to themselves, apart. -/
theorem siblings_apart : Apart (Request.trie ([0, 1] : List ℕ)) (.trie [0, 2]) := by
  simp [Apart]

/-- A nested region is resolved to its ancestor: one zipper. -/
theorem nested_resolves_to_ancestor :
    Resolves [Request.trie ([0] : List ℕ), .trie [0, 1]] (.trie [0, 1]) (.trie [0]) :=
  lexLeast_resolves (by simp) (by simp) (by
    intro other mem below
    simp only [List.mem_cons, Request.trie.injEq, List.mem_nil_iff, or_false] at mem
    rcases mem with rfl | rfl <;> decide)

/-- The join of two sibling regions is their common ancestor: merging them would
serialize two writers that the kernel keeps apart. -/
theorem join_of_siblings : pjoin (Request.trie ([0, 1] : List ℕ)) (.trie [0, 2]) = some (.trie [0]) := by
  decide

/-- A file request and a trie request never join. -/
theorem act_trie_no_join : pjoin (Request.act "a") (Request.trie ([0] : List ℕ)) = none :=
  rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.MORK.WriteResourceResolution
