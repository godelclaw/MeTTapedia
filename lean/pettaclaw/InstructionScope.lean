import AgentWorldState

/-!
# Instruction-scope resolution

Coding agents commonly receive instructions from files attached to nested
directories.  This file gives the resolution policy a small, implementation-
independent semantics.

An effectful adapter discovers scopes and presents them nearest-first.  The
pure resolver then applies four rules:

* only ancestor scopes apply to a target;
* the first applicable scope defining a key wins;
* a missing key falls through to outer scopes;
* an unrelated scope cannot affect the result.

The resolver returns the winning scope together with the value, retaining the
provenance needed by later context and commitment checks.  Filesystem walking,
parsing, caching, and rendering into a model prompt remain outside this pure
semantics.
-/

namespace PettaClaw.InstructionScope

open PettaClaw.AgentWorldState

/-- Paths are sequences of components, independent of any host filesystem. -/
abbrev Path (Segment : Type*) := List Segment

/-- A scope contributes zero or one value for each instruction key. -/
abbrev Rules (Key Value : Type*) := Key → Option Value

/-- An instruction layer attached to a directory. -/
structure Scope (Segment Key Value : Type*) where
  directory : Path Segment
  rules : Rules Key Value

/-- A resolved instruction retains the directory that supplied it. -/
structure Resolution (Segment Value : Type*) where
  directory : Path Segment
  value : Value
deriving DecidableEq

/-- Executable path-prefix recognition. -/
def pathPrefix [DecidableEq Segment] : Path Segment → Path Segment → Bool
  | [], _ => true
  | _ :: _, [] => false
  | head :: pathStart, targetHead :: target =>
      head == targetHead && pathPrefix pathStart target

/-- A scope applies exactly when its directory is an ancestor of the target. -/
def Applies [DecidableEq Segment]
    (scope : Scope Segment Key Value) (target : Path Segment) : Prop :=
  pathPrefix scope.directory target = true

/-- A scope is unrelated to a target when its directory is not a prefix. -/
def Unrelated [DecidableEq Segment]
    (scope : Scope Segment Key Value) (target : Path Segment) : Prop :=
  pathPrefix scope.directory target = false

/-- The executable prefix test has the ordinary mathematical meaning. -/
theorem pathPrefix_eq_true_iff [DecidableEq Segment]
    (pathStart target : Path Segment) :
    pathPrefix pathStart target = true ↔ pathStart.IsPrefix target := by
  induction pathStart generalizing target with
  | nil => simp [pathPrefix]
  | cons head rest ih =>
      cases target with
      | nil => simp [pathPrefix, List.IsPrefix]
      | cons targetHead targetRest =>
          by_cases same : head = targetHead
          · subst targetHead
            constructor
            · intro recognized
              have tailPrefix : rest.IsPrefix targetRest :=
                (ih targetRest).mp (by simpa [pathPrefix] using recognized)
              obtain ⟨suffix, suffixEq⟩ := tailPrefix
              exact ⟨suffix, by simp [suffixEq]⟩
            · rintro ⟨suffix, suffixEq⟩
              have tailEq : rest ++ suffix = targetRest := by
                simpa using suffixEq
              have recognized := (ih targetRest).mpr ⟨suffix, tailEq⟩
              simpa [pathPrefix] using recognized
          · constructor
            · intro recognized
              simp [pathPrefix, same] at recognized
            · rintro ⟨suffix, suffixEq⟩
              have : head = targetHead := by
                simpa using congrArg List.head? suffixEq
              exact (same this).elim

/-- Resolve a key from candidate scopes supplied nearest-first.

Unrelated candidates are ignored.  Applicable candidates that do not define
the requested key fall through to the remaining, more distant candidates.
-/
def resolve [DecidableEq Segment]
    (target : Path Segment) (key : Key) :
    List (Scope Segment Key Value) → Option (Resolution Segment Value)
  | [] => none
  | scope :: outer =>
      match pathPrefix scope.directory target with
      | true =>
          match scope.rules key with
          | some value => some ⟨scope.directory, value⟩
          | none => resolve target key outer
      | false => resolve target key outer

@[simp] theorem resolve_nil [DecidableEq Segment]
    (target : Path Segment) (key : Key) :
    resolve (Value := Value) target key [] = none := by
  rfl

@[simp] theorem resolve_cons_unrelated [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (scope : Scope Segment Key Value) (outer : List (Scope Segment Key Value))
    (unrelated : Unrelated scope target) :
    resolve target key (scope :: outer) = resolve target key outer := by
  have notPrefix : pathPrefix scope.directory target = false := by
    simpa [Unrelated] using unrelated
  simp [resolve, notPrefix]

@[simp] theorem resolve_cons_hit [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (scope : Scope Segment Key Value) (outer : List (Scope Segment Key Value))
    (applicable : Applies scope target) (defines : scope.rules key = some value) :
    resolve target key (scope :: outer) = some ⟨scope.directory, value⟩ := by
  simp [resolve, Applies] at applicable ⊢
  simp [applicable, defines]

@[simp] theorem resolve_cons_fallback [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (scope : Scope Segment Key Value) (outer : List (Scope Segment Key Value))
    (applicable : Applies scope target) (silent : scope.rules key = none) :
    resolve target key (scope :: outer) = resolve target key outer := by
  simp [resolve, Applies] at applicable ⊢
  simp [applicable, silent]

/-- If no nearer candidate resolves a key, resolution falls through unchanged
to the outer candidate list. -/
theorem resolve_append_of_none [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (nearer outer : List (Scope Segment Key Value))
    (silent : resolve target key nearer = none) :
    resolve target key (nearer ++ outer) = resolve target key outer := by
  induction nearer with
  | nil => simp
  | cons scope rest ih =>
      cases recognized : pathPrefix scope.directory target with
      | true =>
        cases defines : scope.rules key with
        | none =>
            have restSilent : resolve target key rest = none := by
              simpa [resolve, recognized, defines] using silent
            simp [resolve, recognized, defines, ih restSilent]
        | some value =>
            simp [resolve, recognized, defines] at silent
      | false =>
        have restSilent : resolve target key rest = none := by
          simpa [resolve, recognized] using silent
        simp [resolve, recognized, ih restSilent]

/-- Once a nearer scope resolves a key, adding outer scopes cannot change the
answer. -/
theorem resolve_append_of_some [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (nearer outer : List (Scope Segment Key Value))
    (result : Resolution Segment Value)
    (hit : resolve target key nearer = some result) :
    resolve target key (nearer ++ outer) = some result := by
  induction nearer with
  | nil => simp at hit
  | cons scope rest ih =>
      cases recognized : pathPrefix scope.directory target with
      | true =>
        cases defines : scope.rules key with
        | none =>
            have restHit : resolve target key rest = some result := by
              simpa [resolve, recognized, defines] using hit
            simp [resolve, recognized, defines, ih restHit]
        | some value =>
            simpa [resolve, recognized, defines] using hit
      | false =>
        have restHit : resolve target key rest = some result := by
          simpa [resolve, recognized] using hit
        simp [resolve, recognized, ih restHit]

/-- Inserting an unrelated scope anywhere in the candidate list cannot change
resolution. -/
theorem unrelated_subtree_noninterference [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (nearer outer : List (Scope Segment Key Value))
    (scope : Scope Segment Key Value)
    (unrelated : Unrelated scope target) :
    resolve target key (nearer ++ scope :: outer) =
      resolve target key (nearer ++ outer) := by
  induction nearer with
  | nil =>
      have notPrefix : pathPrefix scope.directory target = false := by
        simpa [Unrelated] using unrelated
      simp [resolve, notPrefix]
  | cons first rest ih =>
      cases recognized : pathPrefix first.directory target with
      | true =>
        cases defines : first.rules key with
        | none => simp [resolve, recognized, defines, ih]
        | some value => simp [resolve, recognized, defines]
      | false => simp [resolve, recognized, ih]

/-- Resolution never invents an instruction: every returned value is supplied
by an applicable member of the candidate list. -/
theorem resolve_sound [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (scopes : List (Scope Segment Key Value))
    (result : Resolution Segment Value)
    (resolved : resolve target key scopes = some result) :
    ∃ scope ∈ scopes,
      Applies scope target ∧
      scope.rules key = some result.value ∧
      scope.directory = result.directory := by
  induction scopes with
  | nil => simp at resolved
  | cons scope outer ih =>
      cases recognized : pathPrefix scope.directory target with
      | true =>
        have applicable : Applies scope target := by
          simpa [Applies] using recognized
        cases defines : scope.rules key with
        | none =>
            have outerResolved : resolve target key outer = some result := by
              simpa [resolve, recognized, defines] using resolved
            obtain ⟨source, member, sourceApplies, sourceDefines, sameDirectory⟩ :=
              ih outerResolved
            exact ⟨source, by simp [member], sourceApplies, sourceDefines,
              sameDirectory⟩
        | some value =>
            have same : result = ⟨scope.directory, value⟩ := by
              simpa [resolve, recognized, defines] using resolved.symm
            subst result
            exact ⟨scope, by simp, applicable, defines, rfl⟩
      | false =>
        have outerResolved : resolve target key outer = some result := by
          simpa [resolve, recognized] using resolved
        obtain ⟨source, member, sourceApplies, sourceDefines, sameDirectory⟩ :=
          ih outerResolved
        exact ⟨source, by simp [member], sourceApplies, sourceDefines,
          sameDirectory⟩

/-- Every candidate preceding a known winner may be unrelated or silent for
the requested key.  Under the adapter contract that candidates are ordered
nearest-first, this is precisely nearest-applicable-scope resolution. -/
def SilentFor [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (scopes : List (Scope Segment Key Value)) : Prop :=
  ∀ scope ∈ scopes, Unrelated scope target ∨ scope.rules key = none

/-- The first applicable scope that defines a key wins, even if unrelated
candidates are interspersed in the input. -/
theorem first_applicable_defining_scope_sound [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (nearer outer : List (Scope Segment Key Value))
    (winner : Scope Segment Key Value)
    (nearerSilent : SilentFor target key nearer)
    (winnerApplies : Applies winner target)
    (winnerDefines : winner.rules key = some value) :
    resolve target key (nearer ++ winner :: outer) =
      some ⟨winner.directory, value⟩ := by
  induction nearer with
  | nil => simp [winnerApplies, winnerDefines]
  | cons scope rest ih =>
      have scopeSilent := nearerSilent scope (by simp)
      have restSilent : SilentFor target key rest := by
        intro candidate member
        exact nearerSilent candidate (by simp [member])
      cases scopeSilent with
      | inl unrelated =>
          simp [Unrelated] at unrelated
          simp [resolve, unrelated, ih restSilent]
      | inr silent =>
          cases recognized : pathPrefix scope.directory target with
          | true => simp [resolve, recognized, silent, ih restSilent]
          | false => simp [resolve, recognized, ih restSilent]

/-! ## The ancestor-walker contract -/

/-- A scope list is ordered nearest-first when each later directory is an
ancestor of every earlier directory. -/
def NearestFirst [DecidableEq Segment]
    (scopes : List (Scope Segment Key Value)) : Prop :=
  scopes.Pairwise fun nearer outer =>
    pathPrefix outer.directory nearer.directory = true

/-- An adapter supplies a valid chain for a target when every candidate is an
ancestor of the target and candidates are ordered nearest-first. -/
def ChainFor [DecidableEq Segment]
    (target : Path Segment) (scopes : List (Scope Segment Key Value)) : Prop :=
  (∀ scope ∈ scopes, Applies scope target) ∧ NearestFirst scopes

/-- A list of nearer scopes is silent for one instruction key. -/
def SilentForKey (key : Key) (scopes : List (Scope Segment Key Value)) : Prop :=
  ∀ scope ∈ scopes, scope.rules key = none

/-- For a valid ancestor chain, the nearest scope defining a key is selected.

The theorem exposes the exact division of responsibility: discovery proves
`ChainFor`; pure resolution proves first-definition-wins with per-key outward
fallback.
-/
theorem nearest_applicable_scope_sound [DecidableEq Segment]
    (target : Path Segment) (key : Key)
    (nearer outer : List (Scope Segment Key Value))
    (winner : Scope Segment Key Value)
    (chain : ChainFor target (nearer ++ winner :: outer))
    (nearerSilent : SilentForKey key nearer)
    (winnerDefines : winner.rules key = some value) :
    resolve target key (nearer ++ winner :: outer) =
      some ⟨winner.directory, value⟩ := by
  have winnerApplies : Applies winner target :=
    chain.1 winner (by simp)
  apply first_applicable_defining_scope_sound target key nearer outer winner
  · intro scope member
    exact Or.inr (nearerSilent scope member)
  · exact winnerApplies
  · exact winnerDefines

/-! ## Observation and refresh -/

/-- Refresh one discovered scope without confusing inability to read it with
a witnessed deletion. -/
def refreshScope (old : Option (Scope Segment Key Value)) :
    SourceObservation (Scope Segment Key Value) →
      Option (Scope Segment Key Value)
  | .unavailable => old
  | .observed current => current

@[simp] theorem unavailable_preserves_scope
    (old : Option (Scope Segment Key Value)) :
    refreshScope old .unavailable = old := by
  rfl

@[simp] theorem witnessed_absence_removes_scope
    (old : Option (Scope Segment Key Value)) :
    refreshScope old (.observed none) = none := by
  rfl

@[simp] theorem witnessed_presence_replaces_scope
    (old : Option (Scope Segment Key Value))
    (current : Scope Segment Key Value) :
    refreshScope old (.observed (some current)) = some current := by
  rfl

end PettaClaw.InstructionScope

#print axioms PettaClaw.InstructionScope.pathPrefix_eq_true_iff
#print axioms PettaClaw.InstructionScope.resolve_sound
#print axioms PettaClaw.InstructionScope.nearest_applicable_scope_sound
#print axioms PettaClaw.InstructionScope.unrelated_subtree_noninterference
