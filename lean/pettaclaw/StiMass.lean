/-!
# StiMass — the STI economy as a bounded Lyapunov mass

Spec: shared/zahrada/drafts/sti-claimstate-spec-v0.3.md (2026-08-19).
Attention lives on bundles; named stimuli are the ONLY source of STI mass,
each injection bounded by the pinned constant DMAX; decay never increases
a salience. Finite form of spec Invariant A. Self-contained (no Mathlib).
-/

namespace StiMass

/-- Salience of one bundle, in integer STI units. -/
abbrev Salience := Nat

/-- A decay map: never increases the salience it is applied to. -/
structure Decay where
  apply : Salience → Salience
  nonincreasing : ∀ s, apply s ≤ s

/-- Total STI mass over a list of bundle saliences — the spec's V(t). -/
def V : List Salience → Nat
  | [] => 0
  | s :: rest => s + V rest

theorem V_map_decay_le (d : Decay) :
    ∀ ss : List Salience, V (ss.map d.apply) ≤ V ss
  | [] => Nat.le_refl 0
  | s :: rest => Nat.add_le_add (d.nonincreasing s) (V_map_decay_le d rest)

/-- Invariant A, decay half: absent injections, total mass never grows. -/
theorem sti_mass_decreases (d : Decay) (ss : List Salience) :
    V (ss.map d.apply) ≤ V ss :=
  V_map_decay_le d ss

/-- Pointwise injection raises mass by at most the injected total. -/
theorem V_zipWith_add_le : ∀ (ss deltas : List Salience),
    V (ss.zipWith (· + ·) deltas) ≤ V ss + V deltas
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | s :: ss, d :: ds => by
      have ih := V_zipWith_add_le ss ds
      show s + d + V (List.zipWith (· + ·) ss ds) ≤ s + V ss + (d + V ds)
      exact Nat.le_trans (Nat.add_le_add_left ih (s + d)) (by omega)

/-- A list of injections, each individually ≤ DMAX, carries bounded total mass. -/
theorem V_le_length_mul (DMAX : Nat) : ∀ (deltas : List Salience),
    (∀ x ∈ deltas, x ≤ DMAX) → V deltas ≤ deltas.length * DMAX
  | [], _ => Nat.zero_le _
  | d :: ds, h => by
      have hd : d ≤ DMAX := h d List.mem_cons_self
      have hds : V ds ≤ ds.length * DMAX :=
        V_le_length_mul DMAX ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hexp : (d :: ds).length * DMAX = ds.length * DMAX + DMAX := by
        rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      show d + V ds ≤ (d :: ds).length * DMAX
      exact calc d + V ds
          ≤ DMAX + ds.length * DMAX := Nat.add_le_add hd hds
        _ = ds.length * DMAX + DMAX := Nat.add_comm _ _
        _ = (d :: ds).length * DMAX := hexp.symm

/-- Invariant A, finite form: decay plus DMAX-bounded named stimulus
    injections raises total mass by at most the bounded injected amount. -/
theorem sti_step_bounded (d : Decay) (ss deltas : List Salience) (DMAX : Nat)
    (h : ∀ x ∈ deltas, x ≤ DMAX) :
    V ((ss.map d.apply).zipWith (· + ·) deltas) ≤ V ss + deltas.length * DMAX :=
  Nat.le_trans (V_zipWith_add_le _ _)
    (Nat.add_le_add (V_map_decay_le d ss) (V_le_length_mul DMAX deltas h))

/-! ## Named-state transition (probe3-verified 2026-08-20): identity-targeted injections, replaces misaligned zipWith named bridge. -/

abbrev NamedState := List (String × Nat)

/-- Key lookup over association pairs, first match wins. -/
def namedLookup : NamedState → String → Option Nat
  | [], _ => none
  | (k, v) :: rest, n => if k = n then some v else namedLookup rest n

/-- Identity-targeted update: overwrite if name present, leave unchanged if not. -/
def applyOneNamed (n : String) (d : Nat) : NamedState → NamedState
  | [] => []
  | (k, v) :: rest =>
      if k = n then (k, v + d) :: rest
      else (k, v) :: applyOneNamed n d rest

/-- Present-name case: the update is observable through lookup. -/
theorem applyOneNamed_correct (st : NamedState) (n : String) (v d : Nat)
    (h : namedLookup st n = some v) :
    namedLookup (applyOneNamed n d st) n = some (v + d) := by
  induction st with
  | nil => simp [namedLookup] at h
  | cons p rest ih =>
      obtain ⟨k, w⟩ := p
      by_cases hk : k = n
      · subst hk
        simp only [namedLookup, applyOneNamed, if_true, Option.some.injEq] at h ⊢
        obtain rfl := h
        rfl
      · simp only [namedLookup, applyOneNamed, if_neg hk] at h ⊢
        exact ih h

/-- Domain preservation: the update never adds or removes keys. -/
theorem applyOneNamed_preservesKeys (st : NamedState) (n : String) (d : Nat) :
    (applyOneNamed n d st).map Prod.fst = st.map Prod.fst := by
  induction st with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [applyOneNamed]
      by_cases hk : k = n <;> simp [hk, ih]

/-- Fold named deltas left-to-right over the state. -/
def foldNamed (st : NamedState) (nd : List (String × Nat)) : NamedState :=
  nd.foldl (fun s p => applyOneNamed p.1 p.2 s) st

#check foldNamed

-- Regression rows (Codex counterexample shape): [g1=10, g2=20], g2 += 5
#eval foldNamed [("g1", 10), ("g2", 20)] [("g2", 5)]
#eval namedLookup (foldNamed [("g1", 10), ("g2", 20)] [("g2", 5)]) "g1"
#eval namedLookup (foldNamed [("g1", 10), ("g2", 20)] [("g2", 5)]) "g2"
#eval foldNamed [("g1", 10), ("g2", 20)] [("g3", 7)]

/-! ## Exact fixed-point named step

This is the complete one-tick semantic waist used by the executable replay:
decay every existing bundle, apply identity-addressed bounded injections in
source order, clamp successful updates at the cap, and count applied versus
dropped injections.  Classification and journal formatting remain outside the
transition.
-/

structure ExactParams where
  micro : Nat
  retained : Nat
  dmax : Nat
  cap : Nat
  micro_pos : 0 < micro
  retained_le : retained ≤ micro

structure Injection where
  name : String
  delta : Nat
  deriving Repr, DecidableEq

structure StepObservation where
  applied : Nat := 0
  dropped : Nat := 0
  admitted : Nat := 0
  deriving Repr, DecidableEq

structure StepResult where
  state : NamedState
  observation : StepObservation
  deriving Repr, DecidableEq

/-- Exact floor decay in fixed-point units. -/
def exactDecayValue (p : ExactParams) (s : Nat) : Nat :=
  s * p.retained / p.micro

theorem exactDecayValue_le (p : ExactParams) (s : Nat) :
    exactDecayValue p s ≤ s := by
  unfold exactDecayValue
  apply Nat.div_le_of_le_mul
  calc
    s * p.retained ≤ s * p.micro := Nat.mul_le_mul_left s p.retained_le
    _ = p.micro * s := Nat.mul_comm _ _

/-- Decay changes values but preserves the named domain exactly. -/
def decayNamedExact (p : ExactParams) : NamedState → NamedState
  | [] => []
  | (k, v) :: rest => (k, exactDecayValue p v) :: decayNamedExact p rest

theorem decayNamedExact_preservesKeys (p : ExactParams) (st : NamedState) :
    (decayNamedExact p st).map Prod.fst = st.map Prod.fst := by
  induction st with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨k, v⟩ := pair
      simp [decayNamedExact, ih]

/-- Replace the first matching value by its capped increment.  Missing names
    leave the state unchanged. -/
def updateCapped (cap : Nat) (n : String) (d : Nat) : NamedState → NamedState
  | [] => []
  | (k, v) :: rest =>
      if k = n then (k, min cap (v + d)) :: rest
      else (k, v) :: updateCapped cap n d rest

theorem updateCapped_preservesKeys (cap : Nat) (n : String) (d : Nat)
    (st : NamedState) :
    (updateCapped cap n d st).map Prod.fst = st.map Prod.fst := by
  induction st with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨k, v⟩ := pair
      simp only [updateCapped]
      by_cases hk : k = n <;> simp [hk, ih]

/-- Clamp every requested injection at DMAX before it reaches the state. -/
def boundedDelta (p : ExactParams) (i : Injection) : Nat :=
  min i.delta p.dmax

/-- Apply one injection and expose whether its name existed.  `admitted`
    counts bounded requested mass; cap saturation may apply less, never more. -/
def applyExactInjection (p : ExactParams) (r : StepResult)
    (i : Injection) : StepResult :=
  let d := boundedDelta p i
  match namedLookup r.state i.name with
  | none =>
      { state := r.state
        observation :=
          { r.observation with dropped := r.observation.dropped + 1 } }
  | some _ =>
      { state := updateCapped p.cap i.name d r.state
        observation :=
          { applied := r.observation.applied + 1
            dropped := r.observation.dropped
            admitted := r.observation.admitted + d } }

def applyExactInjections (p : ExactParams) :
    StepResult → List Injection → StepResult
  | r, [] => r
  | r, i :: rest => applyExactInjections p (applyExactInjection p r i) rest

/-- One complete tick: decay, then bounded named injection with cap and
    explicit applied/drop observation. -/
def exactStep (p : ExactParams) (st : NamedState)
    (injections : List Injection) : StepResult :=
  applyExactInjections p
    { state := decayNamedExact p st, observation := {} }
    injections

theorem applyExactInjection_preservesKeys (p : ExactParams) (r : StepResult)
    (i : Injection) :
    (applyExactInjection p r i).state.map Prod.fst = r.state.map Prod.fst := by
  unfold applyExactInjection
  simp only
  split <;> simp [updateCapped_preservesKeys]

theorem applyExactInjections_preservesKeys (p : ExactParams) :
    ∀ (r : StepResult) (injections : List Injection),
      (applyExactInjections p r injections).state.map Prod.fst =
        r.state.map Prod.fst
  | _, [] => rfl
  | r, i :: rest => by
      rw [applyExactInjections]
      rw [applyExactInjections_preservesKeys p (applyExactInjection p r i) rest]
      exact applyExactInjection_preservesKeys p r i

theorem exactStep_preservesKeys (p : ExactParams) (st : NamedState)
    (injections : List Injection) :
    (exactStep p st injections).state.map Prod.fst = st.map Prod.fst := by
  rw [exactStep, applyExactInjections_preservesKeys]
  exact decayNamedExact_preservesKeys p st

theorem applyExactInjection_accounts (p : ExactParams) (r : StepResult)
    (i : Injection) :
    (applyExactInjection p r i).observation.applied +
        (applyExactInjection p r i).observation.dropped =
      r.observation.applied + r.observation.dropped + 1 := by
  unfold applyExactInjection
  split <;> simp <;> omega

theorem applyExactInjections_accounts (p : ExactParams) :
    ∀ (r : StepResult) (injections : List Injection),
      (applyExactInjections p r injections).observation.applied +
          (applyExactInjections p r injections).observation.dropped =
        r.observation.applied + r.observation.dropped + injections.length
  | _, [] => by simp [applyExactInjections]
  | r, i :: rest => by
      rw [applyExactInjections]
      rw [applyExactInjections_accounts p (applyExactInjection p r i) rest]
      rw [applyExactInjection_accounts]
      simp only [List.length_cons]
      omega

theorem exactStep_accounts (p : ExactParams) (st : NamedState)
    (injections : List Injection) :
    (exactStep p st injections).observation.applied +
        (exactStep p st injections).observation.dropped = injections.length := by
  rw [exactStep, applyExactInjections_accounts]
  simp

/-- Every value in a named state is at most the configured cap. -/
def StateBounded (cap : Nat) : NamedState → Prop
  | [] => True
  | (_, v) :: rest => v ≤ cap ∧ StateBounded cap rest

theorem decayNamedExact_bounded (p : ExactParams) :
    ∀ (st : NamedState), StateBounded p.cap st →
      StateBounded p.cap (decayNamedExact p st)
  | [], _ => trivial
  | (_, v) :: rest, h => by
      constructor
      · exact Nat.le_trans (exactDecayValue_le p v) h.1
      · exact decayNamedExact_bounded p rest h.2

theorem updateCapped_bounded (cap : Nat) (n : String) (d : Nat) :
    ∀ (st : NamedState), StateBounded cap st →
      StateBounded cap (updateCapped cap n d st)
  | [], _ => trivial
  | (k, v) :: rest, h => by
      simp only [updateCapped]
      by_cases hk : k = n
      · rw [if_pos hk]
        exact ⟨Nat.min_le_left _ _, h.2⟩
      · rw [if_neg hk]
        exact ⟨h.1, updateCapped_bounded cap n d rest h.2⟩

theorem applyExactInjection_bounded (p : ExactParams) (r : StepResult)
    (i : Injection) (h : StateBounded p.cap r.state) :
    StateBounded p.cap (applyExactInjection p r i).state := by
  unfold applyExactInjection
  split
  · exact h
  · exact updateCapped_bounded p.cap i.name (boundedDelta p i) r.state h

theorem applyExactInjections_bounded (p : ExactParams) :
    ∀ (r : StepResult) (injections : List Injection),
      StateBounded p.cap r.state →
      StateBounded p.cap (applyExactInjections p r injections).state
  | _, [], h => h
  | r, i :: rest, h =>
      applyExactInjections_bounded p (applyExactInjection p r i) rest
        (applyExactInjection_bounded p r i h)

theorem exactStep_bounded (p : ExactParams) (st : NamedState)
    (injections : List Injection) (h : StateBounded p.cap st) :
    StateBounded p.cap (exactStep p st injections).state := by
  apply applyExactInjections_bounded
  exact decayNamedExact_bounded p st h

theorem boundedDelta_le (p : ExactParams) (i : Injection) :
    boundedDelta p i ≤ p.dmax :=
  Nat.min_le_right _ _

theorem applyExactInjection_admitted_le (p : ExactParams) (r : StepResult)
    (i : Injection) :
    (applyExactInjection p r i).observation.admitted ≤
      r.observation.admitted + p.dmax := by
  unfold applyExactInjection
  split
  · simp
  · simp only
    exact Nat.add_le_add_left (boundedDelta_le p i) r.observation.admitted

theorem applyExactInjections_admitted_le (p : ExactParams) :
    ∀ (r : StepResult) (injections : List Injection),
      (applyExactInjections p r injections).observation.admitted ≤
        r.observation.admitted + injections.length * p.dmax
  | _, [] => by simp [applyExactInjections]
  | r, i :: rest => by
      rw [applyExactInjections]
      exact calc
        (applyExactInjections p (applyExactInjection p r i) rest).observation.admitted
            ≤ (applyExactInjection p r i).observation.admitted +
                rest.length * p.dmax :=
              applyExactInjections_admitted_le p (applyExactInjection p r i) rest
        _ ≤ (r.observation.admitted + p.dmax) + rest.length * p.dmax :=
              Nat.add_le_add_right (applyExactInjection_admitted_le p r i) _
        _ = r.observation.admitted + (i :: rest).length * p.dmax := by
              simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
              omega

theorem exactStep_admitted_le (p : ExactParams) (st : NamedState)
    (injections : List Injection) :
    (exactStep p st injections).observation.admitted ≤
      injections.length * p.dmax := by
  simpa [exactStep] using
    applyExactInjections_admitted_le p
      { state := decayNamedExact p st, observation := {} } injections

/-- Total mass of an identity-bearing state. -/
def namedMass : NamedState → Nat
  | [] => 0
  | (_, v) :: rest => v + namedMass rest

theorem decayNamedExact_mass_le (p : ExactParams) :
    ∀ (st : NamedState),
      namedMass (decayNamedExact p st) ≤ namedMass st
  | [] => Nat.le_refl 0
  | (_, v) :: rest =>
      Nat.add_le_add (exactDecayValue_le p v)
        (decayNamedExact_mass_le p rest)

theorem updateCapped_mass_le_add (cap : Nat) (n : String) (d : Nat) :
    ∀ (st : NamedState),
      namedMass (updateCapped cap n d st) ≤ namedMass st + d
  | [] => Nat.zero_le _
  | (k, v) :: rest => by
      simp only [updateCapped]
      by_cases hk : k = n
      · rw [if_pos hk]
        simp only [namedMass]
        have hmin : min cap (v + d) ≤ v + d := Nat.min_le_right _ _
        omega
      · rw [if_neg hk]
        simp only [namedMass]
        have ih := updateCapped_mass_le_add cap n d rest
        omega

theorem applyExactInjection_mass_le (p : ExactParams) (r : StepResult)
    (i : Injection) :
    namedMass (applyExactInjection p r i).state ≤
      namedMass r.state + p.dmax := by
  unfold applyExactInjection
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_trans
      (updateCapped_mass_le_add p.cap i.name (boundedDelta p i) r.state)
      (Nat.add_le_add_left (boundedDelta_le p i) _)

theorem applyExactInjections_mass_le (p : ExactParams) :
    ∀ (r : StepResult) (injections : List Injection),
      namedMass (applyExactInjections p r injections).state ≤
        namedMass r.state + injections.length * p.dmax
  | _, [] => by simp [applyExactInjections]
  | r, i :: rest => by
      rw [applyExactInjections]
      exact calc
        namedMass (applyExactInjections p (applyExactInjection p r i) rest).state
            ≤ namedMass (applyExactInjection p r i).state +
                rest.length * p.dmax :=
              applyExactInjections_mass_le p (applyExactInjection p r i) rest
        _ ≤ (namedMass r.state + p.dmax) + rest.length * p.dmax :=
              Nat.add_le_add_right (applyExactInjection_mass_le p r i) _
        _ = namedMass r.state + (i :: rest).length * p.dmax := by
              simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
              omega

/-- Complete one-step Lyapunov envelope for the exact transition.  Cap can
    only reduce the realized increase, so requested admitted mass supplies a
    sound DMAX envelope. -/
theorem exactStep_mass_le (p : ExactParams) (st : NamedState)
    (injections : List Injection) :
    namedMass (exactStep p st injections).state ≤
      namedMass st + injections.length * p.dmax := by
  exact Nat.le_trans
    (applyExactInjections_mass_le p
      { state := decayNamedExact p st, observation := {} } injections)
    (Nat.add_le_add_right (decayNamedExact_mass_le p st) _)

private def demoParams : ExactParams where
  micro := 1000000
  retained := 950000
  dmax := 300000
  cap := 980000
  micro_pos := by decide
  retained_le := by decide

-- Boundary and accounting witnesses: floor decay sends one micro-unit to zero;
-- g2 saturates at cap; the absent g3 injection is counted as dropped.
#eval exactDecayValue demoParams 1
#eval exactStep demoParams [("g1", 1), ("g2", 900000)]
  [{ name := "g2", delta := 300000 }, { name := "g3", delta := 7 }]

theorem demo_decay_boundary : exactDecayValue demoParams 1 = 0 := by decide

theorem demo_cap_and_drop :
    exactStep demoParams [("g1", 1), ("g2", 900000)]
        [{ name := "g2", delta := 300000 }, { name := "g3", delta := 7 }] =
      { state := [("g1", 0), ("g2", 980000)]
        observation := { applied := 1, dropped := 1, admitted := 300000 } } := by
  decide

#print axioms exactDecayValue_le
#print axioms exactStep_preservesKeys
#print axioms exactStep_accounts
#print axioms exactStep_bounded
#print axioms exactStep_admitted_le
#print axioms exactStep_mass_le
#print axioms demo_cap_and_drop

end StiMass
