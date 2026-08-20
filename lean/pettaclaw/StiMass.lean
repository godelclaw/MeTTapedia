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


end StiMass

