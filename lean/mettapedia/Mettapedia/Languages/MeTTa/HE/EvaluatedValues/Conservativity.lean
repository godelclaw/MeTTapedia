import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Simulation

/-!
# Conservativity: the repair changes only incoherent evaluations

The `reevaluate` rule evaluates every returned expression again. It is
coherent exactly where that second evaluation is harmless: where an atom it
returns, evaluated again, comes back unchanged and once (`Program.StableAtom`).

`Program.CoherentAt P t` says that every evaluation the `reevaluate` rule
performs while evaluating `t` — at any depth, through arguments, equation
replies, primitives and returns — returns only stable atoms. The main theorem,
`conservativity`, says that on such inputs every rule is observationally
identical to `reevaluate`: same results, same multiplicities, same order, and
the same divergence. So `evaluatedValues` is a conservative repair: wherever
the old rule was coherent, nothing changes; it differs only where the old
rule re-chose or re-ran a value. The same holds for `rustEqualToInput`.

Two facts about `reevaluate` are proved on the way:

* `eval_reevaluate_erase` — it is blind to marks: terms with equal erasures
  have results with equal erasures.
* `reevaluate_to_new`, `new_to_reevaluate` — the two directions of the
  simulation, by induction on the depth of the run being transported, with
  the step simulation of `Simulation`.

A positive example: in the program with `(= (coin) 0)`, `(= (coin) 1)` and
`(= (twice $x) (pair $x $x))`, every evaluation returns numbers or stuck
`pair` expressions, which are stable, and all rules agree. A negative example:
with two refusing equations for `fr`, the old rule returns `(fr a)` twice, and
evaluating `(fr a)` again returns it twice: `(fr a)` is not stable, and the
old rule disagrees with the others on `(g (fr a))` (see `Probes`).
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## The old rule is blind to marks -/

theorem sim_top_iff {t u : MAtom} : Sim (fun _ => True) t u ↔ t.erase = u.erase :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ => trivial⟩⟩

theorem forall₂_sim_top_iff {R S : List MAtom} :
    List.Forall₂ (Sim (fun _ => True)) R S ↔ List.Forall₂ (fun r s => r.erase = s.erase) R S :=
  ⟨fun h => h.imp fun _ _ hab => hab.1, fun h => h.imp fun _ _ hab => sim_top_iff.mpr hab⟩

theorem reevaluate_erase_sim (P : Program) :
    ∀ n {t u : MAtom} {R : List MAtom}, t.erase = u.erase →
      evalFuel .reevaluate P n t = some R →
      ∃ S, eval .reevaluate P u = some S ∧ List.Forall₂ (fun r s => r.erase = s.erase) R S := by
  intro n
  induction n with
  | zero => intro t u R _ h; simp at h
  | succ n ih =>
    intro t u R htu h
    rw [evalFuel_succ, stepDemand_reevaluate] at h
    obtain ⟨S, hS, hRS⟩ := (openStep_sim (Stab := fun _ => True) P .reevaluate .reevaluate
      (sim_top_iff.mpr htu)).run
      (fun t' u' r htu' hr => by
        obtain ⟨S, hS, hrS⟩ := ih (sim_top_iff.mp htu') hr
        exact ⟨S, hS, forall₂_sim_top_iff.mpr hrS⟩) h
    refine ⟨S, ?_, hRS.imp fun _ _ hab => hab.1⟩
    rw [eval_fix, stepDemand_reevaluate, hS]

/-- **Mark-blindness of `reevaluate`.** -/
theorem eval_reevaluate_erase (P : Program) {t u : MAtom} (h : t.erase = u.erase) :
    (eval .reevaluate P t).map (List.map MAtom.erase) =
      (eval .reevaluate P u).map (List.map MAtom.erase) := by
  cases ht : eval .reevaluate P t with
  | some R =>
    obtain ⟨n, hn⟩ := eval_eq_some_iff.mp ht
    obtain ⟨S, hS, hRS⟩ := reevaluate_erase_sim P n h hn
    rw [hS]
    simp [forall₂_map_eq hRS fun _ _ h => h]
  | none =>
    cases hu : eval .reevaluate P u with
    | none => rfl
    | some S =>
      obtain ⟨n, hn⟩ := eval_eq_some_iff.mp hu
      obtain ⟨R, hR, -⟩ := reevaluate_erase_sim P n h.symm hn
      rw [ht] at hR
      cases hR

theorem eval_reevaluate_observe (P : Program) (t : MAtom) :
    (eval .reevaluate P t).map (List.map MAtom.erase) = observe .reevaluate P t.erase :=
  eval_reevaluate_erase P (erase_code t.erase).symm

/-! ## Stability and coherence -/

/-- `a`, evaluated again under `reevaluate`, returns itself once. -/
def Program.StableAtom (P : Program) (a : Atom) : Prop :=
  observe .reevaluate P a = some [a]

/-- `u` is demanded by one `reevaluate` step of `t`. -/
def Program.Demands (P : Program) (t u : MAtom) : Prop :=
  Demand.Asks (eval .reevaluate P) (openStep .reevaluate P t) u

/-- Every evaluation that `reevaluate` performs while evaluating `t`, at any
depth, returns only stable atoms. -/
def Program.CoherentAt (P : Program) (t : MAtom) : Prop :=
  ∀ u, Relation.ReflTransGen P.Demands t u →
    ∀ S, eval .reevaluate P u = some S → ∀ s ∈ S, P.StableAtom s.erase

theorem Program.CoherentAt.results {P : Program} {t : MAtom} (h : P.CoherentAt t) {S : List MAtom}
    (hS : eval .reevaluate P t = some S) : ∀ s ∈ S, P.StableAtom s.erase :=
  h t .refl S hS

theorem Program.CoherentAt.demand {P : Program} {t u : MAtom} (h : P.CoherentAt t)
    (hu : P.Demands t u) : P.CoherentAt u :=
  fun v hv => h v (Relation.ReflTransGen.head hu hv)

/-- A kept (marked) atom whose erasure is stable is returned once, up to
erasure, by `reevaluate`. -/
theorem kept_reevaluate {P : Program} {t u : MAtom} {S : List MAtom}
    (hstab : P.StableAtom t.erase) (htu : t.erase = u.erase)
    (hS : eval .reevaluate P u = some S) : ∃ s, S = [s] ∧ s.erase = t.erase := by
  have h := eval_reevaluate_observe P u
  rw [hS, ← htu, hstab] at h
  simp only [Option.map_some, Option.some.injEq] at h
  match S, h with
  | [s], h => exact ⟨s, rfl, by simpa using h⟩
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

theorem keeps_root_mark {rule : ReturnRule} {t : MAtom} (h : rule.keeps t = true) :
    t.erase ∈ t.marks := by
  cases t with
  | expr m cs =>
    simp only [ReturnRule.keeps, Bool.and_eq_true] at h
    obtain ⟨-, rfl⟩ := h
    simp
  | _ => simp [ReturnRule.keeps] at h

theorem forall₂_sim_of_below {P : Program} {R S : List MAtom}
    (h : List.Forall₂ (SimBelow P.StableAtom) R S) (hS : ∀ s ∈ S, P.StableAtom s.erase) :
    List.Forall₂ (Sim P.StableAtom) R S := by
  induction h with
  | nil => exact .nil
  | @cons r s R S hrs _ ih =>
    refine .cons (hrs.sim ?_) (ih fun s' hs' => hS s' (List.mem_cons_of_mem _ hs'))
    rw [hrs.1]
    exact hS s List.mem_cons_self

/-! ## The two directions -/

/-- A converged run of any rule is matched by `reevaluate` on a coherent
input. -/
theorem new_to_reevaluate (rule : ReturnRule) (P : Program) :
    ∀ n {t u : MAtom} {R : List MAtom}, Sim P.StableAtom t u → P.CoherentAt u →
      evalFuel rule P n t = some R →
      ∃ S, eval .reevaluate P u = some S ∧ List.Forall₂ (Sim P.StableAtom) R S := by
  intro n
  induction n with
  | zero => intro t u R _ _ h; simp at h
  | succ n ih =>
    intro t u R htu hcoh h
    rw [evalFuel_succ] at h
    by_cases hk : rule.keeps t = true
    · simp only [stepDemand, hk, ↓reduceIte, Demand.run_done, Option.some.injEq] at h
      subst h
      have hstab : P.StableAtom t.erase := htu.2 _ (keeps_root_mark hk)
      have hobs := eval_reevaluate_observe P u
      rw [← htu.1, hstab] at hobs
      obtain ⟨S, hS, -⟩ := Option.map_eq_some_iff.mp hobs
      obtain ⟨s, rfl, hs⟩ := kept_reevaluate hstab htu.1 hS
      exact ⟨[s], hS, .cons ⟨hs.symm, htu.2⟩ .nil⟩
    · rw [stepDemand_of_not_keeps P (by simpa using hk)] at h
      obtain ⟨S, hS, hRS⟩ := (openStep_sim P rule .reevaluate htu).run_asks
        (fun t' u' r htu' _ hask hr => ih htu' (hcoh.demand hask) hr) h
      have hS' : eval .reevaluate P u = some S := by
        rw [eval_fix, stepDemand_reevaluate, hS]
      exact ⟨S, hS', forall₂_sim_of_below hRS (hcoh.results hS')⟩

/-- A converged `reevaluate` run on a coherent input is matched by any rule. -/
theorem reevaluate_to_new (rule : ReturnRule) (P : Program) :
    ∀ n {t u : MAtom} {S : List MAtom}, Sim P.StableAtom t u → P.CoherentAt u →
      evalFuel .reevaluate P n u = some S →
      ∃ R, eval rule P t = some R ∧ List.Forall₂ (Sim P.StableAtom) R S := by
  intro n
  induction n with
  | zero => intro t u S _ _ h; simp at h
  | succ n ih =>
    intro t u S htu hcoh h
    have hSlim : eval .reevaluate P u = some S := eval_of_evalFuel h
    by_cases hk : rule.keeps t = true
    · have hstab : P.StableAtom t.erase := htu.2 _ (keeps_root_mark hk)
      obtain ⟨s, rfl, hs⟩ := kept_reevaluate hstab htu.1 hSlim
      refine ⟨[t], ?_, .cons ⟨hs.symm, htu.2⟩ .nil⟩
      rw [eval_fix]
      simp [stepDemand, hk]
    · rw [evalFuel_succ, stepDemand_reevaluate] at h
      obtain ⟨R, hR, hSR⟩ := (openStep_sim P rule .reevaluate htu).flip.run_asks
        (fun u' t' s htu' hask _ hs =>
          let ⟨R', hR', hR'S⟩ := ih htu'
            (hcoh.demand (hask.mono (evalFuel_extends_eval .reevaluate P n))) hs
          ⟨R', hR', hR'S⟩) h
      have hR' : eval rule P t = some R := by
        rw [eval_fix, stepDemand_of_not_keeps P (by simpa using hk), hR]
      exact ⟨R, hR', forall₂_sim_of_below hSR (hcoh.results hSlim)⟩

/-! ## Conservativity -/

/-- **Conservativity of the repair.** On an input whose `reevaluate`
evaluation is coherent, every rule makes the observation `reevaluate` makes:
the same results, multiplicities and order, or both diverge. For
`evaluatedValues` this is the statement that the repair changes only the
incoherent cases; it holds for `rustEqualToInput` as well. -/
theorem conservativity (rule : ReturnRule) (P : Program) (a : Atom)
    (hcoh : P.CoherentAt (code a)) : observe rule P a = observe .reevaluate P a := by
  have hsim : Sim P.StableAtom (code a) (code a) := Sim.code a
  cases hnew : eval rule P (code a) with
  | some R =>
    obtain ⟨n, hn⟩ := eval_eq_some_iff.mp hnew
    obtain ⟨S, hS, hRS⟩ := new_to_reevaluate rule P n hsim hcoh hn
    simp only [observe, hnew, hS, Option.map_some]
    rw [forall₂_map_eq hRS fun _ _ h => h.1]
  | none =>
    cases hold : eval .reevaluate P (code a) with
    | none => simp [observe, hnew, hold]
    | some S =>
      obtain ⟨n, hn⟩ := eval_eq_some_iff.mp hold
      obtain ⟨R, hR, -⟩ := reevaluate_to_new rule P n hsim hcoh hn
      rw [hnew] at hR
      cases hR

/-- Contrapositive: wherever the rules disagree, the old evaluation passed an
unstable atom through some return. -/
theorem not_coherent_of_disagree {rule : ReturnRule} {P : Program} {a : Atom}
    (h : observe rule P a ≠ observe .reevaluate P a) : ¬ P.CoherentAt (code a) :=
  fun hcoh => h (conservativity rule P a hcoh)

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues
