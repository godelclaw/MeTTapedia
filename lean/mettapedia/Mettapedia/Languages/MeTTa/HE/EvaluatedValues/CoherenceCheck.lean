import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Conservativity

/-!
# A sound check for coherence

`Program.CoherentAt` quantifies over every evaluation the `reevaluate` rule
performs below an input. When that evaluation converges, the demanded terms
form a finite tree, listed by `reachList`; `coherentCheck` evaluates each of
them and checks that every result is a stable atom. `coherentAt_of_check`
proves the check sound, so coherence of concrete inputs (and hence, by
`conservativity`, agreement of every rule with `reevaluate` on them) is
established by
kernel computation.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- The terms demanded transitively by `reevaluate` from `t`, with depth
budget `m`. -/
def reachList (P : Program) : ℕ → MAtom → List MAtom
  | 0, t => [t]
  | m + 1, t =>
    t :: (Demand.askList (evalFuel .reevaluate P m) (openStep .reevaluate P t)).flatMap (reachList P m)

theorem demands_of_evalFuel {P : Program} {m : ℕ} {t u : MAtom} {S : List MAtom}
    (h : evalFuel .reevaluate P (m + 1) t = some S) (hd : P.Demands t u) :
    u ∈ Demand.askList (evalFuel .reevaluate P m) (openStep .reevaluate P t) ∧
      ∃ S', evalFuel .reevaluate P m u = some S' := by
  rw [evalFuel_succ, stepDemand_reevaluate] at h
  obtain ⟨hask, hu⟩ := Demand.Asks.of_run (evalFuel_extends_eval .reevaluate P m) h hd
  exact ⟨hask.mem_askList, hu⟩

/-- Every term reachable from a converging input is listed. -/
theorem mem_reachList {P : Program} {t u : MAtom} (h : Relation.ReflTransGen P.Demands t u) :
    ∀ m S, evalFuel .reevaluate P m t = some S → u ∈ reachList P m t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro m S _; cases m <;> simp [reachList]
  | head hd _ ih =>
    intro m S hS
    cases m with
    | zero => simp at hS
    | succ m =>
      obtain ⟨hmem, S', hS'⟩ := demands_of_evalFuel hS hd
      simp only [reachList, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨_, hmem, ih m S' hS'⟩

/-- `a` evaluates under `reevaluate`, within depth `n`, to itself once. -/
def stableCheck (P : Program) (n : ℕ) (a : Atom) : Bool :=
  match (evalFuel .reevaluate P n (code a)).map (List.map MAtom.erase) with
  | some [b] => decide (b = a)
  | _ => false

/-- Every term demanded below `t` converges within depth `n` to stable atoms. -/
def coherentCheck (P : Program) (n : ℕ) (t : MAtom) : Bool :=
  (reachList P n t).all fun u =>
    match evalFuel .reevaluate P n u with
    | some S => S.all fun s => stableCheck P n s.erase
    | none => false

theorem stableAtom_of_check {P : Program} {n : ℕ} {a : Atom} (h : stableCheck P n a = true) :
    P.StableAtom a := by
  unfold stableCheck at h
  split at h
  · rename_i b hb
    simp only [decide_eq_true_eq] at h
    subst h
    exact observe_of_evalFuel hb
  · simp at h

/-- **Soundness of the coherence check.** -/
theorem coherentAt_of_check {P : Program} {n : ℕ} {t : MAtom} (h : coherentCheck P n t = true) :
    P.CoherentAt t := by
  unfold coherentCheck at h
  rw [List.all_eq_true] at h
  have hconv : ∀ u ∈ reachList P n t, ∃ S, evalFuel .reevaluate P n u = some S ∧
      ∀ s ∈ S, stableCheck P n s.erase = true := by
    intro u hu
    have := h u hu
    split at this
    · rename_i S hS
      exact ⟨S, hS, fun s hs => (List.all_eq_true.mp this) s hs⟩
    · simp at this
  have ht : t ∈ reachList P n t := by cases n <;> simp [reachList]
  obtain ⟨St, hSt, -⟩ := hconv t ht
  intro u hu S hS s hs
  obtain ⟨Su, hSu, hstab⟩ := hconv u (mem_reachList hu n St hSt)
  have : S = Su := by
    obtain ⟨k, hk⟩ := eval_eq_some_iff.mp hS
    exact evalFuel_det .reevaluate P hk hSu
  subst this
  exact stableAtom_of_check (hstab s hs)

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues
