import Mettapedia.TypeTheory.PromotionAdmission.Admission
import Mathlib.Data.Set.Finite.Lattice

/-!
# With a checked certificate, the admission check decides

For well-formed rules every term has finitely many one-step reducts. When the rules terminate,
König's lemma makes the set of all reducts of a term finite (`reachable_finite`), so a search
of large enough budget reaches all of them and is exhausted (`eventually_saturated`). Every
critical pair is then either joined or refuted at that budget.

* **The admission check is eventually decided** (`admissionRun_eventually_decided`): for
  well-formed rules whose certificate orients every rule, some budget gives an established or a
  refuted answer. Below that budget the answer may be incomplete; it never becomes a
  boundary, and it never contradicts the decided answer (`admissionCheck`).
* So, for requests with a checked certificate, the check is a decision procedure for
  convergence, and "incomplete" only marks a budget that was too small.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u v w

open Term Relation

variable {F : Type u} {V : Type v} {W : Type w}
variable [DecidableEq F] [DecidableEq V] [DecidableEq W]

/-- Every reduct is reached at some budget. -/
theorem exists_reach_of_steps {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed)
    {t u : Term F W} (steps : Steps R t u) : ∃ k, u ∈ reach R k t := by
  induction steps with
  | refl => exact ⟨0, self_mem_reach R 0 t⟩
  | tail _ step ih =>
      obtain ⟨k, member⟩ := ih
      exact ⟨k + 1, mem_reach_succ.mpr (Or.inr ⟨_, member, mem_reducts_of_step format step⟩)⟩

/-- **The reducts of a terminating term form a finite set.** -/
theorem reachable_finite {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed) (t : Term F W)
    (accessible : Acc (fun target source => Step R source target) t) :
    {u | Steps R t u}.Finite := by
  induction accessible with
  | intro t _ ih =>
      have split : {u | Steps R t u} =
          insert t (⋃ v ∈ {v | v ∈ reducts R t}, {u | Steps R v u}) := by
        ext u
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_iUnion, exists_prop]
        constructor
        · intro steps
          rcases steps.cases_head with same | ⟨v, step, rest⟩
          · exact Or.inl same.symm
          · exact Or.inr ⟨v, mem_reducts_of_step format step, rest⟩
        · rintro (rfl | ⟨v, member, rest⟩)
          · exact .refl
          · exact ReflTransGen.head (reducts_sound t member) rest
      rw [split]
      refine Set.Finite.insert _ (Set.Finite.biUnion (List.finite_toSet _) fun v member => ?_)
      exact ih v (reducts_sound t member)

/-- **A terminating term's search is exhausted at some budget.** -/
theorem eventually_saturated {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed) (t : Term F W)
    (accessible : Acc (fun target source => Step R source target) t) :
    ∃ k, saturatedAt R k t = true := by
  have finite := reachable_finite format t accessible
  have each : ∀ u ∈ finite.toFinset, ∃ k, u ∈ reach R k t := fun u member =>
    exists_reach_of_steps format (by simpa using member)
  choose depth hdepth using each
  let k := finite.toFinset.attach.sup fun u => depth u.1 u.2
  have covers : ∀ u, Steps R t u → u ∈ reach R k t := by
    intro u steps
    have member : u ∈ finite.toFinset := by simpa using steps
    exact reach_mono (Finset.le_sup (f := fun u : finite.toFinset => depth u.1 u.2)
      (Finset.mem_attach _ ⟨u, member⟩)) (hdepth u member)
  refine ⟨k, saturatedAt_iff.mpr fun v vMember u reduct => covers u ?_⟩
  exact (reach_sound vMember).tail (reducts_sound v reduct)

/-- Saturation at the maximum of the budgets of a finite list of terms. -/
theorem eventually_saturated_list {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed)
    (terminating : TerminatingAt R W) :
    ∀ ts : List (Term F W), ∃ k, ∀ t ∈ ts, saturatedAt R k t = true
  | [] => ⟨0, fun _ member => by simp at member⟩
  | t :: ts => by
      obtain ⟨k₁, h₁⟩ := eventually_saturated format t (terminating t)
      obtain ⟨k₂, h₂⟩ := eventually_saturated_list format terminating ts
      refine ⟨max k₁ k₂, fun s member => ?_⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact (saturated_persists h₁ (le_max_left _ _)).1
      · exact (saturated_persists (h₂ s later) (le_max_right _ _)).1

/-- **With a checked certificate, some budget decides the admission check.** -/
theorem admissionRun_eventually_decided {q : PromotionRequest F V}
    (format : rulesWellFormed q.rules = true) (cert : q.rules.all q.certificate.orients = true) :
    ∃ k, (admissionRun k q).isDecided = true := by
  have terminating : TerminatingAt q.rules (V ⊕ V) :=
    q.certificate.terminating_of_orients fun ρ mem => List.all_eq_true.mp cert ρ mem
  let cps := criticalPairsExact (overlaps q.rules q.rules)
  obtain ⟨k, saturated⟩ := eventually_saturated_list (rulesWellFormed_iff.mp format) terminating
    (cps.flatMap fun cp => [cp.left, cp.right])
  refine ⟨k, ?_⟩
  unfold admissionRun
  rw [dif_pos format]
  by_cases loop : loopExact q.rules = .found
  · rw [dif_pos loop]; rfl
  · rw [dif_neg loop, dif_pos cert]
    by_cases joined : allJoined q.rules k cps = true
    · rw [dif_pos joined]; rfl
    · rw [dif_neg joined]
      have apart : someApart q.rules k cps = true := by
        simp only [allJoined, List.all_eq_true, not_forall] at joined
        obtain ⟨cp, mem, notJoined⟩ := joined
        refine someApart_spec.mpr ⟨cp, mem, notJoined, ?_, ?_⟩
        · exact saturated _ (List.mem_flatMap.mpr ⟨cp, mem, by simp⟩)
        · exact saturated _ (List.mem_flatMap.mpr ⟨cp, mem, by simp⟩)
      rw [dif_pos apart]; rfl

/-! ## Axiom audit -/

#print axioms reachable_finite
#print axioms eventually_saturated
#print axioms admissionRun_eventually_decided

end Mettapedia.TypeTheory.PromotionAdmission
