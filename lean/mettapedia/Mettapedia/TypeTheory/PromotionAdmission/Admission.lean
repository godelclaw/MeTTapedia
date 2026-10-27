import Mettapedia.TypeTheory.PromotionAdmission.Joinability
import Mettapedia.TypeTheory.PromotionAdmission.Termination
import Mettapedia.TypeTheory.PromotionAdmission.Criterion

/-!
# Admitting rules into a bubble: one extend theorem, and a graded admission check

A bubble's rules are extended by new rules `delta`. The extension keeps the decision by
normal forms exactly when it is convergent; this module states the extension theorem with its
two side conditions and the check that establishes them.

* **The extend theorem** (`extend_convergent`). If the base is locally confluent, then the
  extension `base ++ delta` is convergent provided
  1. *the overlap condition*: every overlap of a new rule with any rule, and of a base rule
     with a new rule, joins (`deltaOverlaps`); and
  2. *the termination condition*: the extension terminates.

  Its consequences (`ConvergentRules.decidedOn`, `conv_sound`, `normalize_decides`): every term has
  one normal form, conversion is decided by normal forms on every set of terms, and if every
  rule is valid in a model, every conversion is an equality there.
* **Admission and promotion are the two ways of meeting the overlap condition.**
  - *Admission* gives rules to fresh heads (`FreshHeads`) whose rows do not overlap each other
    (`RowsApart`); the overlap condition then holds by construction, with no evidence
    (`overlapCondition_of_freshHeads`). Both hypotheses are computed (`freshHeadsCheck`,
    `rowsApartCheck`).
  - *Promotion* gives rules to existing heads; the overlap condition is the joinability of the
    computed critical pairs (`overlapCondition_of_criticalPairs`).

  The termination condition is the same in both: a certificate (`LinearInterpretation`) checked
  by the kernel.
* **The admission check** (`admissionCheck`), a graded check with the four outcomes of
  `AuthorityTheory.Outcome` for the judgment "the rules are convergent":
  - outside the fragment when a rule is not well formed, or when the certificate orients no
    rule list (both independent of the budget);
  - refuted when a rule's two sides unify (a loop), or when a critical pair is not joinable;
  - established when the certificate orients every rule and every critical pair joins within the
    budget;
  - incomplete otherwise.

  Every unification inside it runs to completion (`criticalPairsExact`, `loopExact`, by the
  proved termination of unification), so the budget bounds only the search
  for joins. A boundary verdict that waited on a budgeted search would break monotonicity:
  monotonicity forbids an incomplete answer turning into a boundary.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u v

open Term Relation
open Mettapedia.Logic.Relation (Confluent IsNormal IsNormalFormOf DecidedOn CompleteStepSelector)

variable {F : Type u} {V : Type v}

/-! ## Convergence of a rule list -/

/-- **Convergence**: locally confluent and terminating on terms over every variable type of
the rules' universe. -/
def ConvergentRules (R : List (Rule F V)) : Prop :=
  ∀ W : Type v, LocallyConfluentAt R W ∧ TerminatingAt R W

namespace ConvergentRules

variable {R : List (Rule F V)} (h : ConvergentRules R) (W : Type v)
include h

/-- The steps over `W` satisfy the abstract criterion. -/
theorem convergent : Convergent (Step (W := W) R) :=
  ⟨(h W).1, (h W).2⟩

/-- **Confluent**, by Newman's lemma. -/
theorem confluent : Confluent (Step (W := W) R) := (h.convergent W).confluent

/-- **Conversion is decided by normal forms on every set of terms.** -/
theorem decidedOn (S : Set (Term F W)) : DecidedOn (Step R) S := (h.convergent W).decidedOn S

/-- Every term has exactly one normal form. -/
theorem normalForm_unique {t n m : Term F W} (first : IsNormalFormOf (Step R) t n)
    (second : IsNormalFormOf (Step R) t m) : n = m :=
  (h.convergent W).normalForm_unique first second

end ConvergentRules

/-- **Valid rules give sound conversions.** -/
theorem conv_sound {R : List (Rule F V)} {D : Type*} (I : Interpretation F D)
    (valid : ∀ ρ ∈ R, I.Valid ρ) {W : Type*} {s t : Term F W}
    (converted : EqvGen (Step R) s t) (α : W → D) : I.eval α s = I.eval α t :=
  I.conv_sound valid converted α

section Selector

variable [DecidableEq F] [DecidableEq V] {W : Type v} [DecidableEq W]

/-- **The step selector of a rule list**: the first listed reduct. -/
def stepSelector (R : List (Rule F V)) (format : ∀ ρ ∈ R, ρ.WellFormed) :
    CompleteStepSelector (Step (W := W) R) where
  step t :=
    match h : reducts R t with
    | [] => none
    | u :: _ => some ⟨u, reducts_sound t (by rw [h]; exact List.mem_cons_self)⟩
  none_iff_normal t := by
    constructor
    · intro selected u step
      have member := mem_reducts_of_step format step
      split at selected
      · rename_i h; rw [h] at member; simp at member
      · cases selected
    · intro normal
      split
      · rfl
      · rename_i u _ h
        exact absurd (reducts_sound t (by rw [h]; exact List.mem_cons_self)) (normal u)

/-- **Computed normal forms decide conversion** for convergent, well-formed rules. -/
theorem normalize_decides {R : List (Rule F V)} (h : ConvergentRules R)
    (format : ∀ ρ ∈ R, ρ.WellFormed) (s t : Term F W) :
    ((stepSelector R format).normalize s ((h W).2 s)).normalForm =
        ((stepSelector R format).normalize t ((h W).2 t)).normalForm ↔ EqvGen (Step R) s t :=
  (h.convergent W).normalize_decides _ s t

end Selector

/-! ## The extend theorem -/

/-- **The extend theorem.** A locally confluent base extended by new rules is convergent under
two side conditions: the overlaps that involve a new rule join, and the extension terminates. -/
theorem extend_convergent [DecidableEq V] {base delta : List (Rule F V)}
    (baseLC : ∀ W : Type v, LocallyConfluentAt base W)
    (overlapCondition : ∀ W : Type v, ∀ o ∈ deltaOverlaps base delta,
      OverlapJoins (base ++ delta) o W)
    (terminationCondition : ∀ W : Type v, TerminatingAt (base ++ delta) W) :
    ConvergentRules (base ++ delta) :=
  fun W => ⟨locallyConfluent_extend (baseLC W) (overlapCondition W), terminationCondition W⟩

/-! ## Admission: fresh heads meet the overlap condition by construction -/

/-- **Fresh heads**: the head of every new left side occurs in no base left side, and below its
root a new left side uses no head of any rule. -/
structure FreshHeads (base delta : List (Rule F V)) : Prop where
  rootFresh : ∀ ρ ∈ delta, ∀ f, ρ.lhs.head? = some f → ∀ ρ' ∈ base, f ∉ ρ'.lhs.symbols
  patternsFree : ∀ ρ ∈ delta, ∀ p ∈ ρ.lhs.positions, p.1.fill p.2 ≠ p.2 →
    ∀ ρ' ∈ base ++ delta, p.2.head? ≠ ρ'.lhs.head?

/-- **The rows do not overlap**: two different new left sides have no common instance. -/
def RowsApart (delta : List (Rule F V)) : Prop :=
  ∀ ρ₁ ∈ delta, ∀ ρ₂ ∈ delta, ρ₁ ≠ ρ₂ →
    ∀ (W : Type v) (σ τ : V → Term F W), ρ₁.lhs.subst σ ≠ ρ₂.lhs.subst τ

theorem head_eq_of_subst_eq {W : Type*} {s t : Term F V} (sApp : s.isApp = true)
    (tApp : t.isApp = true) {σ τ : V → Term F W} (same : s.subst σ = t.subst τ) :
    s.head? = t.head? := by
  obtain ⟨f, ss, rfl⟩ := (isApp_iff s).mp sApp
  obtain ⟨g, ts, rfl⟩ := (isApp_iff t).mp tApp
  simp only [subst_app, app.injEq] at same
  simp [head?, same.1]

theorem head_mem_symbols {t : Term F V} {f : F} (h : t.head? = some f) : f ∈ t.symbols := by
  cases t with
  | var x => simp [head?] at h
  | app g ts => simp only [head?, Option.some.injEq] at h; subst h; simp

theorem Ctx.symbols_fill {f : F} {s : Term F V} (member : f ∈ s.symbols) :
    ∀ c : Ctx F V, f ∈ (c.fill s).symbols := by
  intro c
  induction c with
  | hole => exact member
  | app g before inner after ih =>
      simp only [Ctx.fill, symbols_app, List.mem_cons, List.flatMap_append, List.flatMap_cons,
        List.mem_append]
      exact Or.inr (Or.inr (Or.inl ih))

theorem subst_agree_of_eq {W : Type*} {σ τ : V → Term F W} :
    ∀ t : Term F V, t.subst σ = t.subst τ → ∀ x ∈ t.vars, σ x = τ x := by
  intro t
  induction t using Term.induction' with
  | var x => intro same y member; simp at member same; subst member; exact same
  | app f args ih =>
      intro same y member
      simp only [subst_app, app.injEq, true_and] at same
      simp only [vars_app, List.mem_flatMap] at member
      obtain ⟨a, aMember, yMember⟩ := member
      exact ih a aMember (List.map_inj_left.mp same a aMember) y yMember

/-- **Admission needs no overlap evidence**: with fresh heads and rows apart, every overlap
that involves a new rule joins. -/
theorem overlapCondition_of_freshHeads {base delta : List (Rule F V)}
    (format : ∀ ρ ∈ base ++ delta, ρ.WellFormed) (fresh : FreshHeads base delta)
    (rows : RowsApart delta) (W : Type v) :
    ∀ o ∈ deltaOverlaps base delta, OverlapJoins (base ++ delta) o W := by
  intro o member σ τ same
  rcases List.mem_append.mp member with newOuter | newInner
  · obtain ⟨outer, inner, position⟩ := mem_overlaps_iff.mp newOuter
    obtain ⟨filled, partApp⟩ := (mem_positions_iff _ _ _).mp position
    have innerApp := (format o.inner inner).1
    have heads := head_eq_of_subst_eq partApp innerApp same
    by_cases root : o.position.1.fill o.position.2 = o.position.2
    · -- the overlap is at the root of the new left side
      have isLhs : o.position.2 = o.outer.lhs := by rw [← filled, root]
      rcases List.mem_append.mp inner with innerBase | innerDelta
      · obtain ⟨f, hf⟩ : ∃ f, o.outer.lhs.head? = some f := by
          obtain ⟨g, gs, eq⟩ := (isApp_iff _).mp (format o.outer (List.mem_append_right _ outer)).1
          exact ⟨g, by simp [eq, head?]⟩
        rw [isLhs] at heads
        exact absurd (head_mem_symbols (heads ▸ hf))
          (fresh.rootFresh _ outer f hf _ innerBase)
      · by_cases sameRule : o.outer = o.inner
        · rw [isLhs, sameRule] at same
          have agree := subst_agree_of_eq _ same
          have rhsSame : o.outer.rhs.subst σ = o.inner.rhs.subst τ := by
            rw [sameRule]
            exact subst_congr _ fun x hx =>
              agree x ((format o.inner (List.mem_append_right _ innerDelta)).2 x hx)
          have holeSame : (o.position.1.subst σ).fill (o.inner.rhs.subst τ) =
              o.inner.rhs.subst τ := by
            have : o.position.1 = .hole := by
              cases hc : o.position.1 with
              | hole => rfl
              | app g before c after =>
                  rw [hc] at root
                  have := congrArg Term.size root
                  simp only [Ctx.fill, size_app, List.map_append, List.map_cons, List.sum_append,
                    List.sum_cons] at this
                  have le : (c.fill o.position.2).size ≥ o.position.2.size := by
                    clear hc root this
                    induction c with
                    | hole => exact le_refl _
                    | app g' b' c' a' ih =>
                        simp only [Ctx.fill, size_app, List.map_append, List.map_cons,
                          List.sum_append, List.sum_cons]
                        omega
                  omega
            rw [this]; rfl
          rw [holeSame, ← rhsSame]
          exact ⟨_, .refl, .refl⟩
        · exact absurd (isLhs ▸ same) (rows _ outer _ innerDelta sameRule W σ τ)
    · exact absurd heads (fresh.patternsFree _ outer _ position root _ inner)
  · obtain ⟨outer, inner, position⟩ := mem_overlaps_iff.mp newInner
    obtain ⟨filled, partApp⟩ := (mem_positions_iff _ _ _).mp position
    have innerApp := (format o.inner (List.mem_append_right _ inner)).1
    have heads := head_eq_of_subst_eq partApp innerApp same
    obtain ⟨g, gs, eq⟩ := (isApp_iff _).mp innerApp
    have hg : o.inner.lhs.head? = some g := by simp [eq, head?]
    have inOuter : g ∈ o.outer.lhs.symbols := by
      rw [← filled]
      exact Ctx.symbols_fill (head_mem_symbols (heads ▸ hg)) _
    exact absurd inOuter (fresh.rootFresh _ inner g hg _ outer)

/-- **Admission is convergent** once the extension terminates. -/
theorem admit_convergent [DecidableEq V] {base delta : List (Rule F V)}
    (format : ∀ ρ ∈ base ++ delta, ρ.WellFormed) (baseLC : ∀ W : Type v, LocallyConfluentAt base W)
    (fresh : FreshHeads base delta) (rows : RowsApart delta)
    (terminationCondition : ∀ W : Type v, TerminatingAt (base ++ delta) W) :
    ConvergentRules (base ++ delta) :=
  extend_convergent baseLC (overlapCondition_of_freshHeads format fresh rows) terminationCondition

section Exact

variable [DecidableEq F] [DecidableEq V]

/-! ## Unification run to completion -/

theorem criticalPairsOf_isSome_exists (os : List (Overlap F V)) :
    ∃ n, (criticalPairsOf n os).isSome = true := by
  obtain ⟨n, cps, h⟩ := criticalPairsOf_eventually os
  exact ⟨n, by simp [h]⟩

/-- **The critical pairs, computed to completion.** -/
def criticalPairsExact (os : List (Overlap F V)) : List (CriticalPair F V) :=
  (criticalPairsOf (Nat.find (criticalPairsOf_isSome_exists os)) os).get
    (Nat.find_spec (criticalPairsOf_isSome_exists os))

theorem criticalPairsExact_spec (os : List (Overlap F V)) :
    criticalPairsOf (Nat.find (criticalPairsOf_isSome_exists os)) os =
      some (criticalPairsExact os) := by
  simp [criticalPairsExact]

theorem criticalPairsExact_eq {os : List (Overlap F V)} {n : ℕ} {cps : List (CriticalPair F V)}
    (h : criticalPairsOf n os = some cps) : criticalPairsExact os = cps := by
  have le : Nat.find (criticalPairsOf_isSome_exists os) ≤ n :=
    Nat.find_min' _ (by simp [h])
  have := criticalPairsOf_mono le (criticalPairsExact_spec os)
  rw [h] at this
  exact (Option.some.inj this).symm

theorem criticalPairsExact_eq_get {os : List (Overlap F V)} {n : ℕ}
    (h : (criticalPairsOf n os).isSome = true) :
    criticalPairsExact os = (criticalPairsOf n os).get h :=
  criticalPairsExact_eq (Option.some_get h).symm

theorem loopSearch_decided_of {fuel : ℕ} :
    ∀ {R : List (Rule F V)}, (∀ ρ ∈ R, unify fuel [(ρ.lhs, ρ.rhs)] ≠ .outOfFuel) →
      loopSearch fuel R ≠ .outOfFuel
  | [], _ => by simp [loopSearch]
  | ρ :: rest, decided => by
      simp only [loopSearch]
      cases hu : unify fuel [(ρ.lhs, ρ.rhs)] with
      | ok θ => simp
      | fail => exact loopSearch_decided_of fun ρ' h => decided ρ' (List.mem_cons_of_mem _ h)
      | outOfFuel => exact absurd hu (decided ρ List.mem_cons_self)

theorem loopSearch_eventually (R : List (Rule F V)) : ∃ n, loopSearch n R ≠ .outOfFuel := by
  have each : ∀ ρ ∈ R, ∃ n, unify n [(ρ.lhs, ρ.rhs)] ≠ .outOfFuel :=
    fun ρ _ => unify_terminates _
  choose n hn using each
  let fuel := (R.attach.map fun ρ => n ρ.1 ρ.2).sum
  have le : ∀ ρ (h : ρ ∈ R), n ρ h ≤ fuel := fun ρ h =>
    nat_le_sum_of_mem (List.mem_map.mpr ⟨⟨ρ, h⟩, List.mem_attach _ _, rfl⟩)
  exact ⟨fuel, loopSearch_decided_of fun ρ h => by
    rw [unify_mono _ _ fuel (le ρ h) (hn ρ h)]; exact hn ρ h⟩

/-- **The loop search, run to completion.** -/
def loopExact (R : List (Rule F V)) : LoopAnswer :=
  loopSearch (Nat.find (loopSearch_eventually R)) R

theorem loopExact_eq {R : List (Rule F V)} {n : ℕ} (h : loopSearch n R ≠ .outOfFuel) :
    loopExact R = loopSearch n R := by
  have le : Nat.find (loopSearch_eventually R) ≤ n := Nat.find_min' _ h
  exact (loopSearch_mono le (Nat.find_spec (loopSearch_eventually R))).symm

theorem loopExact_ne : ∀ (R : List (Rule F V)), loopExact R ≠ .outOfFuel :=
  fun R => Nat.find_spec (loopSearch_eventually R)

/-! ## The admission check -/

/-- A promotion request: the base rules, the new rules, and a termination certificate. -/
structure PromotionRequest (F : Type u) (V : Type v) where
  base : List (Rule F V)
  delta : List (Rule F V)
  certificate : LinearInterpretation F

/-- The rules after the extension. -/
def PromotionRequest.rules (q : PromotionRequest F V) : List (Rule F V) := q.base ++ q.delta

/-- The judgment the admission check decides: the extended rules are convergent. -/
def convergenceAuthority : AuthorityTheory.Authority (PromotionRequest F V) where
  Holds q := ConvergentRules q.rules
  Evidence q := ConvergentRules q.rules
  Obstruction q := ¬ ConvergentRules q.rules
  evidenceSound _ evidence := evidence
  obstructionSound _ obstruction := obstruction

/-- Every critical pair joins within the budget. -/
def allJoined (R : List (Rule F V)) (k : ℕ) (cps : List (CriticalPair F V)) : Bool :=
  cps.all fun cp => joinedAt R k cp.left cp.right

/-- Some critical pair is refuted within the budget. -/
def someApart (R : List (Rule F V)) (k : ℕ) (cps : List (CriticalPair F V)) : Bool :=
  cps.any fun cp => !joinedAt R k cp.left cp.right && saturatedAt R k cp.left &&
    saturatedAt R k cp.right

theorem allJoined_mono {R : List (Rule F V)} {k m : ℕ} (le : k ≤ m) {cps : List (CriticalPair F V)}
    (h : allJoined R k cps = true) : allJoined R m cps = true := by
  simp only [allJoined, List.all_eq_true] at h ⊢
  exact fun cp mem => joinedAt_mono le (h cp mem)

theorem someApart_spec {R : List (Rule F V)} {k : ℕ} {cps : List (CriticalPair F V)} :
    someApart R k cps = true ↔ ∃ cp ∈ cps, joinedAt R k cp.left cp.right ≠ true ∧
      saturatedAt R k cp.left = true ∧ saturatedAt R k cp.right = true := by
  simp [someApart, and_assoc]

theorem someApart_mono {R : List (Rule F V)} {k m : ℕ} (le : k ≤ m) {cps : List (CriticalPair F V)}
    (h : someApart R k cps = true) :
    someApart R m cps = true ∧ allJoined R m cps ≠ true := by
  obtain ⟨cp, mem, notJoined, sat₁, sat₂⟩ := someApart_spec.mp h
  obtain ⟨sat₁', same₁⟩ := saturated_persists sat₁ le
  obtain ⟨sat₂', same₂⟩ := saturated_persists sat₂ le
  have notJoined' : joinedAt R m cp.left cp.right ≠ true := by
    intro joined
    obtain ⟨u, left, right⟩ := joinedAt_iff.mp joined
    exact notJoined (joinedAt_iff.mpr ⟨u, (same₁ u).mp left, (same₂ u).mp right⟩)
  refine ⟨someApart_spec.mpr ⟨cp, mem, notJoined', sat₁', sat₂'⟩, fun all => notJoined' ?_⟩
  simp only [allJoined, List.all_eq_true] at all
  exact all cp mem

/-- Established: the certificate orients every rule and every critical pair joined. -/
theorem convergent_of_checks {R : List (Rule F V)} {I : LinearInterpretation F} {k : ℕ}
    (cert : R.all I.orients = true)
    (joined : allJoined R k (criticalPairsExact (overlaps R R)) = true) : ConvergentRules R := by
  intro W
  refine ⟨locallyConfluent_of_criticalPairs (criticalPairsExact_spec _) fun cp mem => ?_,
    I.terminating_of_orients fun ρ mem => List.all_eq_true.mp cert ρ mem⟩
  simp only [allJoined, List.all_eq_true] at joined
  exact joinedAt_sound (joined cp mem)

/-- Refuted: a critical pair whose reducts are exhausted and disjoint. -/
theorem not_convergent_of_apart {R : List (Rule F V)} {k : ℕ} (format : rulesWellFormed R = true)
    (apart : someApart R k (criticalPairsExact (overlaps R R)) = true) : ¬ ConvergentRules R := by
  obtain ⟨cp, mem, notJoined, sat₁, sat₂⟩ := someApart_spec.mp apart
  have notJoin := not_join_of_saturated (rulesWellFormed_iff.mp format) notJoined ⟨sat₁, sat₂⟩
  exact fun convergent => not_locallyConfluent_of_criticalPair (fun o h => h)
    (criticalPairsExact_spec _) mem notJoin (convergent (V ⊕ V)).1

/-- Refuted: a rule whose sides unify. -/
theorem not_convergent_of_loop {R : List (Rule F V)} (loop : loopExact R = .found) :
    ¬ ConvergentRules R :=
  fun convergent => not_terminating_of_loopSearch loop (convergent V).2

/-- **The admission check at a budget.** -/
def admissionRun (k : ℕ) (q : PromotionRequest F V) :
    AuthorityTheory.AuthorizedOutcome convergenceAuthority FragmentBoundary Unit q :=
  if format : rulesWellFormed q.rules = true then
    if loop : loopExact q.rules = .found then .refuted (not_convergent_of_loop loop)
    else if cert : q.rules.all q.certificate.orients = true then
      if joined : allJoined q.rules k (criticalPairsExact (overlaps q.rules q.rules)) = true then
        .established (convergent_of_checks cert joined)
      else if apart : someApart q.rules k (criticalPairsExact (overlaps q.rules q.rules)) = true then
        .refuted (not_convergent_of_apart format apart)
      else .incomplete ()
    else .outsideFragment .noTerminationCertificate
  else .outsideFragment .ruleFormat

/-- **The admission check is a graded check**: the budget only bounds the search for joins. -/
def admissionCheck :
    GradedChecking.GradedCheck (convergenceAuthority (F := F) (V := V)) FragmentBoundary Unit where
  run := admissionRun
  mono := by
    intro q small large le
    unfold admissionRun
    by_cases format : rulesWellFormed q.rules = true
    · rw [dif_pos format, dif_pos format]
      by_cases loop : loopExact q.rules = .found
      · rw [dif_pos loop, dif_pos loop]; exact .refuted _ _
      · rw [dif_neg loop, dif_neg loop]
        by_cases cert : q.rules.all q.certificate.orients = true
        · rw [dif_pos cert, dif_pos cert]
          by_cases joined : allJoined q.rules small (criticalPairsExact (overlaps q.rules q.rules)) = true
          · rw [dif_pos joined, dif_pos (allJoined_mono le joined)]
            exact .established _ _
          · rw [dif_neg joined]
            by_cases apart : someApart q.rules small (criticalPairsExact (overlaps q.rules q.rules)) = true
            · obtain ⟨apart', notAll⟩ := someApart_mono le apart
              rw [dif_pos apart, dif_neg notAll, dif_pos apart']
              exact .refuted _ _
            · rw [dif_neg apart]
              split
              · exact .incompleteEstablished _ _
              · split
                · exact .incompleteRefuted _ _
                · exact .incomplete _ _
        · rw [dif_neg cert, dif_neg cert]; exact .outsideFragment _
    · rw [dif_neg format, dif_neg format]; exact .outsideFragment _

/-- Reading the established outcome off checked components. -/
theorem admissionRun_established {k n : ℕ} {q : PromotionRequest F V}
    (format : rulesWellFormed q.rules = true) (noLoop : loopSearch n q.rules = .none)
    (cert : q.rules.all q.certificate.orients = true)
    (computed : (criticalPairsOf n (overlaps q.rules q.rules)).isSome = true)
    (joined : allJoined q.rules k ((criticalPairsOf n (overlaps q.rules q.rules)).get computed) = true) :
    ∃ evidence, admissionRun k q = .established evidence := by
  have loop : loopExact q.rules ≠ .found := by
    rw [loopExact_eq (by rw [noLoop]; exact fun h => by cases h), noLoop]
    exact fun h => by cases h
  rw [← criticalPairsExact_eq_get computed] at joined
  unfold admissionRun
  rw [dif_pos format, dif_neg loop, dif_pos cert, dif_pos joined]
  exact ⟨_, rfl⟩

/-- Reading a loop refutation off checked components. -/
theorem admissionRun_refuted_of_loop {k n : ℕ} {q : PromotionRequest F V}
    (format : rulesWellFormed q.rules = true) (found : loopSearch n q.rules = .found) :
    ∃ obstruction, admissionRun k q = .refuted obstruction := by
  have loop : loopExact q.rules = .found := by
    rw [loopExact_eq (by rw [found]; exact fun h => by cases h), found]
  unfold admissionRun
  rw [dif_pos format, dif_pos loop]
  exact ⟨_, rfl⟩

/-- **What an established admission gives**: convergence, the decision by normal forms on
every set of terms, and sound conversions in every model of the rules. -/
theorem admitted_of_established {k : ℕ} {q : PromotionRequest F V}
    {evidence : ConvergentRules q.rules} (_ran : admissionRun k q = .established evidence)
    {D : Type*} (I : Interpretation F D) (valid : ∀ ρ ∈ q.rules, I.Valid ρ) (W : Type v) :
    (∀ S : Set (Term F W), DecidedOn (Step q.rules) S) ∧
      ∀ {s t : Term F W}, EqvGen (Step q.rules) s t → ∀ α, I.eval α s = I.eval α t :=
  ⟨evidence.decidedOn W, fun converted α => I.conv_sound valid converted α⟩

/-! ## The two side conditions, computed -/

/-- **Promotion meets the overlap condition by joined critical pairs.** -/
theorem overlapCondition_of_criticalPairs {base delta : List (Rule F V)} {fuel : ℕ}
    {cps : List (CriticalPair F V)} (computed : criticalPairsOf fuel (deltaOverlaps base delta) = some cps)
    (joins : ∀ cp ∈ cps, Join (Steps (base ++ delta)) cp.left cp.right) (W : Type v) :
    ∀ o ∈ deltaOverlaps base delta, OverlapJoins (base ++ delta) o W :=
  fun _ member => overlapJoins_of_criticalPairs computed joins member

/-- **Promotion is convergent** when its critical pairs join and the extension terminates. -/
theorem promote_convergent {base delta : List (Rule F V)} {fuel : ℕ}
    {cps : List (CriticalPair F V)} (baseLC : ∀ W : Type v, LocallyConfluentAt base W)
    (computed : criticalPairsOf fuel (deltaOverlaps base delta) = some cps)
    (joins : ∀ cp ∈ cps, Join (Steps (base ++ delta)) cp.left cp.right)
    (terminationCondition : ∀ W : Type v, TerminatingAt (base ++ delta) W) :
    ConvergentRules (base ++ delta) :=
  extend_convergent baseLC (overlapCondition_of_criticalPairs computed joins) terminationCondition

/-- The test of fresh heads. -/
def freshHeadsCheck (base delta : List (Rule F V)) : Bool :=
  delta.all fun ρ =>
    (match ρ.lhs.head? with
      | some f => base.all fun ρ' => decide (f ∉ ρ'.lhs.symbols)
      | none => true) &&
    ρ.lhs.positions.all fun p =>
      decide (p.1.fill p.2 = p.2) || (base ++ delta).all fun ρ' => decide (p.2.head? ≠ ρ'.lhs.head?)

theorem freshHeads_of_check {base delta : List (Rule F V)} (h : freshHeadsCheck base delta = true) :
    FreshHeads base delta := by
  simp only [freshHeadsCheck, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  refine ⟨fun ρ mem f hf ρ' mem' => ?_, fun ρ mem p hp root ρ' mem' => ?_⟩
  · have := (h ρ mem).1
    rw [hf] at this
    dsimp only at this
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this ρ' mem'
  · rcases (h ρ mem).2 p hp with same | apart
    · exact absurd same root
    · exact apart ρ' mem'

instance : DecidableEq (Rule F V) := fun a b =>
  decidable_of_iff (a.lhs = b.lhs ∧ a.rhs = b.rhs) (by cases a; cases b; simp)

/-- The test that the rows do not overlap, at a fuel: every unification of two different left
sides fails. A `true` answer is sound at every fuel, because a failure is never exhaustion. -/
def rowsApartCheck (fuel : ℕ) (delta : List (Rule F V)) : Bool :=
  delta.all fun ρ₁ => delta.all fun ρ₂ =>
    decide (ρ₁ = ρ₂) ||
      match unify fuel [(ρ₁.lhs.rename Sum.inl, ρ₂.lhs.rename Sum.inr)] with
      | .fail => true
      | _ => false

theorem rowsApart_of_check {fuel : ℕ} {delta : List (Rule F V)}
    (h : rowsApartCheck fuel delta = true) : RowsApart delta := by
  intro ρ₁ mem₁ ρ₂ mem₂ ne W σ τ same
  simp only [rowsApartCheck, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h ρ₁ mem₁ ρ₂ mem₂ with equal | apart
  · exact ne equal
  · split at apart
    · rename_i hu
      apply unify_fail _ _ hu (Sum.elim σ τ)
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      simpa [rename_inl_subst, rename_inr_subst] using same
    · cases apart

/-- **Computed critical pairs that all join give local confluence**, on every variable type. -/
theorem locallyConfluent_of_allJoined {R : List (Rule F V)} {fuel k : ℕ}
    (computed : (criticalPairsOf fuel (overlaps R R)).isSome = true)
    (joined : allJoined R k ((criticalPairsOf fuel (overlaps R R)).get computed) = true)
    (W : Type v) : LocallyConfluentAt R W := by
  refine locallyConfluent_of_criticalPairs (Option.some_get computed).symm fun cp mem => ?_
  simp only [allJoined, List.all_eq_true] at joined
  exact joinedAt_sound (joined cp mem)

/-- **A computed critical pair refuted within the budget refutes local confluence.** -/
theorem not_locallyConfluent_of_someApart {R : List (Rule F V)} {fuel k : ℕ}
    (format : rulesWellFormed R = true)
    (computed : (criticalPairsOf fuel (overlaps R R)).isSome = true)
    (apart : someApart R k ((criticalPairsOf fuel (overlaps R R)).get computed) = true) :
    ¬ LocallyConfluentAt R (V ⊕ V) := by
  obtain ⟨cp, mem, notJoined, sat₁, sat₂⟩ := someApart_spec.mp apart
  exact not_locallyConfluent_of_criticalPair (fun o h => h) (Option.some_get computed).symm mem
    (not_join_of_saturated (rulesWellFormed_iff.mp format) notJoined ⟨sat₁, sat₂⟩)

/-! ## Supplied joins -/

/-- A supplied join of a critical pair: the common reduct and the two paths to it. -/
abbrev JoinWitness (F : Type u) (V : Type v) :=
  Term F (V ⊕ V) × List (Term F (V ⊕ V)) × List (Term F (V ⊕ V))

/-- Replay one supplied join per critical pair. -/
def joinsReplay (R : List (Rule F V)) (cps : List (CriticalPair F V))
    (witnesses : List (JoinWitness F V)) : Bool :=
  decide (cps.length = witnesses.length) &&
    (cps.zip witnesses).all fun p => checkJoin R p.1.left p.1.right p.2.1 p.2.2.1 p.2.2.2

/-- **Supplied joins, replayed by the kernel, join every critical pair.** -/
theorem joins_of_replay {R : List (Rule F V)} {cps : List (CriticalPair F V)}
    {witnesses : List (JoinWitness F V)} (h : joinsReplay R cps witnesses = true) :
    ∀ cp ∈ cps, Join (Steps R) cp.left cp.right := by
  simp only [joinsReplay, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨lengths, each⟩ := h
  intro cp mem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
  have hw : i < witnesses.length := lengths ▸ hi
  have member : (cps[i], witnesses[i]) ∈ cps.zip witnesses := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi, hw], by simp⟩
  exact checkJoin_sound (each _ member)

/-! ## What a `promote` request carries -/

/-- **A `promote` request.** The proposer supplies the new rules, a root justification of each
(validity in the model the root checker interprets), and a termination certificate. The base
rules and their validity are held by the bubble. The kernel computes everything else: the rule
format, the loop search, the critical pairs, and their joins within a budget (or the replay of
supplied joins). -/
structure PromoteRequest (F : Type u) (V : Type v) {D : Type*} (I : Interpretation F D) where
  request : PromotionRequest F V
  baseValid : ∀ ρ ∈ request.base, I.Valid ρ
  justification : ∀ ρ ∈ request.delta, I.Valid ρ

/-- **An admitted `promote` request keeps the bubble's conversion sound and decided by normal
forms.** -/
theorem PromoteRequest.admitted {D : Type*} {I : Interpretation F D} (p : PromoteRequest F V I)
    {k : ℕ} {evidence : ConvergentRules p.request.rules}
    (ran : admissionRun k p.request = .established evidence) (W : Type v) :
    (∀ S : Set (Term F W), DecidedOn (Step p.request.rules) S) ∧
      ∀ {s t : Term F W}, EqvGen (Step p.request.rules) s t → ∀ α, I.eval α s = I.eval α t := by
  refine admitted_of_established ran I (fun ρ mem => ?_) W
  rcases List.mem_append.mp mem with base | delta
  · exact p.baseValid ρ base
  · exact p.justification ρ delta

end Exact

/-! ## Axiom audit -/

#print axioms extend_convergent
#print axioms overlapCondition_of_freshHeads
#print axioms admit_convergent
#print axioms promote_convergent
#print axioms admissionCheck
#print axioms admissionRun_established
#print axioms admitted_of_established
#print axioms normalize_decides
#print axioms joins_of_replay
#print axioms PromoteRequest.admitted

end Mettapedia.TypeTheory.PromotionAdmission
