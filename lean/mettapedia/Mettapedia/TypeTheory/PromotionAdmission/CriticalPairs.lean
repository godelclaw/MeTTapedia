import Mettapedia.TypeTheory.PromotionAdmission.Unification

/-!
# Critical pairs: computed, complete, and enough for local confluence

Two steps from one term either happen in disjoint arguments, or one happens inside the part
of the other's left side that a variable matched, or the second left side overlaps a
non-variable position of the first. The first two kinds always join. The third kind is
captured by finitely many **critical pairs**, one for each rule, each non-variable position
of its left side, and each rule whose left side unifies there.

* **The pattern lemma** (`step_of_instance`): a step from an instance of a pattern either
  rewrites at a non-variable position of the pattern (an overlap), or rewrites inside the
  value of one variable, and then the result reduces back to an instance of the pattern.
* **The critical-pair lemma** (`locallyConfluent_of_overlapsJoin`): if every overlap instance
  joins, the steps are locally confluent. This is the theorem of Knuth and Bendix (1970) and
  Huet (1980), for rules that need not be linear.
* **The computation** (`criticalPairsOf`): rename the two rules apart (`Sum.inl`, `Sum.inr`),
  unify, and read off the pair. It answers `none` exactly when some unification ran out of
  fuel; some fuel always decides (`criticalPairsOf_eventually`). Every overlap instance is an
  instance of a computed pair (`overlapJoins_of_criticalPairs`): **all overlaps are found**.
  Conversely every computed pair is a genuine peak (`criticalPair_peak`), so one that does not
  join refutes local confluence (`not_locallyConfluent_of_criticalPair`).
* **Promotion only needs the new overlaps** (`locallyConfluent_extend`): when the base is
  locally confluent, the overlaps of the new rules against all rules, and of the base rules
  against the new ones, are the only ones to check.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u v w w'

open Term Relation

variable {F : Type u} {V : Type v}

/-- **Local confluence** of the steps of a rule list on terms over `W`. -/
def LocallyConfluentAt (R : List (Rule F V)) (W : Type w) : Prop :=
  ∀ s t₁ t₂ : Term F W, Step R s t₁ → Step R s t₂ → Join (Steps R) t₁ t₂

/-- An overlap: an outer rule, a non-variable position of its left side, an inner rule. -/
structure Overlap (F : Type u) (V : Type v) where
  outer : Rule F V
  inner : Rule F V
  position : Ctx F V × Term F V

/-- Every instance of the overlap's peak joins. -/
def OverlapJoins (R : List (Rule F V)) (o : Overlap F V) (W : Type w) : Prop :=
  ∀ σ τ : V → Term F W, o.position.2.subst σ = o.inner.lhs.subst τ →
    Join (Steps R) (o.outer.rhs.subst σ) ((o.position.1.subst σ).fill (o.inner.rhs.subst τ))

/-- The overlaps of the rules `A` with inner rules `B`. -/
def overlaps (A B : List (Rule F V)) : List (Overlap F V) :=
  A.flatMap fun ρ₁ => B.flatMap fun ρ₂ => ρ₁.lhs.positions.map fun p => ⟨ρ₁, ρ₂, p⟩

theorem mem_overlaps {A B : List (Rule F V)} {ρ₁ ρ₂ : Rule F V} {p : Ctx F V × Term F V}
    (h₁ : ρ₁ ∈ A) (h₂ : ρ₂ ∈ B) (hp : p ∈ ρ₁.lhs.positions) : (⟨ρ₁, ρ₂, p⟩ : Overlap F V) ∈ overlaps A B := by
  simp only [overlaps, List.mem_flatMap, List.mem_map]
  exact ⟨ρ₁, h₁, ρ₂, h₂, p, hp, rfl⟩

theorem mem_overlaps_iff {A B : List (Rule F V)} {o : Overlap F V} :
    o ∈ overlaps A B ↔ o.outer ∈ A ∧ o.inner ∈ B ∧ o.position ∈ o.outer.lhs.positions := by
  constructor
  · intro member
    simp only [overlaps, List.mem_flatMap, List.mem_map] at member
    obtain ⟨ρ₁, h₁, ρ₂, h₂, p, hp, rfl⟩ := member
    exact ⟨h₁, h₂, hp⟩
  · rintro ⟨h₁, h₂, hp⟩
    exact mem_overlaps h₁ h₂ hp

/-! ## Inversion of a step at an application -/

variable {W : Type w} {X : Type w'}

theorem Step.cases_app {R : List (Rule F V)} {f : F} {args : List (Term F W)} {u : Term F W}
    (step : Step R (.app f args) u) :
    (∃ ρ ∈ R, ∃ τ : V → Term F W, Term.app f args = ρ.lhs.subst τ ∧ u = ρ.rhs.subst τ) ∨
      ∃ (i : ℕ) (h : i < args.length) (t' : Term F W),
        Step R args[i] t' ∧ u = .app f (args.set i t') := by
  generalize hs : Term.app f args = s at step
  cases step with
  | root mem τ =>
      exact Or.inl ⟨_, mem, τ, rfl, rfl⟩
  | arg g args' i h inner =>
      injection hs with hf hargs
      subst hf hargs
      exact Or.inr ⟨i, h, _, inner, rfl⟩

theorem Steps.set {R : List (Rule F V)} (f : F) (args : List (Term F W)) (i : ℕ)
    (h : i < args.length) {a : Term F W} (steps : Steps R args[i] a) :
    Steps R (.app f args) (.app f (args.set i a)) := by
  induction steps with
  | refl => rw [List.set_getElem_self]
  | tail _ step ih =>
      refine ih.tail ?_
      have stepped := Step.arg (R := R) f (args.set i _) i (by simpa using h)
        (by simpa using step)
      simpa using stepped

/-! ## The pattern lemma -/

/-- **A step from an instance of a pattern** rewrites at a non-variable position of the
pattern, or inside the value of one of its variables; in the second case the result reduces
to an instance of the pattern with that value replaced. -/
theorem step_of_instance [DecidableEq X] {R : List (Rule F V)} :
    ∀ (l : Term F X) (σ : X → Term F W) {u : Term F W}, Step R (l.subst σ) u →
      (∃ p ∈ l.positions, ∃ ρ ∈ R, ∃ τ : V → Term F W,
          p.2.subst σ = ρ.lhs.subst τ ∧ u = (p.1.subst σ).fill (ρ.rhs.subst τ)) ∨
        ∃ x ∈ l.vars, ∃ t' : Term F W, Step R (σ x) t' ∧
          Steps R u (l.subst (Function.update σ x t')) := by
  intro l
  induction l using Term.induction' with
  | var x =>
      intro σ u step
      refine Or.inr ⟨x, by simp, u, by simpa using step, ?_⟩
      simp only [subst_var, Function.update_self]
      exact .refl
  | app g ls ih =>
      intro σ u step
      rw [subst_app] at step
      rcases Step.cases_app step with ⟨ρ, mem, τ, same, rfl⟩ | ⟨i, h, t', inner, rfl⟩
      · refine Or.inl ⟨(.hole, .app g ls), by simp [positions], ρ, mem, τ, ?_, rfl⟩
        simpa using same
      · have hi : i < ls.length := by simpa using h
        have elem : (ls.map (Term.subst σ))[i] = ls[i].subst σ := List.getElem_map _
        rw [elem] at inner
        rcases ih ls[i] (List.getElem_mem hi) σ inner with
          ⟨p, pMember, ρ, mem, τ, same, rfl⟩ | ⟨x, xMember, t'', xStep, back⟩
        · left
          refine ⟨(.app g (ls.take i) p.1 (ls.drop (i + 1)), p.2), ?_, ρ, mem, τ, same, ?_⟩
          · obtain ⟨filled, isApp⟩ := (mem_positions_iff _ _ _).mp pMember
            refine (mem_positions_iff _ _ _).mpr ⟨?_, isApp⟩
            simp only [Ctx.fill, filled]
            rw [List.getElem_cons_drop, List.take_append_drop]
          · simp only [Ctx.subst, Ctx.fill]
            rw [List.set_eq_take_cons_drop _ h, List.map_take, List.map_drop]
        · right
          refine ⟨x, ?_, t'', xStep, ?_⟩
          · simp only [vars_app, List.mem_flatMap]
            exact ⟨ls[i], List.getElem_mem hi, xMember⟩
          · simp only [subst_app]
            have each : ∀ y, Steps R (σ y) (Function.update σ x t'' y) := by
              intro y
              by_cases same : y = x
              · subst same; simpa using Relation.ReflTransGen.single xStep
              · simp [Function.update_of_ne same]; exact .refl
            have pointwise : List.Forall₂ (Steps R) ((ls.map (Term.subst σ)).set i t')
                (ls.map (Term.subst (Function.update σ x t''))) := by
              rw [List.forall₂_iff_get]
              refine ⟨by simp, fun j h₁ h₂ => ?_⟩
              simp only [List.get_eq_getElem, List.getElem_map]
              by_cases same : j = i
              · subst same
                simpa using back
              · rw [List.getElem_set_ne (Ne.symm same)]
                simpa using Steps.subst_pointwise each (ls[j]'(by simpa using h₂))
            simpa using Steps.args (R := R) g [] pointwise

/-! ## The critical-pair lemma -/

/-- **The critical-pair lemma**: if every overlap instance of the rules joins, their steps are
locally confluent. -/
theorem locallyConfluent_of_overlapsJoin [DecidableEq V] {R : List (Rule F V)}
    (joins : ∀ o ∈ overlaps R R, OverlapJoins R o W) : LocallyConfluentAt R W := by
  intro s t₁ t₂ first second
  induction first generalizing t₂ with
  | root mem σ =>
      rcases step_of_instance _ σ second with
        ⟨p, pMember, ρ₂, mem₂, τ, same, rfl⟩ | ⟨x, _, t', xStep, back⟩
      · exact joins _ (mem_overlaps mem mem₂ pMember) σ τ same
      · refine ⟨_, Steps.subst_pointwise (fun y => ?_) _, back.tail (.root mem _)⟩
        by_cases same : y = x
        · subst same; simpa using Relation.ReflTransGen.single xStep
        · simp [Function.update_of_ne same]; exact .refl
  | @arg f args i h t₁' inner ih =>
      rcases Step.cases_app second with ⟨ρ₂, mem₂, τ, same, rfl⟩ | ⟨j, h', t₂', inner₂, rfl⟩
      · have outer : Step R (ρ₂.lhs.subst τ) (.app f (args.set i t₁')) :=
          same ▸ Step.arg f args i h inner
        rcases step_of_instance _ τ outer with
          ⟨p, pMember, ρ₁, mem₁, σ, same', hu⟩ | ⟨x, _, t', xStep, back⟩
        · obtain ⟨w, left, right⟩ := joins _ (mem_overlaps mem₂ mem₁ pMember) τ σ same'
          rw [← hu] at right
          exact ⟨w, right, left⟩
        · refine ⟨_, back.tail (.root mem₂ _), Steps.subst_pointwise (fun y => ?_) _⟩
          by_cases same : y = x
          · subst same; simpa using Relation.ReflTransGen.single xStep
          · simp [Function.update_of_ne same]; exact .refl
      · by_cases sameIndex : i = j
        · subst sameIndex
          obtain ⟨w, left, right⟩ := ih t₂' inner₂
          refine ⟨.app f (args.set i w), ?_, ?_⟩
          · have := Steps.set (R := R) f (args.set i t₁') i (by simpa using h) (by simpa using left)
            simpa using this
          · have := Steps.set (R := R) f (args.set i t₂') i (by simpa using h)
              (by simpa using right)
            simpa using this
        · refine ⟨.app f ((args.set i t₁').set j t₂'), ?_, ?_⟩
          · refine Relation.ReflTransGen.single ?_
            exact Step.arg f _ j (by simpa using h')
              (by rw [List.getElem_set_ne sameIndex]; exact inner₂)
          · rw [List.set_comm _ _ sameIndex]
            refine Relation.ReflTransGen.single ?_
            exact Step.arg f _ i (by simpa using h)
              (by rw [List.getElem_set_ne (Ne.symm sameIndex)]; exact inner)

/-- An overlap of rules of a locally confluent list joins in that list. -/
theorem overlapJoins_of_locallyConfluent {R : List (Rule F V)} (lc : LocallyConfluentAt R W)
    {o : Overlap F V} (outer : o.outer ∈ R) (inner : o.inner ∈ R)
    (position : o.position ∈ o.outer.lhs.positions) : OverlapJoins R o W := by
  intro σ τ same
  obtain ⟨filled, _⟩ := (mem_positions_iff _ _ _).mp position
  apply lc (o.outer.lhs.subst σ)
  · exact .root outer σ
  · rw [← filled, Ctx.fill_subst, same]
    exact Ctx.step_fill _ (.root inner τ)

theorem OverlapJoins.mono {R R' : List (Rule F V)} (sub : ∀ ρ ∈ R, ρ ∈ R') {o : Overlap F V}
    (joins : OverlapJoins R o W) : OverlapJoins R' o W := by
  intro σ τ same
  obtain ⟨w, left, right⟩ := joins σ τ same
  exact ⟨w, left.mono sub, right.mono sub⟩

/-- The overlaps a promotion adds: new rules against all rules, base rules against new ones. -/
def deltaOverlaps (base delta : List (Rule F V)) : List (Overlap F V) :=
  overlaps delta (base ++ delta) ++ overlaps base delta

/-- **Promotion only needs the new overlaps.** -/
theorem locallyConfluent_extend [DecidableEq V] {base delta : List (Rule F V)}
    (baseLC : LocallyConfluentAt base W)
    (joins : ∀ o ∈ deltaOverlaps base delta, OverlapJoins (base ++ delta) o W) :
    LocallyConfluentAt (base ++ delta) W := by
  apply locallyConfluent_of_overlapsJoin
  intro o member
  obtain ⟨outer, inner, position⟩ := mem_overlaps_iff.mp member
  rcases List.mem_append.mp outer with outerBase | outerDelta
  · rcases List.mem_append.mp inner with innerBase | innerDelta
    · exact (overlapJoins_of_locallyConfluent baseLC outerBase innerBase position).mono
        (fun ρ h => List.mem_append_left _ h)
    · exact joins o (List.mem_append_right _ (mem_overlaps_iff.mpr ⟨outerBase, innerDelta, position⟩))
  · exact joins o (List.mem_append_left _ (mem_overlaps_iff.mpr ⟨outerDelta, inner, position⟩))

/-! ## Computed critical pairs -/

/-- A critical pair: the peak and its two reducts, over the two renamed-apart rule
variables. -/
structure CriticalPair (F : Type u) (V : Type v) where
  peak : Term F (V ⊕ V)
  left : Term F (V ⊕ V)
  right : Term F (V ⊕ V)

namespace Overlap

/-- The equation whose unifiers are the overlap's instances. -/
def unification (o : Overlap F V) : List (Term F (V ⊕ V) × Term F (V ⊕ V)) :=
  [(o.position.2.rename Sum.inl, o.inner.lhs.rename Sum.inr)]

/-- The critical pair of an overlap at a unifier. -/
def criticalPair (o : Overlap F V) (θ : V ⊕ V → Term F (V ⊕ V)) : CriticalPair F V where
  peak := (o.outer.lhs.rename Sum.inl).subst θ
  left := (o.outer.rhs.rename Sum.inl).subst θ
  right := ((o.position.1.subst fun x => .var (Sum.inl x)).subst θ).fill
    ((o.inner.rhs.rename Sum.inr).subst θ)

end Overlap

/-- The two renamed-apart substitutions, side by side. -/
theorem rename_inl_subst {σ τ : V → Term F W} (t : Term F V) :
    (t.rename Sum.inl).subst (Sum.elim σ τ) = t.subst σ := by
  rw [rename, subst_subst]; rfl

theorem rename_inr_subst {σ τ : V → Term F W} (t : Term F V) :
    (t.rename Sum.inr).subst (Sum.elim σ τ) = t.subst τ := by
  rw [rename, subst_subst]; rfl

section Computed

variable [DecidableEq F] [DecidableEq V]

/-- **The critical pairs of a list of overlaps at a fuel**; `none` when a unification ran
out of fuel. A failed unification contributes nothing: it has no instance. -/
def criticalPairsOf (fuel : ℕ) : List (Overlap F V) → Option (List (CriticalPair F V))
  | [] => some []
  | o :: os =>
      match unify fuel o.unification, criticalPairsOf fuel os with
      | .outOfFuel, _ => none
      | _, none => none
      | .fail, some cps => some cps
      | .ok θ, some cps => some (o.criticalPair θ :: cps)

theorem criticalPairsOf_complete {fuel : ℕ} :
    ∀ {os : List (Overlap F V)} {cps : List (CriticalPair F V)},
      criticalPairsOf fuel os = some cps → ∀ o ∈ os,
        unify fuel o.unification ≠ .outOfFuel ∧
          ∀ θ, unify fuel o.unification = .ok θ → o.criticalPair θ ∈ cps
  | [], _, _, o, member => by simp at member
  | o' :: os, cps, h, o, member => by
      simp only [criticalPairsOf] at h
      split at h
      · cases h
      · cases h
      · rename_i cps' hu hrest
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp member with rfl | later
        · refine ⟨?_, ?_⟩
          · rw [hu]; exact fun h => by cases h
          · intro θ hθ; rw [hu] at hθ; cases hθ
        · exact criticalPairsOf_complete hrest o later
      · rename_i θ' cps' hu hrest
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp member with rfl | later
        · refine ⟨?_, fun θ hθ => ?_⟩
          · rw [hu]; exact fun h => by cases h
          rw [hu] at hθ
          cases hθ
          exact List.mem_cons_self
        · obtain ⟨decided, listed⟩ := criticalPairsOf_complete hrest o later
          exact ⟨decided, fun θ hθ => List.mem_cons_of_mem _ (listed θ hθ)⟩

theorem criticalPairsOf_sound {fuel : ℕ} :
    ∀ {os : List (Overlap F V)} {cps : List (CriticalPair F V)},
      criticalPairsOf fuel os = some cps → ∀ cp ∈ cps,
        ∃ o ∈ os, ∃ θ, unify fuel o.unification = .ok θ ∧ cp = o.criticalPair θ
  | [], cps, h, cp, member => by
      simp only [criticalPairsOf, Option.some.injEq] at h; subst h; simp at member
  | o :: os, cps, h, cp, member => by
      simp only [criticalPairsOf] at h
      split at h
      · cases h
      · cases h
      · rename_i cps' hu hrest
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨o', oMember, θ, hθ, rfl⟩ := criticalPairsOf_sound hrest cp member
        exact ⟨o', List.mem_cons_of_mem _ oMember, θ, hθ, rfl⟩
      · rename_i θ cps' hu hrest
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨o, List.mem_cons_self, θ, hu, rfl⟩
        · obtain ⟨o', oMember, θ', hθ, rfl⟩ := criticalPairsOf_sound hrest cp later
          exact ⟨o', List.mem_cons_of_mem _ oMember, θ', hθ, rfl⟩

theorem criticalPairsOf_some_of_decided {fuel : ℕ} :
    ∀ {os : List (Overlap F V)}, (∀ o ∈ os, unify fuel o.unification ≠ .outOfFuel) →
      ∃ cps, criticalPairsOf fuel os = some cps
  | [], _ => ⟨[], rfl⟩
  | o :: os, decided => by
      obtain ⟨cps, hrest⟩ := criticalPairsOf_some_of_decided (os := os)
        (fun o' h => decided o' (List.mem_cons_of_mem _ h))
      have here := decided o List.mem_cons_self
      simp only [criticalPairsOf, hrest]
      cases hu : unify fuel o.unification with
      | ok θ => exact ⟨_, rfl⟩
      | fail => exact ⟨_, rfl⟩
      | outOfFuel => exact absurd hu here

/-- **More fuel keeps a computed list of critical pairs.** -/
theorem criticalPairsOf_mono {fuel fuel' : ℕ} (le : fuel ≤ fuel')
    {os : List (Overlap F V)} {cps : List (CriticalPair F V)}
    (h : criticalPairsOf fuel os = some cps) : criticalPairsOf fuel' os = some cps := by
  induction os generalizing cps with
  | nil => simpa [criticalPairsOf] using h
  | cons o os ih =>
      have decided := (criticalPairsOf_complete h o List.mem_cons_self).1
      simp only [criticalPairsOf] at h ⊢
      rw [unify_mono fuel _ fuel' le decided]
      split at h
      · cases h
      · cases h
      · rename_i cps' hu hrest
        rw [ih hrest, hu]
        exact h
      · rename_i θ cps' hu hrest
        rw [ih hrest, hu]
        exact h

/-- **Some fuel computes the critical pairs.** -/
theorem criticalPairsOf_eventually (os : List (Overlap F V)) :
    ∃ fuel cps, criticalPairsOf fuel os = some cps := by
  have each : ∀ o ∈ os, ∃ n, unify n o.unification ≠ .outOfFuel :=
    fun o _ => unify_terminates o.unification
  choose n hn using each
  let fuel := (os.attach.map fun o => n o.1 o.2).sum
  have le : ∀ o (h : o ∈ os), n o h ≤ fuel := by
    intro o h
    exact nat_le_sum_of_mem (List.mem_map.mpr ⟨⟨o, h⟩, List.mem_attach _ _, rfl⟩)
  obtain ⟨cps, hcps⟩ := criticalPairsOf_some_of_decided (fuel := fuel) (os := os)
    (fun o h => by rw [unify_mono _ _ fuel (le o h) (hn o h)]; exact hn o h)
  exact ⟨fuel, cps, hcps⟩

/-- **All overlaps are found**: an overlap whose computed critical pair joins has every
instance joined. -/
theorem overlapJoins_of_criticalPairs {R : List (Rule F V)} {fuel : ℕ}
    {os : List (Overlap F V)} {cps : List (CriticalPair F V)}
    (computed : criticalPairsOf fuel os = some cps)
    (joins : ∀ cp ∈ cps, Join (Steps R) cp.left cp.right) {o : Overlap F V} (member : o ∈ os) :
    OverlapJoins R o W := by
  intro σ τ same
  let ρ : V ⊕ V → Term F W := Sum.elim σ τ
  have unifies : Unifies ρ o.unification := by
    intro p hp
    simp only [Overlap.unification, List.mem_singleton] at hp
    subst hp
    simp only [ρ, rename_inl_subst, rename_inr_subst]
    exact same
  obtain ⟨decided, listed⟩ := criticalPairsOf_complete computed o member
  cases hu : unify fuel o.unification with
  | outOfFuel => exact absurd hu decided
  | fail => exact absurd unifies (unify_fail fuel _ hu ρ)
  | ok θ =>
      have general : (fun y => (θ y).subst ρ) = ρ := funext (unify_ok_general hu ρ unifies)
      obtain ⟨w, left, right⟩ := joins _ (listed θ hu)
      refine ⟨w.subst ρ, ?_, ?_⟩
      · have := left.subst ρ
        simp only [Overlap.criticalPair, subst_subst, general] at this
        simpa [ρ, rename_inl_subst] using this
      · have := right.subst ρ
        simp only [Overlap.criticalPair, Ctx.fill_subst, subst_subst, Ctx.subst_subst,
          general] at this
        have outer : o.position.1.subst (fun x => (Term.var (Sum.inl x) : Term F (V ⊕ V)).subst ρ) =
            o.position.1.subst σ := rfl
        simpa [ρ, rename_inr_subst, outer] using this

/-- **The critical-pair lemma, computed**: if the computed critical pairs of all overlaps
join, the steps are locally confluent. -/
theorem locallyConfluent_of_criticalPairs {R : List (Rule F V)} {fuel : ℕ}
    {cps : List (CriticalPair F V)} (computed : criticalPairsOf fuel (overlaps R R) = some cps)
    (joins : ∀ cp ∈ cps, Join (Steps R) cp.left cp.right) : LocallyConfluentAt R W :=
  locallyConfluent_of_overlapsJoin fun _ member =>
    overlapJoins_of_criticalPairs computed joins member

/-- **Promotion, computed**: a locally confluent base and joined critical pairs of the new
overlaps give local confluence of the extension. -/
theorem locallyConfluent_extend_of_criticalPairs {base delta : List (Rule F V)} {fuel : ℕ}
    {cps : List (CriticalPair F V)} (baseLC : LocallyConfluentAt base W)
    (computed : criticalPairsOf fuel (deltaOverlaps base delta) = some cps)
    (joins : ∀ cp ∈ cps, Join (Steps (base ++ delta)) cp.left cp.right) :
    LocallyConfluentAt (base ++ delta) W :=
  locallyConfluent_extend baseLC fun _ member =>
    overlapJoins_of_criticalPairs computed joins member

/-- **Every computed critical pair is a genuine peak.** -/
theorem criticalPair_peak {R : List (Rule F V)} {o : Overlap F V} {θ : V ⊕ V → Term F (V ⊕ V)}
    (outer : o.outer ∈ R) (inner : o.inner ∈ R) (position : o.position ∈ o.outer.lhs.positions)
    {fuel : ℕ} (hu : unify fuel o.unification = .ok θ) :
    Step R (o.criticalPair θ).peak (o.criticalPair θ).left ∧
      Step R (o.criticalPair θ).peak (o.criticalPair θ).right := by
  have unified := unify_ok_unify hu
  have eq := unified _ (List.mem_singleton_self _)
  simp only at eq
  obtain ⟨filled, _⟩ := (mem_positions_iff _ _ _).mp position
  refine ⟨?_, ?_⟩
  · simp only [Overlap.criticalPair, rename, subst_subst]
    exact .root outer _
  · simp only [Overlap.criticalPair]
    rw [← filled, rename, Ctx.fill_subst, Ctx.fill_subst, ← rename, eq, rename, subst_subst,
      rename, subst_subst]
    exact Ctx.step_fill _ (.root inner _)

/-- **A computed critical pair that does not join refutes local confluence.** -/
theorem not_locallyConfluent_of_criticalPair {R : List (Rule F V)} {fuel : ℕ}
    {os : List (Overlap F V)} (sub : ∀ o ∈ os, o ∈ overlaps R R)
    {cps : List (CriticalPair F V)} (computed : criticalPairsOf fuel os = some cps)
    {cp : CriticalPair F V} (member : cp ∈ cps) (apart : ¬ Join (Steps R) cp.left cp.right) :
    ¬ LocallyConfluentAt R (V ⊕ V) := by
  intro lc
  obtain ⟨o, oMember, θ, hu, rfl⟩ := criticalPairsOf_sound computed cp member
  obtain ⟨outer, inner, position⟩ := mem_overlaps_iff.mp (sub o oMember)
  obtain ⟨toLeft, toRight⟩ := criticalPair_peak outer inner position hu
  exact apart (lc _ _ _ toLeft toRight)

end Computed

end Mettapedia.TypeTheory.PromotionAdmission
