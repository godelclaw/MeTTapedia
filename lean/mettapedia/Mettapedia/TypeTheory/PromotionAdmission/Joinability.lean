import Mettapedia.TypeTheory.PromotionAdmission.CriticalPairs
import Mettapedia.TypeTheory.GradedCheck
import Mathlib.Data.List.Dedup

/-!
# Joining a pair within a budget: four outcomes, and "unknown" is never "refuted"

A critical pair is checked by looking for a common reduct. The search is bounded, so its
answer is one of the four outcomes of a graded check (`GradedChecking.GradedCheck`):

* **established**: a common reduct was found within the budget (`joinRun`, sound by
  `reach_sound`);
* **refuted**: both reduct sets were exhausted within the budget (every reduct of a reached
  term was already reached) and they are disjoint. This needs the reducts to be complete,
  which they are for well-formed rules (`mem_reducts_of_step`);
* **outside the fragment**: some rule is not well formed, so reducts cannot be enumerated and
  no refutation would be sound;
* **incomplete**: neither, at this budget.

The check is monotone in the budget (`joinCheck`): a join found persists, an exhausted search
stays exhausted, and only an incomplete answer can change. A pair answered "incomplete" at
one budget and "established" at a larger one is the control
(`Controls.incomplete_then_established`): budget exhaustion is not refutation.

The executable parts: matching with consistency of repeated variables (`matchTerm`,
sound and complete), instantiation (`inst`), all one-step reducts (`reducts`, sound and, for
well-formed rules, complete), the terms reached within `k` steps (`reach`), and the replay of
a supplied join (`checkJoin`, sound), which is how a proposer can hand the kernel the evidence
for a critical pair instead of a budget.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u v w

open Term Relation

variable {F : Type u} {V : Type v} {W : Type w}

/-! ## Matching -/

/-- The partial substitution agrees with a total one. -/
def Extends (b : V → Option (Term F W)) (σ : V → Term F W) : Prop :=
  ∀ x t, b x = some t → σ x = t

/-- One partial substitution extends another. -/
def Grows (b b' : V → Option (Term F W)) : Prop :=
  ∀ x t, b x = some t → b' x = some t

theorem Grows.trans {b₁ b₂ b₃ : V → Option (Term F W)} (h₁ : Grows b₁ b₂) (h₂ : Grows b₂ b₃) :
    Grows b₁ b₃ := fun x t h => h₂ x t (h₁ x t h)

/-! ## Instantiation of a right side -/

mutual
/-- Instantiate by partial bindings; `none` when a variable is unbound. -/
def inst (b : V → Option (Term F W)) : Term F V → Option (Term F W)
  | .var x => b x
  | .app f rs => (instList b rs).map (.app f)
/-- Instantiate a list. -/
def instList (b : V → Option (Term F W)) : List (Term F V) → Option (List (Term F W))
  | [] => some []
  | r :: rs =>
      match inst b r, instList b rs with
      | some t, some ts => some (t :: ts)
      | _, _ => none
end

theorem inst_sound {b : V → Option (Term F W)} {σ : V → Term F W} (ext : Extends b σ) :
    ∀ (r : Term F V) (t : Term F W), inst b r = some t → t = r.subst σ := by
  intro r
  induction r using Term.induction' with
  | var x => intro t h; simp only [inst] at h; simpa using (ext x t h).symm
  | app f rs ih =>
      intro t h
      have list : ∀ (rs' : List (Term F V)) (ts : List (Term F W)), (∀ a ∈ rs', a ∈ rs) →
          instList b rs' = some ts → ts = rs'.map (Term.subst σ) := by
        intro rs'
        induction rs' with
        | nil => intro ts _ h; simp only [instList, Option.some.injEq] at h; simp [← h]
        | cons a rest ihRest =>
            intro ts sub h
            simp only [instList] at h
            split at h
            · rename_i t₁ ts₁ h₁ h₂
              simp only [Option.some.injEq] at h
              subst h
              simp [ih a (sub a (by simp)) t₁ h₁, ihRest ts₁ (fun c hc => sub c (by simp [hc])) h₂]
            · cases h
      simp only [inst, Option.map_eq_some_iff] at h
      obtain ⟨ts, hts, rfl⟩ := h
      simp [list rs ts (fun a h => h) hts]

theorem inst_isSome {b : V → Option (Term F W)} :
    ∀ (r : Term F V), (∀ x ∈ r.vars, ∃ t, b x = some t) → ∃ t, inst b r = some t := by
  intro r
  induction r using Term.induction' with
  | var x => intro bound; simpa [inst] using bound x (by simp)
  | app f rs ih =>
      intro bound
      have list : ∀ (rs' : List (Term F V)), (∀ a ∈ rs', a ∈ rs) →
          (∀ x ∈ rs'.flatMap Term.vars, ∃ t, b x = some t) → ∃ ts, instList b rs' = some ts := by
        intro rs'
        induction rs' with
        | nil => intro _ _; exact ⟨[], rfl⟩
        | cons a rest ihRest =>
            intro sub bound'
            obtain ⟨t₁, h₁⟩ := ih a (sub a (by simp)) (fun x hx => bound' x (by simp [hx]))
            obtain ⟨ts₁, h₂⟩ := ihRest (fun c hc => sub c (by simp [hc]))
              (fun x hx => bound' x (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hx))
            exact ⟨t₁ :: ts₁, by simp [instList, h₁, h₂]⟩
      obtain ⟨ts, h⟩ := list rs (fun a h => h) (by simpa using bound)
      exact ⟨.app f ts, by simp [inst, h]⟩

section Matching

variable [DecidableEq F] [DecidableEq V] [DecidableEq W]

mutual
/-- **Match a pattern** against a term, extending partial bindings; a repeated variable must
match equal terms. -/
def matchTerm : Term F V → Term F W → (V → Option (Term F W)) → Option (V → Option (Term F W))
  | .var x, t, b =>
      match b x with
      | none => some fun y => if y = x then some t else b y
      | some t' => if t' = t then some b else none
  | .app f ls, .app g ts, b => if f = g then matchList ls ts b else none
  | .app _ _, .var _, _ => none
/-- Match a list of patterns against a list of terms of the same length. -/
def matchList : List (Term F V) → List (Term F W) → (V → Option (Term F W)) →
    Option (V → Option (Term F W))
  | [], [], b => some b
  | l :: ls, t :: ts, b =>
      match matchTerm l t b with
      | none => none
      | some b' => matchList ls ts b'
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
end

theorem matchTerm_sound :
    ∀ (l : Term F V) (t : Term F W) (b b' : V → Option (Term F W)), matchTerm l t b = some b' →
      Grows b b' ∧ (∀ x ∈ l.vars, ∃ t', b' x = some t') ∧
        ∀ σ, Extends b' σ → l.subst σ = t := by
  intro l
  induction l using Term.induction' with
  | var x =>
      intro t b b' h
      simp only [matchTerm] at h
      split at h
      · rename_i none
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun y t' hy => ?_, fun y hy => ?_, fun σ ext => ?_⟩
        · have : y ≠ x := fun same => by rw [same, none] at hy; cases hy
          simp [this, hy]
        · simp at hy; subst hy; exact ⟨t, by simp⟩
        · simpa using ext x t (by simp)
      · rename_i t' bound
        split at h
        · rename_i same
          simp only [Option.some.injEq] at h
          subst h same
          exact ⟨fun _ _ h => h, fun y hy => by simp at hy; subst hy; exact ⟨_, bound⟩,
            fun σ ext => by simpa using ext x _ bound⟩
        · cases h
  | app f ls ih =>
      intro t b b' h
      cases t with
      | var _ => simp [matchTerm] at h
      | app g ts =>
          simp only [matchTerm] at h
          split at h
          · rename_i same
            subst same
            have list : ∀ (ls' : List (Term F V)) (ts : List (Term F W)) (b b' : V → Option (Term F W)),
                (∀ a ∈ ls', a ∈ ls) → matchList ls' ts b = some b' →
                  Grows b b' ∧ (∀ x ∈ ls'.flatMap Term.vars, ∃ t', b' x = some t') ∧
                    ∀ σ, Extends b' σ → ls'.map (Term.subst σ) = ts := by
              intro ls'
              induction ls' with
              | nil =>
                  intro ts b b' _ h
                  cases ts with
                  | nil =>
                      simp only [matchList, Option.some.injEq] at h
                      subst h
                      exact ⟨fun _ _ h => h, by simp, fun _ _ => rfl⟩
                  | cons _ _ => simp [matchList] at h
              | cons a rest ihRest =>
                  intro ts b b' sub h
                  cases ts with
                  | nil => simp [matchList] at h
                  | cons t ts =>
                      simp only [matchList] at h
                      split at h
                      · cases h
                      · rename_i b₁ first
                        obtain ⟨grow₁, bound₁, inst₁⟩ := ih a (sub a (by simp)) t b b₁ first
                        obtain ⟨grow₂, bound₂, inst₂⟩ :=
                          ihRest ts b₁ b' (fun c hc => sub c (by simp [hc])) h
                        refine ⟨grow₁.trans grow₂, fun x hx => ?_, fun σ ext => ?_⟩
                        · simp only [List.flatMap_cons, List.mem_append] at hx
                          rcases hx with hx | hx
                          · obtain ⟨t', ht'⟩ := bound₁ x hx
                            exact ⟨t', grow₂ x t' ht'⟩
                          · exact bound₂ x hx
                        · simp only [List.map_cons, List.cons.injEq]
                          exact ⟨inst₁ σ (fun x t' h => ext x t' (grow₂ x t' h)), inst₂ σ ext⟩
            obtain ⟨grow, bound, inst⟩ := list ls ts b b' (fun a h => h) h
            exact ⟨grow, by simpa using bound, fun σ ext => by simp [inst σ ext]⟩
          · cases h

theorem matchTerm_complete :
    ∀ (l : Term F V) (σ : V → Term F W) (b : V → Option (Term F W)), Extends b σ →
      ∃ b', matchTerm l (l.subst σ) b = some b' ∧ Extends b' σ := by
  intro l
  induction l using Term.induction' with
  | var x =>
      intro σ b ext
      cases bound : b x with
      | none =>
          refine ⟨fun y => if y = x then some (σ x) else b y, by simp [matchTerm, bound],
            fun y t h => ?_⟩
          by_cases same : y = x
          · subst same; simp at h; exact h
          · simp [same] at h; exact ext y t h
      | some t' =>
          have : t' = σ x := (ext x t' bound).symm
          exact ⟨b, by simp [matchTerm, bound, this], ext⟩
  | app f ls ih =>
      intro σ b ext
      have list : ∀ (ls' : List (Term F V)) (b : V → Option (Term F W)), (∀ a ∈ ls', a ∈ ls) →
          Extends b σ → ∃ b', matchList ls' (ls'.map (Term.subst σ)) b = some b' ∧ Extends b' σ := by
        intro ls'
        induction ls' with
        | nil => intro b _ ext; exact ⟨b, by simp [matchList], ext⟩
        | cons a rest ihRest =>
            intro b sub ext
            obtain ⟨b₁, h₁, ext₁⟩ := ih a (sub a (by simp)) σ b ext
            obtain ⟨b₂, h₂, ext₂⟩ := ihRest b₁ (fun c hc => sub c (by simp [hc])) ext₁
            exact ⟨b₂, by simp [matchList, h₁, h₂], ext₂⟩
      obtain ⟨b', h, ext'⟩ := list ls b (fun a h => h) ext
      exact ⟨b', by simp [matchTerm, h], ext'⟩

/-! ## One-step reducts -/

/-- The reducts by a step at the root. -/
def rootReducts (R : List (Rule F V)) (t : Term F W) : List (Term F W) :=
  R.filterMap fun ρ => (matchTerm ρ.lhs t fun _ => none).bind fun b => inst b ρ.rhs

mutual
/-- **All one-step reducts** of a term. -/
def reducts (R : List (Rule F V)) : Term F W → List (Term F W)
  | .var x => rootReducts R (.var x)
  | .app f args => rootReducts R (.app f args) ++ argReducts R f [] args
/-- The reducts by a step inside one of the arguments after `before`. -/
def argReducts (R : List (Rule F V)) (f : F) (before : List (Term F W)) :
    List (Term F W) → List (Term F W)
  | [] => []
  | a :: after =>
      (reducts R a).map (fun a' => .app f (before ++ a' :: after)) ++
        argReducts R f (before ++ [a]) after
end

theorem rootReducts_sound {R : List (Rule F V)} {t u : Term F W} (member : u ∈ rootReducts R t) :
    Step R t u := by
  simp only [rootReducts, List.mem_filterMap, Option.bind_eq_some_iff] at member
  obtain ⟨ρ, mem, b, matched, instantiated⟩ := member
  obtain ⟨_, _, sound⟩ := matchTerm_sound ρ.lhs t _ b matched
  let σ : V → Term F W := fun x => (b x).getD t
  have ext : Extends b σ := fun x t' h => by simp [σ, h]
  have lhs := sound σ ext
  have rhs := inst_sound ext ρ.rhs u instantiated
  rw [← lhs, rhs]
  exact .root mem σ

theorem reducts_sound {R : List (Rule F V)} :
    ∀ (t : Term F W) {u : Term F W}, u ∈ reducts R t → Step R t u := by
  intro t
  induction t using Term.induction' with
  | var x => intro u member; exact rootReducts_sound (by simpa [reducts] using member)
  | app f args ih =>
      intro u member
      simp only [reducts, List.mem_append] at member
      rcases member with root | inArg
      · exact rootReducts_sound root
      · have list : ∀ (rest before : List (Term F W)), (∀ a ∈ rest, a ∈ args) →
            u ∈ argReducts R f before rest → Step R (.app f (before ++ rest)) u := by
          intro rest
          induction rest with
          | nil => intro before _ h; simp [argReducts] at h
          | cons a after ihRest =>
              intro before sub h
              simp only [argReducts, List.mem_append, List.mem_map] at h
              rcases h with ⟨a', reduct, rfl⟩ | later
              · exact Step.inArg f before after (ih a (sub a (by simp)) reduct)
              · have := ihRest (before ++ [a]) (fun c hc => sub c (by simp [hc])) later
                simpa using this
        simpa using list args [] (fun a h => h) inArg

theorem rootReducts_complete {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed)
    {ρ : Rule F V} (mem : ρ ∈ R) (σ : V → Term F W) :
    ρ.rhs.subst σ ∈ rootReducts R (ρ.lhs.subst σ) := by
  simp only [rootReducts, List.mem_filterMap, Option.bind_eq_some_iff]
  obtain ⟨b, matched, ext⟩ := matchTerm_complete ρ.lhs σ (fun _ => none) (fun _ _ h => by cases h)
  obtain ⟨_, bound, _⟩ := matchTerm_sound ρ.lhs _ _ b matched
  obtain ⟨t, instantiated⟩ := inst_isSome ρ.rhs (fun x hx => bound x ((format ρ mem).2 x hx))
  exact ⟨ρ, mem, b, matched, by rw [instantiated, inst_sound ext ρ.rhs t instantiated]⟩

theorem rootReducts_sub_reducts {R : List (Rule F V)} (t : Term F W) {u : Term F W}
    (member : u ∈ rootReducts R t) : u ∈ reducts R t := by
  cases t with
  | var x => simpa [reducts] using member
  | app f args => simp [reducts, member]

theorem mem_argReducts_middle (R : List (Rule F V)) (f : F) {a' : Term F W} :
    ∀ (xs before : List (Term F W)) (a : Term F W) (ys : List (Term F W)), a' ∈ reducts R a →
      Term.app f (before ++ xs ++ a' :: ys) ∈ argReducts R f before (xs ++ a :: ys)
  | [], before, a, ys, member => by
      simp only [List.append_nil, List.nil_append, argReducts, List.mem_append, List.mem_map]
      exact Or.inl ⟨a', member, rfl⟩
  | x :: xs, before, a, ys, member => by
      simp only [List.cons_append, argReducts, List.mem_append]
      right
      have := mem_argReducts_middle R f xs (before ++ [x]) a ys member
      simpa using this

/-- **For well-formed rules, every reduct is listed.** -/
theorem mem_reducts_of_step {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed)
    {t u : Term F W} (step : Step R t u) : u ∈ reducts R t := by
  induction step with
  | root mem σ => exact rootReducts_sub_reducts _ (rootReducts_complete format mem σ)
  | arg f args i h _ ih =>
      simp only [reducts, List.mem_append]
      right
      have split : args = args.take i ++ args[i] :: args.drop (i + 1) := by
        rw [List.getElem_cons_drop, List.take_append_drop]
      have := mem_argReducts_middle R f (args.take i) [] args[i] (args.drop (i + 1)) ih
      rw [← split] at this
      rw [List.set_eq_take_cons_drop _ h]
      simpa using this

theorem mem_reducts_iff {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed) (t u : Term F W) :
    u ∈ reducts R t ↔ Step R t u :=
  ⟨reducts_sound t, mem_reducts_of_step format⟩

/-! ## Reached terms -/

/-- The terms reached within `k` steps. -/
def reach (R : List (Rule F V)) : ℕ → Term F W → List (Term F W)
  | 0, t => [t]
  | k + 1, t => (reach R k t ++ (reach R k t).flatMap (reducts R)).dedup

theorem mem_reach_succ {R : List (Rule F V)} {k : ℕ} {t u : Term F W} :
    u ∈ reach R (k + 1) t ↔ u ∈ reach R k t ∨ ∃ v ∈ reach R k t, u ∈ reducts R v := by
  simp [reach, List.mem_dedup, List.mem_flatMap]

theorem self_mem_reach (R : List (Rule F V)) : ∀ (k : ℕ) (t : Term F W), t ∈ reach R k t
  | 0, t => by simp [reach]
  | k + 1, t => mem_reach_succ.mpr (Or.inl (self_mem_reach R k t))

theorem reach_mono {R : List (Rule F V)} {t u : Term F W} {k : ℕ} :
    ∀ {m : ℕ}, k ≤ m → u ∈ reach R k t → u ∈ reach R m t := by
  intro m le member
  induction m with
  | zero => rw [Nat.le_zero.mp le] at member; exact member
  | succ m ih =>
      rcases Nat.lt_or_eq_of_le le with lt | eq
      · exact mem_reach_succ.mpr (Or.inl (ih (by omega)))
      · rw [eq] at member; exact member

/-- **Every reached term is a reduct.** -/
theorem reach_sound {R : List (Rule F V)} : ∀ {k : ℕ} {t u : Term F W}, u ∈ reach R k t → Steps R t u
  | 0, t, u, member => by simp [reach] at member; subst member; exact .refl
  | k + 1, t, u, member => by
      rcases mem_reach_succ.mp member with old | ⟨v, vMember, reduct⟩
      · exact reach_sound old
      · exact (reach_sound vMember).tail (reducts_sound v reduct)

/-- The reached terms are closed under reducts. -/
def saturatedAt (R : List (Rule F V)) (k : ℕ) (t : Term F W) : Bool :=
  (reach R k t).all fun v => (reducts R v).all fun u => decide (u ∈ reach R k t)

theorem saturatedAt_iff {R : List (Rule F V)} {k : ℕ} {t : Term F W} :
    saturatedAt R k t = true ↔ ∀ v ∈ reach R k t, ∀ u ∈ reducts R v, u ∈ reach R k t := by
  simp [saturatedAt]

/-- **A saturated search has reached every reduct.** -/
theorem mem_reach_of_saturated {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed)
    {k : ℕ} {t u : Term F W} (saturated : saturatedAt R k t = true) (steps : Steps R t u) :
    u ∈ reach R k t := by
  induction steps with
  | refl => exact self_mem_reach R k t
  | tail _ step ih => exact saturatedAt_iff.mp saturated _ ih _ (mem_reducts_of_step format step)

theorem reach_succ_iff_of_saturated {R : List (Rule F V)} {k : ℕ} {t : Term F W}
    (saturated : saturatedAt R k t = true) (u : Term F W) :
    u ∈ reach R (k + 1) t ↔ u ∈ reach R k t := by
  rw [mem_reach_succ]
  constructor
  · rintro (old | ⟨v, vMember, reduct⟩)
    · exact old
    · exact saturatedAt_iff.mp saturated v vMember u reduct
  · exact Or.inl

/-- **A saturated search stays saturated, with the same terms.** -/
theorem saturated_persists {R : List (Rule F V)} {k : ℕ} {t : Term F W}
    (saturated : saturatedAt R k t = true) :
    ∀ {m : ℕ}, k ≤ m → saturatedAt R m t = true ∧ ∀ u, u ∈ reach R m t ↔ u ∈ reach R k t := by
  intro m le
  induction m with
  | zero => obtain rfl := Nat.le_zero.mp le; exact ⟨saturated, fun _ => Iff.rfl⟩
  | succ m ih =>
      rcases Nat.lt_or_eq_of_le le with lt | eq
      · obtain ⟨satM, sameM⟩ := ih (by omega)
        have step := reach_succ_iff_of_saturated satM
        refine ⟨saturatedAt_iff.mpr fun v hv u hu => ?_, fun u => (step u).trans (sameM u)⟩
        exact (step u).mpr (saturatedAt_iff.mp satM v ((step v).mp hv) u hu)
      · subst eq; exact ⟨saturated, fun _ => Iff.rfl⟩

/-! ## The check -/

/-- A common reduct within the budget. -/
def joinedAt (R : List (Rule F V)) (k : ℕ) (s t : Term F W) : Bool :=
  (reach R k s).any fun u => decide (u ∈ reach R k t)

theorem joinedAt_iff {R : List (Rule F V)} {k : ℕ} {s t : Term F W} :
    joinedAt R k s t = true ↔ ∃ u ∈ reach R k s, u ∈ reach R k t := by
  simp [joinedAt]

theorem joinedAt_sound {R : List (Rule F V)} {k : ℕ} {s t : Term F W}
    (joined : joinedAt R k s t = true) : Join (Steps R) s t := by
  obtain ⟨u, left, right⟩ := joinedAt_iff.mp joined
  exact ⟨u, reach_sound left, reach_sound right⟩

theorem joinedAt_mono {R : List (Rule F V)} {k m : ℕ} (le : k ≤ m) {s t : Term F W}
    (joined : joinedAt R k s t = true) : joinedAt R m s t = true := by
  obtain ⟨u, left, right⟩ := joinedAt_iff.mp joined
  exact joinedAt_iff.mpr ⟨u, reach_mono le left, reach_mono le right⟩

/-- **An exhausted, disjoint search refutes joinability.** -/
theorem not_join_of_saturated {R : List (Rule F V)} (format : ∀ ρ ∈ R, ρ.WellFormed)
    {k : ℕ} {s t : Term F W} (notJoined : joinedAt R k s t ≠ true)
    (saturated : saturatedAt R k s = true ∧ saturatedAt R k t = true) :
    ¬ Join (Steps R) s t := by
  rintro ⟨u, left, right⟩
  exact notJoined (joinedAt_iff.mpr ⟨u, mem_reach_of_saturated format saturated.1 left,
    mem_reach_of_saturated format saturated.2 right⟩)

/-- What a joinability check certifies. -/
def joinAuthority (R : List (Rule F V)) (W : Type w) :
    AuthorityTheory.Authority (Term F W × Term F W) where
  Holds j := Join (Steps R) j.1 j.2
  Evidence j := Join (Steps R) j.1 j.2
  Obstruction j := ¬ Join (Steps R) j.1 j.2
  evidenceSound _ evidence := evidence
  obstructionSound _ obstruction := obstruction

/-- Why a check is outside its fragment. -/
inductive FragmentBoundary where
  /-- A rule's left side is a variable, or its right side has a variable its left side does
  not: the reducts of a term are then not determined by matching. -/
  | ruleFormat
  /-- No supplied termination certificate orients every rule. -/
  | noTerminationCertificate
  deriving DecidableEq, Repr

/-- The rules are well formed, as a test. -/
def rulesWellFormed (R : List (Rule F V)) : Bool := R.all Rule.wellFormed

omit [DecidableEq F] in
theorem rulesWellFormed_iff {R : List (Rule F V)} :
    rulesWellFormed R = true ↔ ∀ ρ ∈ R, ρ.WellFormed := by
  simp [rulesWellFormed, Rule.wellFormed_iff]

/-- **The joinability check at a budget.** -/
def joinRun (R : List (Rule F V)) (k : ℕ) (j : Term F W × Term F W) :
    AuthorityTheory.AuthorizedOutcome (joinAuthority R W) FragmentBoundary Unit j :=
  if format : rulesWellFormed R = true then
    if joined : joinedAt R k j.1 j.2 = true then .established (joinedAt_sound joined)
    else if saturated : saturatedAt R k j.1 = true ∧ saturatedAt R k j.2 = true then
      .refuted (not_join_of_saturated (rulesWellFormed_iff.mp format) joined saturated)
    else .incomplete ()
  else .outsideFragment .ruleFormat

/-- **The joinability check is a graded check**: only an incomplete answer changes with the
budget. -/
def joinCheck (R : List (Rule F V)) :
    GradedChecking.GradedCheck (joinAuthority R W) FragmentBoundary Unit where
  run := joinRun R
  mono := by
    intro j small large le
    unfold joinRun
    by_cases format : rulesWellFormed R = true
    · simp only [format, dif_pos]
      by_cases joined : joinedAt R small j.1 j.2 = true
      · rw [dif_pos joined, dif_pos (joinedAt_mono le joined)]
        exact .established _ _
      · rw [dif_neg joined]
        by_cases saturated : saturatedAt R small j.1 = true ∧ saturatedAt R small j.2 = true
        · rw [dif_pos saturated]
          obtain ⟨sat₁, same₁⟩ := saturated_persists saturated.1 le
          obtain ⟨sat₂, same₂⟩ := saturated_persists saturated.2 le
          have notJoined : ¬ joinedAt R large j.1 j.2 = true := by
            intro joinedLarge
            obtain ⟨u, left, right⟩ := joinedAt_iff.mp joinedLarge
            exact joined (joinedAt_iff.mpr ⟨u, (same₁ u).mp left, (same₂ u).mp right⟩)
          rw [dif_neg notJoined, dif_pos ⟨sat₁, sat₂⟩]
          exact .refuted _ _
        · rw [dif_neg saturated]
          split
          · exact .incompleteEstablished _ _
          · split
            · exact .incompleteRefuted _ _
            · exact .incomplete _ _
    · simp only [format]
      exact .outsideFragment _

/-- **An incomplete answer is never a refutation**: whatever the budget, a joinable pair is
never refuted. -/
theorem joinRun_not_refuted_of_join {R : List (Rule F V)} {k : ℕ} {j : Term F W × Term F W}
    (joinable : Join (Steps R) j.1 j.2) :
    ∀ obstruction, joinRun R k j ≠ .refuted obstruction :=
  fun obstruction _ => obstruction joinable

/-! ## A supplied join, replayed -/

/-- Each listed term is a one-step reduct of the previous one, and the last is the target. -/
def checkPath (R : List (Rule F V)) : Term F W → List (Term F W) → Term F W → Bool
  | s, [], t => decide (s = t)
  | s, u :: us, t => decide (u ∈ reducts R s) && checkPath R u us t

theorem checkPath_sound {R : List (Rule F V)} :
    ∀ (s : Term F W) (path : List (Term F W)) (t : Term F W), checkPath R s path t = true →
      Steps R s t
  | s, [], t, h => by simp [checkPath] at h; subst h; exact .refl
  | s, u :: us, t, h => by
      simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Relation.ReflTransGen.head (reducts_sound s h.1) (checkPath_sound u us t h.2)

/-- **A supplied join**: two paths to a common term, replayed step by step. -/
def checkJoin (R : List (Rule F V)) (s t w : Term F W) (left right : List (Term F W)) : Bool :=
  checkPath R s left w && checkPath R t right w

theorem checkJoin_sound {R : List (Rule F V)} {s t w : Term F W} {left right : List (Term F W)}
    (h : checkJoin R s t w left right = true) : Join (Steps R) s t := by
  simp only [checkJoin, Bool.and_eq_true] at h
  exact ⟨w, checkPath_sound s left w h.1, checkPath_sound t right w h.2⟩

end Matching

end Mettapedia.TypeTheory.PromotionAdmission
