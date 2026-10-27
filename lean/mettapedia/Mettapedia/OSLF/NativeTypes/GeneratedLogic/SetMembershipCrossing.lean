import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTwoWay
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution

/-!
# Fixed points that cross steps back, decided on the hereditarily finite sets

A fixed point whose variable occurs under steps back sees larger sets, and no height bounds it. When every occurrence
of the variable sits at no greater two-way depth than the binder (`Formula.crossingBody`: the body is two-way in its
variable, and the depth with the variable read at the body's own depth stays within it), every unfolding of the
fixed point is a two-way formula of depth at most that bound (`unfold_twoWayDepth_le`).

- **Types bound the iteration.** Two-way formulas of depth at most `D` hold alike at sets bisimilar up to `D`, and every
  hereditarily finite set is bisimilar up to `D` to its truncation, a subset of `V_D`. So each unfolding is determined
  by its values at the finitely many subsets of `V_D` (`unfold_iff_of_stable`).
- **A stable unfolding is the fixed point.** The unfoldings from falsity rise and those from truth fall
  (`unfold_mono_bot`, `unfold_anti_top`); when two consecutive ones agree on the subsets of `V_D`, they agree everywhere,
  and the first is the least, or the greatest, fixed point (`sat_mu_iff_unfold`, `sat_nu_iff_unfold`).
- **The iteration stabilizes within the number of types** (`stableIndex_isSome`): a chain that rises at a subset of
  `V_D` at every step would rise more often than there are subsets.
- **The decision** (`eliminate`, `evalCrossing`): fixed points with crossing bodies, under the two-way formers, are
  replaced by their stable unfoldings, and the resulting two-way formula is evaluated. It is exact
  (`evalCrossing_iff`) and answers every formula of the fragment (`evalCrossing_isSome`). The bound is a tower of
  exponentials in the depth, so it decides without being practical.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Formula

/-- **Two-way bodies**: two-way formulas in which variables may occur. -/
def bodyTwoWay : {n : ℕ} → Formula n → Bool
  | _, .var _ => true
  | _, .top | _, .bot | _, .empty _ | _, .nonEmpty _ | _, .is _ | _, .isNot _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    bodyTwoWay left && bodyTwoWay right
  | _, .possibly _ inner | _, .necessarily _ inner | _, .sometimeBefore _ inner | _, .alwaysBefore _ inner =>
    bodyTwoWay inner
  | _, .someOf (.base _) inner | _, .everyOf (.base _) inner => bodyTwoWay inner
  | _, _ => false

/-- **The two-way depth with the variables read at a depth.** -/
def depthWith (depth : ℕ) : {n : ℕ} → Formula n → ℕ
  | _, .var _ => depth
  | _, .empty _ | _, .nonEmpty _ => 1
  | _, .is term | _, .isNot term => SetReadings.height term + 1
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    max (depthWith depth left) (depthWith depth right)
  | _, .possibly _ inner | _, .necessarily _ inner => depthWith depth inner + 1
  | _, .sometimeBefore _ inner | _, .alwaysBefore _ inner => depthWith depth inner - 1
  | _, _ => 0

/-- The depth bound of a body: its depth with its variable read at depth zero. -/
def crossingDepth (body : Formula 1) : ℕ := body.depthWith 0

/-- **A crossing body**: two-way in its variable, which occurs at no greater depth than the binder. -/
def crossingBody (body : Formula 1) : Bool :=
  body.bodyTwoWay && decide (body.depthWith body.crossingDepth ≤ body.crossingDepth)

theorem depthWith_mono {first second : ℕ} (le : first ≤ second) :
    ∀ {n : ℕ} (formula : Formula n), formula.depthWith first ≤ formula.depthWith second
  | _, .var _ => le
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    max_le_max (depthWith_mono le left) (depthWith_mono le right)
  | _, .possibly _ inner | _, .necessarily _ inner => Nat.succ_le_succ (depthWith_mono le inner)
  | _, .sometimeBefore _ inner | _, .alwaysBefore _ inner => Nat.sub_le_sub_right (depthWith_mono le inner) 1
  | _, .top | _, .bot | _, .empty _ | _, .nonEmpty _ | _, .is _ | _, .isNot _ | _, .mu _ | _, .nu _
  | _, .atLeast _ _ _ _ | _, .allButFewer _ _ _ _ | _, .built _ _ | _, .everyBuilt _ _ | _, .single _ _
  | _, .everySingle _ _ | _, .body _ | _, .everyBody _ | _, .multiBody _ _ | _, .everyMultiBody _ _ | _, .bound _
  | _, .notBound _ | _, .typed _ | _, .untyped _ | _, .mapsAll _ _ | _, .mapsSome _ _ | _, .someOf _ _
  | _, .everyOf _ _ | _, .inRelation _ | _, .notInRelation _ => le_refl _

/-- **Substituting two-way formulas into a two-way body gives a two-way formula.** -/
theorem twoWay_subst {m : ℕ} {substitution : Fin m → Formula 0} (each : ∀ index, (substitution index).twoWay = true) :
    ∀ (formula : Formula m), formula.bodyTwoWay = true → (formula.subst substitution).twoWay = true
  | .var index, _ => each index
  | .top, _ | .bot, _ | .empty _, _ | .nonEmpty _, _ | .is _, _ | .isNot _, _ => rfl
  | .and left right, fragment | .or left right, fragment => by
    simp only [bodyTwoWay, Bool.and_eq_true] at fragment
    simp only [Formula.subst, twoWay, twoWay_subst each left fragment.1, twoWay_subst each right fragment.2,
      Bool.and_self]
  | .split _ left right, fragment | .everySplit _ left right, fragment => by
    simp only [bodyTwoWay, Bool.and_eq_true] at fragment
    simp only [Formula.subst, twoWay, twoWay_subst each left fragment.1, twoWay_subst each right fragment.2,
      Bool.and_self]
  | .possibly _ inner, fragment | .necessarily _ inner, fragment | .sometimeBefore _ inner, fragment
  | .alwaysBefore _ inner, fragment => by
    simp only [bodyTwoWay] at fragment
    simp only [Formula.subst, twoWay, twoWay_subst each inner fragment]
  | .someOf (.base _) inner, fragment | .everyOf (.base _) inner, fragment => by
    simp only [bodyTwoWay] at fragment
    simp only [Formula.subst, twoWay, twoWay_subst each inner fragment]
  | .mu _, fragment | .nu _, fragment | .atLeast _ _ _ _, fragment | .allButFewer _ _ _ _, fragment
  | .built _ _, fragment | .everyBuilt _ _, fragment | .single _ _, fragment | .everySingle _ _, fragment
  | .body _, fragment | .everyBody _, fragment | .multiBody _ _, fragment | .everyMultiBody _ _, fragment
  | .bound _, fragment | .notBound _, fragment | .typed _, fragment | .untyped _, fragment | .mapsAll _ _, fragment
  | .mapsSome _ _, fragment | .someOf (.collection _ _) _, fragment | .someOf (.arrow _ _) _, fragment
  | .someOf (.multiBinder _) _, fragment | .everyOf (.collection _ _) _, fragment | .everyOf (.arrow _ _) _, fragment
  | .everyOf (.multiBinder _) _, fragment | .inRelation _, fragment | .notInRelation _, fragment =>
    absurd fragment Bool.false_ne_true

/-- **The depth of a substitution** is the body's depth with its variables read at the substituted depth. -/
theorem twoWayDepth_subst {m : ℕ} {substitution : Fin m → Formula 0} {depth : ℕ}
    (each : ∀ index, (substitution index).twoWayDepth = depth) :
    ∀ (formula : Formula m), formula.bodyTwoWay = true → (formula.subst substitution).twoWayDepth = formula.depthWith depth
  | .var index, _ => each index
  | .top, _ | .bot, _ | .empty _, _ | .nonEmpty _, _ | .is _, _ | .isNot _, _ => rfl
  | .and left right, fragment | .or left right, fragment => by
    simp only [bodyTwoWay, Bool.and_eq_true] at fragment
    simp only [Formula.subst, twoWayDepth, depthWith, twoWayDepth_subst each left fragment.1,
      twoWayDepth_subst each right fragment.2]
  | .split _ left right, fragment | .everySplit _ left right, fragment => by
    simp only [bodyTwoWay, Bool.and_eq_true] at fragment
    simp only [Formula.subst, twoWayDepth, depthWith, twoWayDepth_subst each left fragment.1,
      twoWayDepth_subst each right fragment.2]
  | .possibly _ inner, fragment | .necessarily _ inner, fragment | .sometimeBefore _ inner, fragment
  | .alwaysBefore _ inner, fragment => by
    simp only [bodyTwoWay] at fragment
    simp only [Formula.subst, twoWayDepth, depthWith, twoWayDepth_subst each inner fragment]
  | .someOf (.base _) _, _ | .everyOf (.base _) _, _ => rfl
  | .mu _, fragment | .nu _, fragment | .atLeast _ _ _ _, fragment | .allButFewer _ _ _ _, fragment
  | .built _ _, fragment | .everyBuilt _ _, fragment | .single _ _, fragment | .everySingle _ _, fragment
  | .body _, fragment | .everyBody _, fragment | .multiBody _ _, fragment | .everyMultiBody _ _, fragment
  | .bound _, fragment | .notBound _, fragment | .typed _, fragment | .untyped _, fragment | .mapsAll _ _, fragment
  | .mapsSome _ _, fragment | .someOf (.collection _ _) _, fragment | .someOf (.arrow _ _) _, fragment
  | .someOf (.multiBinder _) _, fragment | .everyOf (.collection _ _) _, fragment | .everyOf (.arrow _ _) _, fragment
  | .everyOf (.multiBinder _) _, fragment | .inRelation _, fragment | .notInRelation _, fragment =>
    absurd fragment Bool.false_ne_true

end Formula

namespace SetReadings

/-! ## Unfoldings -/

/-- **The unfoldings of a fixed point**: the body applied again and again to a start. -/
def unfold (body : Formula 1) (start : Formula 0) : ℕ → Formula 0
  | 0 => start
  | count + 1 => body.subst fun _ => unfold body start count

variable {body : Formula 1}

theorem unfold_twoWay (fragment : body.bodyTwoWay = true) {start : Formula 0} (startTwoWay : start.twoWay = true) :
    ∀ count, (unfold body start count).twoWay = true
  | 0 => startTwoWay
  | count + 1 => Formula.twoWay_subst (fun _ => unfold_twoWay fragment startTwoWay count) body fragment

/-- **Every unfolding of a crossing body stays within its depth bound.** -/
theorem unfold_twoWayDepth_le (crossing : body.crossingBody = true) {start : Formula 0}
    (startDepth : start.twoWayDepth ≤ body.crossingDepth) :
    ∀ count, (unfold body start count).twoWayDepth ≤ body.crossingDepth
  | 0 => startDepth
  | count + 1 => by
    simp only [Formula.crossingBody, Bool.and_eq_true, decide_eq_true_eq] at crossing
    show (body.subst fun _ => unfold body start count).twoWayDepth ≤ body.crossingDepth
    rw [Formula.twoWayDepth_subst (fun _ => rfl) body crossing.1]
    exact (Formula.depthWith_mono (unfold_twoWayDepth_le (by simpa [Formula.crossingBody, crossing.1] using crossing.2)
      startDepth count) body).trans crossing.2

/-- An unfolding holds where the body holds with the previous unfolding's truth set for its variable. -/
theorem sat_unfold_succ (start : Formula 0) (count : ℕ) (element : HF) :
    HFSets.sat Env.closed (unfold body start (count + 1)) element ↔
      HFSets.sat (Env.closed.extend {other | HFSets.sat Env.closed (unfold body start count) other}) body element := by
  show HFSets.sat Env.closed (body.subst fun _ => unfold body start count) element ↔ _
  rw [HFSets.sat_close]
  have same : (fun index : Fin 1 => {other | HFSets.sat Env.closed ((fun _ => unfold body start count) index) other}) =
      Env.closed.extend {other | HFSets.sat Env.closed (unfold body start count) other} := by
    funext index
    rw [Fin.fin_one_eq_zero index]
    rfl
  rw [same]

/-- The step of a fixed point: the body's truth set with a set for its variable. -/
def stepSet (body : Formula 1) (set : Set HF) : Set HF := {element | HFSets.sat (Env.closed.extend set) body element}

theorem stepSet_mono {small large : Set HF} (sub : small ⊆ large) : stepSet body small ⊆ stepSet body large := by
  intro element holds
  refine HFSets.sat_mono body (fun index => ?_) element holds
  refine Fin.cases ?_ (fun index' => index'.elim0) index
  simpa [Env.extend] using sub

theorem unfold_succ_set (start : Formula 0) (count : ℕ) :
    {element | HFSets.sat Env.closed (unfold body start (count + 1)) element} =
      stepSet body {element | HFSets.sat Env.closed (unfold body start count) element} := by
  ext element
  exact sat_unfold_succ start count element

/-- **The unfoldings from falsity rise.** -/
theorem unfold_mono_bot : ∀ count, ∀ element, HFSets.sat Env.closed (unfold body .bot count) element →
    HFSets.sat Env.closed (unfold body .bot (count + 1)) element
  | 0, _, holds => holds.elim
  | count + 1, element, holds => by
    have sub : {other | HFSets.sat Env.closed (unfold body .bot count) other} ⊆
        {other | HFSets.sat Env.closed (unfold body .bot (count + 1)) other} :=
      fun other => unfold_mono_bot count other
    have := stepSet_mono (body := body) sub (show element ∈ stepSet body _ from (sat_unfold_succ .bot count element).mp holds)
    exact (sat_unfold_succ .bot (count + 1) element).mpr this

/-- **The unfoldings from truth fall.** -/
theorem unfold_anti_top : ∀ count, ∀ element, HFSets.sat Env.closed (unfold body .top (count + 1)) element →
    HFSets.sat Env.closed (unfold body .top count) element
  | 0, _, _ => trivial
  | count + 1, element, holds => by
    have sub : {other | HFSets.sat Env.closed (unfold body .top (count + 1)) other} ⊆
        {other | HFSets.sat Env.closed (unfold body .top count) other} :=
      fun other => unfold_anti_top count other
    have := stepSet_mono (body := body) sub
      (show element ∈ stepSet body _ from (sat_unfold_succ .top (count + 1) element).mp holds)
    exact (sat_unfold_succ .top count element).mpr this

/-! ## Stability on the truncations -/

/-- **Two consecutive unfoldings agree on the subsets of `V_D`.** -/
def stableAt (body : Formula 1) (start : Formula 0) (depth count : ℕ) : Bool :=
  (subsetTerms depth).all fun part =>
    evalTwoWay (unfold body start count) part == evalTwoWay (unfold body start (count + 1)) part

/-- Every hereditarily finite set is bisimilar up to a depth to a subset term of `V_depth`. -/
theorem exists_subsetTerm (depth : ℕ) (element : HF) :
    ∃ part, ∃ member : part ∈ subsetTerms depth, extensional.BisimUpTo depth element.1 (hfOf (subsetTerms_hf member)).1 := by
  obtain ⟨part, member, same⟩ := subset_iff_subsetTerms.mp (truncSet_subset depth element.1)
  refine ⟨part, member, ?_⟩
  show extensional.BisimUpTo depth element.1 (zfOf part)
  rw [same]
  exact bisim_truncSet depth element.1

/-- **Stability on the truncations is stability everywhere**, for a crossing body. -/
theorem unfold_iff_of_stable (crossing : body.crossingBody = true) {start : Formula 0} (startTwoWay : start.twoWay = true)
    (startDepth : start.twoWayDepth ≤ body.crossingDepth) {count : ℕ}
    (stable : stableAt body start body.crossingDepth count = true) (element : HF) :
    HFSets.sat Env.closed (unfold body start count) element ↔ HFSets.sat Env.closed (unfold body start (count + 1)) element := by
  have fragment : body.bodyTwoWay = true := by
    simp only [Formula.crossingBody, Bool.and_eq_true] at crossing
    exact crossing.1
  obtain ⟨part, member, related⟩ := exists_subsetTerm body.crossingDepth element
  have agree := beq_iff_eq.mp (List.all_eq_true.mp stable part member)
  rw [twoWay_sat_iff _ (unfold_twoWay fragment startTwoWay count) _ (unfold_twoWayDepth_le crossing startDepth count)
      Env.closed related,
    twoWay_sat_iff _ (unfold_twoWay fragment startTwoWay (count + 1)) _
      (unfold_twoWayDepth_le crossing startDepth (count + 1)) Env.closed related,
    ← evalTwoWay_iff _ (unfold_twoWay fragment startTwoWay count),
    ← evalTwoWay_iff _ (unfold_twoWay fragment startTwoWay (count + 1)), agree]

/-- **A stable unfolding from falsity is the least fixed point.** -/
theorem sat_mu_iff_unfold {count : ℕ}
    (stable : ∀ element, HFSets.sat Env.closed (unfold body .bot count) element ↔
      HFSets.sat Env.closed (unfold body .bot (count + 1)) element) (element : HF) :
    HFSets.sat Env.closed (.mu body) element ↔ HFSets.sat Env.closed (unfold body .bot count) element := by
  constructor
  · intro holds
    refine holds {other | HFSets.sat Env.closed (unfold body .bot count) other} fun other inside => ?_
    exact (stable other).mpr ((sat_unfold_succ .bot count other).mpr inside)
  · intro holds closed prefixed
    have below : ∀ step, ∀ other, HFSets.sat Env.closed (unfold body .bot step) other → other ∈ closed := by
      intro step
      induction step with
      | zero => exact fun _ impossible => impossible.elim
      | succ step ih =>
        intro other inside
        exact prefixed other (stepSet_mono (body := body) (fun other' => ih other')
          (show other ∈ stepSet body _ from (sat_unfold_succ .bot step other).mp inside))
    exact below count element holds

/-- **A stable unfolding from truth is the greatest fixed point.** -/
theorem sat_nu_iff_unfold {count : ℕ}
    (stable : ∀ element, HFSets.sat Env.closed (unfold body .top count) element ↔
      HFSets.sat Env.closed (unfold body .top (count + 1)) element) (element : HF) :
    HFSets.sat Env.closed (.nu body) element ↔ HFSets.sat Env.closed (unfold body .top count) element := by
  constructor
  · rintro ⟨invariant, member, preserved⟩
    have within : ∀ step, ∀ other ∈ invariant, HFSets.sat Env.closed (unfold body .top step) other := by
      intro step
      induction step with
      | zero => exact fun _ _ => trivial
      | succ step ih =>
        intro other inside
        exact (sat_unfold_succ .top step other).mpr
          (stepSet_mono (body := body) (fun other' inside' => ih other' inside') (preserved other inside))
    exact within count element member
  · intro holds
    exact ⟨{other | HFSets.sat Env.closed (unfold body .top count) other}, holds, fun other inside =>
      (sat_unfold_succ .top count other).mp ((stable other).mp inside)⟩

/-! ## The iteration stabilizes within the number of types -/

/-- A pointwise rise makes a filter no shorter. -/
theorem length_filter_le_of_imp {α : Type} {first second : α → Bool} :
    ∀ {values : List α}, (∀ value ∈ values, first value = true → second value = true) →
      (values.filter first).length ≤ (values.filter second).length
  | [], _ => le_refl _
  | value :: values, rise => by
    have rest := length_filter_le_of_imp (values := values) fun other inside => rise other (List.mem_cons_of_mem _ inside)
    by_cases firstHolds : first value = true
    · simp only [List.filter_cons, firstHolds, rise value List.mem_cons_self firstHolds, if_true, List.length_cons]
      omega
    · simp only [Bool.not_eq_true] at firstHolds
      simp only [List.filter_cons, firstHolds, Bool.false_eq_true, if_false]
      by_cases secondHolds : second value = true
      · simp only [secondHolds, if_true, List.length_cons]
        omega
      · simp only [Bool.not_eq_true] at secondHolds
        simp only [secondHolds, Bool.false_eq_true, if_false]
        exact rest

/-- A strict rise at some element makes a filter longer. -/
theorem length_filter_lt {α : Type} {first second : α → Bool} :
    ∀ {values : List α}, (∀ value ∈ values, first value = true → second value = true) →
      (∃ value ∈ values, first value = false ∧ second value = true) →
        (values.filter first).length < (values.filter second).length
  | [], _, ⟨_, impossible, _⟩ => absurd impossible List.not_mem_nil
  | value :: values, rise, ⟨witness, member, low, high⟩ => by
    have restRise : ∀ other ∈ values, first other = true → second other = true :=
      fun other inside => rise other (List.mem_cons_of_mem _ inside)
    rcases List.mem_cons.mp member with rfl | inRest
    · have restLe := length_filter_le_of_imp restRise
      simp only [List.filter_cons, low, high, if_true, Bool.false_eq_true, if_false, List.length_cons]
      omega
    · have restLt := length_filter_lt restRise ⟨witness, inRest, low, high⟩
      by_cases firstHolds : first value = true
      · simp only [List.filter_cons, firstHolds, rise value List.mem_cons_self firstHolds, if_true,
          List.length_cons]
        omega
      · simp only [Bool.not_eq_true] at firstHolds
        simp only [List.filter_cons, firstHolds, Bool.false_eq_true, if_false]
        by_cases secondHolds : second value = true
        · simp only [secondHolds, if_true, List.length_cons]
          omega
        · simp only [Bool.not_eq_true] at secondHolds
          simp only [secondHolds, Bool.false_eq_true, if_false]
          exact restLt

/-- **A chain that rises pointwise stops rising within the number of points.** -/
theorem exists_stable {α : Type} (values : List α) (chain : ℕ → α → Bool)
    (rising : ∀ count, ∀ value ∈ values, chain count value = true → chain (count + 1) value = true) :
    ∃ count ≤ values.length, ∀ value ∈ values, chain count value = chain (count + 1) value := by
  by_contra never
  push Not at never
  have grows : ∀ count ≤ values.length + 1, count ≤ (values.filter (chain count)).length := by
    intro count
    induction count with
    | zero => exact fun _ => Nat.zero_le _
    | succ count ih =>
      intro le
      obtain ⟨value, member, differ⟩ := never count (by omega)
      have strict : (values.filter (chain count)).length < (values.filter (chain (count + 1))).length := by
        refine length_filter_lt (rising count) ⟨value, member, ?_, ?_⟩
        · cases low : chain count value
          · rfl
          · exact absurd (low.trans (rising count value member low).symm) differ
        · cases high : chain (count + 1) value
          · cases low : chain count value
            · exact absurd (low.trans high.symm) differ
            · exact absurd (rising count value member low) (by rw [high]; decide)
          · rfl
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih (by omega)) strict)
  have := grows (values.length + 1) le_rfl
  have bound := List.length_filter_le (chain (values.length + 1)) values
  omega

/-- The first stable unfolding on the truncations, searched up to the number of truncations. -/
def stableIndex (body : Formula 1) (start : Formula 0) : Option ℕ :=
  (List.range ((subsetTerms body.crossingDepth).length + 1)).find? (stableAt body start body.crossingDepth)

theorem stableAt_of_index {start : Formula 0} {count : ℕ} (found : stableIndex body start = some count) :
    stableAt body start body.crossingDepth count = true :=
  List.find?_some found

/-- The search finds a stable unfolding when some rising chain tracks the unfoldings on the truncations. -/
theorem stableIndex_isSome_of {start : Formula 0} (chain : ℕ → Pattern → Bool)
    (rising : ∀ count, ∀ part ∈ subsetTerms body.crossingDepth, chain count part = true → chain (count + 1) part = true)
    (tracks : ∀ count, ∀ part ∈ subsetTerms body.crossingDepth, chain count part = chain (count + 1) part →
      evalTwoWay (unfold body start count) part = evalTwoWay (unfold body start (count + 1)) part) :
    (stableIndex body start).isSome = true := by
  obtain ⟨count, bound, stable⟩ := exists_stable (subsetTerms body.crossingDepth) chain rising
  have stableHere : stableAt body start body.crossingDepth count = true :=
    List.all_eq_true.mpr fun part member => beq_iff_eq.mpr (tracks count part member (stable part member))
  cases found : stableIndex body start with
  | some _ => rfl
  | none =>
    have := List.find?_eq_none.mp found count (List.mem_range.mpr (Nat.lt_succ_of_le bound))
    exact absurd stableHere this

/-- **The search finds a stable unfolding from falsity** for a crossing body. -/
theorem stableIndex_isSome_bot (crossing : body.crossingBody = true) : (stableIndex body .bot).isSome = true := by
  have fragment : body.bodyTwoWay = true := by
    simp only [Formula.crossingBody, Bool.and_eq_true] at crossing
    exact crossing.1
  refine stableIndex_isSome_of (fun count part => evalTwoWay (unfold body .bot count) part) ?_ fun _ _ _ same => same
  intro count part member low
  have exact := fun step => evalTwoWay_iff (unfold body .bot step) (unfold_twoWay fragment rfl step)
    (subsetTerms_hf member)
  exact (exact (count + 1)).mpr (unfold_mono_bot count _ ((exact count).mp low))

/-- **The search finds a stable unfolding from truth** for a crossing body. -/
theorem stableIndex_isSome_top (crossing : body.crossingBody = true) : (stableIndex body .top).isSome = true := by
  have fragment : body.bodyTwoWay = true := by
    simp only [Formula.crossingBody, Bool.and_eq_true] at crossing
    exact crossing.1
  refine stableIndex_isSome_of (fun count part => !evalTwoWay (unfold body .top count) part) ?_
    fun _ _ _ same => by simpa using same
  intro count part member low
  have exact := fun step => evalTwoWay_iff (unfold body .top step) (unfold_twoWay fragment rfl step)
    (subsetTerms_hf member)
  simp only [Bool.not_eq_true'] at low ⊢
  cases high : evalTwoWay (unfold body .top (count + 1)) part
  · rfl
  · have := unfold_anti_top count _ ((exact (count + 1)).mp high)
    rw [← exact count, low] at this
    cases this

/-! ## The decision -/

/-- **Replace each crossing fixed point by its stable unfolding**, under the two-way formers; at any number of free
variables, deciding closed fixed points only. -/
def eliminateAt : {n : ℕ} → Formula n → Option (Formula n)
  | n, .mu body => match n, body with
    | 0, body => if body.crossingBody then (stableIndex body .bot).map (unfold body .bot) else none
    | _ + 1, _ => none
  | n, .nu body => match n, body with
    | 0, body => if body.crossingBody then (stableIndex body .top).map (unfold body .top) else none
    | _ + 1, _ => none
  | _, .top => some .top
  | _, .bot => some .bot
  | _, .empty kind => some (.empty kind)
  | _, .nonEmpty kind => some (.nonEmpty kind)
  | _, .is term => some (.is term)
  | _, .isNot term => some (.isNot term)
  | _, .and left right => do pure (.and (← eliminateAt left) (← eliminateAt right))
  | _, .or left right => do pure (.or (← eliminateAt left) (← eliminateAt right))
  | _, .split kind left right => do pure (.split kind (← eliminateAt left) (← eliminateAt right))
  | _, .everySplit kind left right => do pure (.everySplit kind (← eliminateAt left) (← eliminateAt right))
  | _, .possibly label inner => (eliminateAt inner).map (.possibly label)
  | _, .necessarily label inner => (eliminateAt inner).map (.necessarily label)
  | _, .sometimeBefore label inner => (eliminateAt inner).map (.sometimeBefore label)
  | _, .alwaysBefore label inner => (eliminateAt inner).map (.alwaysBefore label)
  | _, .someOf (.base sort) inner => (eliminateAt inner).map (.someOf (.base sort))
  | _, .everyOf (.base sort) inner => (eliminateAt inner).map (.everyOf (.base sort))
  | _, _ => none

/-- **Replace each crossing fixed point of a closed formula by its stable unfolding.** -/
def eliminate (formula : Formula 0) : Option (Formula 0) := eliminateAt formula

/-- **The decision of a formula with crossing fixed points** at a hereditary term. -/
def evalCrossing (formula : Formula 0) (term : Pattern) : Option Bool :=
  (eliminate formula).map fun twoWayFormula => evalTwoWay twoWayFormula term

/-- **The crossing fragment** at any number of free variables: closed fixed points with crossing bodies, under the
two-way formers. -/
def crossingAt : {n : ℕ} → Formula n → Bool
  | n, .mu body | n, .nu body => match n, body with
    | 0, body => body.crossingBody
    | _ + 1, _ => false
  | _, .top | _, .bot | _, .empty _ | _, .nonEmpty _ | _, .is _ | _, .isNot _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    crossingAt left && crossingAt right
  | _, .possibly _ inner | _, .necessarily _ inner | _, .sometimeBefore _ inner | _, .alwaysBefore _ inner =>
    crossingAt inner
  | _, .someOf (.base _) inner | _, .everyOf (.base _) inner => crossingAt inner
  | _, _ => false

/-- **The crossing fragment**: fixed points with crossing bodies, under the two-way formers. -/
def crossing (formula : Formula 0) : Bool := crossingAt formula

theorem crossing_unfold_bot {body : Formula 1} (crossingBody : body.crossingBody = true) {count : ℕ}
    (found : stableIndex body .bot = some count) (element : HF) :
    HFSets.sat Env.closed (.mu body) element ↔ HFSets.sat Env.closed (unfold body .bot count) element :=
  sat_mu_iff_unfold (unfold_iff_of_stable crossingBody rfl (Nat.zero_le _) (stableAt_of_index found)) element

theorem crossing_unfold_top {body : Formula 1} (crossingBody : body.crossingBody = true) {count : ℕ}
    (found : stableIndex body .top = some count) (element : HF) :
    HFSets.sat Env.closed (.nu body) element ↔ HFSets.sat Env.closed (unfold body .top count) element :=
  sat_nu_iff_unfold (unfold_iff_of_stable crossingBody rfl (Nat.zero_le _) (stableAt_of_index found)) element

theorem bodyTwoWay_of_crossing {body : Formula 1} (crossingBody : body.crossingBody = true) : body.bodyTwoWay = true := by
  simp only [Formula.crossingBody, Bool.and_eq_true] at crossingBody
  exact crossingBody.1

/-- **Elimination keeps the meaning**: it gives a two-way formula that holds where the formula does. -/
theorem eliminate_spec : ∀ (formula : Formula 0) {result : Formula 0}, eliminate formula = some result →
    result.twoWay = true ∧ ∀ element : HF, HFSets.sat Env.closed formula element ↔ HFSets.sat Env.closed result element
  | .mu body, result, found => by
    simp only [eliminate, eliminateAt] at found
    split at found
    · rename_i crossingBody
      obtain ⟨count, index, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨unfold_twoWay (bodyTwoWay_of_crossing crossingBody) rfl count, crossing_unfold_bot crossingBody index⟩
    · cases found
  | .nu body, result, found => by
    simp only [eliminate, eliminateAt] at found
    split at found
    · rename_i crossingBody
      obtain ⟨count, index, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨unfold_twoWay (bodyTwoWay_of_crossing crossingBody) rfl count, crossing_unfold_top crossingBody index⟩
    · cases found
  | .top, _, found | .bot, _, found | .empty _, _, found | .nonEmpty _, _, found | .is _, _, found
  | .isNot _, _, found => by
    simp only [eliminate, eliminateAt, Option.some.injEq] at found
    subst found
    exact ⟨rfl, fun _ => Iff.rfl⟩
  | .and left right, result, found => by
    simp only [eliminate, eliminateAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
    obtain ⟨left', leftFound, right', rightFound, rfl⟩ := found
    obtain ⟨leftTwo, leftSame⟩ := eliminate_spec left leftFound
    obtain ⟨rightTwo, rightSame⟩ := eliminate_spec right rightFound
    exact ⟨by simp [Formula.twoWay, leftTwo, rightTwo], fun element => and_congr (leftSame element) (rightSame element)⟩
  | .or left right, result, found => by
    simp only [eliminate, eliminateAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
    obtain ⟨left', leftFound, right', rightFound, rfl⟩ := found
    obtain ⟨leftTwo, leftSame⟩ := eliminate_spec left leftFound
    obtain ⟨rightTwo, rightSame⟩ := eliminate_spec right rightFound
    exact ⟨by simp [Formula.twoWay, leftTwo, rightTwo], fun element => or_congr (leftSame element) (rightSame element)⟩
  | .split kind left right, result, found => by
    simp only [eliminate, eliminateAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
    obtain ⟨left', leftFound, right', rightFound, rfl⟩ := found
    obtain ⟨leftTwo, leftSame⟩ := eliminate_spec left leftFound
    obtain ⟨rightTwo, rightSame⟩ := eliminate_spec right rightFound
    refine ⟨by simp [Formula.twoWay, leftTwo, rightTwo], fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact exists_congr fun first => exists_congr fun second =>
      and_congr_right fun _ => and_congr (leftSame first) (rightSame second)
  | .everySplit kind left right, result, found => by
    simp only [eliminate, eliminateAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
    obtain ⟨left', leftFound, right', rightFound, rfl⟩ := found
    obtain ⟨leftTwo, leftSame⟩ := eliminate_spec left leftFound
    obtain ⟨rightTwo, rightSame⟩ := eliminate_spec right rightFound
    refine ⟨by simp [Formula.twoWay, leftTwo, rightTwo], fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact forall_congr' fun first => forall_congr' fun second =>
      imp_congr_right fun _ => or_congr (leftSame first) (rightSame second)
  | .possibly label inner, result, found => by
    simp only [eliminate, eliminateAt, Option.map_eq_some_iff] at found
    obtain ⟨inner', innerFound, rfl⟩ := found
    obtain ⟨innerTwo, innerSame⟩ := eliminate_spec inner innerFound
    refine ⟨by simpa [Formula.twoWay] using innerTwo, fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact exists_congr fun next => and_congr_right fun _ => innerSame next
  | .necessarily label inner, result, found => by
    simp only [eliminate, eliminateAt, Option.map_eq_some_iff] at found
    obtain ⟨inner', innerFound, rfl⟩ := found
    obtain ⟨innerTwo, innerSame⟩ := eliminate_spec inner innerFound
    refine ⟨by simpa [Formula.twoWay] using innerTwo, fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact forall_congr' fun next => imp_congr_right fun _ => innerSame next
  | .sometimeBefore label inner, result, found => by
    simp only [eliminate, eliminateAt, Option.map_eq_some_iff] at found
    obtain ⟨inner', innerFound, rfl⟩ := found
    obtain ⟨innerTwo, innerSame⟩ := eliminate_spec inner innerFound
    refine ⟨by simpa [Formula.twoWay] using innerTwo, fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact exists_congr fun previous => and_congr_right fun _ => innerSame previous
  | .alwaysBefore label inner, result, found => by
    simp only [eliminate, eliminateAt, Option.map_eq_some_iff] at found
    obtain ⟨inner', innerFound, rfl⟩ := found
    obtain ⟨innerTwo, innerSame⟩ := eliminate_spec inner innerFound
    refine ⟨by simpa [Formula.twoWay] using innerTwo, fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact forall_congr' fun previous => imp_congr_right fun _ => innerSame previous
  | .someOf (.base sort) inner, result, found => by
    simp only [eliminate, eliminateAt, Option.map_eq_some_iff] at found
    obtain ⟨inner', innerFound, rfl⟩ := found
    obtain ⟨innerTwo, innerSame⟩ := eliminate_spec inner innerFound
    refine ⟨by simpa [Formula.twoWay] using innerTwo, fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact exists_congr fun witness => and_congr_right fun _ => innerSame witness
  | .everyOf (.base sort) inner, result, found => by
    simp only [eliminate, eliminateAt, Option.map_eq_some_iff] at found
    obtain ⟨inner', innerFound, rfl⟩ := found
    obtain ⟨innerTwo, innerSame⟩ := eliminate_spec inner innerFound
    refine ⟨by simpa [Formula.twoWay] using innerTwo, fun element => ?_⟩
    simp only [NativeStructure.sat]
    exact forall_congr' fun witness => imp_congr_right fun _ => innerSame witness
  | .var index, _, _ => index.elim0
  | .atLeast _ _ _ _, _, found | .allButFewer _ _ _ _, _, found | .built _ _, _, found | .everyBuilt _ _, _, found
  | .single _ _, _, found | .everySingle _ _, _, found | .body _, _, found | .everyBody _, _, found
  | .multiBody _ _, _, found | .everyMultiBody _ _, _, found | .bound _, _, found | .notBound _, _, found
  | .typed _, _, found | .untyped _, _, found | .mapsAll _ _, _, found | .mapsSome _ _, _, found
  | .someOf (.collection _ _) _, _, found | .someOf (.arrow _ _) _, _, found | .someOf (.multiBinder _) _, _, found
  | .everyOf (.collection _ _) _, _, found | .everyOf (.arrow _ _) _, _, found
  | .everyOf (.multiBinder _) _, _, found | .inRelation _, _, found | .notInRelation _, _, found => by
    simp [eliminate, eliminateAt] at found

/-- **Elimination answers every formula of the crossing fragment.** -/
theorem eliminate_isSome : ∀ (formula : Formula 0), crossing formula = true → (eliminate formula).isSome = true
  | .mu body, fragment => by
    simp only [crossing, crossingAt] at fragment
    simp only [eliminate, eliminateAt, fragment, if_true, Option.isSome_map]
    exact stableIndex_isSome_bot fragment
  | .nu body, fragment => by
    simp only [crossing, crossingAt] at fragment
    simp only [eliminate, eliminateAt, fragment, if_true, Option.isSome_map]
    exact stableIndex_isSome_top fragment
  | .top, _ | .bot, _ | .empty _, _ | .nonEmpty _, _ | .is _, _ | .isNot _, _ => by simp [eliminate, eliminateAt]
  | .and left right, fragment | .or left right, fragment | .split _ left right, fragment
  | .everySplit _ left right, fragment => by
    simp only [crossing, crossingAt, Bool.and_eq_true] at fragment
    obtain ⟨left', leftFound⟩ := Option.isSome_iff_exists.mp (eliminate_isSome left fragment.1)
    obtain ⟨right', rightFound⟩ := Option.isSome_iff_exists.mp (eliminate_isSome right fragment.2)
    simp only [eliminate] at leftFound rightFound
    simp [eliminate, eliminateAt, leftFound, rightFound]
  | .possibly _ inner, fragment | .necessarily _ inner, fragment | .sometimeBefore _ inner, fragment
  | .alwaysBefore _ inner, fragment | .someOf (.base _) inner, fragment | .everyOf (.base _) inner, fragment => by
    simp only [crossing, crossingAt] at fragment
    simp only [eliminate, eliminateAt, Option.isSome_map]
    exact eliminate_isSome inner fragment
  | .var index, _ => index.elim0
  | .atLeast _ _ _ _, fragment | .allButFewer _ _ _ _, fragment | .built _ _, fragment | .everyBuilt _ _, fragment
  | .single _ _, fragment | .everySingle _ _, fragment | .body _, fragment | .everyBody _, fragment
  | .multiBody _ _, fragment | .everyMultiBody _ _, fragment | .bound _, fragment | .notBound _, fragment
  | .typed _, fragment | .untyped _, fragment | .mapsAll _ _, fragment | .mapsSome _ _, fragment
  | .someOf (.collection _ _) _, fragment | .someOf (.arrow _ _) _, fragment | .someOf (.multiBinder _) _, fragment
  | .everyOf (.collection _ _) _, fragment | .everyOf (.arrow _ _) _, fragment
  | .everyOf (.multiBinder _) _, fragment | .inRelation _, fragment | .notInRelation _, fragment => by
    simp [crossing, crossingAt] at fragment

/-- **The decision is exact**, among the hereditarily finite sets. -/
theorem evalCrossing_iff {formula : Formula 0} {term : Pattern} {answer : Bool}
    (found : evalCrossing formula term = some answer) (holds : IsHF term) :
    answer = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  obtain ⟨result, eliminated, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨twoWay, same⟩ := eliminate_spec formula eliminated
  exact (evalTwoWay_iff result twoWay holds).trans (same _).symm

/-- **The decision answers every formula of the crossing fragment.** -/
theorem evalCrossing_isSome {formula : Formula 0} (fragment : crossing formula = true) (term : Pattern) :
    (evalCrossing formula term).isSome = true := by
  simp only [evalCrossing, Option.isSome_map]
  exact eliminate_isSome formula fragment

end SetReadings

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
