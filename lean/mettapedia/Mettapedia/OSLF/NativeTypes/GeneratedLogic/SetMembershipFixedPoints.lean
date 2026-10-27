import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipDetermined

/-!
# Fixed points under steps back

The two-way formulas of `SetMembershipTwoWay` have no fixed points; a step back over a fixed point asks for a set
containing `x` whose whole descent has a property, which no depth bounds. Here fixed points nest freely, decided through
the types of `SetMembershipTypes`, with two conditions on each variable, read along the path from its binder
(`Formula.guardedIn`):

- **guarded**: it sits under a step forward taken after its binder, so its value at a set is read at the members;
- **not crossing**: no step back or sort lies between it and its binder, so its value is never read at a container or
  at an arbitrary set.

Such formulas are **guarded** (`Formula.guarded`). The two-way formulas are guarded (`guarded_of_twoWay`), and so are
`μX. empty ∨ ◇◇X`, `νX. (μY. empty ∨ ◇◇Y) ∧ □X` and `μX. is 2 ∨ ◇(μY. X ∨ ◇◇Y)`, whose inner body reads the outer
variable; `νX. μY. (empty ∧ X) ∨ ◇Y` is not, since `X` meets no step forward before it occurs.

- **The closure** (`closureWith`, `guardedClosure`) collects, for each subformula, its instance with the closed fixed
  points of the enclosing binders put back for their variables, and the names of the named sets' members. Its length
  does not depend on what is put back (`length_closureWith`).
- **It is local** (`guardedClosure_isLocal`): each instance is decided by the members' types. A fixed point unfolds to
  its body (`sat_subst_mu`), whose top uses the fixed point's own variable only under a step forward, where only its
  membership in the closure matters. The variables of the enclosing binders that may appear at the top are already
  decided, since a step forward lies between them and their binders (`closureWith_local`).

So a step back over a guarded formula is decided by trying `x` with the subsets of `V_(2^m)`, for the `m` entries of its
closure (`sometimeBefore_guarded_iff`, `guardedBound`), and some set has a guarded formula exactly when a set of that
stage has it (`someOf_guarded_iff`). The evaluation is in `SetMembershipFixedPointDecision`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Formula

/-- **Guarded formulas**, with two masks on the free variables: `now` says which may occur here, and `later` which may
occur under a step forward. A step forward moves `later` to `now`, a step back or a sort forbids every variable, and a
fixed point adds its variable to `later` only. -/
def guardedIn : {n : ℕ} → (Fin n → Bool) → (Fin n → Bool) → Formula n → Bool
  | _, _, _, .top | _, _, _, .bot | _, _, _, .empty _ | _, _, _, .nonEmpty _ | _, _, _, .is _
  | _, _, _, .isNot _ => true
  | _, now, _, .var index => now index
  | _, now, later, .and left right | _, now, later, .or left right | _, now, later, .split _ left right
  | _, now, later, .everySplit _ left right => guardedIn now later left && guardedIn now later right
  | _, _, later, .possibly _ inner | _, _, later, .necessarily _ inner => guardedIn later later inner
  | _, _, _, .sometimeBefore _ inner | _, _, _, .alwaysBefore _ inner =>
    guardedIn (fun _ => false) (fun _ => false) inner
  | _, _, _, .someOf (.base _) inner | _, _, _, .everyOf (.base _) inner =>
    guardedIn (fun _ => false) (fun _ => false) inner
  | _, now, later, .mu inner | _, now, later, .nu inner =>
    guardedIn (Fin.cons false now : Fin (_ + 1) → Bool) (Fin.cons true later : Fin (_ + 1) → Bool) inner
  | _, _, _, _ => false

/-- **A guarded formula**: closed, each fixed-point variable under a step forward after its binder and under no step
back or sort. -/
def guarded (formula : Formula 0) : Bool := formula.guardedIn Fin.elim0 Fin.elim0

/-- Two-way formulas have no variables, so they are guarded under any masks. -/
theorem guardedIn_of_twoWay : ∀ {n : ℕ} (now later : Fin n → Bool) (formula : Formula n),
    formula.twoWay = true → formula.guardedIn now later = true
  | _, _, _, .top, _ | _, _, _, .bot, _ | _, _, _, .empty _, _ | _, _, _, .nonEmpty _, _ | _, _, _, .is _, _
  | _, _, _, .isNot _, _ => rfl
  | _, now, later, .and left right, two | _, now, later, .or left right, two
  | _, now, later, .split _ left right, two | _, now, later, .everySplit _ left right, two => by
    simp only [twoWay, Bool.and_eq_true] at two
    simp only [guardedIn, guardedIn_of_twoWay now later left two.1, guardedIn_of_twoWay now later right two.2,
      Bool.and_self]
  | _, _, later, .possibly _ inner, two | _, _, later, .necessarily _ inner, two =>
    guardedIn_of_twoWay later later inner two
  | _, _, _, .sometimeBefore _ inner, two | _, _, _, .alwaysBefore _ inner, two =>
    guardedIn_of_twoWay _ _ inner two
  | _, _, _, .someOf (.base _) inner, two | _, _, _, .everyOf (.base _) inner, two =>
    guardedIn_of_twoWay _ _ inner two
  | _, _, _, .var _, two | _, _, _, .mu _, two | _, _, _, .nu _, two | _, _, _, .typed _, two
  | _, _, _, .untyped _, two | _, _, _, .single _ _, two | _, _, _, .everySingle _ _, two
  | _, _, _, .atLeast _ _ _ _, two | _, _, _, .allButFewer _ _ _ _, two | _, _, _, .built _ _, two
  | _, _, _, .everyBuilt _ _, two | _, _, _, .body _, two | _, _, _, .everyBody _, two
  | _, _, _, .multiBody _ _, two | _, _, _, .everyMultiBody _ _, two | _, _, _, .bound _, two
  | _, _, _, .notBound _, two | _, _, _, .mapsAll _ _, two | _, _, _, .mapsSome _ _, two
  | _, _, _, .someOf (.collection _ _) _, two | _, _, _, .someOf (.arrow _ _) _, two
  | _, _, _, .someOf (.multiBinder _) _, two | _, _, _, .everyOf (.collection _ _) _, two
  | _, _, _, .everyOf (.arrow _ _) _, two | _, _, _, .everyOf (.multiBinder _) _, two
  | _, _, _, .inRelation _, two | _, _, _, .notInRelation _, two =>
    absurd two Bool.false_ne_true

theorem guarded_of_twoWay {formula : Formula 0} (two : formula.twoWay = true) : formula.guarded = true :=
  guardedIn_of_twoWay _ _ formula two

end Formula

namespace SetReadings

/-! ## Closures -/

/-- **The instances of a formula's subformulas**: the closed formulas `u` put back for the free variables, each fixed
point's own instance put back for its variable, and the names of the named sets' members. -/
def closureWith : {n : ℕ} → (Fin n → Formula 0) → Formula n → List (Formula 0)
  | _, u, .and left right => (Formula.and left right).subst u :: (closureWith u left ++ closureWith u right)
  | _, u, .or left right => (Formula.or left right).subst u :: (closureWith u left ++ closureWith u right)
  | _, u, .split kind left right =>
    (Formula.split kind left right).subst u :: (closureWith u left ++ closureWith u right)
  | _, u, .everySplit kind left right =>
    (Formula.everySplit kind left right).subst u :: (closureWith u left ++ closureWith u right)
  | _, u, .possibly label inner => (Formula.possibly label inner).subst u :: closureWith u inner
  | _, u, .necessarily label inner => (Formula.necessarily label inner).subst u :: closureWith u inner
  | _, u, .sometimeBefore label inner => (Formula.sometimeBefore label inner).subst u :: closureWith u inner
  | _, u, .alwaysBefore label inner => (Formula.alwaysBefore label inner).subst u :: closureWith u inner
  | _, u, .someOf type inner => (Formula.someOf type inner).subst u :: closureWith u inner
  | _, u, .everyOf type inner => (Formula.everyOf type inner).subst u :: closureWith u inner
  | _, u, .atLeast count direction label inner =>
    (Formula.atLeast count direction label inner).subst u :: closureWith u inner
  | _, u, .allButFewer count direction label inner =>
    (Formula.allButFewer count direction label inner).subst u :: closureWith u inner
  | _, u, .single kind inner => (Formula.single kind inner).subst u :: closureWith u inner
  | _, u, .everySingle kind inner => (Formula.everySingle kind inner).subst u :: closureWith u inner
  | _, u, .mu inner =>
    (Formula.mu inner).subst u :: closureWith (Fin.cons ((Formula.mu inner).subst u) u : Fin (_ + 1) → Formula 0) inner
  | _, u, .nu inner =>
    (Formula.nu inner).subst u :: closureWith (Fin.cons ((Formula.nu inner).subst u) u : Fin (_ + 1) → Formula 0) inner
  | _, _, .is target => nameClosure target
  | _, _, .isNot target => .isNot target :: nameClosure target
  | _, u, formula => [formula.subst u]

/-- **The closure of a guarded formula.** -/
def guardedClosure (formula : Formula 0) : List (Formula 0) := closureWith Fin.elim0 formula

/-- The length of a closure, read off the formula. -/
def closureSize : {n : ℕ} → Formula n → ℕ
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    closureSize left + closureSize right + 1
  | _, .possibly _ inner | _, .necessarily _ inner | _, .sometimeBefore _ inner | _, .alwaysBefore _ inner
  | _, .someOf _ inner | _, .everyOf _ inner => closureSize inner + 1
  | _, .atLeast _ _ _ inner | _, .allButFewer _ _ _ inner | _, .single _ inner | _, .everySingle _ inner =>
    closureSize inner + 1
  | _, .mu inner | _, .nu inner => closureSize inner + 1
  | _, .is target => (nameClosure target).length
  | _, .isNot target => (nameClosure target).length + 1
  | _, _ => 1

/-- **The length of a closure does not depend on what is put back.** -/
theorem length_closureWith : ∀ {n : ℕ} (u : Fin n → Formula 0) (formula : Formula n),
    (closureWith u formula).length = closureSize formula
  | _, u, .and left right | _, u, .or left right | _, u, .split _ left right | _, u, .everySplit _ left right => by
    simp only [closureWith, closureSize, List.length_cons, List.length_append, length_closureWith u left,
      length_closureWith u right]
  | _, u, .possibly _ inner | _, u, .necessarily _ inner | _, u, .sometimeBefore _ inner
  | _, u, .alwaysBefore _ inner | _, u, .someOf _ inner | _, u, .everyOf _ inner
  | _, u, .atLeast _ _ _ inner | _, u, .allButFewer _ _ _ inner | _, u, .single _ inner
  | _, u, .everySingle _ inner => by
    simp only [closureWith, closureSize, List.length_cons, length_closureWith u inner]
  | _, u, .mu inner | _, u, .nu inner => by
    simp only [closureWith, closureSize, List.length_cons, length_closureWith _ inner]
  | _, _, .is _ => rfl
  | _, _, .isNot _ => rfl
  | _, _, .top | _, _, .bot | _, _, .var _
  | _, _, .built _ _ | _, _, .everyBuilt _ _ | _, _, .empty _ | _, _, .nonEmpty _
  | _, _, .body _ | _, _, .everyBody _ | _, _, .multiBody _ _
  | _, _, .everyMultiBody _ _ | _, _, .bound _ | _, _, .notBound _ | _, _, .typed _ | _, _, .untyped _
  | _, _, .mapsAll _ _ | _, _, .mapsSome _ _ | _, _, .inRelation _ | _, _, .notInRelation _ => rfl

theorem subst_mem_closureWith {n : ℕ} (u : Fin n → Formula 0) (formula : Formula n) :
    formula.subst u ∈ closureWith u formula := by
  cases formula <;> simp [closureWith, Formula.subst, is_mem_nameClosure]

/-! ## Unfolding substituted fixed points -/

theorem closedTruth_cons {n : ℕ} (fixed : Formula 0) (u : Fin n → Formula 0) :
    (fun index => {other | HFSets.sat Env.closed ((Fin.cons fixed u : Fin (n + 1) → Formula 0) index) other}) =
      Env.extend (fun index => {other | HFSets.sat Env.closed (u index) other}) {other | HFSets.sat Env.closed fixed other} := by
  funext index
  induction index using Fin.cases with
  | zero => rfl
  | succ index => rfl

/-- **A substituted least fixed point unfolds**, with its own instance put back for its variable. -/
theorem sat_subst_mu {n : ℕ} (inner : Formula (n + 1)) (u : Fin n → Formula 0) (x : HF) :
    HFSets.sat Env.closed ((Formula.mu inner).subst u) x ↔
      HFSets.sat Env.closed (inner.subst (Fin.cons ((Formula.mu inner).subst u) u : Fin (n + 1) → Formula 0)) x := by
  rw [HFSets.sat_close, HFSets.sat_close, closedTruth_cons, HFSets.sat_mu_unfold, HFSets.sat_subst,
    HFSets.truthSets_unfolding]
  have same : {other | HFSets.sat (fun index => {other | HFSets.sat Env.closed (u index) other}) (.mu inner) other} =
      {other | HFSets.sat Env.closed ((Formula.mu inner).subst u) other} := by
    ext other
    exact (HFSets.sat_close u (.mu inner) other).symm
  rw [same]

/-- **A substituted greatest fixed point unfolds.** -/
theorem sat_subst_nu {n : ℕ} (inner : Formula (n + 1)) (u : Fin n → Formula 0) (x : HF) :
    HFSets.sat Env.closed ((Formula.nu inner).subst u) x ↔
      HFSets.sat Env.closed (inner.subst (Fin.cons ((Formula.nu inner).subst u) u : Fin (n + 1) → Formula 0)) x := by
  rw [HFSets.sat_close, HFSets.sat_close, closedTruth_cons, HFSets.sat_nu_unfold, HFSets.sat_subst,
    HFSets.truthSets_unfolding]
  have same : {other | HFSets.sat (fun index => {other | HFSets.sat Env.closed (u index) other}) (.nu inner) other} =
      {other | HFSets.sat Env.closed ((Formula.nu inner).subst u) other} := by
    ext other
    exact (HFSets.sat_close u (.nu inner) other).symm
  rw [same]

/-- Putting back nothing changes nothing. -/
theorem sat_subst_elim0 (formula : Formula 0) (x : HF) :
    HFSets.sat Env.closed (formula.subst (Fin.elim0 : Fin 0 → Formula 0)) x ↔ HFSets.sat Env.closed formula x := by
  rw [HFSets.sat_close]
  have : (fun index : Fin 0 => {other | HFSets.sat Env.closed ((Fin.elim0 : Fin 0 → Formula 0) index) other}) =
      Env.closed := funext fun index => index.elim0
  rw [this]

/-! ## Local closures -/

theorem cons_masks_mono {n : ℕ} {now later : Fin n → Bool} (mono : ∀ index, now index = true → later index = true) :
    ∀ index, (Fin.cons false now : Fin (n + 1) → Bool) index = true →
      (Fin.cons true later : Fin (n + 1) → Bool) index = true := by
  intro index
  induction index using Fin.cases with
  | zero => exact fun _ => rfl
  | succ index => exact mono index

/-- The hypothesis on the variables, carried under a fixed point: its own variable may not occur at the top. -/
theorem cons_now_determined {C : List (Formula 0)} {n : ℕ} {now : Fin n → Bool} {u : Fin n → Formula 0}
    (fixed : Formula 0) (nowHyp : ∀ index, now index = true → Determined C (HFSets.sat Env.closed (u index))) :
    ∀ index, (Fin.cons false now : Fin (n + 1) → Bool) index = true →
      Determined C (HFSets.sat Env.closed ((Fin.cons fixed u : Fin (n + 1) → Formula 0) index)) := by
  intro index
  induction index using Fin.cases with
  | zero => exact fun never => absurd never Bool.false_ne_true
  | succ index => exact nowHyp index

/-- Under a step forward, the fixed point's own variable reads its instance, once that is decided. -/
theorem cons_later_determined {C : List (Formula 0)} {n : ℕ} {later : Fin n → Bool} {u : Fin n → Formula 0}
    {fixed : Formula 0} (fixedDetermined : Determined C (HFSets.sat Env.closed fixed))
    (laterHyp : ∀ index, later index = true → Determined C (HFSets.sat Env.closed (u index))) :
    ∀ index, (Fin.cons true later : Fin (n + 1) → Bool) index = true →
      Determined C (HFSets.sat Env.closed ((Fin.cons fixed u : Fin (n + 1) → Formula 0) index)) := by
  intro index
  induction index using Fin.cases with
  | zero => exact fun _ => fixedDetermined
  | succ index => exact laterHyp index

/-- **The closure of a guarded formula is decided by the members' types.** The top of each instance is decided once
the variables that may occur there are (first part); every instance is decided once the variables that may occur under
a step forward are (second part). Under a fixed point its own variable may occur only under a step forward, where it
reads the fixed point's instance, which the first part decides. -/
theorem closureWith_local : ∀ {n : ℕ} (now later : Fin n → Bool) (u : Fin n → Formula 0) (formula : Formula n),
    formula.guardedIn now later = true → (∀ index, now index = true → later index = true) →
    ∀ C : List (Formula 0), closureWith u formula ⊆ C →
      ((∀ index, now index = true → Determined C (HFSets.sat Env.closed (u index))) →
        Determined C (HFSets.sat Env.closed (formula.subst u))) ∧
      ((∀ index, later index = true → Determined C (HFSets.sat Env.closed (u index))) →
        ∀ φ ∈ closureWith u formula, Determined C (HFSets.sat Env.closed φ))
  | _, _, _, u, .top, _, _, _, _ => ⟨fun _ => Determined.const True, fun _ φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact Determined.const True⟩
  | _, _, _, u, .bot, _, _, _, _ => ⟨fun _ => Determined.const False, fun _ φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact Determined.const False⟩
  | _, _, _, u, .empty kind, _, _, _, _ => ⟨fun _ => determined_empty kind, fun _ φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact determined_empty kind⟩
  | _, _, _, u, .nonEmpty kind, _, _, _, _ => ⟨fun _ => determined_nonEmpty kind, fun _ φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact determined_nonEmpty kind⟩
  | _, _, _, u, .var index, ok, mono, _, _ => ⟨fun nowHyp => nowHyp index ok, fun laterHyp φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact laterHyp index (mono index ok)⟩
  | _, _, _, u, .is target, _, _, C, within =>
    ⟨fun _ => determined_is (names_of_nameClosure within),
      fun _ φ found => (nameClosure_isLocal target φ found).mono within⟩
  | _, _, _, u, .isNot target, _, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    refine ⟨fun _ => determined_isNot (names_of_nameClosure within.2), fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact determined_isNot (names_of_nameClosure within.2)
    · exact (nameClosure_isLocal target φ found).mono within.2
  | _, now, later, u, .and left right, ok, mono, C, within => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_local now later u left ok.1 mono C within.2.1
    have rightLocal := closureWith_local now later u right ok.2 mono C within.2.2
    refine ⟨fun nowHyp => (leftLocal.1 nowHyp).and (rightLocal.1 nowHyp), fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact (leftLocal.1 fun index h => laterHyp index (mono index h)).and
        (rightLocal.1 fun index h => laterHyp index (mono index h))
    · exact leftLocal.2 laterHyp φ found
    · exact rightLocal.2 laterHyp φ found
  | _, now, later, u, .or left right, ok, mono, C, within => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_local now later u left ok.1 mono C within.2.1
    have rightLocal := closureWith_local now later u right ok.2 mono C within.2.2
    refine ⟨fun nowHyp => (leftLocal.1 nowHyp).or (rightLocal.1 nowHyp), fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact (leftLocal.1 fun index h => laterHyp index (mono index h)).or
        (rightLocal.1 fun index h => laterHyp index (mono index h))
    · exact leftLocal.2 laterHyp φ found
    · exact rightLocal.2 laterHyp φ found
  | _, now, later, u, .split kind left right, ok, mono, C, within => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_local now later u left ok.1 mono C within.2.1
    have rightLocal := closureWith_local now later u right ok.2 mono C within.2.2
    refine ⟨fun nowHyp => determined_split kind (leftLocal.1 nowHyp) (rightLocal.1 nowHyp),
      fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact determined_split kind (leftLocal.1 fun index h => laterHyp index (mono index h))
        (rightLocal.1 fun index h => laterHyp index (mono index h))
    · exact leftLocal.2 laterHyp φ found
    · exact rightLocal.2 laterHyp φ found
  | _, now, later, u, .everySplit kind left right, ok, mono, C, within => by
    simp only [Formula.guardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_local now later u left ok.1 mono C within.2.1
    have rightLocal := closureWith_local now later u right ok.2 mono C within.2.2
    refine ⟨fun nowHyp => determined_everySplit kind (leftLocal.1 nowHyp) (rightLocal.1 nowHyp),
      fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact determined_everySplit kind (leftLocal.1 fun index h => laterHyp index (mono index h))
        (rightLocal.1 fun index h => laterHyp index (mono index h))
    · exact leftLocal.2 laterHyp φ found
    · exact rightLocal.2 laterHyp φ found
  | _, now, later, u, .possibly label inner, ok, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_local later later u inner ok (fun _ h => h) C within.2
    have head : Determined C (HFSets.sat Env.closed ((Formula.possibly label inner).subst u)) :=
      determined_possibly (within.2 (subst_mem_closureWith u inner)) label
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head
    · exact innerLocal.2 laterHyp φ found
  | _, now, later, u, .necessarily label inner, ok, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_local later later u inner ok (fun _ h => h) C within.2
    have head : Determined C (HFSets.sat Env.closed ((Formula.necessarily label inner).subst u)) :=
      determined_necessarily (within.2 (subst_mem_closureWith u inner)) label
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head
    · exact innerLocal.2 laterHyp φ found
  | _, _, _, u, .sometimeBefore label inner, ok, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have smallLocal : IsLocal (closureWith u inner) := fun φ found =>
      (closureWith_local _ _ u inner ok (fun _ h => h) (closureWith u inner) (List.Subset.refl _)).2
        (fun _ never => absurd never Bool.false_ne_true) φ found
    have head : Determined C (HFSets.sat Env.closed ((Formula.sometimeBefore label inner).subst u)) :=
      determined_sometimeBefore within.2 smallLocal (subst_mem_closureWith u inner) label
    refine ⟨fun _ => head, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head
    · exact (smallLocal φ found).mono within.2
  | _, _, _, u, .alwaysBefore label inner, ok, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have smallLocal : IsLocal (closureWith u inner) := fun φ found =>
      (closureWith_local _ _ u inner ok (fun _ h => h) (closureWith u inner) (List.Subset.refl _)).2
        (fun _ never => absurd never Bool.false_ne_true) φ found
    have head : Determined C (HFSets.sat Env.closed ((Formula.alwaysBefore label inner).subst u)) :=
      determined_alwaysBefore within.2 smallLocal (subst_mem_closureWith u inner) label
    refine ⟨fun _ => head, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head
    · exact (smallLocal φ found).mono within.2
  | _, _, _, u, .someOf (.base sort) inner, ok, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_local _ _ u inner ok (fun _ h => h) C within.2
    refine ⟨fun _ => determined_someOf _ _, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact determined_someOf _ _
    · exact innerLocal.2 (fun _ never => absurd never Bool.false_ne_true) φ found
  | _, _, _, u, .everyOf (.base sort) inner, ok, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_local _ _ u inner ok (fun _ h => h) C within.2
    refine ⟨fun _ => determined_everyOf _ _, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact determined_everyOf _ _
    · exact innerLocal.2 (fun _ never => absurd never Bool.false_ne_true) φ found
  | _, now, later, u, .mu inner, ok, mono, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_local _ _ _ inner ok (cons_masks_mono mono) C within.2
    have head : (∀ index, now index = true → Determined C (HFSets.sat Env.closed (u index))) →
        Determined C (HFSets.sat Env.closed ((Formula.mu inner).subst u)) := fun nowHyp =>
      Determined.of_iff (sat_subst_mu inner u) (innerLocal.1 (cons_now_determined _ nowHyp))
    refine ⟨head, fun laterHyp φ found => ?_⟩
    have fixedDetermined := head fun index h => laterHyp index (mono index h)
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact fixedDetermined
    · exact innerLocal.2 (cons_later_determined fixedDetermined laterHyp) φ found
  | _, now, later, u, .nu inner, ok, mono, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_local _ _ _ inner ok (cons_masks_mono mono) C within.2
    have head : (∀ index, now index = true → Determined C (HFSets.sat Env.closed (u index))) →
        Determined C (HFSets.sat Env.closed ((Formula.nu inner).subst u)) := fun nowHyp =>
      Determined.of_iff (sat_subst_nu inner u) (innerLocal.1 (cons_now_determined _ nowHyp))
    refine ⟨head, fun laterHyp φ found => ?_⟩
    have fixedDetermined := head fun index h => laterHyp index (mono index h)
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact fixedDetermined
    · exact innerLocal.2 (cons_later_determined fixedDetermined laterHyp) φ found
  | _, _, _, _, .typed _, ok, _, _, _ | _, _, _, _, .untyped _, ok, _, _, _
  | _, _, _, _, .single _ _, ok, _, _, _ | _, _, _, _, .everySingle _ _, ok, _, _, _
  | _, _, _, _, .atLeast _ _ _ _, ok, _, _, _ | _, _, _, _, .allButFewer _ _ _ _, ok, _, _, _
  | _, _, _, _, .built _ _, ok, _, _, _ | _, _, _, _, .everyBuilt _ _, ok, _, _, _
  | _, _, _, _, .body _, ok, _, _, _ | _, _, _, _, .everyBody _, ok, _, _, _
  | _, _, _, _, .multiBody _ _, ok, _, _, _ | _, _, _, _, .everyMultiBody _ _, ok, _, _, _
  | _, _, _, _, .bound _, ok, _, _, _ | _, _, _, _, .notBound _, ok, _, _, _
  | _, _, _, _, .mapsAll _ _, ok, _, _, _ | _, _, _, _, .mapsSome _ _, ok, _, _, _
  | _, _, _, _, .someOf (.collection _ _) _, ok, _, _, _ | _, _, _, _, .someOf (.arrow _ _) _, ok, _, _, _
  | _, _, _, _, .someOf (.multiBinder _) _, ok, _, _, _ | _, _, _, _, .everyOf (.collection _ _) _, ok, _, _, _
  | _, _, _, _, .everyOf (.arrow _ _) _, ok, _, _, _ | _, _, _, _, .everyOf (.multiBinder _) _, ok, _, _, _
  | _, _, _, _, .inRelation _, ok, _, _, _ | _, _, _, _, .notInRelation _, ok, _, _, _ =>
    absurd ok Bool.false_ne_true

/-- **The closure of a guarded formula is local.** -/
theorem guardedClosure_isLocal {formula : Formula 0} (ok : formula.guarded = true) :
    IsLocal (guardedClosure formula) := fun φ found =>
  (closureWith_local Fin.elim0 Fin.elim0 Fin.elim0 formula ok (fun index => index.elim0) _ (List.Subset.refl _)).2
    (fun index => index.elim0) φ found

/-- **Under a step back or a sort**, where no variable occurs, the closure is local whatever is put back. -/
theorem closureWith_isLocal {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.guardedIn (fun _ => false) (fun _ => false) = true) : IsLocal (closureWith u formula) :=
  fun φ found => (closureWith_local _ _ u formula ok (fun _ h => h) _ (List.Subset.refl _)).2
    (fun _ never => absurd never Bool.false_ne_true) φ found

/-! ## Steps back over guarded formulas -/

/-- The stage that serves a formula: `V_(2^m)`, for the `m` entries of its closure. -/
def guardedBound {n : ℕ} (formula : Formula n) : ℕ := 2 ^ closureSize formula

theorem typeBound_closureWith_le {n : ℕ} (u : Fin n → Formula 0) (formula : Formula n) :
    typeBound (closureWith u formula) ≤ guardedBound formula := by
  rw [guardedBound, ← length_closureWith u formula]
  exact typeBound_le_pow

/-- **Some set containing `x` has a guarded formula exactly when `x` added to some subset of a finite stage has it.** -/
theorem sometimeBefore_guarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.guardedIn (fun _ => false) (fun _ => false) = true) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.sometimeBefore label (formula.subst u)) x ↔
      memberLabel label ∧ ∃ part, ∃ within : part ⊆ stage (guardedBound formula),
        HFSets.sat Env.closed (formula.subst u) (insertStage x within) :=
  sometimeBefore_iff_stage (closureWith_isLocal u ok) (typeBound_closureWith_le u formula)
    (subst_mem_closureWith u formula) label x

theorem alwaysBefore_guarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.guardedIn (fun _ => false) (fun _ => false) = true) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.alwaysBefore label (formula.subst u)) x ↔
      (memberLabel label → ∀ part, ∀ within : part ⊆ stage (guardedBound formula),
        HFSets.sat Env.closed (formula.subst u) (insertStage x within)) :=
  alwaysBefore_iff_stage (closureWith_isLocal u ok) (typeBound_closureWith_le u formula)
    (subst_mem_closureWith u formula) label x

/-- **Some set has a guarded formula exactly when some set of a finite stage has it.** -/
theorem someOf_guarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.guardedIn (fun _ => false) (fun _ => false) = true) (x : HF) :
    HFSets.sat Env.closed (.someOf (.base "Set") (formula.subst u)) x ↔
      ∃ y : HF, y.1 ∈ stage (guardedBound formula) ∧ HFSets.sat Env.closed (formula.subst u) y :=
  someOf_iff_stage (closureWith_isLocal u ok) (typeBound_closureWith_le u formula) (subst_mem_closureWith u formula) x

theorem everyOf_guarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.guardedIn (fun _ => false) (fun _ => false) = true) (x : HF) :
    HFSets.sat Env.closed (.everyOf (.base "Set") (formula.subst u)) x ↔
      ∀ y : HF, y.1 ∈ stage (guardedBound formula) → HFSets.sat Env.closed (formula.subst u) y :=
  everyOf_iff_stage (closureWith_isLocal u ok) (typeBound_closureWith_le u formula) (subst_mem_closureWith u formula) x

end SetReadings

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
