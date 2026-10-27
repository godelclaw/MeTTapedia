import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedFormers
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPoints

/-!
# Counting and singletons with fixed points under steps back

The guarded formulas of `SetMembershipFixedPoints`, with counting members and singletons added, are decided through
the counts of the members' types up to a cap (`SetMembershipCountedTypes`).

- **Count-guarded formulas** (`Formula.countGuardedIn`): counting members (forward) and singletons read the members,
  as a step forward does, so a variable may sit under them where it may sit under a step forward. Counting containers
  (backward) is outside the fragment. Guarded formulas are count-guarded (`countGuardedIn_of_guardedIn`).
- **The cap a formula's top needs** (`topCap`): one for the formers that read only which types the members have, `k`
  for at least `k` members, two for a singleton, the sum of the parts' caps for a split, the cap of its closure for a
  step back, and a free variable's own cap. **The cap of a closure** (`closureCap`) is the largest cap its instances
  need.
- **The closure of a count-guarded formula is count-local** at its closure cap (`closureWith_countLocal`,
  `countGuardedClosure_isCountLocal`).

So a step back over a count-guarded formula is decided by trying `x` with the subsets of a finite stage,
`2 ^ m · (c + 1)` for the `m` entries of its closure and its closure cap `c` (`countedStage`,
`sometimeBefore_countGuarded_iff`), and some set has a count-guarded formula exactly when a set of that stage has it
(`someOf_countGuarded_iff`). The evaluation is in `SetMembershipCountedDecision`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Formula

/-- **Count-guarded formulas**: the guarded formulas with counting members and singletons, which move `later` to
`now` as a step forward does. -/
def countGuardedIn : {n : ℕ} → (Fin n → Bool) → (Fin n → Bool) → Formula n → Bool
  | _, _, _, .top | _, _, _, .bot | _, _, _, .empty _ | _, _, _, .nonEmpty _ | _, _, _, .is _
  | _, _, _, .isNot _ => true
  | _, now, _, .var index => now index
  | _, now, later, .and left right | _, now, later, .or left right | _, now, later, .split _ left right
  | _, now, later, .everySplit _ left right => countGuardedIn now later left && countGuardedIn now later right
  | _, _, later, .possibly _ inner | _, _, later, .necessarily _ inner => countGuardedIn later later inner
  | _, _, later, .atLeast _ .forward _ inner | _, _, later, .allButFewer _ .forward _ inner
  | _, _, later, .single _ inner | _, _, later, .everySingle _ inner => countGuardedIn later later inner
  | _, _, _, .sometimeBefore _ inner | _, _, _, .alwaysBefore _ inner =>
    countGuardedIn (fun _ => false) (fun _ => false) inner
  | _, _, _, .someOf (.base _) inner | _, _, _, .everyOf (.base _) inner =>
    countGuardedIn (fun _ => false) (fun _ => false) inner
  | _, now, later, .mu inner | _, now, later, .nu inner =>
    countGuardedIn (Fin.cons false now : Fin (_ + 1) → Bool) (Fin.cons true later : Fin (_ + 1) → Bool) inner
  | _, _, _, _ => false

/-- **A count-guarded formula**: closed and count-guarded. -/
def countGuarded (formula : Formula 0) : Bool := formula.countGuardedIn Fin.elim0 Fin.elim0

mutual
/-- **The cap a formula's top needs**, with each free variable's cap given. -/
def topCap : {n : ℕ} → (Fin n → ℕ) → Formula n → ℕ
  | _, caps, .var index => caps index
  | _, caps, .and left right | _, caps, .or left right => max (topCap caps left) (topCap caps right)
  | _, caps, .split _ left right | _, caps, .everySplit _ left right => topCap caps left + topCap caps right
  | _, _, .atLeast count _ _ _ | _, _, .allButFewer count _ _ _ => max 1 count
  | _, _, .single _ _ | _, _, .everySingle _ _ => 2
  | _, caps, .sometimeBefore _ inner | _, caps, .alwaysBefore _ inner => closureCap caps inner
  | _, caps, .mu inner | _, caps, .nu inner => topCap (Fin.cons 1 caps : Fin (_ + 1) → ℕ) inner
  | _, _, _ => 1

/-- **The cap a formula's closure needs**: the largest cap its instances need. A fixed point's variable has the cap
of the fixed point's top. -/
def closureCap : {n : ℕ} → (Fin n → ℕ) → Formula n → ℕ
  | _, caps, .var index => caps index
  | _, caps, .and left right | _, caps, .or left right =>
    max (max (topCap caps left) (topCap caps right)) (max (closureCap caps left) (closureCap caps right))
  | _, caps, .split _ left right | _, caps, .everySplit _ left right =>
    max (topCap caps left + topCap caps right) (max (closureCap caps left) (closureCap caps right))
  | _, caps, .possibly _ inner | _, caps, .necessarily _ inner | _, caps, .someOf _ inner
  | _, caps, .everyOf _ inner => max 1 (closureCap caps inner)
  | _, caps, .atLeast count _ _ inner | _, caps, .allButFewer count _ _ inner => max (max 1 count) (closureCap caps inner)
  | _, caps, .single _ inner | _, caps, .everySingle _ inner => max 2 (closureCap caps inner)
  | _, caps, .sometimeBefore _ inner | _, caps, .alwaysBefore _ inner => closureCap caps inner
  | _, caps, .mu inner | _, caps, .nu inner =>
    max (topCap (Fin.cons 1 caps : Fin (_ + 1) → ℕ) inner)
      (closureCap (Fin.cons (topCap (Fin.cons 1 caps : Fin (_ + 1) → ℕ) inner) caps : Fin (_ + 1) → ℕ) inner)
  | _, _, _ => 1
end

/-- Caps are positive where the variables' are. -/
theorem one_le_caps : ∀ {n : ℕ} {caps : Fin n → ℕ} (formula : Formula n), (∀ index, 1 ≤ caps index) →
    1 ≤ topCap caps formula ∧ 1 ≤ closureCap caps formula
  | _, _, .var index, positive => ⟨positive index, positive index⟩
  | _, _, .and left right, positive | _, _, .or left right, positive => by
    have l := one_le_caps left positive
    have r := one_le_caps right positive
    simp only [topCap, closureCap]
    omega
  | _, _, .split _ left right, positive | _, _, .everySplit _ left right, positive => by
    have l := one_le_caps left positive
    have r := one_le_caps right positive
    simp only [topCap, closureCap]
    omega
  | _, _, .possibly _ inner, _ | _, _, .necessarily _ inner, _ | _, _, .someOf _ inner, _
  | _, _, .everyOf _ inner, _ => by simp only [topCap, closureCap]; omega
  | _, _, .atLeast _ _ _ inner, _ | _, _, .allButFewer _ _ _ inner, _ => by simp only [topCap, closureCap]; omega
  | _, _, .single _ inner, _ | _, _, .everySingle _ inner, _ => by simp only [topCap, closureCap]; omega
  | _, _, .sometimeBefore _ inner, positive | _, _, .alwaysBefore _ inner, positive => by
    have i := one_le_caps inner positive
    simp only [topCap, closureCap]
    omega
  | _, caps, .mu inner, positive | _, caps, .nu inner, positive => by
    have consPositive : ∀ index, 1 ≤ (Fin.cons 1 caps : Fin (_ + 1) → ℕ) index := fun index => by
      induction index using Fin.cases with
      | zero => exact le_rfl
      | succ index => exact positive index
    have i := one_le_caps inner consPositive
    simp only [topCap, closureCap]
    omega
  | _, _, .top, _ | _, _, .bot, _ | _, _, .empty _, _ | _, _, .nonEmpty _, _ | _, _, .is _, _
  | _, _, .isNot _, _ | _, _, .built _ _, _ | _, _, .everyBuilt _ _, _ | _, _, .body _, _
  | _, _, .everyBody _, _ | _, _, .multiBody _ _, _ | _, _, .everyMultiBody _ _, _ | _, _, .bound _, _
  | _, _, .notBound _, _ | _, _, .typed _, _ | _, _, .untyped _, _ | _, _, .mapsAll _ _, _
  | _, _, .mapsSome _ _, _ | _, _, .inRelation _, _ | _, _, .notInRelation _, _ => by
    simp only [topCap, closureCap]
    omega

theorem topCap_le_closureCap : ∀ {n : ℕ} {caps : Fin n → ℕ} (formula : Formula n),
    topCap caps formula ≤ closureCap caps formula
  | _, _, .var _ => le_rfl
  | _, _, .and _ _ | _, _, .or _ _ | _, _, .split _ _ _ | _, _, .everySplit _ _ _ => by
    simp only [topCap, closureCap]
    omega
  | _, _, .possibly _ _ | _, _, .necessarily _ _ | _, _, .someOf _ _ | _, _, .everyOf _ _ => by
    simp only [topCap, closureCap]
    omega
  | _, _, .atLeast _ _ _ _ | _, _, .allButFewer _ _ _ _ | _, _, .single _ _ | _, _, .everySingle _ _ => by
    simp only [topCap, closureCap]
    omega
  | _, _, .sometimeBefore _ _ | _, _, .alwaysBefore _ _ => le_rfl
  | _, _, .mu _ | _, _, .nu _ => by
    simp only [topCap, closureCap]
    omega
  | _, _, .top | _, _, .bot | _, _, .empty _ | _, _, .nonEmpty _ | _, _, .is _ | _, _, .isNot _
  | _, _, .built _ _ | _, _, .everyBuilt _ _ | _, _, .body _ | _, _, .everyBody _ | _, _, .multiBody _ _
  | _, _, .everyMultiBody _ _ | _, _, .bound _ | _, _, .notBound _ | _, _, .typed _ | _, _, .untyped _
  | _, _, .mapsAll _ _ | _, _, .mapsSome _ _ | _, _, .inRelation _ | _, _, .notInRelation _ => le_rfl

end Formula

namespace SetReadings

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula (topCap closureCap one_le_caps topCap_le_closureCap)

/-! ## Count-local closures -/

theorem cons_positive {n : ℕ} {caps : Fin n → ℕ} (positive : ∀ index, 1 ≤ caps index) {c : ℕ} (one : 1 ≤ c) :
    ∀ index, 1 ≤ (Fin.cons c caps : Fin (n + 1) → ℕ) index := by
  intro index
  induction index using Fin.cases with
  | zero => exact one
  | succ index => exact positive index

/-- The hypothesis on the variables, carried under a fixed point: its own variable may not occur at the top. -/
theorem cons_now_counted {C : List (Formula 0)} {n : ℕ} {now : Fin n → Bool} {u : Fin n → Formula 0}
    {caps : Fin n → ℕ} (fixed : Formula 0) {c : ℕ}
    (nowHyp : ∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) :
    ∀ index, (Fin.cons false now : Fin (n + 1) → Bool) index = true →
      CountDetermined C ((Fin.cons c caps : Fin (n + 1) → ℕ) index)
        (HFSets.sat Env.closed ((Fin.cons fixed u : Fin (n + 1) → Formula 0) index)) := by
  intro index
  induction index using Fin.cases with
  | zero => exact fun never => absurd never Bool.false_ne_true
  | succ index => exact nowHyp index

/-- Under a step forward, the fixed point's own variable reads its instance, once that is decided. -/
theorem cons_later_counted {C : List (Formula 0)} {n : ℕ} {later : Fin n → Bool} {u : Fin n → Formula 0}
    {caps : Fin n → ℕ} {fixed : Formula 0} {c : ℕ} (fixedDetermined : CountDetermined C c (HFSets.sat Env.closed fixed))
    (laterHyp : ∀ index, later index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) :
    ∀ index, (Fin.cons true later : Fin (n + 1) → Bool) index = true →
      CountDetermined C ((Fin.cons c caps : Fin (n + 1) → ℕ) index)
        (HFSets.sat Env.closed ((Fin.cons fixed u : Fin (n + 1) → Formula 0) index)) := by
  intro index
  induction index using Fin.cases with
  | zero => exact fun _ => fixedDetermined
  | succ index => exact laterHyp index

/-- **The closure of a count-guarded formula is decided by the counts of the members' types.** The top of each
instance is decided at the top's cap once the variables that may occur there are (first part); every instance is decided
at the closure's cap once the variables that may occur under a step forward are (second part). -/
theorem closureWith_countLocal : ∀ {n : ℕ} (now later : Fin n → Bool) (u : Fin n → Formula 0) (caps : Fin n → ℕ)
    (formula : Formula n), formula.countGuardedIn now later = true → (∀ index, now index = true → later index = true) →
    (∀ index, 1 ≤ caps index) → ∀ C : List (Formula 0), closureWith u formula ⊆ C →
      ((∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        CountDetermined C (topCap caps formula) (HFSets.sat Env.closed (formula.subst u))) ∧
      ((∀ index, later index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        ∀ φ ∈ closureWith u formula, CountDetermined C (closureCap caps formula) (HFSets.sat Env.closed φ))
  | _, _, _, u, _, .top, _, _, _, _, _ => ⟨fun _ => CountDetermined.const True, fun _ φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact CountDetermined.const True⟩
  | _, _, _, u, _, .bot, _, _, _, _, _ => ⟨fun _ => CountDetermined.const False, fun _ φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact CountDetermined.const False⟩
  | _, _, _, u, _, .empty kind, _, _, _, _, _ => ⟨fun _ => (determined_empty kind).counted le_rfl, fun _ φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact (determined_empty kind).counted le_rfl⟩
  | _, _, _, u, _, .nonEmpty kind, _, _, _, _, _ => ⟨fun _ => (determined_nonEmpty kind).counted le_rfl,
      fun _ φ found => by
        simp only [closureWith, Formula.subst, List.mem_singleton] at found
        subst found
        exact (determined_nonEmpty kind).counted le_rfl⟩
  | _, _, _, u, caps, .var index, ok, mono, positive, _, _ => ⟨fun nowHyp => nowHyp index ok, fun laterHyp φ found => by
      simp only [closureWith, Formula.subst, List.mem_singleton] at found
      subst found
      exact laterHyp index (mono index ok)⟩
  | _, _, _, u, _, .is target, _, _, _, C, within =>
    ⟨fun _ => (determined_is (names_of_nameClosure within)).counted le_rfl,
      fun _ φ found => ((nameClosure_isLocal target φ found).mono within).counted le_rfl⟩
  | _, _, _, u, _, .isNot target, _, _, _, C, within => by
    simp only [closureWith, List.cons_subset] at within
    refine ⟨fun _ => (determined_isNot (names_of_nameClosure within.2)).counted le_rfl, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact (determined_isNot (names_of_nameClosure within.2)).counted le_rfl
    · exact ((nameClosure_isLocal target φ found).mono within.2).counted le_rfl
  | _, now, later, u, caps, .and left right, ok, mono, positive, C, within => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_countLocal now later u caps left ok.1 mono positive C within.2.1
    have rightLocal := closureWith_countLocal now later u caps right ok.2 mono positive C within.2.2
    have top : (∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        CountDetermined C (topCap caps (.and left right)) (HFSets.sat Env.closed ((Formula.and left right).subst u)) :=
      fun nowHyp => ((leftLocal.1 nowHyp).mono (le_max_left _ _)).and ((rightLocal.1 nowHyp).mono (le_max_right _ _))
    refine ⟨top, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact (top fun index h => laterHyp index (mono index h)).mono (topCap_le_closureCap _)
    · exact (leftLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
    · exact (rightLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .or left right, ok, mono, positive, C, within => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_countLocal now later u caps left ok.1 mono positive C within.2.1
    have rightLocal := closureWith_countLocal now later u caps right ok.2 mono positive C within.2.2
    have top : (∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        CountDetermined C (topCap caps (.or left right)) (HFSets.sat Env.closed ((Formula.or left right).subst u)) :=
      fun nowHyp => ((leftLocal.1 nowHyp).mono (le_max_left _ _)).or ((rightLocal.1 nowHyp).mono (le_max_right _ _))
    refine ⟨top, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact (top fun index h => laterHyp index (mono index h)).mono (topCap_le_closureCap _)
    · exact (leftLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
    · exact (rightLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .split kind left right, ok, mono, positive, C, within => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_countLocal now later u caps left ok.1 mono positive C within.2.1
    have rightLocal := closureWith_countLocal now later u caps right ok.2 mono positive C within.2.2
    have one := (one_le_caps left positive).1
    have top : (∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        CountDetermined C (topCap caps (.split kind left right))
          (HFSets.sat Env.closed ((Formula.split kind left right).subst u)) :=
      fun nowHyp => countDetermined_split kind (by omega) (leftLocal.1 nowHyp) (rightLocal.1 nowHyp)
    refine ⟨top, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact (top fun index h => laterHyp index (mono index h)).mono (topCap_le_closureCap _)
    · exact (leftLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
    · exact (rightLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .everySplit kind left right, ok, mono, positive, C, within => by
    simp only [Formula.countGuardedIn, Bool.and_eq_true] at ok
    simp only [closureWith, List.cons_subset, List.append_subset] at within
    have leftLocal := closureWith_countLocal now later u caps left ok.1 mono positive C within.2.1
    have rightLocal := closureWith_countLocal now later u caps right ok.2 mono positive C within.2.2
    have one := (one_le_caps left positive).1
    have top : (∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        CountDetermined C (topCap caps (.everySplit kind left right))
          (HFSets.sat Env.closed ((Formula.everySplit kind left right).subst u)) :=
      fun nowHyp => countDetermined_everySplit kind (by omega) (leftLocal.1 nowHyp) (rightLocal.1 nowHyp)
    refine ⟨top, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons, List.mem_append] at found
    rcases found with rfl | found | found
    · exact (top fun index h => laterHyp index (mono index h)).mono (topCap_le_closureCap _)
    · exact (leftLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
    · exact (rightLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .possibly label inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal later later u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C 1 (HFSets.sat Env.closed ((Formula.possibly label inner).subst u)) :=
      (determined_possibly (within.2 (subst_mem_closureWith u inner)) label).counted le_rfl
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .necessarily label inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal later later u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C 1 (HFSets.sat Env.closed ((Formula.necessarily label inner).subst u)) :=
      (determined_necessarily (within.2 (subst_mem_closureWith u inner)) label).counted le_rfl
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .atLeast count .forward label inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal later later u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C (max 1 count)
        (HFSets.sat Env.closed ((Formula.atLeast count .forward label inner).subst u)) :=
      countDetermined_atLeast (within.2 (subst_mem_closureWith u inner)) count label (le_max_right _ _)
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .allButFewer count .forward label inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal later later u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C (max 1 count)
        (HFSets.sat Env.closed ((Formula.allButFewer count .forward label inner).subst u)) :=
      countDetermined_allButFewer (within.2 (subst_mem_closureWith u inner)) count label (le_max_right _ _)
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .single kind inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal later later u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C 2 (HFSets.sat Env.closed ((Formula.single kind inner).subst u)) :=
      countDetermined_single (within.2 (subst_mem_closureWith u inner)) kind le_rfl
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .everySingle kind inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal later later u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C 2 (HFSets.sat Env.closed ((Formula.everySingle kind inner).subst u)) :=
      countDetermined_everySingle (within.2 (subst_mem_closureWith u inner)) kind le_rfl
    refine ⟨fun _ => head, fun laterHyp φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 laterHyp φ found).mono (by simp only [closureCap]; omega)
  | _, _, _, u, caps, .sometimeBefore label inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have smallLocal : IsCountLocal (closureWith u inner) (closureCap caps inner) := fun φ found =>
      (closureWith_countLocal _ _ u caps inner ok (fun _ h => h) positive (closureWith u inner)
        (List.Subset.refl _)).2 (fun _ never => absurd never Bool.false_ne_true) φ found
    have head : CountDetermined C (closureCap caps inner)
        (HFSets.sat Env.closed ((Formula.sometimeBefore label inner).subst u)) :=
      countDetermined_sometimeBefore within.2 le_rfl smallLocal (subst_mem_closureWith u inner) label
    refine ⟨fun _ => head, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head
    · exact (smallLocal φ found).mono_closure within.2 le_rfl
  | _, _, _, u, caps, .alwaysBefore label inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have smallLocal : IsCountLocal (closureWith u inner) (closureCap caps inner) := fun φ found =>
      (closureWith_countLocal _ _ u caps inner ok (fun _ h => h) positive (closureWith u inner)
        (List.Subset.refl _)).2 (fun _ never => absurd never Bool.false_ne_true) φ found
    have head : CountDetermined C (closureCap caps inner)
        (HFSets.sat Env.closed ((Formula.alwaysBefore label inner).subst u)) :=
      countDetermined_alwaysBefore within.2 le_rfl smallLocal (subst_mem_closureWith u inner) label
    refine ⟨fun _ => head, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head
    · exact (smallLocal φ found).mono_closure within.2 le_rfl
  | _, _, _, u, caps, .someOf (.base sort) inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal _ _ u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C 1 (HFSets.sat Env.closed ((Formula.someOf (.base sort) inner).subst u)) :=
      (determined_someOf _ _).counted le_rfl
    refine ⟨fun _ => head, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 (fun _ never => absurd never Bool.false_ne_true) φ found).mono
        (by simp only [closureCap]; omega)
  | _, _, _, u, caps, .everyOf (.base sort) inner, ok, _, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have innerLocal := closureWith_countLocal _ _ u caps inner ok (fun _ h => h) positive C within.2
    have head : CountDetermined C 1 (HFSets.sat Env.closed ((Formula.everyOf (.base sort) inner).subst u)) :=
      (determined_everyOf _ _).counted le_rfl
    refine ⟨fun _ => head, fun _ φ found => ?_⟩
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact head.mono (by simp only [closureCap]; omega)
    · exact (innerLocal.2 (fun _ never => absurd never Bool.false_ne_true) φ found).mono
        (by simp only [closureCap]; omega)
  | _, now, later, u, caps, .mu inner, ok, mono, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have topLocal := closureWith_countLocal _ _ _ (Fin.cons 1 caps) inner ok (cons_masks_mono mono)
      (cons_positive positive le_rfl) C within.2
    have head : (∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        CountDetermined C (topCap caps (.mu inner)) (HFSets.sat Env.closed ((Formula.mu inner).subst u)) :=
      fun nowHyp => CountDetermined.of_iff (fun x => (sat_subst_mu inner u x).symm)
        (topLocal.1 (cons_now_counted _ nowHyp))
    refine ⟨head, fun laterHyp φ found => ?_⟩
    have fixedDetermined := head fun index h => laterHyp index (mono index h)
    have one := (one_le_caps (caps := Fin.cons 1 caps) inner (cons_positive positive le_rfl)).1
    have innerLocal := closureWith_countLocal _ _ _ (Fin.cons (topCap caps (.mu inner)) caps) inner ok
      (cons_masks_mono mono) (cons_positive positive one) C within.2
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact fixedDetermined.mono (by simp only [topCap, closureCap]; omega)
    · exact (innerLocal.2 (cons_later_counted fixedDetermined laterHyp) φ found).mono
        (by simp only [topCap, closureCap]; omega)
  | _, now, later, u, caps, .nu inner, ok, mono, positive, C, within => by
    simp only [closureWith, List.cons_subset] at within
    have topLocal := closureWith_countLocal _ _ _ (Fin.cons 1 caps) inner ok (cons_masks_mono mono)
      (cons_positive positive le_rfl) C within.2
    have head : (∀ index, now index = true → CountDetermined C (caps index) (HFSets.sat Env.closed (u index))) →
        CountDetermined C (topCap caps (.nu inner)) (HFSets.sat Env.closed ((Formula.nu inner).subst u)) :=
      fun nowHyp => CountDetermined.of_iff (fun x => (sat_subst_nu inner u x).symm)
        (topLocal.1 (cons_now_counted _ nowHyp))
    refine ⟨head, fun laterHyp φ found => ?_⟩
    have fixedDetermined := head fun index h => laterHyp index (mono index h)
    have one := (one_le_caps (caps := Fin.cons 1 caps) inner (cons_positive positive le_rfl)).1
    have innerLocal := closureWith_countLocal _ _ _ (Fin.cons (topCap caps (.nu inner)) caps) inner ok
      (cons_masks_mono mono) (cons_positive positive one) C within.2
    simp only [closureWith, List.mem_cons] at found
    rcases found with rfl | found
    · exact fixedDetermined.mono (by simp only [topCap, closureCap]; omega)
    · exact (innerLocal.2 (cons_later_counted fixedDetermined laterHyp) φ found).mono
        (by simp only [topCap, closureCap]; omega)
  | _, _, _, _, _, .atLeast _ .backward _ _, ok, _, _, _, _ | _, _, _, _, _, .allButFewer _ .backward _ _, ok, _, _, _, _
  | _, _, _, _, _, .typed _, ok, _, _, _, _ | _, _, _, _, _, .untyped _, ok, _, _, _, _
  | _, _, _, _, _, .built _ _, ok, _, _, _, _ | _, _, _, _, _, .everyBuilt _ _, ok, _, _, _, _
  | _, _, _, _, _, .body _, ok, _, _, _, _ | _, _, _, _, _, .everyBody _, ok, _, _, _, _
  | _, _, _, _, _, .multiBody _ _, ok, _, _, _, _ | _, _, _, _, _, .everyMultiBody _ _, ok, _, _, _, _
  | _, _, _, _, _, .bound _, ok, _, _, _, _ | _, _, _, _, _, .notBound _, ok, _, _, _, _
  | _, _, _, _, _, .mapsAll _ _, ok, _, _, _, _ | _, _, _, _, _, .mapsSome _ _, ok, _, _, _, _
  | _, _, _, _, _, .someOf (.collection _ _) _, ok, _, _, _, _ | _, _, _, _, _, .someOf (.arrow _ _) _, ok, _, _, _, _
  | _, _, _, _, _, .someOf (.multiBinder _) _, ok, _, _, _, _
  | _, _, _, _, _, .everyOf (.collection _ _) _, ok, _, _, _, _
  | _, _, _, _, _, .everyOf (.arrow _ _) _, ok, _, _, _, _ | _, _, _, _, _, .everyOf (.multiBinder _) _, ok, _, _, _, _
  | _, _, _, _, _, .inRelation _, ok, _, _, _, _ | _, _, _, _, _, .notInRelation _, ok, _, _, _, _ =>
    absurd ok Bool.false_ne_true

/-- **The closure of a count-guarded formula is count-local** at its closure cap. -/
theorem countGuardedClosure_isCountLocal {formula : Formula 0} (ok : formula.countGuarded = true) :
    IsCountLocal (guardedClosure formula) (closureCap Fin.elim0 formula) := fun φ found =>
  (closureWith_countLocal Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 formula ok (fun index => index.elim0)
    (fun index => index.elim0) _ (List.Subset.refl _)).2 (fun index => index.elim0) φ found

/-- **Under a step back or a sort**, where no variable occurs, the closure is count-local whatever is put back. -/
theorem closureWith_isCountLocal {n : ℕ} (u : Fin n → Formula 0) (caps : Fin n → ℕ) (positive : ∀ index, 1 ≤ caps index)
    {formula : Formula n} (ok : formula.countGuardedIn (fun _ => false) (fun _ => false) = true) :
    IsCountLocal (closureWith u formula) (closureCap caps formula) :=
  fun φ found => (closureWith_countLocal _ _ u caps formula ok (fun _ h => h) positive _ (List.Subset.refl _)).2
    (fun _ never => absurd never Bool.false_ne_true) φ found

/-! ## Steps back over count-guarded formulas -/

/-- **The stage that serves a count-guarded formula**: `2 ^ m · (c + 1)`, for the `m` entries of its closure and its
closure cap `c`. -/
def countedStage {n : ℕ} (formula : Formula n) : ℕ :=
  2 ^ closureSize formula * (closureCap (fun _ => 1) formula + 1)

theorem rich_countedStage {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.countGuardedIn (fun _ => false) (fun _ => false) = true) :
    Rich (closureWith u formula) (closureCap (fun _ => 1) formula) (countedStage formula) := by
  have loc := closureWith_isCountLocal u (fun _ => 1) (fun _ => le_rfl) ok
  have one := (one_le_caps (caps := fun _ => 1) formula (fun _ => le_rfl)).2
  exact (rich_countedBound loc one).mono (Nat.mul_le_mul_right _ (typeBound_closureWith_le u formula))

/-- **Some set containing `x` has a count-guarded formula exactly when `x` with some subset of the counted stage has
it.** -/
theorem sometimeBefore_countGuarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.countGuardedIn (fun _ => false) (fun _ => false) = true) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.sometimeBefore label (formula.subst u)) x ↔
      memberLabel label ∧ ∃ part, ∃ within : part ⊆ stage (countedStage formula),
        HFSets.sat Env.closed (formula.subst u) (insertStage x within) :=
  sometimeBefore_iff_rich (closureWith_isCountLocal u (fun _ => 1) (fun _ => le_rfl) ok) (rich_countedStage u ok)
    (subst_mem_closureWith u formula) label x

theorem alwaysBefore_countGuarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.countGuardedIn (fun _ => false) (fun _ => false) = true) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.alwaysBefore label (formula.subst u)) x ↔
      (memberLabel label → ∀ part, ∀ within : part ⊆ stage (countedStage formula),
        HFSets.sat Env.closed (formula.subst u) (insertStage x within)) :=
  alwaysBefore_iff_rich (closureWith_isCountLocal u (fun _ => 1) (fun _ => le_rfl) ok) (rich_countedStage u ok)
    (subst_mem_closureWith u formula) label x

/-- **Some set has a count-guarded formula exactly when some set of the counted stage has it.** -/
theorem someOf_countGuarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.countGuardedIn (fun _ => false) (fun _ => false) = true) (x : HF) :
    HFSets.sat Env.closed (.someOf (.base "Set") (formula.subst u)) x ↔
      ∃ y : HF, y.1 ∈ stage (countedStage formula) ∧ HFSets.sat Env.closed (formula.subst u) y :=
  someOf_iff_rich (rich_countedStage u ok) (subst_mem_closureWith u formula) x

theorem everyOf_countGuarded_iff {n : ℕ} (u : Fin n → Formula 0) {formula : Formula n}
    (ok : formula.countGuardedIn (fun _ => false) (fun _ => false) = true) (x : HF) :
    HFSets.sat Env.closed (.everyOf (.base "Set") (formula.subst u)) x ↔
      ∀ y : HF, y.1 ∈ stage (countedStage formula) → HFSets.sat Env.closed (formula.subst u) y :=
  everyOf_iff_rich (rich_countedStage u ok) (subst_mem_closureWith u formula) x

end SetReadings

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
