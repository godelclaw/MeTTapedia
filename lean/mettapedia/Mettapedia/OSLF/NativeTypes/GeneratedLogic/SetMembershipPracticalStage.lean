import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipRepresentatives
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedDecision

/-!
# The practical stage: searching representatives

The evaluation of count-guarded formulas (`evalCounted`) answers a step back or a sort by searching the subsets of
`V_k` for a stage `k` of the order of `2^n`, for a closure of `n` formulas, which is far beyond reach once `n` passes
two or three. The types it needs are few, and one representative of each serves (`SetMembershipRepresentatives`).

- **Growing the representatives** (`growReps`): from none, add each set formed of representatives whose type, read by
  evaluating the closure, no representative has, until a round adds none (`repsCheck` then holds).
- **The practical evaluation** (`evalPractical`): at a step back or a sort over a guarded body whose closure is
  count-guarded and whose grown representatives are closed, search the representatives; elsewhere evaluate as before.
  Each condition is checked as the evaluation runs.
- **It agrees with the evaluation** (`evalPractical_eq`) on every count-guarded formula at every hereditary term, so it
  is exact among the hereditarily finite sets (`evalPractical_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Growing representatives -/

/-- Add a candidate when no representative has its type. -/
def addRep (vec : Pattern → List Bool) (reps : List Pattern) (candidate : Pattern) : List Pattern :=
  if reps.any (fun r => vec r == vec candidate) then reps else reps ++ [candidate]

/-- One round: every set formed of the representatives is a candidate. -/
def growStep (vec : Pattern → List Bool) (reps : List Pattern) : List Pattern :=
  (reps.sublists.map set).foldl (addRep vec) reps

/-- Rounds until one adds no representative, within the fuel. -/
def growReps (vec : Pattern → List Bool) : ℕ → List Pattern → List Pattern
  | 0, reps => reps
  | fuel + 1, reps => if (growStep vec reps).length = reps.length then reps else growReps vec fuel (growStep vec reps)

/-- **Closed representatives, checked**: every set formed of them has the type of one of them. -/
def repsCheck (vec : Pattern → List Bool) (reps : List Pattern) : Bool :=
  reps.sublists.all fun sub => reps.any fun r => vec r == vec (set sub)

theorem addRep_hf {vec : Pattern → List Bool} {reps : List Pattern} {candidate : Pattern}
    (all : ∀ r ∈ reps, IsHF r) (holds : IsHF candidate) : ∀ r ∈ addRep vec reps candidate, IsHF r := by
  intro r member
  unfold addRep at member
  split at member
  · exact all r member
  · rcases List.mem_append.mp member with inside | fresh
    · exact all r inside
    · rw [List.mem_singleton.mp fresh]
      exact holds

theorem foldl_addRep_hf {vec : Pattern → List Bool} :
    ∀ (candidates : List Pattern) {reps : List Pattern}, (∀ r ∈ reps, IsHF r) → (∀ c ∈ candidates, IsHF c) →
      ∀ r ∈ candidates.foldl (addRep vec) reps, IsHF r
  | [], _, all, _ => all
  | candidate :: candidates, _, all, fresh => by
    simp only [List.foldl_cons]
    exact foldl_addRep_hf candidates (addRep_hf all (fresh candidate List.mem_cons_self))
      fun c member => fresh c (List.mem_cons_of_mem _ member)

theorem growStep_hf {vec : Pattern → List Bool} {reps : List Pattern} (all : ∀ r ∈ reps, IsHF r) :
    ∀ r ∈ growStep vec reps, IsHF r :=
  foldl_addRep_hf _ all fun c member => by
    obtain ⟨sub, subSub, rfl⟩ := List.mem_map.mp member
    exact set_hf fun value found => all value ((List.mem_sublists.mp subSub).subset found)

theorem growReps_hf {vec : Pattern → List Bool} :
    ∀ (fuel : ℕ) {reps : List Pattern}, (∀ r ∈ reps, IsHF r) → ∀ r ∈ growReps vec fuel reps, IsHF r
  | 0, _, all => all
  | fuel + 1, reps, all => by
    simp only [growReps]
    split
    · exact all
    · exact growReps_hf fuel (growStep_hf all)

/-! ## Types read by evaluating a closure -/

/-- The truth of each formula of a closure at a term. -/
def closureVec (closure : List (Formula 0)) (term : Pattern) : List Bool := closure.map fun ψ => evalCounted ψ term

theorem closureVec_eq_iff {closure : List (Formula 0)} (guarded : ∀ ψ ∈ closure, ψ.countGuarded = true)
    {first second : Pattern} (firstHolds : IsHF first) (secondHolds : IsHF second) :
    closureVec closure first = closureVec closure second ↔ termType closure first = termType closure second := by
  rw [termType_eq firstHolds, termType_eq secondHolds]
  constructor
  · intro same
    ext φ
    simp only [mem_typeOf]
    refine and_congr_right fun inside => ?_
    have entry : evalCounted φ first = evalCounted φ second :=
      List.map_inj_left.mp same φ inside
    rw [← evalCounted_iff (guarded φ inside) firstHolds, ← evalCounted_iff (guarded φ inside) secondHolds, entry]
  · intro same
    apply List.map_congr_left
    intro ψ inside
    have key := congrArg (ψ ∈ ·) same
    simp only [mem_typeOf, eq_iff_iff] at key
    apply Bool.eq_iff_iff.mpr
    rw [evalCounted_iff (guarded ψ inside) firstHolds, evalCounted_iff (guarded ψ inside) secondHolds]
    exact ⟨fun holds => (key.mp ⟨inside, holds⟩).2, fun holds => (key.mpr ⟨inside, holds⟩).2⟩

/-- **Checked representatives are closed**, when the closure's formulas are count-guarded. -/
theorem repsClosed_of_check {closure : List (Formula 0)} (guarded : ∀ ψ ∈ closure, ψ.countGuarded = true)
    {reps : List Pattern} (all : ∀ r ∈ reps, IsHF r) (checked : repsCheck (closureVec closure) reps = true) :
    RepsClosed closure reps where
  hf := all
  sets sub subSub := by
    simp only [repsCheck, List.all_eq_true, List.any_eq_true, beq_iff_eq] at checked
    obtain ⟨r, inside, same⟩ := checked sub subSub
    have subHolds : IsHF (set sub) :=
      set_hf fun value found => all value ((List.mem_sublists.mp subSub).subset found)
    exact ⟨r, inside, (closureVec_eq_iff guarded (all r inside) subHolds).mp same⟩

/-! ## The practical evaluation -/

/-- The representatives grown for a body, read by its guarded closure. -/
def bodyReps (inner : Formula 0) : List Pattern :=
  growReps (closureVec (guardedClosure inner)) (2 ^ (guardedClosure inner).length + 1) []

/-- **Whether a body's representatives serve**: the body is guarded, its closure is count-guarded, and its grown
representatives are closed. -/
def practicalOK (inner : Formula 0) : Bool :=
  inner.guardedIn (fun _ => false) (fun _ => false) && (guardedClosure inner).all Formula.countGuarded &&
    repsCheck (closureVec (guardedClosure inner)) (bodyReps inner)

/-- **The practical evaluation**, over a closed formula: a step back or a sort searches the representatives of its body
where they serve; everything else is evaluated as before. It is stated over every scope, like the evaluation, so that
it recurses structurally. -/
def evalPracticalWith : {n : ℕ} → (Fin n → Pattern → Bool) → Formula n → Pattern → Bool
  | 0, read, .and left right, term => evalPracticalWith read left term && evalPracticalWith read right term
  | 0, read, .or left right, term => evalPracticalWith read left term || evalPracticalWith read right term
  | 0, read, .possibly label inner, term =>
    decide (memberLabel label) && (membersOf term).any (evalPracticalWith read inner)
  | 0, read, .necessarily label inner, term =>
    !decide (memberLabel label) || (membersOf term).all (evalPracticalWith read inner)
  | 0, read, .sometimeBefore label inner, term =>
    if practicalOK inner then
      decide (memberLabel label) &&
        (bodyReps inner).sublists.any fun sub => evalPracticalWith read inner (set (term :: sub))
    else evalCountedWith read (.sometimeBefore label inner) term
  | 0, read, .alwaysBefore label inner, term =>
    if practicalOK inner then
      !decide (memberLabel label) ||
        (bodyReps inner).sublists.all fun sub => evalPracticalWith read inner (set (term :: sub))
    else evalCountedWith read (.alwaysBefore label inner) term
  | 0, read, .someOf (.base sort) inner, term =>
    if practicalOK inner then decide (sort = "Set") && (bodyReps inner).any (evalPracticalWith read inner)
    else evalCountedWith read (.someOf (.base sort) inner) term
  | 0, read, .everyOf (.base sort) inner, term =>
    if practicalOK inner then !decide (sort = "Set") || (bodyReps inner).all (evalPracticalWith read inner)
    else evalCountedWith read (.everyOf (.base sort) inner) term
  | _, read, formula, term => evalCountedWith read formula term

/-- **The practical evaluation** of a closed formula. -/
def evalPractical (formula : Formula 0) (term : Pattern) : Bool := evalPracticalWith Fin.elim0 formula term

/-! ## The practical evaluation agrees -/

theorem elim0_false : (fun _ : Fin 0 => false) = (Fin.elim0 : Fin 0 → Bool) := funext fun index => index.elim0

theorem any_congr_of_mem {α : Type} : ∀ {l : List α} {p q : α → Bool}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
  | [], _, _, _ => rfl
  | a :: _, _, _, agree => by
    rw [List.any_cons, List.any_cons, agree a List.mem_cons_self,
      any_congr_of_mem fun b member => agree b (List.mem_cons_of_mem a member)]

theorem all_congr_of_mem {α : Type} : ∀ {l : List α} {p q : α → Bool}, (∀ a ∈ l, p a = q a) → l.all p = l.all q
  | [], _, _, _ => rfl
  | a :: _, _, _, agree => by
    rw [List.all_cons, List.all_cons, agree a List.mem_cons_self,
      all_congr_of_mem fun b member => agree b (List.mem_cons_of_mem a member)]

/-- The facts a serving body gives: its closure is local and count-guarded, and its representatives are closed. -/
theorem practicalOK_parts {inner : Formula 0} (ok : practicalOK inner = true) :
    IsLocal (guardedClosure inner) ∧ (∀ ψ ∈ guardedClosure inner, ψ.countGuarded = true) ∧
      RepsClosed (guardedClosure inner) (bodyReps inner) := by
  simp only [practicalOK, Bool.and_eq_true, List.all_eq_true] at ok
  obtain ⟨⟨guarded, closureGuarded⟩, checked⟩ := ok
  exact ⟨closureWith_isLocal Fin.elim0 guarded, closureGuarded,
    repsClosed_of_check closureGuarded (growReps_hf _ fun _ member => nomatch member) checked⟩

theorem body_mem (inner : Formula 0) : inner.subst (Fin.elim0 : Fin 0 → Formula 0) ∈ guardedClosure inner :=
  subst_mem_closureWith Fin.elim0 inner

theorem container_hf {inner : Formula 0} (closed : RepsClosed (guardedClosure inner) (bodyReps inner)) {term : Pattern}
    (holds : IsHF term) {sub : List Pattern} (subSub : sub ∈ (bodyReps inner).sublists) : IsHF (set (term :: sub)) :=
  set_hf fun value found => by
    rcases List.mem_cons.mp found with rfl | found
    · exact holds
    · exact closed.hf value ((List.mem_sublists.mp subSub).subset found)

/-- **The practical evaluation is the evaluation**, on every count-guarded formula at every hereditary term. -/
theorem evalPracticalWith_eq : ∀ (formula : Formula 0), formula.countGuarded = true → ∀ {term : Pattern}, IsHF term →
    evalPracticalWith Fin.elim0 formula term = evalCounted formula term
  | .and left right, ok, term, holds => by
    simp only [Formula.countGuarded, Formula.countGuardedIn, Bool.and_eq_true] at ok
    rw [evalPracticalWith, evalPracticalWith_eq left ok.1 holds, evalPracticalWith_eq right ok.2 holds]
    rfl
  | .or left right, ok, term, holds => by
    simp only [Formula.countGuarded, Formula.countGuardedIn, Bool.and_eq_true] at ok
    rw [evalPracticalWith, evalPracticalWith_eq left ok.1 holds, evalPracticalWith_eq right ok.2 holds]
    rfl
  | .possibly label inner, ok, term, holds => by
    have innerOk : inner.countGuarded = true := ok
    rw [evalPracticalWith, any_congr_of_mem fun value member => evalPracticalWith_eq inner innerOk (hf_members holds value member)]
    rfl
  | .necessarily label inner, ok, term, holds => by
    have innerOk : inner.countGuarded = true := ok
    rw [evalPracticalWith, all_congr_of_mem fun value member => evalPracticalWith_eq inner innerOk (hf_members holds value member)]
    rfl
  | .sometimeBefore label inner, ok, term, holds => by
    have innerOk : inner.countGuarded = true := by
      have : inner.countGuardedIn (fun _ => false) (fun _ => false) = true := ok
      rwa [elim0_false] at this
    rw [evalPracticalWith]
    split
    · rename_i serving
      obtain ⟨loc, closureGuarded, closed⟩ := practicalOK_parts serving
      rw [any_congr_of_mem fun sub subSub => evalPracticalWith_eq inner innerOk (container_hf closed holds subSub)]
      apply Bool.eq_iff_iff.mpr
      rw [evalCounted_iff ok holds, ← sat_subst_elim0]
      show _ ↔ HFSets.sat Env.closed (.sometimeBefore label (inner.subst Fin.elim0)) (hfOf holds)
      rw [sometimeBefore_iff_reps loc closed (body_mem inner) label holds]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
      refine and_congr_right fun _ => ⟨fun ⟨sub, subSub, eval⟩ => ?_, fun ⟨sub, subSub, containerHolds, sat⟩ => ?_⟩
      · have containerHolds := container_hf closed holds subSub
        exact ⟨sub, subSub, containerHolds,
          (sat_subst_elim0 _ _).mpr ((evalCounted_iff innerOk containerHolds).mp eval)⟩
      · exact ⟨sub, subSub, (evalCounted_iff innerOk containerHolds).mpr ((sat_subst_elim0 _ _).mp sat)⟩
    · rfl
  | .alwaysBefore label inner, ok, term, holds => by
    have innerOk : inner.countGuarded = true := by
      have : inner.countGuardedIn (fun _ => false) (fun _ => false) = true := ok
      rwa [elim0_false] at this
    rw [evalPracticalWith]
    split
    · rename_i serving
      obtain ⟨loc, closureGuarded, closed⟩ := practicalOK_parts serving
      rw [all_congr_of_mem fun sub subSub => evalPracticalWith_eq inner innerOk (container_hf closed holds subSub)]
      apply Bool.eq_iff_iff.mpr
      rw [evalCounted_iff ok holds, ← sat_subst_elim0]
      show _ ↔ HFSets.sat Env.closed (.alwaysBefore label (inner.subst Fin.elim0)) (hfOf holds)
      rw [alwaysBefore_iff_reps loc closed (body_mem inner) label holds]
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
      constructor
      · rintro (unlabelled | every) labelled sub subSub containerHolds
        · exact absurd labelled unlabelled
        · exact (sat_subst_elim0 _ _).mpr ((evalCounted_iff innerOk containerHolds).mp (every sub subSub))
      · intro every
        by_cases labelled : memberLabel label
        · exact .inr fun sub subSub => (evalCounted_iff innerOk (container_hf closed holds subSub)).mpr
            ((sat_subst_elim0 _ _).mp (every labelled sub subSub (container_hf closed holds subSub)))
        · exact .inl labelled
    · rfl
  | .someOf (.base sort) inner, ok, term, holds => by
    have innerOk : inner.countGuarded = true := by
      have : inner.countGuardedIn (fun _ => false) (fun _ => false) = true := ok
      rwa [elim0_false] at this
    rw [evalPracticalWith]
    split
    · rename_i serving
      obtain ⟨loc, closureGuarded, closed⟩ := practicalOK_parts serving
      rw [any_congr_of_mem fun r rIn => evalPracticalWith_eq inner innerOk (closed.hf r rIn)]
      by_cases isSet : sort = "Set"
      · subst isSet
        apply Bool.eq_iff_iff.mpr
        rw [evalCounted_iff ok holds, ← sat_subst_elim0]
        show _ ↔ HFSets.sat Env.closed (.someOf (.base "Set") (inner.subst Fin.elim0)) (hfOf holds)
        rw [someOf_iff_reps loc closed (body_mem inner) (hfOf holds)]
        simp only [decide_true, Bool.true_and, List.any_eq_true]
        exact ⟨fun ⟨r, rIn, eval⟩ => ⟨r, rIn, (sat_subst_elim0 _ _).mpr ((evalCounted_iff innerOk _).mp eval)⟩,
          fun ⟨r, rIn, sat⟩ => ⟨r, rIn, (evalCounted_iff innerOk _).mpr ((sat_subst_elim0 _ _).mp sat)⟩⟩
      · simp [evalCounted, evalCountedWith, isSet]
    · rfl
  | .everyOf (.base sort) inner, ok, term, holds => by
    have innerOk : inner.countGuarded = true := by
      have : inner.countGuardedIn (fun _ => false) (fun _ => false) = true := ok
      rwa [elim0_false] at this
    rw [evalPracticalWith]
    split
    · rename_i serving
      obtain ⟨loc, closureGuarded, closed⟩ := practicalOK_parts serving
      rw [all_congr_of_mem fun r rIn => evalPracticalWith_eq inner innerOk (closed.hf r rIn)]
      by_cases isSet : sort = "Set"
      · subst isSet
        apply Bool.eq_iff_iff.mpr
        rw [evalCounted_iff ok holds, ← sat_subst_elim0]
        show _ ↔ HFSets.sat Env.closed (.everyOf (.base "Set") (inner.subst Fin.elim0)) (hfOf holds)
        rw [everyOf_iff_reps loc closed (body_mem inner) (hfOf holds)]
        simp only [decide_true, Bool.not_true, Bool.false_or, List.all_eq_true]
        exact ⟨fun every r rIn => (sat_subst_elim0 _ _).mpr ((evalCounted_iff innerOk _).mp (every r rIn)),
          fun every r rIn => (evalCounted_iff innerOk _).mpr ((sat_subst_elim0 _ _).mp (every r rIn))⟩
      · simp [evalCounted, evalCountedWith, isSet]
    · rfl
  | .top, _, _, _ | .bot, _, _, _ | .empty _, _, _, _ | .nonEmpty _, _, _, _ | .is _, _, _, _ | .isNot _, _, _, _
  | .atLeast _ _ _ _, _, _, _ | .allButFewer _ _ _ _, _, _, _ | .single _ _, _, _, _ | .everySingle _ _, _, _, _
  | .split _ _ _, _, _, _ | .everySplit _ _ _, _, _, _ | .mu _, _, _, _ | .nu _, _, _, _
  | .someOf (.arrow _ _) _, _, _, _ | .someOf (.collection _ _) _, _, _, _ | .someOf (.multiBinder _) _, _, _, _
  | .everyOf (.arrow _ _) _, _, _, _ | .everyOf (.collection _ _) _, _, _, _ | .everyOf (.multiBinder _) _, _, _, _
  | .built _ _, _, _, _ | .everyBuilt _ _, _, _, _ | .body _, _, _, _ | .everyBody _, _, _, _
  | .multiBody _ _, _, _, _ | .everyMultiBody _ _, _, _, _ | .bound _, _, _, _ | .notBound _, _, _, _
  | .typed _, _, _, _ | .untyped _, _, _, _ | .mapsAll _ _, _, _, _ | .mapsSome _ _, _, _, _
  | .inRelation _, _, _, _ | .notInRelation _, _, _, _ => rfl

theorem evalPractical_eq (formula : Formula 0) (ok : formula.countGuarded = true) {term : Pattern} (holds : IsHF term) :
    evalPractical formula term = evalCounted formula term :=
  evalPracticalWith_eq formula ok holds

/-- **The practical evaluation is exact** among the hereditarily finite sets, on count-guarded formulas. -/
theorem evalPractical_iff {formula : Formula 0} (ok : formula.countGuarded = true) {term : Pattern} (holds : IsHF term) :
    evalPractical formula term = true ↔ HFSets.sat Env.closed formula (hfOf holds) := by
  rw [evalPractical_eq formula ok holds]
  exact evalCounted_iff ok holds

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
