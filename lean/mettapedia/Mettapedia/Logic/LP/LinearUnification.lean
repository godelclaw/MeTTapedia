import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.Logic.LP.Narrowing

/-!
# Unifying linear terms

A term is linear when no variable occurs in it twice (`Term.Linear`, decided by
`Term.linearCheck`).

- Substituting into a linear term keeps it linear when the images of its variables are linear and
  pairwise share no variable (`Term.Linear.applyTerm`).
- Filling a context of a linear term with a linear term that shares no variable with the context
  keeps it linear (`Term.Linear.fill`).
- Equations whose sides are linear and pairwise share no variable (`LinearEquations`) unify by
  overlaying their sides: the most general unifier sends the variables of the left sides to linear
  terms, pairwise without a shared variable (`unifyTotal_overlay`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP

open Mettapedia.Logic.LP.FirstOrderRewriting (Context)
open Mettapedia.Logic.LP.Narrowing (outsideVars)

variable {σ : LPSignature} [DecidableEq σ.vars]

/-! ## Linear terms -/

/-- **No variable occurs twice.** -/
def Term.Linear : Term σ → Prop
  | .var _ => True
  | .const _ => True
  | .app _ arguments => (∀ i, (arguments i).Linear) ∧
      ∀ i j, i ≠ j → Disjoint (arguments i).freeVars (arguments j).freeVars

/-- Linearity, decided. -/
def Term.linearCheck : Term σ → Bool
  | .var _ => true
  | .const _ => true
  | .app _ arguments => (List.finRange _).all (fun i => (arguments i).linearCheck) &&
      (List.finRange _).all fun i => (List.finRange _).all fun j =>
        decide (i = j) || decide (Disjoint (arguments i).freeVars (arguments j).freeVars)

theorem Term.linearCheck_iff : ∀ term : Term σ, term.linearCheck = true ↔ term.Linear
  | .var _ => by simp [Term.linearCheck, Term.Linear]
  | .const _ => by simp [Term.linearCheck, Term.Linear]
  | .app _ arguments => by
    simp only [Term.linearCheck, Term.Linear, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, Bool.or_eq_true, decide_eq_true_eq]
    exact and_congr (forall_congr' fun i => Term.linearCheck_iff (arguments i))
      (forall₂_congr fun _ _ => or_iff_not_imp_left)

theorem Term.linear_of_freeVars_empty : ∀ {term : Term σ}, term.freeVars = ∅ → term.Linear
  | .var _, empty => by simp [Term.freeVars] at empty
  | .const _, _ => trivial
  | .app _ arguments, empty => by
    have each : ∀ i, (arguments i).freeVars = ∅ := fun i => Finset.eq_empty_of_forall_notMem fun v member => by
      have inside := Term.mem_freeVars_app.mpr ⟨i, member⟩
      rw [empty] at inside
      exact Finset.notMem_empty v inside
    exact ⟨fun i => Term.linear_of_freeVars_empty (each i), fun i _ _ => by
      rw [each i]
      exact Finset.disjoint_empty_left _⟩

/-- **A substitution instance of a linear term is linear** when the images of its variables are
linear and pairwise share no variable. -/
theorem Term.Linear.applyTerm (θ : Subst σ) : ∀ (term : Term σ), term.Linear →
    (∀ v ∈ term.freeVars, (θ v).Linear) →
    (∀ v ∈ term.freeVars, ∀ w ∈ term.freeVars, v ≠ w → Disjoint (θ v).freeVars (θ w).freeVars) →
    (θ.applyTerm term).Linear
  | .var v, _, images, _ => images v (by simp [Term.freeVars])
  | .const _, _, _, _ => trivial
  | .app f arguments, ⟨each, apart⟩, images, disjoint => by
    have inside : ∀ i, ∀ v ∈ (arguments i).freeVars, v ∈ (Term.app f arguments).freeVars :=
      fun i v member => Term.mem_freeVars_app.mpr ⟨i, member⟩
    rw [Subst.applyTerm_app]
    refine ⟨fun i => Term.Linear.applyTerm θ (arguments i) (each i) (fun v member => images v (inside i v member))
      (fun v vMember w wMember => disjoint v (inside i v vMember) w (inside i w wMember)), fun i j different => ?_⟩
    rw [Finset.disjoint_left]
    intro x left right
    obtain ⟨v, vMember, xv⟩ := Subst.mem_freeVars_applyTerm.mp left
    obtain ⟨w, wMember, xw⟩ := Subst.mem_freeVars_applyTerm.mp right
    have vw : v ≠ w := fun same => Finset.disjoint_left.mp (apart i j different) vMember (same ▸ wMember)
    exact Finset.disjoint_left.mp (disjoint v (inside i v vMember) w (inside j w wMember) vw) xv xw

/-! ## Contexts of linear terms -/

theorem freeVars_fill_subset (context : Context σ) (hole : Term σ) :
    (context.fill hole).freeVars ⊆ hole.freeVars ∪ outsideVars context := by
  induction context with
  | hole => simp [Context.fill]
  | app f arguments position inner ih =>
    intro v member
    simp only [Context.fill] at member
    obtain ⟨i, occurs⟩ := Term.mem_freeVars_app.mp member
    simp only [outsideVars, Finset.mem_union]
    by_cases here : i = position
    · subst here
      rw [Function.update_self] at occurs
      rcases Finset.mem_union.mp (ih occurs) with inHole | outside
      · exact Or.inl inHole
      · exact Or.inr (Or.inr outside)
    · rw [Function.update_of_ne here] at occurs
      exact Or.inr (Or.inl (Finset.mem_biUnion.mpr ⟨i, by simpa using here, occurs⟩))

/-- In a linear term, the hole is linear and shares no variable with its context. -/
theorem Term.Linear.of_fill : ∀ (context : Context σ) {hole : Term σ}, (context.fill hole).Linear →
    hole.Linear ∧ Disjoint hole.freeVars (outsideVars context)
  | .hole, _, linear => ⟨linear, by simp [outsideVars]⟩
  | .app _ arguments position inner, hole, ⟨each, apart⟩ => by
    have atPosition := each position
    simp only [Function.update_self] at atPosition
    obtain ⟨holeLinear, holeApart⟩ := Term.Linear.of_fill inner atPosition
    refine ⟨holeLinear, ?_⟩
    simp only [outsideVars]
    refine Finset.disjoint_union_right.mpr ⟨(Finset.disjoint_biUnion_right _ _ _).mpr fun i kept => ?_, holeApart⟩
    have different : i ≠ position := by simpa using kept
    have apartHere := apart position i (Ne.symm different)
    simp only [Function.update_self, Function.update_of_ne different] at apartHere
    exact apartHere.mono_left (Narrowing.freeVars_hole_subset inner hole)

/-- **Refilling keeps a term linear**: a linear term sharing no variable with the context. -/
theorem Term.Linear.fill : ∀ (context : Context σ) {hole other : Term σ}, (context.fill hole).Linear →
    other.Linear → Disjoint other.freeVars (outsideVars context) → (context.fill other).Linear
  | .hole, _, _, _, otherLinear, _ => otherLinear
  | .app _ arguments position inner, hole, other, ⟨each, apart⟩, otherLinear, otherApart => by
    simp only [outsideVars, Finset.disjoint_union_right, Finset.disjoint_biUnion_right] at otherApart
    obtain ⟨otherArguments, otherInner⟩ := otherApart
    have innerLinear : (inner.fill hole).Linear := by simpa using each position
    have filled := Term.Linear.fill inner innerLinear otherLinear otherInner
    have filledApart : ∀ j, j ≠ position → Disjoint (inner.fill other).freeVars (arguments j).freeVars := by
      intro j different
      have before := apart position j (Ne.symm different)
      simp only [Function.update_self, Function.update_of_ne different] at before
      rw [Finset.disjoint_left]
      intro v inFilled inArgument
      rcases Finset.mem_union.mp (freeVars_fill_subset inner other inFilled) with inOther | outside
      · exact Finset.disjoint_left.mp (otherArguments j (by simpa using different)) inOther inArgument
      · exact Finset.disjoint_left.mp before (Narrowing.outsideVars_subset_fill inner hole outside) inArgument
    refine ⟨fun i => ?_, fun i j different => ?_⟩
    · by_cases here : i = position
      · subst here
        simpa using filled
      · simpa [Function.update_of_ne here] using each i
    · by_cases first : i = position
      · subst first
        simpa [Function.update_of_ne (Ne.symm different)] using filledApart j (Ne.symm different)
      · by_cases second : j = position
        · subst second
          simpa [Function.update_of_ne first] using (filledApart i first).symm
        · simpa [Function.update_of_ne first, Function.update_of_ne second] using apart i j different

/-- A variable at a position of a linear term occurs nowhere else. -/
theorem Term.Linear.not_mem_outside {context : Context σ} {v : σ.vars}
    (linear : (context.fill (.var v)).Linear) : v ∉ outsideVars context :=
  fun outside => Finset.disjoint_left.mp (Term.Linear.of_fill context linear).2 (by simp [Term.freeVars]) outside

/-! ## Unifying linear equations -/

/-- The variables of an equation. -/
def pairVars (equation : Term σ × Term σ) : Finset σ.vars := equation.1.freeVars ∪ equation.2.freeVars

/-- **Linear equations**: every side is linear, and no variable occurs in two sides. -/
def LinearEquations (equations : List (Term σ × Term σ)) : Prop :=
  (∀ equation ∈ equations, equation.1.Linear ∧ equation.2.Linear ∧
      Disjoint equation.1.freeVars equation.2.freeVars) ∧
    equations.Pairwise fun first second => Disjoint (pairVars first) (pairVars second)

/-- A variable of a left side. -/
def LeftVar (equations : List (Term σ × Term σ)) (v : σ.vars) : Prop :=
  ∃ equation ∈ equations, v ∈ equation.1.freeVars

/-- **An overlay**: the variables of the left sides go to linear terms, pairwise without a shared
variable. -/
def Overlay (θ : Subst σ) (equations : List (Term σ × Term σ)) : Prop :=
  ∀ v, LeftVar equations v → (θ v).Linear ∧
    ∀ w, LeftVar equations w → v ≠ w → Disjoint (θ v).freeVars (θ w).freeVars

theorem LinearEquations.head {left right : Term σ} {rest : List (Term σ × Term σ)}
    (linear : LinearEquations ((left, right) :: rest)) :
    left.Linear ∧ right.Linear ∧ Disjoint left.freeVars right.freeVars ∧
      Disjoint (left.freeVars ∪ right.freeVars) (eqVars rest) ∧ LinearEquations rest := by
  obtain ⟨each, pairwise⟩ := linear
  obtain ⟨leftLinear, rightLinear, apart⟩ := each (left, right) List.mem_cons_self
  rw [List.pairwise_cons] at pairwise
  refine ⟨leftLinear, rightLinear, apart, ?_, fun equation member => each equation (List.mem_cons_of_mem _ member),
    pairwise.2⟩
  rw [Finset.disjoint_right]
  intro v inRest inHead
  obtain ⟨equation, member, occurs⟩ := mem_eqVars.mp inRest
  exact Finset.disjoint_left.mp (pairwise.1 equation member) inHead (Finset.mem_union.mpr occurs)

theorem leftVar_cons {left right : Term σ} {rest : List (Term σ × Term σ)} {v : σ.vars} :
    LeftVar ((left, right) :: rest) v ↔ v ∈ left.freeVars ∨ LeftVar rest v := by
  simp [LeftVar]

theorem leftVar_mem {equations : List (Term σ × Term σ)} {v : σ.vars} (left : LeftVar equations v) :
    v ∈ eqVars equations := by
  obtain ⟨equation, member, occurs⟩ := left
  exact mem_eqVars.mpr ⟨equation, member, .inl occurs⟩

theorem applyEqs_single_absent {v : σ.vars} {term : Term σ} :
    ∀ {rest : List (Term σ × Term σ)}, v ∉ eqVars rest → (Subst.single v term).applyEqs rest = rest
  | [], _ => rfl
  | (first, second) :: rest, absent => by
    have fixes : ∀ side : Term σ, v ∉ side.freeVars → (Subst.single v term).applyTerm side = side :=
      fun side outside => Subst.applyTerm_eq_self fun u inside =>
        Subst.single_ne _ fun same => outside (same ▸ inside)
    simp only [eqVars, Finset.mem_union, not_or] at absent
    change ((Subst.single v term).applyTerm first, (Subst.single v term).applyTerm second) ::
      (Subst.single v term).applyEqs rest = _
    rw [fixes first absent.1.1, fixes second absent.1.2, applyEqs_single_absent absent.2]

theorem comp_single_ne (μ : Subst σ) {v x : σ.vars} (term : Term σ) (different : x ≠ v) :
    (μ ∘ₛ Subst.single v term) x = μ x := by
  show μ.applyTerm (Subst.single v term x) = μ x
  rw [Subst.single_ne _ different]
  rfl

theorem comp_single_eq (μ : Subst σ) (v : σ.vars) (term : Term σ) :
    (μ ∘ₛ Subst.single v term) v = μ.applyTerm term := by
  show μ.applyTerm (Subst.single v term v) = _
  rw [Subst.single_eq]

/-- Binding a left variable to a right side keeps an overlay. -/
theorem Overlay.bindLeft {μ : Subst σ} {v : σ.vars} {term : Term σ} {rest : List (Term σ × Term σ)}
    (linear : LinearEquations ((.var v, term) :: rest)) (child : Overlay μ rest)
    (relevant : μ.RelevantIdempotent (eqVars rest)) :
    Overlay (μ ∘ₛ Subst.single v term) ((.var v, term) :: rest) := by
  obtain ⟨_, termLinear, _, headApart, _⟩ := linear.head
  have vAbsent : v ∉ eqVars rest :=
    Finset.disjoint_left.mp headApart (Finset.mem_union_left _ (by simp [Term.freeVars]))
  have termAbsent : ∀ u ∈ term.freeVars, u ∉ eqVars rest :=
    fun u inside => Finset.disjoint_left.mp headApart (Finset.mem_union_right _ inside)
  have atV : (μ ∘ₛ Subst.single v term) v = term := by
    rw [comp_single_eq]
    exact Subst.applyTerm_eq_self fun u inside => relevant.fixes u (termAbsent u inside)
  have elsewhere : ∀ x, LeftVar rest x → (μ ∘ₛ Subst.single v term) x = μ x := fun x left =>
    comp_single_ne μ term fun same => vAbsent (same ▸ leftVar_mem left)
  have apartFromTerm : ∀ x, LeftVar rest x → Disjoint term.freeVars (μ x).freeVars := fun x left =>
    Finset.disjoint_left.mpr fun u inTerm inImage =>
      termAbsent u inTerm (relevant.range x (leftVar_mem left) inImage)
  intro x left
  rcases leftVar_cons.mp left with isV | inRest
  · obtain rfl : x = v := by simpa [Term.freeVars] using isV
    rw [atV]
    refine ⟨termLinear, fun w wLeft different => ?_⟩
    rcases leftVar_cons.mp wLeft with wIsV | wRest
    · exact absurd (by simpa [Term.freeVars] using wIsV : w = x).symm different
    · rw [elsewhere w wRest]
      exact apartFromTerm w wRest
  · rw [elsewhere x inRest]
    refine ⟨(child x inRest).1, fun w wLeft different => ?_⟩
    rcases leftVar_cons.mp wLeft with wIsV | wRest
    · obtain rfl : w = v := by simpa [Term.freeVars] using wIsV
      rw [atV]
      exact (apartFromTerm x inRest).symm
    · rw [elsewhere w wRest]
      exact (child x inRest).2 w wRest different

/-- Binding a right variable to a left side keeps an overlay. -/
theorem Overlay.bindRight {μ : Subst σ} {v : σ.vars} {term : Term σ} {rest : List (Term σ × Term σ)}
    (linear : LinearEquations ((term, .var v) :: rest)) (child : Overlay μ rest)
    (relevant : μ.RelevantIdempotent (eqVars rest)) :
    Overlay (μ ∘ₛ Subst.single v term) ((term, .var v) :: rest) := by
  obtain ⟨_, _, headSides, headApart, _⟩ := linear.head
  have vAbsent : v ∉ eqVars rest :=
    Finset.disjoint_left.mp headApart (Finset.mem_union_right _ (by simp [Term.freeVars]))
  have termAbsent : ∀ u ∈ term.freeVars, u ∉ eqVars rest :=
    fun u inside => Finset.disjoint_left.mp headApart (Finset.mem_union_left _ inside)
  have inTerm : ∀ x ∈ term.freeVars, (μ ∘ₛ Subst.single v term) x = .var x := fun x inside => by
    rw [comp_single_ne μ term fun same => Finset.disjoint_left.mp headSides inside (by simp [Term.freeVars, same])]
    exact relevant.fixes x (termAbsent x inside)
  have elsewhere : ∀ x, LeftVar rest x → (μ ∘ₛ Subst.single v term) x = μ x := fun x left =>
    comp_single_ne μ term fun same => vAbsent (same ▸ leftVar_mem left)
  have apartFromTerm : ∀ x ∈ term.freeVars, ∀ y, LeftVar rest y → Disjoint (Term.var x : Term σ).freeVars (μ y).freeVars :=
    fun x inside y left => Finset.disjoint_left.mpr fun u isX inImage => by
      simp only [Term.freeVars, Finset.mem_singleton] at isX
      subst isX
      exact termAbsent u inside (relevant.range y (leftVar_mem left) inImage)
  intro x left
  rcases leftVar_cons.mp left with xTerm | xRest
  · rw [inTerm x xTerm]
    refine ⟨trivial, fun w wLeft different => ?_⟩
    rcases leftVar_cons.mp wLeft with wTerm | wRest
    · rw [inTerm w wTerm]
      simpa [Term.freeVars] using different
    · rw [elsewhere w wRest]
      exact apartFromTerm x xTerm w wRest
  · rw [elsewhere x xRest]
    refine ⟨(child x xRest).1, fun w wLeft different => ?_⟩
    rcases leftVar_cons.mp wLeft with wTerm | wRest
    · rw [inTerm w wTerm]
      exact (apartFromTerm w wTerm x xRest).symm
    · rw [elsewhere w wRest]
      exact (child x xRest).2 w wRest different

theorem Overlay.dropGround {θ : Subst σ} {left right : Term σ} {rest : List (Term σ × Term σ)}
    (ground : left.freeVars = ∅) (child : Overlay θ rest) : Overlay θ ((left, right) :: rest) := by
  have only : ∀ x, LeftVar ((left, right) :: rest) x → LeftVar rest x := fun x inside =>
    (leftVar_cons.mp inside).resolve_left fun member => by simp [ground] at member
  exact fun x inside => ⟨(child x (only x inside)).1,
    fun w wInside different => (child x (only x inside)).2 w (only w wInside) different⟩

/-- Decomposing an application keeps linear equations and their left variables. -/
theorem LinearEquations.decompose {f : σ.functionSymbols} {ts us : Fin (σ.functionArity f) → Term σ}
    {rest : List (Term σ × Term σ)} (linear : LinearEquations ((.app f ts, .app f us) :: rest)) :
    LinearEquations (finPairsToList ts us ++ rest) := by
  obtain ⟨⟨tsEach, tsApart⟩, ⟨usEach, usApart⟩, headSides, headApart, restLinear⟩ := linear.head
  have tsInside : ∀ i, (ts i).freeVars ⊆ (Term.app f ts).freeVars := fun i _ member =>
    Term.mem_freeVars_app.mpr ⟨i, member⟩
  have usInside : ∀ i, (us i).freeVars ⊆ (Term.app f us).freeVars := fun i _ member =>
    Term.mem_freeVars_app.mpr ⟨i, member⟩
  have pairInside : ∀ i, pairVars (ts i, us i) ⊆ (Term.app f ts).freeVars ∪ (Term.app f us).freeVars :=
    fun i => Finset.union_subset_union (tsInside i) (usInside i)
  refine ⟨fun equation member => ?_, ?_⟩
  · rcases List.mem_append.mp member with inPairs | inRest
    · simp only [finPairsToList, List.mem_map, List.mem_finRange, true_and] at inPairs
      obtain ⟨i, rfl⟩ := inPairs
      exact ⟨tsEach i, usEach i, (headSides.mono_left (tsInside i)).mono_right (usInside i)⟩
    · exact restLinear.1 equation inRest
  · refine List.pairwise_append.mpr ⟨?_, restLinear.2, fun first firstMember second secondMember => ?_⟩
    · unfold finPairsToList
      refine List.pairwise_map.mpr ((List.nodup_finRange _).pairwise_of_forall_ne fun i _ j _ different => ?_)
      simp only [pairVars, Finset.disjoint_union_left, Finset.disjoint_union_right]
      exact ⟨⟨tsApart i j different, (headSides.symm.mono_left (usInside i)).mono_right (tsInside j)⟩,
        ⟨(headSides.mono_left (tsInside i)).mono_right (usInside j), usApart i j different⟩⟩
    · simp only [finPairsToList, List.mem_map, List.mem_finRange, true_and] at firstMember
      obtain ⟨i, rfl⟩ := firstMember
      refine (headApart.mono_left (pairInside i)).mono_right fun v inside => ?_
      exact mem_eqVars.mpr ⟨second, secondMember, Finset.mem_union.mp inside⟩

theorem leftVar_decompose {f : σ.functionSymbols} {ts us : Fin (σ.functionArity f) → Term σ}
    {rest : List (Term σ × Term σ)} {v : σ.vars} :
    LeftVar (finPairsToList ts us ++ rest) v ↔ LeftVar ((.app f ts, .app f us) :: rest) v := by
  rw [leftVar_cons, Term.mem_freeVars_app]
  constructor
  · rintro ⟨equation, member, occurs⟩
    rcases List.mem_append.mp member with inPairs | inRest
    · simp only [finPairsToList, List.mem_map, List.mem_finRange, true_and] at inPairs
      obtain ⟨i, rfl⟩ := inPairs
      exact Or.inl ⟨i, occurs⟩
    · exact Or.inr ⟨equation, inRest, occurs⟩
  · rintro (⟨i, occurs⟩ | ⟨equation, member, occurs⟩)
    · exact ⟨(ts i, us i), List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩), occurs⟩
    · exact ⟨equation, List.mem_append_right _ member, occurs⟩

/-- **Unifying linear equations overlays them**: the most general unifier sends the variables of
the left sides to linear terms, pairwise without a shared variable. -/
theorem unifyTotal_overlay [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (θ : Subst σ) (accepted : unifyTotal equations = some θ)
    (linear : LinearEquations equations) : Overlay θ equations := by
  fun_induction unifyTotal equations generalizing θ with
  | case1 =>
    rintro v ⟨_, member, _⟩
    cases member
  | case2 rest other inductionHypothesis =>
    obtain ⟨_, _, apart, _⟩ := linear.head
    exact absurd apart (by simp [Term.freeVars])
  | case3 rest v other notEqual childResult inductionHypothesis => simp at accepted
  | case4 rest v other notEqual childTheta childResult inductionHypothesis =>
    simp at accepted
    subst θ
    have vAbsent : v ∉ eqVars rest := Finset.disjoint_left.mp linear.head.2.2.2.1 (by simp [Term.freeVars])
    rw [applyEqs_single_absent vAbsent] at childResult inductionHypothesis
    exact Overlay.bindLeft linear (inductionHypothesis childTheta childResult linear.head.2.2.2.2)
      (unifyTotal_relevantIdempotent rest childTheta childResult)
  | case5 rest v term notVariable occurs => simp at accepted
  | case6 rest v term notVariable notOccurs childResult inductionHypothesis => simp at accepted
  | case7 rest v term notVariable notOccurs childTheta childResult inductionHypothesis =>
    simp at accepted
    subst θ
    have vAbsent : v ∉ eqVars rest := Finset.disjoint_left.mp linear.head.2.2.2.1 (by simp [Term.freeVars])
    rw [applyEqs_single_absent vAbsent] at childResult inductionHypothesis
    exact Overlay.bindLeft linear (inductionHypothesis childTheta childResult linear.head.2.2.2.2)
      (unifyTotal_relevantIdempotent rest childTheta childResult)
  | case8 rest constant v childResult inductionHypothesis => simp at accepted
  | case9 rest constant v childTheta childResult inductionHypothesis =>
    simp at accepted
    subst θ
    have vAbsent : v ∉ eqVars rest := Finset.disjoint_left.mp linear.head.2.2.2.1 (by simp [Term.freeVars])
    rw [applyEqs_single_absent vAbsent] at childResult inductionHypothesis
    exact Overlay.bindRight linear (inductionHypothesis childTheta childResult linear.head.2.2.2.2)
      (unifyTotal_relevantIdempotent rest childTheta childResult)
  | case10 rest constant inductionHypothesis =>
    exact Overlay.dropGround rfl (inductionHypothesis θ accepted linear.head.2.2.2.2)
  | case11 rest left right notEqual => simp at accepted
  | case12 rest constant function arguments => simp at accepted
  | case13 rest function arguments v occurs => simp at accepted
  | case14 rest function arguments v notOccurs childResult inductionHypothesis => simp at accepted
  | case15 rest function arguments v notOccurs childTheta childResult inductionHypothesis =>
    simp at accepted
    subst θ
    have vAbsent : v ∉ eqVars rest := Finset.disjoint_left.mp linear.head.2.2.2.1 (by simp [Term.freeVars])
    rw [applyEqs_single_absent vAbsent] at childResult inductionHypothesis
    exact Overlay.bindRight linear (inductionHypothesis childTheta childResult linear.head.2.2.2.2)
      (unifyTotal_relevantIdempotent rest childTheta childResult)
  | case16 rest function arguments constant => simp at accepted
  | case17 rest function right left inductionHypothesis =>
    have child := inductionHypothesis θ accepted linear.decompose
    exact fun v inside => ⟨(child v (leftVar_decompose.mpr inside)).1,
      fun w wInside different => (child v (leftVar_decompose.mpr inside)).2 w (leftVar_decompose.mpr wInside) different⟩
  | case18 rest leftFunction leftArguments rightFunction rightArguments notEqual => simp at accepted

end Mettapedia.Logic.LP
