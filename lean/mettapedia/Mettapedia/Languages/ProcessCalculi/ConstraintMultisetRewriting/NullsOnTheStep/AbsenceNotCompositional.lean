import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullSeparations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StoreComposition
import Mettapedia.OSLF.Syntax.RhoScopedParallelEvents

/-!
# Absence is not compositional

An absence claim has the whole store as its scope. Putting another store beside it can falsify the
claim, so admission of an absence-guarded firing is not monotone under the union of stores, while
admission of firings that only take, read, make and tell is.

## On the first-order step

Two configurations side by side (`union`) hold the union of the stores and both knowledges.

* `valid_union`: a firing admitted at `C` is admitted beside `D` when its made identities are new to
  `D`, `D`'s knowledge has the identity solution, and its checks hold on the union.
* `positive_monotone`: **take, read, make and tell admission is monotone** under the union.
* `absent_union_iff`: an absence claim holds on a union exactly when it holds on each part.
* `guarded_union_iff`: **the grade of absence**: an absence-guarded firing admitted at `C` stays
  admitted beside `D` exactly when `D` has no occurrence of the pattern.
* `absence_not_monotone`: `spawn` (make `T` where `U` is absent) is admitted at the empty store and
  refused beside the store holding `U`.

This is the step's form of the boundary of the knowledge-tensor reading of runs
(`absence_has_no_additive_tensor_reading`): absence has no additive reading, because the frame rule
holds for it only on its grade.

## Stores, terms and rho

* `storeStep_frameClosed`: every store step of a reaction is closed under adding a frame;
  `absentStep_not_frameClosed`, `no_reaction_is_absence`: the absence step is not, so no reaction
  presents it.
* `reduces_parClosed`: reduction modulo the structural congruence is closed under parallel
  composition; `absentReduces_not_parClosed`, `parClosed_not_absence`: so no such relation is the
  absence step read through heating.
* `rho_step_not_join_sensitive`: the reduction of every rho rule set is closed under parallel
  composition (`RhoScopedParallelEvents.step_join`), so no relation that a parallel component can
  switch off, as an absence guard is switched off by the absent process, is a rho reduction.
  Absence is not definable inside rho. It is meaningful on owned stores read as a whole, which is
  what the step's guard reads (`absence_admits`, `guarded_union_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition

open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled)

/-! ## On the first-order step -/

/-- Two configurations side by side. -/
def union (C D : Conf) : Conf := ⟨C.equations ++ D.equations, C.present ∪ D.present⟩

/-- **A valid firing stays valid beside another store** whose occurrences its made identities
avoid, whose knowledge has the identity solution, and where its checks hold on the union. -/
theorem valid_union {C D : Conf} {f : Fir} (valid : f.Valid ground Prod.fst C)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present)
    (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2)
    (checks : ∀ c ∈ f.rule.checks, c.Holds ground () Prod.fst (union C D).present)
    (noQueries : f.queries = []) : f.Valid ground Prod.fst (union C D) := by
  have firing := valid.firing
  obtain ⟨takenSub, keptSub, apart, fresh, _⟩ := firing.occurrences
  refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
    firing.outputs, ⟨fun o member => Finset.mem_union_left _ (takenSub member),
      fun o member => Finset.mem_union_left _ (keptSub member), apart, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · show Disjoint _ (C.present ∪ D.present)
    rw [Finset.disjoint_union_right]
    refine ⟨fresh, Finset.disjoint_left.mpr fun {o} made inD => freshInD o ?_ inD⟩
    exact List.mem_toFinset.mp made
  · intro query member
    simp [Selection.commit] at member
  · obtain ⟨u, solved⟩ := firing.consistent
    refine ⟨u, fun e member => ?_⟩
    simp only [Selection.problem, union, List.mem_append] at member
    rcases member with (((old | added) | taken) | read) | told
    · exact solved e (by simp [Selection.problem, old])
    · exact knowledgeD e added
    · exact solved e (by simp [Selection.problem, taken])
    · exact solved e (by simp [Selection.problem, read])
    · exact solved e (by simp [Selection.problem, told])
  · intro check member u _
    exact checks check member
  · intro query member
    rw [noQueries] at member
    exact absurd member List.not_mem_nil

/-- **Take, read, make and tell admission is monotone under the union of stores.** -/
theorem positive_monotone {C D : Conf} {f : Fir} (noChecks : f.rule.checks = [])
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2) :
    base.Admits (s := union C D) f :=
  valid_union admitted freshInD knowledgeD
    (by rw [noChecks]; exact fun c member => absurd member List.not_mem_nil) noQueries

/-- **An absence claim holds on a union exactly when it holds on each part.** -/
theorem absent_union_iff {C D : Conf} {p : Expr} :
    (Check.absent p).Holds ground () Prod.fst (union C D).present ↔
      (Check.absent p).Holds ground () Prod.fst C.present ∧
        (Check.absent p).Holds ground () Prod.fst D.present := by
  constructor
  · intro onUnion
    exact ⟨fun o member => onUnion o (Finset.mem_union_left _ member),
      fun o member => onUnion o (Finset.mem_union_right _ member)⟩
  · rintro ⟨onC, onD⟩ o member
    rcases Finset.mem_union.mp member with inC | inD
    · exact onC o inC
    · exact onD o inD

/-- The absence check of an admitted guarded firing holds where it fires. -/
theorem guard_holds {C : Conf} {f : Fir} {p : Expr} (guard : f.rule.checks = [.absent p])
    (valid : f.Valid ground Prod.fst C) : (Check.absent p).Holds ground () Prod.fst C.present := by
  obtain ⟨u, solved⟩ := valid.firing.consistent
  exact valid.firing.checks _ (by rw [guard]; exact List.mem_singleton_self _) u solved

/-- **The grade of absence**: an absence-guarded firing admitted at `C` stays admitted beside `D`
exactly when `D` has no occurrence of the pattern. -/
theorem guarded_union_iff {C D : Conf} {f : Fir} {p : Expr} (guard : f.rule.checks = [.absent p])
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f)
    (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) (knowledgeD : ∀ e ∈ D.equations, e.1 = e.2) :
    base.Admits (s := union C D) f ↔ (Check.absent p).Holds ground () Prod.fst D.present := by
  constructor
  · intro onUnion
    exact (absent_union_iff.mp (guard_holds guard onUnion)).2
  · intro onD
    refine valid_union admitted freshInD knowledgeD ?_ noQueries
    rw [guard]
    intro c member
    rw [List.mem_singleton.mp member]
    exact absent_union_iff.mpr ⟨guard_holds guard admitted, onD⟩

/-- **Absence is not monotone**: `spawn` is admitted at the empty store and refused beside the store
holding `U`. -/
theorem absence_not_monotone :
    ∃ (C D : Conf) (f : Fir), base.Admits (s := C) f ∧ ¬ base.Admits (s := union C D) f := by
  refine ⟨Separations.emptyS.1, Separations.onlyU.1, Separations.spawnAt.1,
    Separations.spawn_admitted.1, fun onUnion => ?_⟩
  have clear := (guarded_union_iff (D := Separations.onlyU.1) (f := Separations.spawnAt.1) rfl rfl
    Separations.spawn_admitted.1 (by decide) (by decide)).mp onUnion
  exact clear (factU, 0) (by decide) rfl

/-! ## Stores, terms and rho -/

section Stores

variable {A : Type*}

open StoreComposition

/-- A relation on stores closed under adding a frame. -/
def FrameClosed (R : Multiset A → Multiset A → Prop) : Prop :=
  ∀ before after frame, R before after → R (before + frame) (after + frame)

/-- **Every store step of a reaction is closed under adding a frame.** -/
theorem storeStep_frameClosed (react : Reaction A) : FrameClosed (StoreStep react) := by
  rintro before after frame ⟨consumed, produced, rest, reacts, rfl, rfl⟩
  exact ⟨consumed, produced, rest + frame, reacts, Multiset.add_assoc _ _ _,
    Multiset.add_assoc _ _ _⟩

/-- The absence step: make `a` where `c` is absent. -/
def AbsentStep (c a : A) (before after : Multiset A) : Prop := c ∉ before ∧ after = before + {a}

theorem absentStep_not_frameClosed (c a : A) : ¬ FrameClosed (AbsentStep c a) := by
  intro closed
  have here : AbsentStep c a 0 {a} := ⟨Multiset.notMem_zero c, (Multiset.zero_add _).symm⟩
  exact (closed 0 {a} {c} here).1 (by simp)

/-- **No reaction presents the absence step.** -/
theorem no_reaction_is_absence (c a : A) (react : Reaction A) :
    ¬ ∀ before after, StoreStep react before after ↔ AbsentStep c a before after := by
  intro same
  apply absentStep_not_frameClosed c a
  intro before after frame step
  exact (same _ _).mp (storeStep_frameClosed react before after frame ((same _ _).mpr step))

/-- A relation on terms closed under parallel composition. -/
def ParClosed (R : Term A → Term A → Prop) : Prop :=
  ∀ t t' u, R t t' → R (Term.join t u) (Term.join t' u)

/-- **Reduction modulo the congruence is closed under parallel composition.** -/
theorem reduces_parClosed (react : Reaction A) : ParClosed (Reduces react) := by
  rintro t t' u ⟨s, s', first, inner, last⟩
  exact ⟨Term.join s u, Term.join s' u,
    Term.Congruent.join_congr first (Term.Congruent.refl u), LocalStep.left u inner,
    Term.Congruent.join_congr last (Term.Congruent.refl u)⟩

/-- The absence step read on terms through heating. -/
def AbsentReduces (c a : A) (t t' : Term A) : Prop := AbsentStep c a (Term.heat t) (Term.heat t')

theorem absentReduces_not_parClosed (c a : A) : ¬ ParClosed (AbsentReduces c a) := by
  intro closed
  have here : AbsentReduces c a Term.unit (Term.atom a) := ⟨by simp, by simp⟩
  exact (closed _ _ (Term.atom c) here).1 (by simp)

/-- **No relation closed under parallel composition is the absence step.** -/
theorem parClosed_not_absence {R : Term A → Term A → Prop} (closed : ParClosed R) (c a : A) :
    ¬ ∀ t t', R t t' ↔ AbsentReduces c a t t' := by
  intro same
  apply absentReduces_not_parClosed c a
  intro t t' u step
  exact (same _ _).mp (closed t t' u ((same _ _).mpr step))

end Stores

section Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres

variable {Index : Type*} {rules : Index → RhoScopedParallelEvents.ProcessRule} {admitted : Index → Prop}
  {context : Ctx sig}

/-- **Absence is not definable inside rho.** The reduction of every rho rule set is closed under
parallel composition, so no relation that some parallel component switches off is a rho
reduction. -/
theorem rho_step_not_join_sensitive {R : Process context → Process context → Prop}
    {first second extra : Process context} (holds : R first second)
    (switchedOff : ¬ R (join first extra) (join second extra)) :
    ¬ ∀ x y, RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted) x y ↔ R x y := by
  intro same
  exact switchedOff ((same _ _).mp (RhoScopedParallelEvents.step_join ((same _ _).mpr holds) extra))

end Rho

#print axioms valid_union
#print axioms positive_monotone
#print axioms absent_union_iff
#print axioms guarded_union_iff
#print axioms absence_not_monotone
#print axioms no_reaction_is_absence
#print axioms parClosed_not_absence
#print axioms rho_step_not_join_sensitive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
