import Mettapedia.GSLT.OpenEnded.SufficientBubbles
import Mathlib.Order.Closure
import Mathlib.Order.FixedPoints
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.TFAE

/-!
# Closure systems: one structure, several presentations

A family of bubbles has a least member above every seed exactly when it is a
closure system. This file proves that the following descriptions of a family
`F` of elements of a complete lattice coincide (`tfae_mooreFamily`):

1. `F` is closed under all meets (a Moore family);
2. `F` is the set of closed elements of a closure operator;
3. `F` is the set of prefixed points of a monotone operator;
4. `F` is the set of models of a set of Horn implications `a ≤ x → b ≤ x`;
5. the inclusion of `F` has a left adjoint (`F` is a reflective sub-order;
   `reflection` is the adjunction of thin categories);
6. `F` is the set of carriers of the Eilenberg–Moore algebras of a monad on
   the lattice viewed as a thin category;
7. every element has a least member of `F` above it.

The Horn presentation (4) and the operator presentation (3) translate into
each other directly: the prefixed points of a monotone operator `T` are the
models of the implications `a ≤ x → T a ≤ x` (`prefixedPoints_eq_respects`).

On a poset, closure operators and monads are the same thing
(`closureMonadEquiv`), and every monad is idempotent (`isIso_μ_app`). The least
member above a seed is a least fixed point (`isLeast_lfp_seeded`), and a least
fixed point is an initial algebra (`lfpIsInitial`), whose structure map is an
isomorphism (`lfpAlgebra_str_isIso`).

For bubbles (sets of generators):

* the Horn clauses of `SufficientBubbles` are presentation (4) split one
  conclusion at a time (`hornModels_eq_respects`, `respects_eq_hornModels`,
  `tfae_bubbles`);
* the Horn closure is the least fixed point of the one-step (immediate
  consequence) operator (`hornClosure_eq_lfp`);
* every monotone operator on bubbles is the one-step operator of a Horn
  theory, the rules `A → g` with `g ∈ T A` (`oneStep_rulesOf`), so every least
  fixed point of a monotone operator on bubbles is a Horn closure
  (`lfp_eq_hornClosure`); this is the correspondence between monotone
  operators and rule sets of inductive definitions (Aczel 1977);
* a monotone operator is the one-step operator of a finitary Horn theory
  exactly when it preserves unions of nonempty directed families
  (`oneStep_finitaryRulesOf_iff`), and finitary Horn theories present exactly
  the closure systems closed under directed unions
  (`hornModels_finitary_iff`); a family closed under intersections but not
  under directed unions has no finitary Horn presentation
  (`finiteOrAll_not_finitary`);
* two different Horn theories can present one closure system
  (`chain_hornModels_eq`, `chain_theories_ne`).

The closure system is determined by any one of these presentations, and none
of them mentions an order of evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.ClosureSystems

open Set CategoryTheory
open Mettapedia.GSLT.OpenEnded.SufficientBubbles

universe u

/-! ## Moore families in a complete lattice -/

section CompleteLattice

variable {L : Type u} [CompleteLattice L]

/-- Closed under all meets, including the empty one. -/
def MooreFamily (F : Set L) : Prop :=
  ∀ S ⊆ F, sInf S ∈ F

/-- Every element has a least member of the family above it. -/
def LeastAboveEvery (F : Set L) : Prop :=
  ∀ a : L, ∃ m, IsLeast {x | x ∈ F ∧ a ≤ x} m

/-- An element is a model of a set of Horn implications `(a, b)`: whenever it
lies above `a`, it lies above `b`. -/
def Respects (R : Set (L × L)) (x : L) : Prop :=
  ∀ p ∈ R, p.1 ≤ x → p.2 ≤ x

/-- The prefixed points of a monotone operator. -/
def prefixedPoints (T : L →o L) : Set L :=
  {x | T x ≤ x}

theorem mooreFamily_prefixedPoints (T : L →o L) : MooreFamily (prefixedPoints T) := by
  intro S included
  exact le_sInf fun s member => (T.monotone (sInf_le member)).trans (included member)

/-- **The prefixed points of a monotone operator are the models of a Horn
presentation of it**: the implications `a ≤ x → T a ≤ x`. -/
theorem prefixedPoints_eq_respects (T : L →o L) :
    prefixedPoints T = {x | Respects (range fun a => (a, T a)) x} := by
  ext x
  constructor
  · rintro prefixed _ ⟨a, rfl⟩ below
    exact (T.monotone below).trans prefixed
  · intro respects
    exact respects _ ⟨x, rfl⟩ le_rfl

theorem mooreFamily_respects (R : Set (L × L)) : MooreFamily {x | Respects R x} := by
  intro S included p member below
  exact le_sInf fun s memberS => included memberS p member (below.trans (sInf_le memberS))

theorem mooreFamily_closed (c : ClosureOperator L) : MooreFamily {x | c.IsClosed x} :=
  fun _ included => ClosureOperator.sInf_isClosed included

/-- The closure operator of a Moore family. -/
def closureOf {F : Set L} (moore : MooreFamily F) : ClosureOperator L :=
  ClosureOperator.ofCompletePred (· ∈ F) fun S included => moore S included

theorem isClosed_closureOf {F : Set L} (moore : MooreFamily F) (x : L) :
    (closureOf moore).IsClosed x ↔ x ∈ F :=
  Iff.rfl

/-- The closure of `a` is the least member of the family above `a`. -/
theorem isLeast_closureOf {F : Set L} (moore : MooreFamily F) (a : L) :
    IsLeast {x | x ∈ F ∧ a ≤ x} (closureOf moore a) :=
  ⟨⟨(isClosed_closureOf moore _).mp ((closureOf moore).isClosed_closure a),
      (closureOf moore).le_closure a⟩,
    fun x member => (closureOf moore).closure_min member.2 ((isClosed_closureOf moore x).mpr member.1)⟩

/-- The reflection of an element into a Moore family. -/
def reflect {F : Set L} (moore : MooreFamily F) (a : L) : F :=
  ⟨closureOf moore a, (isLeast_closureOf moore a).1.1⟩

/-- **A Moore family is a reflective sub-order**: the reflection is left adjoint
to the inclusion. -/
theorem gc_reflect {F : Set L} (moore : MooreFamily F) :
    GaloisConnection (reflect moore) (Subtype.val : F → L) := by
  intro a y
  constructor
  · intro le
    exact ((closureOf moore).le_closure a).trans le
  · intro le
    exact (isLeast_closureOf moore a).2 ⟨y.2, le⟩

/-- The reflection as an adjunction between thin categories. -/
def reflection {F : Set L} (moore : MooreFamily F) :
    (gc_reflect moore).monotone_l.functor ⊣ (gc_reflect moore).monotone_u.functor :=
  (gc_reflect moore).adjunction

/-- **A reflective sub-order is a Moore family.** -/
theorem mooreFamily_of_gc {F : Set L} {l : L → F}
    (gc : GaloisConnection l (Subtype.val : F → L)) : MooreFamily F := by
  intro S included
  have below : ((l (sInf S) : F) : L) ≤ sInf S :=
    le_sInf fun s member => (gc (sInf S) ⟨s, included member⟩).mpr (sInf_le member)
  have same : ((l (sInf S) : F) : L) = sInf S := le_antisymm below (gc.le_u_l (sInf S))
  exact same ▸ (l (sInf S)).2

end CompleteLattice

/-! ## Closure operators are the monads on a poset -/

section Monads

variable {P : Type u} [PartialOrder P]

/-- A closure operator as a monad on the poset viewed as a thin category. -/
def closureToMonad (c : ClosureOperator P) : Monad P where
  toFunctor := c.monotone.functor
  η := { app := fun x => homOfLE (c.le_closure x), naturality := fun _ _ _ => Subsingleton.elim _ _ }
  μ := { app := fun x => homOfLE (c.idempotent x).le,
         naturality := fun _ _ _ => Subsingleton.elim _ _ }
  assoc _ := Subsingleton.elim _ _
  left_unit _ := Subsingleton.elim _ _
  right_unit _ := Subsingleton.elim _ _

/-- A monad on a poset as a closure operator. -/
def monadToClosure (T : Monad P) : ClosureOperator P :=
  ClosureOperator.mk' T.obj (fun _ _ le => leOfHom (T.map (homOfLE le)))
    (fun x => leOfHom (T.η.app x)) (fun x => leOfHom (T.μ.app x))

theorem closureToMonad_obj (c : ClosureOperator P) (x : P) : (closureToMonad c).obj x = c x :=
  rfl

theorem monadToClosure_apply (T : Monad P) (x : P) : monadToClosure T x = T.obj x :=
  rfl

theorem monadToClosure_closureToMonad (c : ClosureOperator P) :
    monadToClosure (closureToMonad c) = c :=
  ClosureOperator.ext _ _ fun _ => rfl

/-- A monad on a poset is determined by its action on elements. -/
theorem monad_ext_of_obj {T₁ T₂ : Monad P} (same : ∀ x, T₁.obj x = T₂.obj x) : T₁ = T₂ := by
  obtain ⟨F₁, η₁, μ₁, _, _, _⟩ := T₁
  obtain ⟨F₂, η₂, μ₂, _, _, _⟩ := T₂
  obtain rfl : F₁ = F₂ := CategoryTheory.Functor.ext same (fun _ _ _ => Subsingleton.elim _ _)
  obtain rfl : η₁ = η₂ := NatTrans.ext (funext fun _ => Subsingleton.elim _ _)
  obtain rfl : μ₁ = μ₂ := NatTrans.ext (funext fun _ => Subsingleton.elim _ _)
  rfl

/-- **Closure operators on a poset are exactly the monads on it.** -/
def closureMonadEquiv : ClosureOperator P ≃ Monad P where
  toFun := closureToMonad
  invFun := monadToClosure
  left_inv := monadToClosure_closureToMonad
  right_inv _ := monad_ext_of_obj fun _ => rfl

/-- **Every monad on a poset is idempotent**: its multiplication is an
isomorphism. -/
theorem isIso_μ_app (T : Monad P) (x : P) : IsIso (T.μ.app x) :=
  (PartialOrder.isIso_iff_eq _).mpr
    (le_antisymm (leOfHom (T.μ.app x)) (leOfHom (T.η.app (T.obj x))))

/-- **The Eilenberg–Moore algebras of a monad on a poset are its closed
elements.** -/
theorem exists_algebra_iff (T : Monad P) (x : P) :
    (∃ A : T.Algebra, A.A = x) ↔ (monadToClosure T).IsClosed x := by
  rw [ClosureOperator.isClosed_iff_closure_le, monadToClosure_apply]
  constructor
  · rintro ⟨A, rfl⟩
    exact leOfHom A.a
  · intro le
    exact ⟨⟨x, homOfLE le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩

end Monads

/-! ## Least fixed points and initial algebras -/

section FixedPoints

variable {L : Type u} [CompleteLattice L]

/-- The operator whose least fixed point is the least prefixed point above a
seed. -/
def seeded (T : L →o L) (a : L) : L →o L where
  toFun x := a ⊔ T x
  monotone' _ _ le := sup_le_sup_left (T.monotone le) a

/-- **The least prefixed point above a seed is a least fixed point.** -/
theorem isLeast_lfp_seeded (T : L →o L) (a : L) :
    IsLeast {x | x ∈ prefixedPoints T ∧ a ≤ x} (OrderHom.lfp (seeded T a)) := by
  have prefixed : ∀ x, seeded T a x ≤ x ↔ x ∈ prefixedPoints T ∧ a ≤ x := fun x => by
    change a ⊔ T x ≤ x ↔ T x ≤ x ∧ a ≤ x
    rw [sup_le_iff, and_comm]
  have least := OrderHom.isLeast_lfp_le (seeded T a)
  exact ⟨(prefixed _).mp least.1, fun x member => least.2 ((prefixed x).mpr member)⟩

/-- The least fixed point with its structure map, as an algebra of the monotone
operator viewed as an endofunctor of the thin category. -/
def lfpAlgebra (T : L →o L) : Endofunctor.Algebra T.monotone.functor :=
  ⟨OrderHom.lfp T, homOfLE (OrderHom.map_lfp T).le⟩

/-- **A least fixed point is an initial algebra.** -/
def lfpIsInitial (T : L →o L) : Limits.IsInitial (lfpAlgebra T) :=
  Limits.IsInitial.ofUniqueHom
    (fun A => ⟨homOfLE (OrderHom.lfp_le T (leOfHom A.str)), Subsingleton.elim _ _⟩)
    (fun _ _ => Endofunctor.Algebra.ext (Subsingleton.elim _ _))

/-- The structure map of the initial algebra is an isomorphism: the least
fixed point is recovered as a fixed point from initiality alone. -/
theorem lfpAlgebra_str_isIso (T : L →o L) : IsIso (lfpAlgebra T).str :=
  Endofunctor.Algebra.Initial.str_isIso (lfpIsInitial T)

end FixedPoints

/-! ## The equivalence of presentations -/

section Equivalence

variable {L : Type u} [CompleteLattice L]

/-- **Seven presentations of one closure system.** -/
theorem tfae_mooreFamily (F : Set L) : List.TFAE
    [MooreFamily F,
     ∃ c : ClosureOperator L, F = {x | c.IsClosed x},
     ∃ T : L →o L, F = prefixedPoints T,
     ∃ R : Set (L × L), F = {x | Respects R x},
     ∃ l : L → F, GaloisConnection l Subtype.val,
     ∃ T : Monad L, F = {x | ∃ A : T.Algebra, A.A = x},
     LeastAboveEvery F] := by
  tfae_have 1 → 2 := fun moore =>
    ⟨closureOf moore, by ext x; exact (isClosed_closureOf moore x).symm⟩
  tfae_have 2 → 3 := by
    rintro ⟨c, rfl⟩
    exact ⟨c.toOrderHom, by ext x; exact ClosureOperator.isClosed_iff_closure_le⟩
  tfae_have 3 → 1 := by
    rintro ⟨T, rfl⟩
    exact mooreFamily_prefixedPoints T
  tfae_have 1 → 4 := by
    intro moore
    refine ⟨range fun a => (a, closureOf moore a), ?_⟩
    ext x
    constructor
    · rintro member _ ⟨a, rfl⟩ below
      exact (closureOf moore).closure_min below ((isClosed_closureOf moore x).mpr member)
    · intro respects
      have below : closureOf moore x ≤ x := respects _ ⟨x, rfl⟩ le_rfl
      have same : closureOf moore x = x := le_antisymm below ((closureOf moore).le_closure x)
      exact same ▸ (isLeast_closureOf moore x).1.1
  tfae_have 4 → 1 := by
    rintro ⟨R, rfl⟩
    exact mooreFamily_respects R
  tfae_have 1 → 5 := fun moore => ⟨reflect moore, gc_reflect moore⟩
  tfae_have 5 → 1 := by
    rintro ⟨l, gc⟩
    exact mooreFamily_of_gc gc
  tfae_have 2 → 6 := by
    rintro ⟨c, rfl⟩
    refine ⟨closureToMonad c, ?_⟩
    ext x
    change c.IsClosed x ↔ ∃ A : (closureToMonad c).Algebra, A.A = x
    rw [exists_algebra_iff, monadToClosure_closureToMonad]
  tfae_have 6 → 2 := by
    rintro ⟨T, rfl⟩
    exact ⟨monadToClosure T, by ext x; exact exists_algebra_iff T x⟩
  tfae_have 1 → 7 := fun moore a => ⟨_, isLeast_closureOf moore a⟩
  tfae_have 7 → 1 := by
    intro leastAbove S included
    obtain ⟨m, ⟨member, above⟩, smallest⟩ := leastAbove (sInf S)
    have below : m ≤ sInf S := le_sInf fun s memberS => smallest ⟨included memberS, sInf_le memberS⟩
    exact (le_antisymm below above) ▸ member
  tfae_finish

end Equivalence

/-! ## Bubbles: Horn clauses and the other presentations -/

section Bubbles

variable {G : Type u}

theorem mooreFamily_iff_intersectionClosed (F : Set (Set G)) :
    MooreFamily F ↔ IntersectionClosed F :=
  Iff.rfl

theorem leastAboveEvery_iff_leastAboveEverySeed (F : Set (Set G)) :
    LeastAboveEvery F ↔ LeastAboveEverySeed F :=
  Iff.rfl

/-- **Closure under nonempty meets is closure under all meets up to the
top.** This connects `exists_least_iff_meetClosed` to the presentations above.
The families closed under nonempty meets are the model classes of Horn
theories that may also contain goal clauses (clauses without a conclusion);
this file formalizes definite clauses only, and adding the top passes from one
case to the other. -/
theorem meetClosed_iff_mooreFamily_insert_univ (Suff : Set G → Prop) :
    MeetClosed Suff ↔ MooreFamily (insert univ {S | Suff S}) := by
  constructor
  · intro closed S included
    by_cases nonempty : ({T | T ∈ S ∧ Suff T} : Set (Set G)).Nonempty
    · have same : sInf S = ⋂₀ {T | T ∈ S ∧ Suff T} := by
        rw [sInf_eq_sInter]
        apply subset_antisymm
        · exact subset_sInter fun T member => sInter_subset_of_mem member.1
        · intro g member T memberT
          rcases included memberT with isUniv | sufficient
          · exact isUniv ▸ mem_univ g
          · exact member T ⟨memberT, sufficient⟩
      rw [same]
      exact Or.inr (closed _ nonempty fun T member => member.2)
    · left
      rw [sInf_eq_sInter]
      apply eq_univ_of_forall
      intro g T memberT
      rcases included memberT with isUniv | sufficient
      · exact isUniv ▸ mem_univ g
      · exact absurd ⟨T, memberT, sufficient⟩ nonempty
  · intro moore F' nonempty allSufficient
    rcases moore F' (fun T member => Or.inr (allSufficient T member)) with isUniv | sufficient
    · obtain ⟨T, memberT⟩ := nonempty
      have whole : T = univ := eq_univ_of_forall fun g =>
        (show g ∈ ⋂₀ F' from (sInf_eq_sInter F') ▸ isUniv.symm ▸ mem_univ g) T memberT
      change sInf F' = univ at isUniv
      rw [← sInf_eq_sInter, isUniv, ← whole]
      exact allSufficient T memberT
    · rw [← sInf_eq_sInter]
      exact sufficient

/-- The lattice implications `(A, {g})` of single-conclusion Horn clauses. -/
def toPairs (theory : Set (HornClause G)) : Set (Set G × Set G) :=
  (fun clause => (clause.premises, {clause.conclusion})) '' theory

/-- A lattice implication `(A, B)` as the Horn clauses `A → g`, one for each
`g ∈ B`. -/
def toHornClauses (R : Set (Set G × Set G)) : Set (HornClause G) :=
  {clause | ∃ p ∈ R, p.1 = clause.premises ∧ clause.conclusion ∈ p.2}

theorem hornModels_eq_respects (theory : Set (HornClause G)) :
    hornModels theory = {S | Respects (toPairs theory) S} := by
  ext S
  constructor
  · rintro closed _ ⟨clause, member, rfl⟩ premisesIn
    exact singleton_subset_iff.mpr (closed clause member premisesIn)
  · intro respects clause member premisesIn
    exact singleton_subset_iff.mp (respects _ ⟨clause, member, rfl⟩ premisesIn)

/-- **A conclusion set is the same as one conclusion at a time.** -/
theorem respects_eq_hornModels (R : Set (Set G × Set G)) :
    {S | Respects R S} = hornModels (toHornClauses R) := by
  ext S
  constructor
  · rintro respects clause ⟨p, member, premises, conclusion⟩ premisesIn
    exact respects p member (premises ▸ premisesIn) conclusion
  · intro closed p member premisesIn g inConclusion
    exact closed ⟨p.1, g⟩ ⟨p, member, rfl, inConclusion⟩ premisesIn

/-- **For bubbles, the Horn-definable families are exactly the closure
systems**, alongside the other presentations. -/
theorem tfae_bubbles (F : Set (Set G)) : List.TFAE
    [IntersectionClosed F,
     ∃ theory : Set (HornClause G), hornModels theory = F,
     ∃ c : ClosureOperator (Set G), F = {x | c.IsClosed x},
     ∃ T : Set G →o Set G, F = prefixedPoints T,
     ∃ T : Monad (Set G), F = {x | ∃ A : T.Algebra, A.A = x},
     LeastAboveEverySeed F] := by
  have general := tfae_mooreFamily F
  tfae_have 1 ↔ 2 := by
    rw [← leastAbove_iff_intersectionClosed, leastAbove_iff_hornDefinable]
  tfae_have 1 ↔ 3 := general.out 0 1
  tfae_have 1 ↔ 4 := general.out 0 2
  tfae_have 1 ↔ 5 := general.out 0 5
  tfae_have 1 ↔ 6 := (leastAbove_iff_intersectionClosed F).symm
  tfae_finish

/-! ### The Horn closure is a least fixed point -/

/-- The one-step (immediate consequence) operator of a Horn theory above
seeds: the seeds, and the conclusions of the clauses whose premises are
present. -/
def oneStep (theory : Set (HornClause G)) (seeds : Set G) : Set G →o Set G where
  toFun S := seeds ∪ {g | ∃ clause ∈ theory, clause.premises ⊆ S ∧ clause.conclusion = g}
  monotone' _ _ le := union_subset_union_right _
    fun _ ⟨clause, member, premisesIn, conclusion⟩ =>
      ⟨clause, member, premisesIn.trans le, conclusion⟩

theorem oneStep_le_iff (theory : Set (HornClause G)) (seeds S : Set G) :
    oneStep theory seeds S ≤ S ↔ S ∈ hornModels theory ∧ seeds ⊆ S := by
  constructor
  · intro le
    exact ⟨fun clause member premisesIn =>
      le (Or.inr ⟨clause, member, premisesIn, rfl⟩), fun _ member => le (Or.inl member)⟩
  · rintro ⟨closed, seedsIn⟩ g (member | ⟨clause, member, premisesIn, rfl⟩)
    · exact seedsIn member
    · exact closed clause member premisesIn

/-- **The Horn closure is the least fixed point of the one-step operator.** -/
theorem hornClosure_eq_lfp (theory : Set (HornClause G)) (seeds : Set G) :
    hornClosure theory seeds = OrderHom.lfp (oneStep theory seeds) := by
  have same : {S | S ∈ hornModels theory ∧ seeds ⊆ S} = {S | oneStep theory seeds S ≤ S} := by
    ext S
    exact (oneStep_le_iff theory seeds S).symm
  have least := OrderHom.isLeast_lfp_le (oneStep theory seeds)
  rw [← same] at least
  exact (isLeast_hornClosure theory seeds).unique least

/-! ### Every monotone operator on bubbles is a Horn theory -/

/-- The rules of a monotone operator: `A → g` whenever `g ∈ T A`. -/
def rulesOf (T : Set G →o Set G) : Set (HornClause G) :=
  {clause | clause.conclusion ∈ T clause.premises}

/-- **Every monotone operator on bubbles is the one-step operator of a Horn
theory**, its rules. -/
theorem oneStep_rulesOf (T : Set G →o Set G) : oneStep (rulesOf T) ∅ = T := by
  ext S g
  constructor
  · rintro (absurd | ⟨clause, member, premisesIn, rfl⟩)
    · exact absurd.elim
    · exact T.monotone premisesIn member
  · intro member
    exact Or.inr ⟨⟨S, g⟩, member, subset_rfl, rfl⟩

/-- **Every least fixed point of a monotone operator on bubbles is a Horn
closure.** -/
theorem lfp_eq_hornClosure (T : Set G →o Set G) :
    OrderHom.lfp T = hornClosure (rulesOf T) ∅ := by
  rw [hornClosure_eq_lfp, oneStep_rulesOf]

/-- The finitary rules of a monotone operator: `A → g` with `A` finite and
`g ∈ T A`. -/
def finitaryRulesOf (T : Set G →o Set G) : Set (HornClause G) :=
  {clause | clause.premises.Finite ∧ clause.conclusion ∈ T clause.premises}

/-- A monotone operator on bubbles preserves unions of nonempty directed
families (the reverse inclusion holds for every monotone operator). -/
def PreservesDirectedUnions (T : Set G →o Set G) : Prop :=
  ∀ D : Set (Set G), D.Nonempty → DirectedOn (· ⊆ ·) D → T (⋃₀ D) ⊆ ⋃ S ∈ D, T S

/-- **A monotone operator on bubbles is the one-step operator of a finitary
Horn theory exactly when it preserves directed unions.** -/
theorem oneStep_finitaryRulesOf_iff (T : Set G →o Set G) :
    oneStep (finitaryRulesOf T) ∅ = T ↔ PreservesDirectedUnions T := by
  constructor
  · intro same D nonempty directed g member
    rw [← same] at member
    rcases member with absurd | ⟨clause, ⟨finite, valid⟩, premisesIn, rfl⟩
    · exact absurd.elim
    · obtain ⟨S, memberS, contained⟩ :=
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion nonempty directed finite premisesIn
      exact mem_iUnion₂.mpr ⟨S, memberS, T.monotone contained valid⟩
  · intro preserves
    ext S g
    constructor
    · rintro (absurd | ⟨clause, ⟨_, valid⟩, premisesIn, rfl⟩)
      · exact absurd.elim
      · exact T.monotone premisesIn valid
    · intro member
      let D : Set (Set G) := {A | A ⊆ S ∧ A.Finite}
      have union : ⋃₀ D = S := by
        apply subset_antisymm
        · rintro x ⟨A, ⟨inS, _⟩, inA⟩
          exact inS inA
        · intro x inS
          exact ⟨{x}, ⟨singleton_subset_iff.mpr inS, finite_singleton x⟩, mem_singleton x⟩
      have directed : DirectedOn (· ⊆ ·) D := by
        rintro A ⟨inA, finiteA⟩ B ⟨inB, finiteB⟩
        exact ⟨A ∪ B, ⟨union_subset inA inB, finiteA.union finiteB⟩, subset_union_left,
          subset_union_right⟩
      have inUnion : g ∈ T (⋃₀ D) := by
        rw [union]
        exact member
      obtain ⟨A, ⟨inS, finite⟩, inT⟩ :=
        mem_iUnion₂.mp (preserves D ⟨∅, empty_subset S, finite_empty⟩ directed inUnion)
      exact Or.inr ⟨⟨A, g⟩, ⟨finite, inT⟩, inS, rfl⟩

/-! ### Finite premises are compactness -/

/-- Every premise set is finite. -/
def Finitary (theory : Set (HornClause G)) : Prop :=
  ∀ clause ∈ theory, clause.premises.Finite

/-- Closed under unions of nonempty directed subfamilies. -/
def DirectedUnionClosed (F : Set (Set G)) : Prop :=
  ∀ D ⊆ F, D.Nonempty → DirectedOn (· ⊆ ·) D → ⋃₀ D ∈ F

theorem directedUnionClosed_hornModels {theory : Set (HornClause G)}
    (finitary : Finitary theory) : DirectedUnionClosed (hornModels theory) := by
  intro D included nonempty directed clause member premisesIn
  obtain ⟨S, memberS, contained⟩ :=
    DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion nonempty directed
      (finitary clause member) premisesIn
  exact mem_sUnion_of_mem (included memberS clause member contained) memberS

/-- The finitary Horn clauses valid in a family. -/
def finitaryHornTheoryOf (F : Set (Set G)) : Set (HornClause G) :=
  {clause | clause.premises.Finite ∧
    clause.conclusion ∈ closureIn F clause.premises}

theorem finitary_finitaryHornTheoryOf (F : Set (Set G)) : Finitary (finitaryHornTheoryOf F) :=
  fun _ member => member.1

theorem subset_closureIn (F : Set (Set G)) (A : Set G) : A ⊆ closureIn F A :=
  subset_sInter fun _ member => member.2

theorem closureIn_mono (F : Set (Set G)) {A B : Set G} (le : A ⊆ B) :
    closureIn F A ⊆ closureIn F B :=
  sInter_subset_sInter fun _ member => ⟨member.1, le.trans member.2⟩

theorem closureIn_mem {F : Set (Set G)} (closed : IntersectionClosed F) (A : Set G) :
    closureIn F A ∈ F :=
  closed _ fun _ member => member.1

/-- **An intersection-closed family closed under directed unions is presented
by a finitary Horn theory.** -/
theorem models_finitaryHornTheoryOf {F : Set (Set G)} (closed : IntersectionClosed F)
    (directed : DirectedUnionClosed F) : hornModels (finitaryHornTheoryOf F) = F := by
  ext S
  constructor
  · intro respects
    let D : Set (Set G) := {C | ∃ A ⊆ S, A.Finite ∧ C = closureIn F A}
    have union : ⋃₀ D = S := by
      apply subset_antisymm
      · rintro g ⟨C, ⟨A, inS, finite, rfl⟩, member⟩
        exact respects ⟨A, g⟩ ⟨finite, member⟩ inS
      · intro g member
        exact ⟨closureIn F {g}, ⟨{g}, singleton_subset_iff.mpr member, finite_singleton g, rfl⟩,
          subset_closureIn F {g} (mem_singleton g)⟩
    have inF : ⋃₀ D ∈ F := by
      refine directed D ?_ ⟨closureIn F ∅, ∅, empty_subset S, finite_empty, rfl⟩ ?_
      · rintro _ ⟨A, _, _, rfl⟩
        exact closureIn_mem closed A
      · rintro _ ⟨A, inA, finiteA, rfl⟩ _ ⟨B, inB, finiteB, rfl⟩
        exact ⟨closureIn F (A ∪ B), ⟨A ∪ B, union_subset inA inB, finiteA.union finiteB, rfl⟩,
          closureIn_mono F subset_union_left, closureIn_mono F subset_union_right⟩
    exact union ▸ inF
  · intro memberF clause valid premisesIn
    exact valid.2 S ⟨memberF, premisesIn⟩

/-- **Finitary Horn theories present exactly the closure systems closed under
directed unions.** -/
theorem hornModels_finitary_iff (F : Set (Set G)) :
    (∃ theory, Finitary theory ∧ hornModels theory = F) ↔
      IntersectionClosed F ∧ DirectedUnionClosed F := by
  constructor
  · rintro ⟨theory, finitary, rfl⟩
    exact ⟨fun F' included => hornModels_sInter_mem theory F' included,
      directedUnionClosed_hornModels finitary⟩
  · rintro ⟨closed, directed⟩
    exact ⟨_, finitary_finitaryHornTheoryOf F, models_finitaryHornTheoryOf closed directed⟩

end Bubbles

/-! ## Examples -/

/-- The finite sets of naturals together with all of them. -/
def finiteOrAll : Set (Set ℕ) :=
  {S | S.Finite ∨ S = univ}

theorem finiteOrAll_intersectionClosed : IntersectionClosed finiteOrAll := by
  intro F' included
  by_cases allUniv : ∀ S ∈ F', S = univ
  · right
    exact eq_univ_of_forall fun n S member => (allUniv S member).symm ▸ mem_univ n
  · obtain ⟨S, notAll⟩ := not_forall.mp allUniv
    obtain ⟨member, notUniv⟩ := Classical.not_imp.mp notAll
    left
    rcases included member with finite | isUniv
    · exact finite.subset (sInter_subset_of_mem member)
    · exact absurd isUniv notUniv

/-- Even numbers below a bound. -/
def evensBelow (n : ℕ) : Set ℕ :=
  {m | m < n ∧ m % 2 = 0}

theorem evensBelow_finite (n : ℕ) : (evensBelow n).Finite :=
  (finite_lt_nat n).subset fun _ member => member.1

theorem evens_not_finite : ¬ ({m | m % 2 = 0} : Set ℕ).Finite := by
  intro finite
  obtain ⟨bound, isBound⟩ := finite.bddAbove
  have member : 2 * (bound + 1) ∈ ({m | m % 2 = 0} : Set ℕ) := by
    change 2 * (bound + 1) % 2 = 0
    omega
  have := isBound member
  omega

/-- **Closed under intersections, not under directed unions.** -/
theorem finiteOrAll_not_directedUnionClosed : ¬ DirectedUnionClosed finiteOrAll := by
  intro directed
  have union : ⋃₀ range evensBelow = {m | m % 2 = 0} := by
    ext m
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, member⟩
      exact member.2
    · intro even
      exact ⟨evensBelow (m + 1), ⟨m + 1, rfl⟩, Nat.lt_succ_self m, even⟩
  have inF := directed (range evensBelow) (by rintro _ ⟨n, rfl⟩; exact Or.inl (evensBelow_finite n))
    (range_nonempty _) (by
      rintro _ ⟨n, rfl⟩ _ ⟨k, rfl⟩
      refine ⟨evensBelow (max n k), ⟨max n k, rfl⟩, ?_, ?_⟩
      · exact fun m member => ⟨lt_of_lt_of_le member.1 (le_max_left n k), member.2⟩
      · exact fun m member => ⟨lt_of_lt_of_le member.1 (le_max_right n k), member.2⟩)
  rw [union] at inF
  rcases inF with finite | isUniv
  · exact evens_not_finite finite
  · have one : (1 : ℕ) ∈ ({m | m % 2 = 0} : Set ℕ) := isUniv ▸ mem_univ 1
    change 1 % 2 = 0 at one
    omega

/-- **A closure system not closed under directed unions has no finitary Horn
presentation.** -/
theorem finiteOrAll_not_finitary :
    ¬ ∃ theory : Set (HornClause ℕ), Finitary theory ∧ hornModels theory = finiteOrAll :=
  fun presented => finiteOrAll_not_directedUnionClosed
    ((hornModels_finitary_iff finiteOrAll).mp presented).2

/-- A positive example: the computation-preservation theory of
`SufficientBubbles` is finitary. -/
theorem pkgTheory_finitary : Finitary pkgTheory := by
  rintro clause (rfl | rfl)
  · exact finite_empty
  · exact finite_singleton _

/-- One step of a finitary Horn theory preserves directed unions. -/
theorem preservesDirectedUnions_oneStep {G : Type u} {theory : Set (HornClause G)}
    (finitary : Finitary theory) : PreservesDirectedUnions (oneStep theory ∅) := by
  intro D nonempty directed g member
  rcases member with absurd | ⟨clause, inTheory, premisesIn, rfl⟩
  · exact absurd.elim
  · obtain ⟨S, memberS, contained⟩ :=
      DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion nonempty directed
        (finitary clause inTheory) premisesIn
    exact mem_iUnion₂.mpr ⟨S, memberS, Or.inr ⟨clause, inTheory, contained, rfl⟩⟩

/-- A positive example: one step of the computation-preservation theory
preserves directed unions. -/
theorem pkgStep_preservesDirectedUnions : PreservesDirectedUnions (oneStep pkgTheory ∅) :=
  preservesDirectedUnions_oneStep pkgTheory_finitary

/-- Infinitude as an operator on bubbles: everything when the bubble is
infinite, nothing otherwise. -/
def infinitude : Set ℕ →o Set ℕ where
  toFun S := {_n | S.Infinite}
  monotone' _ _ le _ infinite := Set.Infinite.mono le infinite

/-- **A monotone operator that does not preserve directed unions**: the
finite initial segments are directed, their union is infinite, and none of them
is. -/
theorem infinitude_not_preservesDirectedUnions : ¬ PreservesDirectedUnions infinitude := by
  intro preserves
  have directed : DirectedOn (· ⊆ ·) (range fun n : ℕ => {m : ℕ | m < n}) := by
    rintro _ ⟨n, rfl⟩ _ ⟨k, rfl⟩
    exact ⟨{m | m < max n k}, ⟨max n k, rfl⟩,
      fun m below => lt_of_lt_of_le below (le_max_left n k),
      fun m below => lt_of_lt_of_le below (le_max_right n k)⟩
  have union : ⋃₀ range (fun n : ℕ => {m : ℕ | m < n}) = univ := by
    apply eq_univ_of_forall
    intro m
    exact ⟨{i | i < m + 1}, ⟨m + 1, rfl⟩, Nat.lt_succ_self m⟩
  have whole : (0 : ℕ) ∈ infinitude (⋃₀ range fun n : ℕ => {m : ℕ | m < n}) := by
    rw [union]
    exact infinite_univ
  obtain ⟨_, ⟨n, rfl⟩, inS⟩ := mem_iUnion₂.mp (preserves _ (range_nonempty _) directed whole)
  exact inS (finite_lt_nat n)

/-- **Infinitude is presented by its infinitary rules and by no finitary Horn
theory.** -/
theorem infinitude_rules :
    oneStep (rulesOf infinitude) ∅ = infinitude ∧
      oneStep (finitaryRulesOf infinitude) ∅ ≠ infinitude :=
  ⟨oneStep_rulesOf infinitude, fun same =>
    infinitude_not_preservesDirectedUnions ((oneStep_finitaryRulesOf_iff infinitude).mp same)⟩

/-- Three generators in a chain. -/
inductive Tri
  | a
  | b
  | c
  deriving DecidableEq

open Tri

/-- `a` requires `b`, and `b` requires `c`. -/
def chainTheory : Set (HornClause Tri) :=
  {⟨{a}, b⟩, ⟨{b}, c⟩}

/-- The same requirements with the derived clause `a` requires `c` added. -/
def chainTheory' : Set (HornClause Tri) :=
  insert ⟨{a}, c⟩ chainTheory

/-- **Two Horn theories, one closure system.** -/
theorem chain_hornModels_eq : hornModels chainTheory = hornModels chainTheory' := by
  ext S
  constructor
  · intro closed clause member premisesIn
    rcases member with rfl | member
    · have hb : b ∈ S := closed ⟨{a}, b⟩ (Or.inl rfl) premisesIn
      exact closed ⟨{b}, c⟩ (Or.inr rfl) (singleton_subset_iff.mpr hb)
    · exact closed clause member premisesIn
  · intro closed clause member premisesIn
    exact closed clause (Or.inr member) premisesIn

/-- The two Horn theories are different. -/
theorem chain_theories_ne : chainTheory ≠ chainTheory' := by
  intro same
  have member : (⟨{a}, c⟩ : HornClause Tri) ∈ chainTheory := same ▸ Or.inl rfl
  rcases member with absurd | absurd
  · have := congrArg HornClause.conclusion absurd
    cases this
  · have := congrArg HornClause.conclusion absurd
    have premises := congrArg HornClause.premises absurd
    simp only at premises
    have : a ∈ ({b} : Set Tri) := premises ▸ mem_singleton a
    cases this

#print axioms tfae_mooreFamily
#print axioms closureMonadEquiv
#print axioms isIso_μ_app
#print axioms exists_algebra_iff
#print axioms isLeast_lfp_seeded
#print axioms lfpIsInitial
#print axioms lfpAlgebra_str_isIso
#print axioms meetClosed_iff_mooreFamily_insert_univ
#print axioms hornModels_eq_respects
#print axioms respects_eq_hornModels
#print axioms tfae_bubbles
#print axioms hornClosure_eq_lfp
#print axioms prefixedPoints_eq_respects
#print axioms oneStep_rulesOf
#print axioms lfp_eq_hornClosure
#print axioms oneStep_finitaryRulesOf_iff
#print axioms preservesDirectedUnions_oneStep
#print axioms infinitude_rules
#print axioms hornModels_finitary_iff
#print axioms finiteOrAll_intersectionClosed
#print axioms finiteOrAll_not_finitary
#print axioms chain_hornModels_eq
#print axioms chain_theories_ne

end Mettapedia.GSLT.OpenEnded.ClosureSystems
