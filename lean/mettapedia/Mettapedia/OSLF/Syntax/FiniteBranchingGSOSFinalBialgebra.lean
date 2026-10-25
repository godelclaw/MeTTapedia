import Mettapedia.CategoryTheory.CoalgebraMonadBialgebra
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSDistributive
import Mettapedia.OSLF.Syntax.FiniteBranchingFinalSemantics
import Mettapedia.Computability.ComputationalTrinity

/-!
# The final compatible algebra for labelwise finite GSOS

The actual GSOS lifting acts on the independently constructed final
unordered action trees. Finality supplies its complete free-term action,
including all successor sets. The action satisfies the original monad
laws and is terminal among compatible algebras. Complete operational
observation preserves this action; no action alphabet bound or recovery
of erased branch occurrences is needed.

Closed terms with their operational behaviour form the initial compatible
algebra, and the semantics is the unique compatible map to the final one.
Two closed terms have the same semantics exactly when they are bisimilar.
Closed syntax, any compatible model and final behaviour form a commuting
computational-trinity comparison; the comparison loses program information
exactly when two distinct closed terms are bisimilar, and then no exact
trinity has the semantics as its program-to-space map.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.FinalBialgebra

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u} (law : Law S Actions)

abbrev CompatibleAlgebra :=
  CoalgebraMonadBialgebra.CompatibleAlgebra (Distributive.lifting law)

def finalAlgebra : CompatibleAlgebra law :=
  CoalgebraMonadBialgebra.finalAlgebra (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions)

def isFinal : Limits.IsTerminal (finalAlgebra law) :=
  CoalgebraMonadBialgebra.isFinalAlgebra (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions)

theorem action_readout :
    (finalAlgebra law).a = FinalSemantics.observe S Actions
      (IndexedGSOS.Operational.liftObject (lawEquiv S Actions law)
        (FinalSemantics.finalObject S Actions)) :=
  FinalSemantics.observe_unique S Actions _ _

theorem action_coiteration (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (FinalSemantics.finalObject S Actions).V base sort) :
    (finalAlgebra law).a.f base sort term =
      FiniteActionTree.Tree.coiterate
        (Operational.coalgebra law (FinalSemantics.finalObject S Actions).str base sort)
        (fun _ => PUnit.unit) term := by
  rw [action_readout]
  rfl

theorem action_unit :
    S.termMonad.η.app (FinalSemantics.finalObject S Actions).V ≫ (finalAlgebra law).a.f =
      𝟙 (FinalSemantics.finalObject S Actions).V :=
  congrArg Endofunctor.Coalgebra.Hom.f (finalAlgebra law).unit

theorem action_multiplication :
    S.termMonad.μ.app (FinalSemantics.finalObject S Actions).V ≫ (finalAlgebra law).a.f =
      S.termMonad.map (finalAlgebra law).a.f ≫ (finalAlgebra law).a.f :=
  congrArg Endofunctor.Coalgebra.Hom.f (finalAlgebra law).assoc

theorem action_successors (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (FinalSemantics.finalObject S Actions).V base sort)
    (action : Actions sort) :
    FiniteActionTree.Tree.step ((finalAlgebra law).a.f base sort term) action =
      FinitePowerset.map ((finalAlgebra law).a.f base sort)
        (Operational.coalgebra law (FinalSemantics.finalObject S Actions).str
          base sort term action) :=
  (congrArg (fun arrow => arrow base sort term action) (finalAlgebra law).a.h).symm

def observation (algebra : CompatibleAlgebra law) : algebra ⟶ finalAlgebra law :=
  CoalgebraMonadBialgebra.observation (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions) algebra

theorem observation_readout (algebra : CompatibleAlgebra law) :
    (observation law algebra).f = FinalSemantics.observe S Actions algebra.A :=
  FinalSemantics.observe_unique S Actions _ _

theorem observation_preserves_action (algebra : CompatibleAlgebra law) :
    S.termMonad.map (FinalSemantics.observe S Actions algebra.A).f ≫
        (finalAlgebra law).a.f =
      algebra.a.f ≫ (FinalSemantics.observe S Actions algebra.A).f := by
  have compatible := congrArg Endofunctor.Coalgebra.Hom.f (observation law algebra).h
  change S.termMonad.map (observation law algebra).f.f ≫ (finalAlgebra law).a.f =
    algebra.a.f ≫ (observation law algebra).f.f at compatible
  rw [observation_readout] at compatible
  exact compatible

theorem operational_observation
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    S.termMonad.map (FinalSemantics.observe S Actions object).f ≫ (finalAlgebra law).a.f =
      (FinalSemantics.observe S Actions
        (IndexedGSOS.Operational.liftObject (lawEquiv S Actions law) object)).f :=
  congrArg Endofunctor.Coalgebra.Hom.f
    (FinalSemantics.observe_unique S Actions _
      ((Distributive.lifting law).map (FinalSemantics.observe S Actions object) ≫
        (finalAlgebra law).a))

/-! ## Closed terms: the initial compatible algebra -/

/-- The operational coalgebra of closed terms. -/
abbrev closedOperational : Endofunctor.Coalgebra (behaviourFunctor S Actions) :=
  IndexedGSOS.Operational.liftObject (lawEquiv S Actions law)
    (CoalgebraMonadBialgebra.initialCoalgebra (B := behaviourFunctor S Actions) S.noVariablesInitial)

/-- Closed terms with their operational behaviour. -/
def initialAlgebra : CompatibleAlgebra law :=
  CoalgebraMonadBialgebra.initialAlgebra (Distributive.lifting law) S.noVariablesInitial

/-- Closed terms are initial among compatible algebras. -/
def isInitial : Limits.IsInitial (initialAlgebra law) :=
  CoalgebraMonadBialgebra.isInitialAlgebra (Distributive.lifting law) S.noVariablesInitial

/-- The unique compatible map from closed syntax to final behaviour. -/
def semantics : initialAlgebra law ⟶ finalAlgebra law :=
  CoalgebraMonadBialgebra.semantics (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions) S.noVariablesInitial

/-- The semantics of a closed term is the final unfolding of its operational behaviour. -/
theorem semantics_readout :
    (semantics law).f = FinalSemantics.observe S Actions (closedOperational law) :=
  FinalSemantics.observe_unique S Actions _ _

/-- Two closed terms have the same semantics exactly when they are bisimilar. -/
theorem semantics_eq_iff_bisimilar (sort : S.Srt) (first second : S.ClosedTerm sort) :
    (semantics law).f.f PUnit.unit sort first = (semantics law).f.f PUnit.unit sort second ↔
      Bisimulation.Bisimilar (closedOperational law) (closedOperational law)
        PUnit.unit sort first second := by
  rw [semantics_readout]
  exact FinalSemantics.kernel_iff_bisimilar S Actions (closedOperational law)
    (closedOperational law) PUnit.unit sort first second

/-! ## The semantics as a computational-trinity comparison -/

open Mettapedia.Computability.ComputationalTrinity

/-- A family read at every sort at once. -/
abbrev AllSorts (X : S.Families) : Type u := Σ sort : S.Srt, X PUnit.unit sort

/-- A family map read at every sort; it keeps the sort. -/
def allSortsMap {X Y : S.Families} (mapping : X ⟶ Y) (element : AllSorts X) : AllSorts Y :=
  ⟨element.1, mapping PUnit.unit element.1 element.2⟩

/-- A face that does not vary with its context. -/
abbrev constantFace (X : S.Families) : Face.{0, 0, u} (Discrete PUnit) :=
  (Functor.const (Discrete PUnit)ᵒᵖ).obj (AllSorts X)

/-- A family map as a map of constant faces. -/
abbrev constantMap {X Y : S.Families} (mapping : X ⟶ Y) : constantFace X ⟶ constantFace Y :=
  (Functor.const (Discrete PUnit)ᵒᵖ).map (↾(allSortsMap mapping))

/-- Closed syntax, a compatible model and final behaviour. The program-to-logic
leg is the unique map out of the closed terms, the logic-to-space leg is the
model's final observation, and the triangle commutes by initiality. -/
def trinity (model : CompatibleAlgebra law) : Comparison.{0, 0, u} (Discrete PUnit) where
  program := constantFace (initialAlgebra law).A.V
  logic := constantFace model.A.V
  space := constantFace (finalAlgebra law).A.V
  programToLogic := constantMap ((isInitial law).to model).f.f
  logicToSpace := constantMap (observation law model).f.f
  programToSpace := constantMap (semantics law).f.f
  coherence := by
    have triangle := congrArg (fun mapping => mapping.f.f)
      (CoalgebraMonadBialgebra.semantics_factors (Distributive.lifting law)
        (FinalSemantics.isFinal S Actions) S.noVariablesInitial model)
    ext context element
    change allSortsMap (observation law model).f.f
        (allSortsMap ((isInitial law).to model).f.f element) =
      allSortsMap (semantics law).f.f element
    have pointwise := congrArg (fun mapping => mapping PUnit.unit element.1 element.2) triangle
    exact Sigma.ext rfl (heq_of_eq pointwise)

/-- The comparison forgets program identity exactly when two distinct closed
terms of one sort are bisimilar. -/
theorem trinity_loses_iff (model : CompatibleAlgebra law) :
    (trinity law model).LosesProgramInformation ↔
      ∃ (sort : S.Srt) (first second : S.ClosedTerm sort), first ≠ second ∧
        Bisimulation.Bisimilar (closedOperational law) (closedOperational law)
          PUnit.unit sort first second := by
  constructor
  · rintro ⟨_, ⟨sort, first⟩, ⟨other, second⟩, distinct, same⟩
    change (⟨sort, (semantics law).f.f PUnit.unit sort first⟩ : AllSorts _) =
      ⟨other, (semantics law).f.f PUnit.unit other second⟩ at same
    obtain ⟨rfl, same⟩ := Sigma.mk.inj same
    refine ⟨sort, first, second, fun equal => distinct (by rw [equal]), ?_⟩
    exact (semantics_eq_iff_bisimilar law sort first second).mp (eq_of_heq same)
  · rintro ⟨sort, first, second, distinct, related⟩
    refine ⟨Opposite.op (Discrete.mk PUnit.unit), ⟨sort, first⟩, ⟨sort, second⟩,
      fun equal => distinct (eq_of_heq (Sigma.mk.inj equal).2), ?_⟩
    change (⟨sort, (semantics law).f.f PUnit.unit sort first⟩ : AllSorts _) =
      ⟨sort, (semantics law).f.f PUnit.unit sort second⟩
    rw [(semantics_eq_iff_bisimilar law sort first second).mpr related]

/-- When distinct closed terms are bisimilar, the semantics is not the
program-to-space map of any exact trinity. -/
theorem not_exact_of_bisimilar (model : CompatibleAlgebra law) {sort : S.Srt}
    {first second : S.ClosedTerm sort} (distinct : first ≠ second)
    (related : Bisimulation.Bisimilar (closedOperational law) (closedOperational law)
      PUnit.unit sort first second) :
    ¬ ∃ isomorphism : (trinity law model).program ≅ (trinity law model).space,
      isomorphism.hom = (trinity law model).programToSpace :=
  (trinity law model).no_programSpace_iso_of_losesProgramInformation
    ((trinity_loses_iff law model).mpr ⟨sort, first, second, distinct, related⟩)

end Mettapedia.OSLF.FiniteBranching.FinalBialgebra
