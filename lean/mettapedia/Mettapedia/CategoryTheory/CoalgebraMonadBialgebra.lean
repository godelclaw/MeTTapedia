import Mettapedia.CategoryTheory.CoalgebraMonadDistributive
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Compatible algebras and a final behavior algebra

An actual monad lifting to endofunctor coalgebras gives a monad on that
coalgebra category. Its Eilenberg–Moore algebras retain both the original
monad algebra and its earned coalgebra compatibility. A final coalgebra
has a unique such action, obtained from its final map; the algebra laws
and finality in the compatible-algebra category follow from coalgebra
finality. Every final observation is therefore an algebra morphism.

## From the initial to the final compatible algebra

An initial object carries exactly one coalgebra structure, and that coalgebra
is initial (`isInitialCoalgebra`). The lifted monad's free algebra on it is
initial among compatible algebras (`isInitialAlgebra`): for a GSOS lifting it
is the closed syntax with its operational behaviour. The unique compatible
map from it to the final compatible algebra is the semantics (`semantics`).

* Every compatible algebra lies on a commuting triangle between the two ends
  (`semantics_factors`); neither end is presupposed by the other.
* The semantics is at once the final coalgebra map of the operational model
  (`semantics_operational`) and the initial algebra map of the syntax into the
  algebra carried by the final behaviours (`semantics_denotational`), so the
  operational and denotational readings are one arrow (`operational_eq_denotational`).
* The kernel of any compatible map, in particular of the semantics, is closed
  under the monad action (`kernel_closed`): behavioural equivalence is a
  congruence.

This is the bialgebraic semantics of D. Turi and G. Plotkin, *Towards a
mathematical operational semantics*, LICS 1997; see B. Klin, *Bialgebras for
structural operational semantics: an introduction*, TCS 412(38), 2011.
For a single endofunctor, `Coalgebra.InitialFinal.meeting_underlying_eq`
records the corresponding identification of the algebra and coalgebra maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.CoalgebraMonadBialgebra

open _root_.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {B : C ⥤ C} {T : Monad C}
    (lifting : CoalgebraMonadDistributive.Lift B T)

/-- The original monad functor acts on actual behavior coalgebras. -/
def liftedFunctor : Endofunctor.Coalgebra B ⥤ Endofunctor.Coalgebra B where
  obj := lifting.object
  map := lifting.map
  map_id object := by
    apply Endofunctor.Coalgebra.ext
    exact T.map_id object.V
  map_comp first second := by
    apply Endofunctor.Coalgebra.ext
    exact T.map_comp first.f second.f

/-- The original unit is a natural coalgebra morphism. -/
def liftedUnit : 𝟭 (Endofunctor.Coalgebra B) ⟶ liftedFunctor lifting where
  app := lifting.unit
  naturality {_ _} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact T.η.naturality mapping.f

/-- The original multiplication is a natural coalgebra morphism. -/
def liftedMultiplication : liftedFunctor lifting ⋙ liftedFunctor lifting ⟶
    liftedFunctor lifting where
  app := lifting.multiplication
  naturality {_ _} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact T.μ.naturality mapping.f

/-- A genuine monad on behavior coalgebras, with all three laws earned. -/
def liftedMonad : Monad (Endofunctor.Coalgebra B) where
  toFunctor := liftedFunctor lifting
  η := liftedUnit lifting
  μ := liftedMultiplication lifting
  assoc object := by
    apply Endofunctor.Coalgebra.ext
    exact T.assoc object.V
  left_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact T.left_unit object.V
  right_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact T.right_unit object.V

/-- Compatible algebras use the actual Eilenberg–Moore category of the lifted monad. -/
abbrev CompatibleAlgebra := Monad.Algebra (liftedMonad lifting)

/-- Forgetting behavior retains the independently given original monad algebra. -/
def underlyingAlgebra (algebra : CompatibleAlgebra lifting) : Monad.Algebra T where
  A := algebra.A.V
  a := algebra.a.f
  unit := congrArg Endofunctor.Coalgebra.Hom.f algebra.unit
  assoc := congrArg Endofunctor.Coalgebra.Hom.f algebra.assoc

/-- The action's behavior compatibility is part of its actual coalgebra morphism. -/
theorem action_compatible (algebra : CompatibleAlgebra lifting) :
    lifting.structureMap algebra.A ≫ B.map algebra.a.f =
      algebra.a.f ≫ algebra.A.str :=
  algebra.a.h

/-- A compatible algebra map preserves the original monad algebra action. -/
def underlyingMap {first second : CompatibleAlgebra lifting} (mapping : first ⟶ second) :
    underlyingAlgebra lifting first ⟶ underlyingAlgebra lifting second where
  f := mapping.f.f
  h := congrArg Endofunctor.Coalgebra.Hom.f mapping.h

/-- The category retains both actual structure maps under forgetting. -/
def forgetBehaviour : CompatibleAlgebra lifting ⥤ Monad.Algebra T where
  obj := underlyingAlgebra lifting
  map := underlyingMap lifting
  map_id _ := rfl
  map_comp _ _ := rfl

variable {finalObject : Endofunctor.Coalgebra B} (finality : Limits.IsTerminal finalObject)

/-- The complete final behavior action is the unique actual lifted coalgebra map. -/
def finalAlgebra : CompatibleAlgebra lifting where
  A := finalObject
  a := finality.from (lifting.object finalObject)
  unit := finality.hom_ext _ _
  assoc := finality.hom_ext _ _

/-- Any compatible algebra's final observation preserves its whole algebra action. -/
def observation (algebra : CompatibleAlgebra lifting) :
    algebra ⟶ finalAlgebra lifting finality where
  f := finality.from algebra.A
  h := finality.hom_ext _ _

theorem observation_unique (algebra : CompatibleAlgebra lifting)
    (mapping : algebra ⟶ finalAlgebra lifting finality) :
    mapping = observation lifting finality algebra := by
  apply Monad.Algebra.Hom.ext
  exact finality.hom_ext _ _

/-- The independently constructed final behavior algebra is terminal among compatible algebras. -/
def isFinalAlgebra : Limits.IsTerminal (finalAlgebra lifting finality) :=
  Limits.IsTerminal.ofUniqueHom (observation lifting finality)
    (observation_unique lifting finality)

/-- Complete final observation commutes with the original monad action. -/
theorem observation_action (algebra : CompatibleAlgebra lifting) :
    T.map (finality.from algebra.A).f ≫
        (finality.from (lifting.object finalObject)).f =
      algebra.a.f ≫ (finality.from algebra.A).f :=
  congrArg Endofunctor.Coalgebra.Hom.f (observation lifting finality algebra).h

/-! ## The initial compatible algebra and the semantics -/

/-- The kernel of a compatible algebra map is closed under the monad action:
two generalized elements identified by the map stay identified after the same
term context is applied and the source action evaluates it. -/
theorem kernel_closed {source target : CompatibleAlgebra lifting} (mapping : source ⟶ target)
    {X : C} (first second : X ⟶ source.A.V)
    (same : first ≫ mapping.f.f = second ≫ mapping.f.f) :
    T.map first ≫ source.a.f ≫ mapping.f.f = T.map second ≫ source.a.f ≫ mapping.f.f := by
  have square : T.map mapping.f.f ≫ target.a.f = source.a.f ≫ mapping.f.f :=
    congrArg Endofunctor.Coalgebra.Hom.f mapping.h
  rw [← square, ← Category.assoc, ← T.map_comp, same, T.map_comp, Category.assoc]

/-- The free algebra of a monad on an initial object is initial among its algebras. -/
def freeIsInitial {D : Type*} [Category D] (M : Monad D) {start : D}
    (initial : Limits.IsInitial start) : Limits.IsInitial (M.free.obj start) :=
  Limits.IsInitial.ofUniqueHom
    (fun algebra => (M.adj.homEquiv start algebra).symm (initial.to algebra.A))
    (fun algebra _ =>
      (M.adj.homEquiv start algebra).eq_symm_apply.mpr (initial.hom_ext _ _))

variable {zero : C} (initial : Limits.IsInitial zero)

/-- The unique coalgebra structure on an initial object. -/
def initialCoalgebra : Endofunctor.Coalgebra B where
  V := zero
  str := initial.to (B.obj zero)

/-- The coalgebra on an initial object is initial among all coalgebras. -/
def isInitialCoalgebra : Limits.IsInitial (initialCoalgebra (B := B) initial) :=
  Limits.IsInitial.ofUniqueHom
    (fun object => { f := initial.to object.V, h := initial.hom_ext _ _ })
    (fun _ _ => Endofunctor.Coalgebra.Hom.ext (initial.hom_ext _ _))

/-- Syntax over no variables, with its lifted behaviour: the free compatible
algebra on the initial coalgebra. -/
def initialAlgebra : CompatibleAlgebra lifting :=
  (liftedMonad lifting).free.obj (initialCoalgebra initial)

/-- The free compatible algebra on the initial coalgebra is initial. -/
def isInitialAlgebra : Limits.IsInitial (initialAlgebra lifting initial) :=
  freeIsInitial (liftedMonad lifting) (isInitialCoalgebra initial)

/-- The semantics: the unique compatible algebra map from syntax to behaviour. -/
def semantics : initialAlgebra lifting initial ⟶ finalAlgebra lifting finality :=
  (isInitialAlgebra lifting initial).to (finalAlgebra lifting finality)

/-- Initiality and finality select the same map. -/
theorem semantics_eq_observation :
    semantics lifting finality initial = observation lifting finality (initialAlgebra lifting initial) :=
  observation_unique lifting finality _ _

/-- Every compatible algebra lies between syntax and behaviour on a commuting
triangle; the two legs are its unique incoming and outgoing compatible maps. -/
theorem semantics_factors (algebra : CompatibleAlgebra lifting) :
    (isInitialAlgebra lifting initial).to algebra ≫ observation lifting finality algebra =
      semantics lifting finality initial :=
  (isInitialAlgebra lifting initial).hom_ext _ _

/-- Operationally, the semantics is the final coalgebra map of the lifted
behaviour on the syntax over the initial object. -/
theorem semantics_operational :
    (semantics lifting finality initial).f =
      finality.from (lifting.object (initialCoalgebra initial)) :=
  finality.hom_ext _ _

/-- Denotationally, the semantics is the initial monad-algebra map from the
syntax over the initial object into the algebra carried by the final behaviours. -/
theorem semantics_denotational :
    (semantics lifting finality initial).f.f =
      ((freeIsInitial T initial).to
        (underlyingAlgebra lifting (finalAlgebra lifting finality))).f :=
  congrArg Monad.Algebra.Hom.f ((freeIsInitial T initial).hom_ext
    (underlyingMap lifting (semantics lifting finality initial)) _)

/-- The operational and the denotational semantics are the same arrow. -/
theorem operational_eq_denotational :
    (finality.from (lifting.object (initialCoalgebra initial))).f =
      ((freeIsInitial T initial).to
        (underlyingAlgebra lifting (finalAlgebra lifting finality))).f :=
  (congrArg Endofunctor.Coalgebra.Hom.f (semantics_operational lifting finality initial)).symm.trans
    (semantics_denotational lifting finality initial)

end Mettapedia.CategoryTheory.CoalgebraMonadBialgebra
