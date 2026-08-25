import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorMaskUpdate

/-!
# Reindexing invariance of deletion-stable interface codes

The finite interface of a bounded graph window has no preferred enumeration.
An executable closure may therefore compare two codes only after accounting
for a bijective renaming of their coordinates.  This file proves that the
three-row exterior-component code, deletion masks, and local adjacency updates
are all natural under such a renaming.

In particular, extracting an exact code after precomposing the interface map
with an equivalence is the same as reindexing the previously extracted code.
The proof includes the load-bearing exterior row: bijective reindexing leaves
the set of strictly exterior graph vertices, hence its induced graph and its
components, unchanged.

The result is graph-generic.  It does not choose a canonical enumeration or
assert that two unrelated source windows are isomorphic.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorReindex

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceDeletionComponentFactorUpdate
open SimpleGraph

/-- Pull all three rows of an interface code back along a coordinate
equivalence. -/
def reindexInterfaceExteriorCode {Old New : Type*}
    (code : BoundedInterfaceExteriorCode Old) (coordinate : New ≃ Old) :
    BoundedInterfaceExteriorCode New where
  vertexEq left right := code.vertexEq (coordinate left) (coordinate right)
  directAdj left right := code.directAdj (coordinate left) (coordinate right)
  exteriorConnected left right :=
    code.exteriorConnected (coordinate left) (coordinate right)

@[simp]
theorem reindexInterfaceExteriorCode_vertexEq {Old New : Type*}
    (code : BoundedInterfaceExteriorCode Old) (coordinate : New ≃ Old)
    (left right : New) :
    (reindexInterfaceExteriorCode code coordinate).vertexEq left right =
      code.vertexEq (coordinate left) (coordinate right) :=
  rfl

@[simp]
theorem reindexInterfaceExteriorCode_directAdj {Old New : Type*}
    (code : BoundedInterfaceExteriorCode Old) (coordinate : New ≃ Old)
    (left right : New) :
    (reindexInterfaceExteriorCode code coordinate).directAdj left right =
      code.directAdj (coordinate left) (coordinate right) :=
  rfl

@[simp]
theorem reindexInterfaceExteriorCode_exteriorConnected {Old New : Type*}
    (code : BoundedInterfaceExteriorCode Old) (coordinate : New ≃ Old)
    (left right : New) :
    (reindexInterfaceExteriorCode code coordinate).exteriorConnected left right =
      code.exteriorConnected (coordinate left) (coordinate right) :=
  rfl

/-- Primitive finite steps are invariant under coordinate renaming. -/
@[simp]
theorem reindexInterfaceExteriorCode_factoredStep_iff {Old New : Type*}
    (code : BoundedInterfaceExteriorCode Old) (coordinate : New ≃ Old)
    (left right : New) :
    InterfaceExteriorFactoredStep
        (reindexInterfaceExteriorCode code coordinate) left right ↔
      InterfaceExteriorFactoredStep code (coordinate left) (coordinate right) :=
  Iff.rfl

/-- A bijective renaming represents the same set of ambient vertices. -/
@[simp]
theorem outsideInterface_comp_equiv_iff {N Old New : Type*}
    (interfaceVertex : Old → N) (coordinate : New ≃ Old) (vertex : N) :
    OutsideInterface (interfaceVertex ∘ coordinate) vertex ↔
      OutsideInterface interfaceVertex vertex := by
  constructor
  · intro houtside slot
    obtain ⟨newSlot, rfl⟩ := coordinate.surjective slot
    exact houtside newSlot
  · intro houtside slot
    exact houtside (coordinate slot)

/-- Consequently the graph induced strictly outside the interface is literally
unchanged by a coordinate equivalence. -/
theorem exteriorGraph_comp_equiv_eq {N Old New : Type*}
    (graph : SimpleGraph N) (interfaceVertex : Old → N)
    (coordinate : New ≃ Old) :
    exteriorGraph graph (interfaceVertex ∘ coordinate) =
      exteriorGraph graph interfaceVertex := by
  unfold exteriorGraph
  congr 1
  funext vertex
  apply propext
  exact outsideInterface_comp_equiv_iff interfaceVertex coordinate vertex

/-- Exact extraction commutes with every bijective coordinate change.  The
exterior-component row is preserved because the represented ambient set is
unchanged, not because it is discarded. -/
theorem exactInterfaceExteriorCode_comp_equiv
    {N Old New : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Old → N) (coordinate : New ≃ Old) :
    exactInterfaceExteriorCode graph (interfaceVertex ∘ coordinate) =
      reindexInterfaceExteriorCode
        (exactInterfaceExteriorCode graph interfaceVertex) coordinate := by
  classical
  unfold exactInterfaceExteriorCode reindexInterfaceExteriorCode
  congr 1
  funext left right
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Function.comp_apply]
  rw [exteriorGraph_comp_equiv_eq graph interfaceVertex coordinate]
  constructor
  · rintro ⟨entry, exit, hentry, hexit, hadjEntry, hreach, hadjExit⟩
    exact ⟨entry, exit,
      (outsideInterface_comp_equiv_iff interfaceVertex coordinate entry).1
        hentry,
      (outsideInterface_comp_equiv_iff interfaceVertex coordinate exit).1
        hexit,
      hadjEntry, hreach, hadjExit⟩
  · rintro ⟨entry, exit, hentry, hexit, hadjEntry, hreach, hadjExit⟩
    exact ⟨entry, exit,
      (outsideInterface_comp_equiv_iff interfaceVertex coordinate entry).2
        hentry,
      (outsideInterface_comp_equiv_iff interfaceVertex coordinate exit).2
        hexit,
      hadjEntry, hreach, hadjExit⟩

/-- Pull a deletion mask back through the same coordinate equivalence. -/
def reindexInterfaceMask {Old New : Type*} (removed : Old → Bool)
    (coordinate : New ≃ Old) : New → Bool :=
  removed ∘ coordinate

/-- Row masking is natural under bijective reindexing. -/
theorem reindexInterfaceExteriorCode_mask {Old New : Type*}
    (code : BoundedInterfaceExteriorCode Old) (removed : Old → Bool)
    (coordinate : New ≃ Old) :
    reindexInterfaceExteriorCode (maskInterfaceExteriorCode code removed)
        coordinate =
      maskInterfaceExteriorCode (reindexInterfaceExteriorCode code coordinate)
        (reindexInterfaceMask removed coordinate) :=
  rfl

/-- Pull a finite local adjacency table back through a coordinate
equivalence. -/
def reindexInterfaceAdjacency {Old New : Type*}
    (adjacency : Old → Old → Bool) (coordinate : New ≃ Old) :
    New → New → Bool :=
  fun left right => adjacency (coordinate left) (coordinate right)

/-- Adding a local adjacency table is natural under the same reindexing. -/
theorem reindexInterfaceExteriorCode_addAdjacency {Old New : Type*}
    (code : BoundedInterfaceExteriorCode Old)
    (adjacency : Old → Old → Bool) (coordinate : New ≃ Old) :
    reindexInterfaceExteriorCode
        (addInterfaceAdjacency code adjacency) coordinate =
      addInterfaceAdjacency (reindexInterfaceExteriorCode code coordinate)
        (reindexInterfaceAdjacency adjacency coordinate) :=
  rfl

@[simp]
theorem reindexInterfaceExteriorCode_refl {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface) :
    reindexInterfaceExteriorCode code (Equiv.refl Interface) = code := by
  cases code
  rfl

/-- Successive coordinate changes compose without changing any row. -/
theorem reindexInterfaceExteriorCode_trans {First Second Third : Type*}
    (code : BoundedInterfaceExteriorCode First)
    (secondToFirst : Second ≃ First) (thirdToSecond : Third ≃ Second) :
    reindexInterfaceExteriorCode
        (reindexInterfaceExteriorCode code secondToFirst) thirdToSecond =
      reindexInterfaceExteriorCode code
        (thirdToSecond.trans secondToFirst) := by
  rfl

/-- Two interface codes represent the same finite receipt when a bijective
coordinate renaming identifies every row. -/
def InterfaceExteriorCodeIsomorphic {Left Right : Type*}
    (left : BoundedInterfaceExteriorCode Left)
    (right : BoundedInterfaceExteriorCode Right) : Prop :=
  ∃ coordinate : Right ≃ Left,
    reindexInterfaceExteriorCode left coordinate = right

theorem interfaceExteriorCodeIsomorphic_refl {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface) :
    InterfaceExteriorCodeIsomorphic code code :=
  ⟨Equiv.refl Interface, reindexInterfaceExteriorCode_refl code⟩

theorem interfaceExteriorCodeIsomorphic_symm {Left Right : Type*}
    {left : BoundedInterfaceExteriorCode Left}
    {right : BoundedInterfaceExteriorCode Right}
    (h : InterfaceExteriorCodeIsomorphic left right) :
    InterfaceExteriorCodeIsomorphic right left := by
  rcases h with ⟨coordinate, rfl⟩
  refine ⟨coordinate.symm, ?_⟩
  rw [reindexInterfaceExteriorCode_trans]
  simp

theorem interfaceExteriorCodeIsomorphic_trans {First Second Third : Type*}
    {first : BoundedInterfaceExteriorCode First}
    {second : BoundedInterfaceExteriorCode Second}
    {third : BoundedInterfaceExteriorCode Third}
    (hfirst : InterfaceExteriorCodeIsomorphic first second)
    (hsecond : InterfaceExteriorCodeIsomorphic second third) :
    InterfaceExteriorCodeIsomorphic first third := by
  rcases hfirst with ⟨secondToFirst, rfl⟩
  rcases hsecond with ⟨thirdToSecond, rfl⟩
  refine ⟨thirdToSecond.trans secondToFirst, ?_⟩
  exact reindexInterfaceExteriorCode_trans first secondToFirst thirdToSecond

end GoertzelV24InterfaceDeletionComponentFactorReindex

end Mettapedia.GraphTheory.FourColor
