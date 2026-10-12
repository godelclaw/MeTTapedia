import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Isolation
import Mettapedia.Machines.TransactionalSearchCode

/-!
# The committed mode is the semantics of the search regions of the flat code

`Machines.TransactionalSearchCode` has finite search regions with two kinds of
effect.  A write of the binding store is snapshotted at a choice and restored.
An effect on the world persists: the world flows from the left alternative into
the right one, also when the left one has no answer.  Its `lower_exact` compiles
a region to flat code with an undo trail, exactly.

The committed run of a region of this development is that semantics, with every
step read as a guarded effect on the world and the readout of a leaf held in the
binding store:

* `Region.toSearch` and `searchSemantics` give the reading;
* `Region.committed_eq_source`: the committed run is
  `TransactionalSearchCode.source` of the region read so;
* `Region.committed_compiled`: so the committed run is what the compiled flat
  code computes: the answers it emits, the world it leaves, and the binding
  store restored.

The other mode has no counterpart there: the binding store of a search region is
restored and never published, and its world is never isolated.
`SearchRegions.branchLocal_is_not_source` is the instance in which the two
differ.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines

universe u

variable {Location Value Answer : Type u} [DecidableEq Location] [Zero Value] [Add Value]
  [SepAlgebra Value]

/-- **A region read as a search region of the flat code.**  A step is a guard
that it can fire, followed by the effect of firing it on the world.  A leaf
binds its readout in the one slot of the binding store and answers. -/
def Region.toSearch : Region Location Value Answer →
    TransactionalSearchCode.Region Unit (Readout Location Value Answer)
      (Step Location Value) (Step Location Value)
  | .fail => .fail
  | .answer readout => .write () readout .answer
  | .step first rest => .guard first (.perform first rest.toSearch)
  | .orElse left right => .choice left.toSearch right.toSearch

/-- The reading of the tests, the effects and the observation: a step is tested
by whether it fires on the world and performed by firing it; the answer is read
from the world by the readout the leaf bound. -/
def searchSemantics :
    TransactionalSearchCode.Semantics Unit (Readout Location Value Answer)
      (Step Location Value) (Step Location Value) (Location → Value) Answer where
  test step _ world := (step.fire world).isSome
  effect step world := (step.fire world).getD world
  observe bindings world := (bindings ()).value world

/-- **The committed run is the semantics of the search region**: the same
answers in the same order and the same world, whatever the binding store holds
on entry. -/
theorem Region.committed_eq_source (region : Region Location Value Answer)
    (bindings : Unit → Readout Location Value Answer) (world : Location → Value) :
    TransactionalSearchCode.source searchSemantics region.toSearch bindings world =
      region.committed world := by
  induction region generalizing bindings world with
  | fail => rfl
  | answer readout =>
      simp [Region.toSearch, TransactionalSearchCode.source, searchSemantics, Region.committed]
  | step first rest ih =>
      cases fired : first.fire world with
      | none =>
          have tested : searchSemantics.test first bindings world = false := by
            show (first.fire world).isSome = false
            rw [fired]
            rfl
          simp only [Region.toSearch, TransactionalSearchCode.source, Region.committed, tested,
            fired]
          rfl
      | some next =>
          have tested : searchSemantics.test first bindings world = true := by
            show (first.fire world).isSome = true
            rw [fired]
            rfl
          have performed :
              (searchSemantics (Answer := Answer)).effect first world = next := by
            show (first.fire world).getD world = next
            rw [fired]
            rfl
          simp only [Region.toSearch, TransactionalSearchCode.source, Region.committed, tested,
            performed, fired, if_true]
          exact ih bindings next
  | orElse left right ihLeft ihRight =>
      simp only [Region.toSearch, TransactionalSearchCode.source, Region.committed, ihLeft,
        ihRight]

/-- **The committed run is what the compiled flat code computes**: it emits the
answers of the committed run, leaves its world, and restores the binding store. -/
theorem Region.committed_compiled (region : Region Location Value Answer)
    (bindings : Unit → Readout Location Value Answer) (world : Location → Value) :
    (TransactionalSearchCode.execute searchSemantics
        (TransactionalSearchCode.lower region.toSearch) ⟨bindings, [], world, [], 0⟩).emitted =
        (region.committed world).1 ∧
      (TransactionalSearchCode.execute searchSemantics
        (TransactionalSearchCode.lower region.toSearch) ⟨bindings, [], world, [], 0⟩).world =
        (region.committed world).2 ∧
      (TransactionalSearchCode.execute searchSemantics
        (TransactionalSearchCode.lower region.toSearch) ⟨bindings, [], world, [], 0⟩).bindings =
        bindings := by
  rw [TransactionalSearchCode.lower_exact searchSemantics region.toSearch _ rfl,
    Region.committed_eq_source]
  exact ⟨List.nil_append _, rfl, rfl⟩

/-! ## Controls -/

namespace SearchRegions

open SharedSpace

/-- **Positive**: the two siblings that add an atom to one space and read it, as
a search region, give the answers of the committed run. -/
theorem source_of_siblings :
    (TransactionalSearchCode.source searchSemantics
        (Region.alternatives [sibling .a, sibling .b]).toSearch
        (fun _ => Readout.valueAt ()) empty).1 = [{.a}, {.a, .b}] := by
  rw [Region.committed_eq_source]
  exact committed_answers.1

/-- **Negative**: the branch-local run of the same siblings does not give the
answers of the search region: there each sibling reads its own atom only. -/
theorem branchLocal_is_not_source :
    ((Region.alternatives [sibling .a, sibling .b]).branchLocal empty).map Prod.fst ≠
      (TransactionalSearchCode.source searchSemantics
        (Region.alternatives [sibling .a, sibling .b]).toSearch
        (fun _ => Readout.valueAt ()) empty).1 := by
  rw [Region.committed_eq_source, committed_answers.1, branchLocal_answers.1]
  decide

end SearchRegions

#print axioms Region.committed_eq_source
#print axioms Region.committed_compiled
#print axioms SearchRegions.source_of_siblings
#print axioms SearchRegions.branchLocal_is_not_source

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
