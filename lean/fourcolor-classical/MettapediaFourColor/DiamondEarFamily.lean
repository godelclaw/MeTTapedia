import MettapediaFourColor.BoundaryEarGSLT
import MettapediaFourColor.DiamondJointRepair
import MettapediaFourColor.DiamondSplitRepair

/-!
# Three diamond cores, unbounded ear families

Every finite ear route from configurations 1, 2 or 4 inherits its core's
boundary repair. The same transfer proof handles all routes and reconstructs
actual colourings and their GSLT histories. The core arguments remain distinct:
configuration 2 supplies a retained base, configuration 1 uses split transfer,
and configuration 4 uses coupled repair. No additional catalogue certificate
is removed by this contextual family theorem.
-/

namespace FourColor.DiamondEarFamily

open Color DiamondConfigurations KempeBoundarySplit BoundaryEarGSLT
open Mettapedia.GSLT.Ultrainfinite

inductive Core | one | two | four

def core : Core → Object
  | .one => ⟨Fin 10, graph001, 4, 5, [0, 1, 2, 3], by decide +kernel⟩
  | .two => ⟨Fin 11, graph002, 0, 1, [2, 3, 4, 5, 6], by decide +kernel⟩
  | .four => ⟨Fin 12, graph004, 4, 5, [6, 7, 0, 1, 2, 3], by decide +kernel⟩

instance (c : Core) : Finite (core c).Vertex := by
  cases c <;> dsimp [core] <;> infer_instance

/-- Keep the stronger D-repair inputs for the first two cores and the joint
contract for the third. The coupling is never weakened to separate sides. -/
def Seed : Core → List Color → Prop
  | .one, et => et.length = 6 ∧ (0 : Color) ∉ et ∧ et.sum = 0
  | .two, et => et.length = 7 ∧ (0 : Color) ∉ et ∧ et.sum = 0
  | .four, et =>
      (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et

theorem seed_inhabited (c : Core) :
    ∃ et, Seed c et ∧ et ≠ [] ∧ (0 : Color) ∉ et := by
  cases c with
  | one => exact ⟨[c1, c1, c1, c1, c1, c1], by dsimp [Seed]; decide +kernel⟩
  | two => exact ⟨[c1, c2, c3, c1, c1, c1, c1], by dsimp [Seed]; decide +kernel⟩
  | four =>
    refine ⟨trace [c0, c2, c0, c2, c1, c2, c1, c2], ?_,
      by decide +kernel, by decide +kernel⟩
    exact (DiamondJointContract.contractTrace_iff _).mpr
      ⟨c0, c1, c2, c2, c2, c2, by decide +kernel, rfl⟩

theorem input_inhabited (c : Core) {target : Object} (route : Route Step (core c) target) :
    ∃ et, Input route (Seed c) et := by
  obtain ⟨et, h, _, _⟩ := BoundaryEarGSLT.input_inhabited route (seed_inhabited c)
  exact ⟨et, h⟩

theorem base (c : Core) (et : List Color) (start : Seed c et) :
    KempeCoclosure (GraphTrace (core c).graph (core c).boundary) et := by
  intro Q closed outside
  cases c with
  | one =>
    obtain ⟨t, ht, hQ⟩ := DiamondSplitRepair.transferred_repair et
      start.1 start.2.1 start.2.2 Q closed outside
    exact ⟨t, (reducibilityTrace001 _).mp ht, hQ⟩
  | two =>
    obtain ⟨t, ht, hQ⟩ := DiamondSplitRepair.base_repair et
      start.1 start.2.1 start.2.2 Q closed outside
    exact ⟨t, (reducibilityTrace002 _).mp ht, hQ⟩
  | four =>
    obtain ⟨t, ht, hQ⟩ := DiamondJointRepair.contract_repair et start Q closed outside
    exact ⟨t, (reducibilityTrace004 _).mp ht, hQ⟩

/-- One contextual law handles every member; no new finite repair check per ear. -/
theorem repair (c : Core) {target : Object} (route : Route Step (core c) target)
    (et : List Color) (start : Input route (Seed c) et) :
    KempeCoclosure (GraphTrace target.graph target.boundary) et :=
  BoundaryEarGSLT.repair route (base c) et start

/-- The selected compatible colouring comes with every intermediate witness. -/
theorem compatible_history (c : Core) {target : Object} (route : Route Step (core c) target)
    {Q : List Color → Prop} (et : List Color) (start : Input route (Seed c) et)
    (closed : KempeClosed Q) (outside : Q et) :
    ∃ k : target.graph.Coloring Color, ∃ initial : (core c).graph.Coloring Color,
      Q (trace (target.boundary.map k)) ∧ semantics.Supports route initial k :=
  repair_with_history route (base c) et start closed outside

/-- Each core generates genuine graphs with arbitrarily many additional vertices. -/
theorem arbitrary_size (c : Core) (n : ℕ) :
    Nat.card (iterate (core c) n).1.Vertex = Nat.card (core c).Vertex + n := by
  rw [BoundaryEarGSLT.size (iterate (core c) n).2 inferInstance, iterate_length]

end FourColor.DiamondEarFamily
