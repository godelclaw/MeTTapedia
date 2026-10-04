import MettapediaFourColor.BoundaryFanRepair
import MettapediaFourColor.BoundaryRepairTransport
import MettapediaFourColor.TriangleStripAnchors

/-!
# Two exact parent interfaces of the six-triangle source

Each end of D0099 is obtained from its exact parent by the same fan
operation. The checked graph isomorphisms retain every edge and the ordered
boundary. A successful parent repair transfers to D0099 against the same
exterior. A parent repair is an explicit input; neither parent is asserted
to have a complete repair. Internal graph shape alone does not identify
either parent with D0092.
-/

namespace FourColor.StripParentFan

open SimpleGraph Color KempeBoundarySplit KempeBoundaryFan BoundaryFanRepair
open TriangleStripAnchors

/-- False selects the end at source vertex 12, true the end at vertex 19. -/
def image : Bool → Fin 18 → Fin 19
  | false => ![0,1,2,3,4,5,6,11,8,9,10,12,13,14,15,16,17,18]
  | true => ![18,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]

def omitted (side : Bool) : Fin 19 := if side then 0 else 7
def left (side : Bool) : Fin 18 := if side then 10 else 6
def middle (side : Bool) : Fin 18 := if side then 0 else 7
def right (side : Bool) : Fin 18 := if side then 1 else 8
def rest : Bool → List (Fin 18)
  | false => [9,10,0,1,2,3,4,5]
  | true => [2,3,4,5,6,7,8,9]
def shift (side : Bool) : ℕ := if side then 10 else 6

def parent (side : Bool) := input0099.graph.comap (image side)

instance (side : Bool) : DecidableRel (parent side).Adj := by
  intro u v
  change Decidable (input0099.graph.Adj _ _)
  infer_instance

instance (side : Bool) : DecidableRel
    (grow (parent side) (left side) (middle side) (right side)).Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [grow] <;> infer_instance

def point (side : Bool) : Option (Fin 18) → Fin 19 :=
  fun v => v.elim (omitted side) (image side)

theorem bijective : ∀ side, Function.Bijective (point side) := by decide +kernel

/-- Both constructions agree with the entire source graph, including all ports. -/
noncomputable def sourceIso (side : Bool) :
    grow (parent side) (left side) (middle side) (right side) ≃g input0099.graph where
  toEquiv := Equiv.ofBijective (point side) (bijective side)
  map_rel_iff' := by
    have checked : ∀ s x y, input0099.graph.Adj (point s x) (point s y) ↔
        (grow (parent s) (left s) (middle s) (right s)).Adj x y := by decide +kernel
    exact checked side

theorem path_edges : ∀ side,
    (parent side).Adj (left side) (middle side) ∧
    (parent side).Adj (middle side) (right side) := by decide +kernel

theorem boundary : ∀ side,
    (newPorts (left side) (right side) (rest side)).map (sourceIso side) =
      input0099.boundary.rotate (shift side) := by decide +kernel

theorem parent_boundary : ∀ side,
    oldPorts (left side) (middle side) (right side) (rest side) =
      ((List.finRange 11).map (fun x => x.castAdd 7)).rotate (shift side) := by decide +kernel

/-- Exact source semantics of the composed fan operation at either end. -/
theorem source_trace (side : Bool) (et : List Color) :
    GraphTrace input0099.graph (input0099.boundary.rotate (shift side)) et ↔
      Fan (GraphTrace (parent side)
        (oldPorts (left side) (middle side) (right side) (rest side))) et := by
  rw [← boundary side, ← BoundaryRepairTransport.trace_iff]
  exact trace_exact _ _ _ _ _ (path_edges side).1 (path_edges side).2 et

/-- Parent strategies compose into genuine D0099 colourings with the same
exterior predicate. This does not supply those parent strategies. -/
theorem source_repair (side : Bool) {a b c d : Color} (t : List Color)
    (rel : Related a b c d)
    (old : KempeCoclosure (GraphTrace (parent side)
      (oldPorts (left side) (middle side) (right side) (rest side))) (c :: d :: t)) :
    KempeCoclosure (GraphTrace input0099.graph
      (input0099.boundary.rotate (shift side))) (a :: b :: t) :=
  KempeBoundaryFan.repair (fun a b c d t h hp =>
    (source_trace side _).mpr ⟨a,b,c,d,t,rfl,h,hp⟩) t rel old

end FourColor.StripParentFan
