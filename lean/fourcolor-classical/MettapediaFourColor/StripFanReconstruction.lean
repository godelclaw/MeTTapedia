import MettapediaFourColor.StripFanProgram
import MettapediaFourColor.StripPhaseDisk

/-!
# Compatible seven-vertex source reconstruction

The insertion program retains every edge of D0099 except those incident
with core vertex 2. Its whole-graph colouring restricts to the original
exterior and reconstructs the actual induced source on seven core vertices.
No initial boundary pattern or shared-palette condition is required.
The remaining degree-seven vertex and geometric supply remain open.
-/

namespace FourColor.StripFanReconstruction

open Color KempeBoundarySplit StripResponseSummary StripSourceExtension
open StripPartialColouring TriangleStripAnchors StripFanProgram

variable {V : Type*} (H : SimpleGraph V) (p : Fin 11 → V)

abbrev Carrier (V : Type*) := Option (Option (Option (Option (Option (Option (Option (V)))))))
def old (v : V) : Carrier V := some (some (some (some (some (some (some (v)))))))
def core : Fin 8 → Carrier V := ![some (some (some (some (some (some (none)))))),some (some (some (some (none)))),none,some (some (some (some (some (none))))),none,some (some (none)),some (none),some (some (some (none)))]

theorem old_adj (u v : V) : (graph7 H p).Adj (old u) (old v) ↔ H.Adj u v := Iff.rfl

def restrict (D : (graph7 H p).Coloring Color) : H.Coloring Color :=
  .mk (fun v => D (old v)) (fun h => D.valid ((old_adj H p _ _).mpr h))

theorem attachment_adj : ∀ (v : Fin 8) (i : Fin 11), v ≠ 2 → i ∈ attachments v →
    (graph7 H p).Adj (core v) (old (p i)) := by
  intro v i hv hi
  fin_cases v <;> fin_cases i <;> simp [attachments] at hv hi
  all_goals simp [graph1, graph2, graph3, graph4, graph5, graph6, graph7,
    core, old, BoundaryFanRepair.grow, BoundaryFourFanRepair.grow]

theorem core_adj : ∀ e ∈ edges, e.1 ≠ 2 → e.2 ≠ 2 →
    (graph7 H p).Adj (core e.1) (core e.2) := by
  intro e he
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [graph1,graph2,graph3,graph4,graph5,graph6,graph7,core,old,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]

def omitted : Finset (Fin 8) := {2}
abbrev Source := input0099.graph.induce {v | Live omitted v}
def sourcePort (i : Fin 11) : {v : Fin 19 // Live omitted v} := ⟨port i,live_port omitted i⟩

/-- Every retained source edge is checked against the actual constructed graph. -/
theorem reconstruct
    (embedding : ∀ i j, input0099.graph.Adj (port i) (port j) → H.Adj (p i) (p j))
    (D : (graph7 H p).Coloring Color) :
    ∃ k : Source.Coloring Color, ∀ i, k (sourcePort i) = restrict H p D (p i) := by
  let b : Boundary := fun i => restrict H p D (p i)
  let f : Fin 8 → Color := fun v => D (core v)
  have proper : ProperBoundary b := fun i j he => (restrict H p D).valid (embedding i j he)
  have valid : ValidExcept b omitted f := by
    constructor
    · intro v hv i hi
      exact D.valid (attachment_adj H p v i (by simpa [omitted] using hv) hi)
    · intro e he h1 h2
      exact D.valid (core_adj H p e he (by simpa [omitted] using h1) (by simpa [omitted] using h2))
  let k : Source.Coloring Color := .mk (fun v => completeColour b f v.val)
    (fun {u v} he => partial_valid b omitted f proper valid u.val v.val u.property v.property he)
  exact ⟨k,fun i => colour_port b f i⟩

/-- One construction restores all seven vertices for every compatible
Kempe-closed exterior. The ordered boundary may contain repeated ports. -/
theorem compatible
    (embedding : ∀ i j, input0099.graph.Adj (port i) (port j) → H.Adj (p i) (p j))
    (closed : KempeClosed (GraphTrace H (List.ofFn p))) (C : H.Coloring Color) :
    ∃ D : H.Coloring Color, ∃ k : Source.Coloring Color,
      ∀ i, k (sourcePort i) = D (p i) := by
  have initial : KempeClosed (GraphTrace H (ring0 p)) := by
    simpa [ring0,List.ofFn_succ] using closed
  obtain ⟨D⟩ := StripFanProgram.colourable H p embedding initial C
  obtain ⟨k,hk⟩ := reconstruct H p embedding D
  exact ⟨restrict H p D,k,hk⟩

section Geometry

open SimpleGraph PatchDisk PatchDisk.Reading PatchDiskSources
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation ExceptionalOverlap

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}

/-- An actual spherical source reading supplies the closure used by all
seven insertions. No condition on the starting boundary colours is added. -/
theorem from_reading (r : Reading d0099 data)
    (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (ambient : (SimpleGraphBridge.rotationHypermap data).Planar)
    (C : (G.induce (keep r)).Coloring Color) :
    ∃ D : (G.induce (keep r)).Coloring Color, ∃ k : Source.Coloring Color,
      ∀ i, k (sourcePort i) = D (PatchDisk.Reading.port r i) := by
  exact compatible _ (PatchDisk.Reading.port r)
    (fun _ _ edge => r.hom.map_rel edge)
    (r.exterior_closed tri cyclic conn ambient) C

/-- The previously certified planar disk is a concrete consumer. -/
theorem disk_consumer :
    ∃ D : StripPhaseObstruction.exterior.Coloring Color, ∃ k : Source.Coloring Color,
      ∀ i, k (sourcePort i) = D (StripPhaseObstruction.ports i) := by
  exact compatible _ StripPhaseObstruction.ports (by decide +kernel)
    StripPhaseDisk.closed (StripPhaseObstruction.state 0)

end Geometry

end FourColor.StripFanReconstruction
