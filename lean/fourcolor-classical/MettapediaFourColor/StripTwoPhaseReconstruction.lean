import MettapediaFourColor.StripTwoPhaseProgress
import MettapediaFourColor.GraphTraceAlignment
import MettapediaFourColor.StripPhaseDisk

/-!
# Compatible actual witnesses after two-stage partial progress

The exterior graph is retained. Its closure yields a new exterior colouring
whose entire boundary agrees with one colouring of the source minus one
core vertex. The concrete planar disk discharges the closure premise.
This is existential reconstruction, not a bound on physical recolouring
history length and not restoration of the last hole.
-/

namespace FourColor.StripTwoPhaseProgress

open Color SimpleGraph TriangleStripAnchors StripResponseSummary
open StripPartialColouring KempeBoundarySplit

/-- Seven source vertices and the same exterior have compatible colourings.
No favourable exterior or partial source witness is supplied as a premise. -/
theorem compatible {V : Type*} (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (GraphTrace H (List.ofFn ports))) (s : Fin 4)
    (initial : GraphTrace H (List.ofFn ports) (List.ofFn (source (s.natAdd 5)))) :
    ∃ h : Fin 8, ∃ D : H.Coloring Color,
      ∃ k : (input0099.graph.induce {v | Live {h} v}).Coloring Color,
        ∀ i, k ⟨port i,live_port {h} i⟩ = D (ports i) := by
  obtain ⟨et,ht,D,hD⟩ := progress s _ closed initial
  obtain ⟨h,b,k,hb,hk⟩ := StripPuncturedExtension.reconstruct ht
  let ps (i : Fin 11) : {v : Fin 19 // Live {h} v} := ⟨port i,live_port {h} i⟩
  have same : trace ((List.ofFn ps).map k) = trace ((List.ofFn ports).map D) := by
    simpa only [List.map_ofFn, Function.comp_def, ps, hk] using hb.trans hD
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align (List.ofFn ps) k
    ((List.ofFn ports).map D) (by simp) same
  have pointwise : (fun i => aligned (ps i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [List.map_ofFn, Function.comp_def] using ha)
  exact ⟨h,D,aligned,fun i => congrFun pointwise i⟩

/-- The previously certified planar disk has the first hard input. -/
theorem disk_input : GraphTrace StripPhaseObstruction.exterior
    (List.ofFn StripPhaseObstruction.ports) (List.ofFn (source (5 : Fin 9))) :=
  ⟨StripPhaseObstruction.state 0, by decide +kernel⟩

/-- This consumer obtains the exterior closure from its planar rotation. -/
theorem disk_progress :
    ∃ h : Fin 8, ∃ D : StripPhaseObstruction.exterior.Coloring Color,
      ∃ k : (input0099.graph.induce {v | Live {h} v}).Coloring Color,
        ∀ i, k ⟨port i,live_port {h} i⟩ = D (StripPhaseObstruction.ports i) :=
  compatible _ _ StripPhaseDisk.closed 0 disk_input

end FourColor.StripTwoPhaseProgress
