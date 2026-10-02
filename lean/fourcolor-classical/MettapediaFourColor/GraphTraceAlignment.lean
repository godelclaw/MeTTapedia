import MettapediaFourColor.KempeBoundarySplit
import MettapediaFourColor.PatchWitness

/-! # Aligning genuine graph-colouring witnesses at a shared boundary

Equal edge traces determine all boundary colours up to one global translation.
The translation preserves proper colouring and aligns every port at once,
including repeated ports. This exposes the same alignment used by the
Gonthier--Werner patch construction for ordinary graph-colouring witnesses.
-/

namespace FourColor.GraphTraceAlignment

theorem align {V : Type*} {G : SimpleGraph V} (ports : List V)
    (k : G.Coloring Color) (boundary : List Color)
    (hlen : ports.length = boundary.length)
    (ht : trace (ports.map k) = trace boundary) :
    ∃ aligned : G.Coloring Color, ports.map aligned = boundary := by
  let c := (ports.map k).headD 0 + boundary.headD 0
  let aligned : G.Coloring Color := .mk (fun v => c + k v) (by
    intro v w adj eq
    exact k.valid adj (add_left_cancel eq))
  have he := ringColors_eq_shift (by simpa using hlen) ht
  refine ⟨aligned, ?_⟩
  change ports.map (fun v => c + k v) = boundary
  simpa only [c, List.map_map, Function.comp_def] using he.symm

end FourColor.GraphTraceAlignment
