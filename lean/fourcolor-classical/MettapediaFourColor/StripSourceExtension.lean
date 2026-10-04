import MettapediaFourColor.StripResponseSummary

/-!
# Reconstruction from symbolic source relations

The boundary remains an argument of every elimination relation. A proper
boundary and an inhabited terminal relation reconstruct a colouring of the
entire decoded D0099 graph. The same theorem applies after boundary updates.
-/

namespace FourColor.StripSourceExtension

open Color TriangleStripAnchors StripResponseSummary

def ProperBoundary (b : Boundary) : Prop :=
  ∀ i j, input0099.graph.Adj (port i) (port j) → b i ≠ b j

instance (b : Boundary) : Decidable (ProperBoundary b) := by
  unfold ProperBoundary
  infer_instance

def completeColour (b : Boundary) (f : Fin 8 → Color) : Fin 19 → Color :=
  fun v => Fin.addCases (m := 11) (n := 8) (motive := fun _ => Color) b f v

@[simp] theorem colour_port (b : Boundary) (f : Fin 8 → Color) (i : Fin 11) :
    completeColour b f (port i) = b i := by
  change Fin.addCases b f (Fin.castAdd 8 i) = b i
  simp

@[simp] theorem colour_core (b : Boundary) (f : Fin 8 → Color) (i : Fin 8) :
    completeColour b f (vertex0099 i) = f i := by
  change Fin.addCases b f (Fin.natAdd 11 i) = f i
  simp

/-- Reconstruction checks all four classes of source incidences. -/
theorem complete_valid (b : Boundary) (f : Fin 8 → Color)
    (hb : ProperBoundary b) (hf : ValidCore b f) :
    ∀ u v, input0099.graph.Adj u v → completeColour b f u ≠ completeColour b f v := by
  intro u
  refine Fin.addCases (m := 11) (n := 8)
    (motive := fun u => ∀ v, input0099.graph.Adj u v →
      completeColour b f u ≠ completeColour b f v) (fun i => ?_) (fun i => ?_) u
  · intro v
    refine Fin.addCases (m := 11) (n := 8)
      (motive := fun v => input0099.graph.Adj (port i) v →
        completeColour b f (port i) ≠ completeColour b f v) (fun j => ?_) (fun j => ?_) v
    · intro h
      change completeColour b f (port i) ≠ completeColour b f (port j)
      simpa only [colour_port] using hb i j h
    · intro h
      change completeColour b f (port i) ≠ completeColour b f (vertex0099 j)
      simpa only [colour_port, colour_core] using
        (hf.1 j i ((attachments_complete j i).mp h.symm)).symm
  · intro v
    refine Fin.addCases (m := 11) (n := 8)
      (motive := fun v => input0099.graph.Adj (vertex0099 i) v →
        completeColour b f (vertex0099 i) ≠ completeColour b f v) (fun j => ?_) (fun j => ?_) v
    · intro h
      change completeColour b f (vertex0099 i) ≠ completeColour b f (port j)
      simpa only [colour_port, colour_core] using
        hf.1 i j ((attachments_complete i j).mp h)
    · intro h
      change completeColour b f (vertex0099 i) ≠ completeColour b f (vertex0099 j)
      rw [colour_core, colour_core]
      rcases (edges_complete i j).mp h with he | he
      · exact hf.2 (i,j) he
      · exact (hf.2 (j,i) he).symm

def colouring (b : Boundary) (f : Fin 8 → Color)
    (hb : ProperBoundary b) (hf : ValidCore b f) : input0099.graph.Coloring Color :=
  .mk (completeColour b f) (fun h => complete_valid b f hb hf _ _ h)

/-- Symbolic elimination supplies a complete source witness, without a
precomputed table of interior colourings. -/
theorem graphTrace (b : Boundary) (hb : ProperBoundary b) (h : ∃ a c, r5 b a c) :
    KempeBoundarySplit.GraphTrace input0099.graph input0099.boundary
      (trace (List.ofFn b)) := by
  obtain ⟨f, hf⟩ := (terminal_iff b).mp h
  refine ⟨colouring b f hb hf, ?_⟩
  have eq : input0099.boundary.map (colouring b f hb hf) = List.ofFn b := by
    change (List.finRange 11).map (fun i => completeColour b f (port i)) = _
    simp only [colour_port, ← List.ofFn_eq_map]
  rw [eq]

theorem terminal_iff_graphTrace (b : Boundary) (hb : ProperBoundary b) :
    (∃ a c, r5 b a c) ↔ KempeBoundarySplit.GraphTrace input0099.graph
      input0099.boundary (trace (List.ofFn b)) := by
  exact ⟨graphTrace b hb, fun h => Classical.byContradiction (fun hn => no_trace b hn h)⟩

end FourColor.StripSourceExtension
