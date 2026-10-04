import MettapediaFourColor.StripPartialColouring

/-!
# The retained source path has connected fixed-boundary Kempe fibres

The partial source has five hidden vertices in a path. The existing forest
fibre theorem connects any two of its proper colourings with the same
boundary by actual Kempe moves avoiding that boundary. Greedy choices need
not be frozen during the subsequent coupled restoration.
-/

namespace FourColor.StripSpineFibre

open SimpleGraph Relation StripPartialColouring StripResponseSummary TriangleStripAnchors

instance (h : Finset (Fin 8)) (v : Fin 19) : Decidable (Live h v) := by
  refine Fin.addCases (m := 11) (n := 8)
    (motive := fun v => Decidable (Live h v)) (fun i => ?_) (fun i => ?_) v
  · exact isTrue (live_port h i)
  · exact decidable_of_iff (i ∉ h) (live_core h i).symm

abbrev Retained := {v : Fin 19 // Live holes v}
abbrev graph := input0099.graph.induce {v | Live holes v}
def hidden : Set Retained := {v | 11 ≤ v.val.val}

def rank (v : Fin 19) : ℕ :=
  if v = 14 then 0 else if v = 12 then 1 else
  if v = 15 then 2 else if v = 17 then 3 else 4

theorem rank_injective : ∀ u v : Fin 19,
    Live holes u → Live holes v → 11 ≤ u.val → 11 ≤ v.val → rank u = rank v → u = v :=
  by decide +kernel

theorem unique_later : ∀ u v w : Fin 19,
    Live holes u → Live holes v → Live holes w →
    11 ≤ u.val → 11 ≤ v.val → 11 ≤ w.val →
    input0099.graph.Adj u v → input0099.graph.Adj u w →
    rank u < rank v → rank u < rank w → v = w := by decide +kernel

/-- Acyclicity follows from the exact source edges, not from a patch drawing. -/
theorem hidden_forest : (graph.induce hidden).IsAcyclic := by
  apply KempeTriangleAnchors.acyclic_of_unique_later (fun v => rank v.val.val)
  · intro u v h
    exact Subtype.ext (Subtype.ext (rank_injective _ _ u.val.property v.val.property
      u.property v.property h))
  · intro u v w huv huw hv hw
    exact Subtype.ext (Subtype.ext (unique_later _ _ _
      u.val.property v.val.property w.val.property u.property v.property w.property huv huw hv hw))

/-- The entire boundary is fixed by every Kempe move in the supplied history. -/
theorem fibres_connected (C D : graph.Coloring Color)
    (agree : ∀ i, C ⟨port i, live_port holes i⟩ = D ⟨port i, live_port holes i⟩) :
    ReflTransGen (graph.KempeStepAvoiding hiddenᶜ) C D := by
  apply KempeForestFibre.fibre_path hidden hidden_forest C D
  intro x hx
  have small : x.val.val < 11 := Nat.lt_of_not_le hx
  let i : Fin 11 := ⟨x.val.val,small⟩
  have eq : x = ⟨port i, live_port holes i⟩ := Subtype.ext (Fin.ext rfl)
  simpa only [eq] using agree i

/-- Any existing partial source witness can reach the canonical greedy one
without changing a boundary colour. This does not assert completion of holes. -/
theorem canonical_reachable (b : Boundary) (hb : StripSourceExtension.ProperBoundary b)
    (C : graph.Coloring Color)
    (agree : ∀ i, C ⟨port i, live_port holes i⟩ = b i) :
    ReflTransGen (graph.KempeStepAvoiding hiddenᶜ) C (sourceSpine b hb) := by
  apply fibres_connected
  intro i
  rw [agree i, sourceSpine_boundary]

end FourColor.StripSpineFibre
