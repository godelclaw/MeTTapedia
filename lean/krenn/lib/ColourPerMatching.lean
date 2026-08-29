import Amplitude
import Mettapedia.Combinatorics.Matching.EdgeColoring

/-! Krenn–Gu specialization of the generic edge-colouring construction. -/

namespace ColourPerMatching

open Amplitude

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three-colour form: such a colouring is a GHZ configuration. -/
theorem isGHZ_of_colouring [Nonempty V] (ec : V → V → Option (Fin 3))
    (hsymm : ∀ u v, ec u v = ec v u)
    (hmono : ∀ σ ∈ pairings V, (∀ x, (ec x (σ x)).isSome) → ∀ x y : V, ∀ k l : Fin 3,
      ec x (σ x) = some k → ec y (σ y) = some l → k = l)
    (huniq : ∀ k : Fin 3,
      ((pairings V).filter (fun σ => ∀ x, ec x (σ x) = some k)).card = 1) :
    KrennGu.IsGHZ (weightOf ec hsymm) := by
  obtain ⟨hone, hzero⟩ := amplitude_spec ec hsymm hmono huniq
  refine ⟨fun k => by rw [hone k]; norm_num, fun c hc => hzero c (fun hconst => hc ?_)⟩
  obtain ⟨x⟩ := ‹Nonempty V›
  exact ⟨c x, fun v => hconst v x⟩

end ColourPerMatching
