import Mettapedia.GraphTheory.Kempe.Chain
import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Proof-relevant physical Kempe histories

Saturated-chain certificates are provided by `Kempe.Chain`. Physical
switches compose through the existing proof-relevant GSLT route type.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeChainCertificate

open Mettapedia.GSLT.Ultrainfinite

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- A step retains its colour pair and actual connected component. -/
inductive Step : G.Coloring α → G.Coloring α → Type _ where
  | switch (C : G.Coloring α) (a b : α)
      (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
      Step C (C.swapOnKempeComponent a b K)

/-- Finite physical recolouring histories use the same free route type as
the construction language. There is no bound on their length. -/
abbrev History (C D : G.Coloring α) := Route Step C D

theorem Step.toKempeStep {C D : G.Coloring α} (step : Step C D) : G.KempeStep C D := by
  cases step with
  | switch a b K => exact ⟨a, b, K, rfl⟩

/-- The proof-relevant histories present the existing Kempe closure;
forgetting their step witnesses changes no reachability assertion. -/
theorem nonempty_history_iff {C D : G.Coloring α} :
    Nonempty (History C D) ↔ D ∈ G.KempeClosure C := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | refl => exact .refl
    | cons step rest ih =>
      exact (Relation.ReflTransGen.single step.toKempeStep).trans ih
  · intro h
    induction h with
    | refl => exact ⟨.refl _⟩
    | tail _ step ih =>
      obtain ⟨p⟩ := ih
      obtain ⟨a, b, K, rfl⟩ := step
      exact ⟨p.append (.cons (.switch _ a b K) (.refl _))⟩

/-- A predicate closed under physical switches holds along every history. -/
theorem history_preserves (P : G.Coloring α → Prop)
    (hstep : ∀ C a b K, P C → P (C.swapOnKempeComponent a b K))
    {C D : G.Coloring α} (p : History C D) : P C → P D := by
  induction p with
  | refl => exact id
  | cons step rest ih =>
      cases step with
      | switch a b K => exact fun h => ih (hstep _ a b K h)

end Mettapedia.GraphTheory.FourColor.KempeChainCertificate
