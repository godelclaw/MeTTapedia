import Mettapedia.CogArch.Attention.ThreeTimescale
import Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport

/-!
# Conservative activation spreading in a three-timescale attention bank

The dynamics use generic finite mass transport. A caller chooses the graph,
spread fraction and round count. STI moves across items while MTI, LTI and
all reserves remain unchanged. Evidence, confidence and proof status are not
attention balances. This is a semantic model, not a command admission policy.
-/

noncomputable section
namespace Mettapedia.CogArch.Attention.Spreading
open Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport
variable {ι : Type*} [Fintype ι]

/-- Update STI only; MTI, LTI and all reserves retain their identities. -/
def spreadBank (P : Kernel ι) (d : ℝ) (b : ThreeTimescale.Bank ι) : ThreeTimescale.Bank ι where
  values i h := match h with
    | .sti => step P d (fun j => b.values j .sti) i
    | .mti => b.values i .mti
    | .lti => b.values i .lti
  reserve := b.reserve

theorem spreadBank_total (P : Kernel ι) (d : ℝ) (b : ThreeTimescale.Bank ι)
    (h : ThreeTimescale.Horizon) : ThreeTimescale.total (spreadBank P d b) h = ThreeTimescale.total b h := by
  cases h with
  | sti =>
    change b.reserve .sti + mass (step P d (fun j => b.values j .sti)) =
      b.reserve .sti + mass (fun j => b.values j .sti)
    rw [step_mass]
  | mti => rfl
  | lti => rfl


end Mettapedia.CogArch.Attention.Spreading
