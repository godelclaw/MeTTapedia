import Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport

/-!
# Broad finite-round premise discovery

Expand every supplied outgoing neighbour before applying a ranking view.
Increasing the round count expands the discovered pool; it need not improve
every score or the final top-k recall. A needed premise outside the supplied
graph cannot be recovered by changing its ranking. Zero rounds retains the
seed premises. These sets describe discovery, not permission to read a source.
-/

noncomputable section

namespace Mettapedia.CognitiveArchitecture.Attention.PremiseActivation

open Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport
open scoped Classical

variable {ι : Type*} [Fintype ι]

def pool (P : Kernel ι) (seed : Set ι) (rounds : ℕ) : Finset ι :=
  Finset.univ.filter fun i => i ∈ reachable P seed rounds

@[simp] theorem mem_pool (P : Kernel ι) (seed : Set ι) (n : ℕ) (i : ι) :
    i ∈ pool P seed n ↔ i ∈ reachable P seed n := by simp [pool]

theorem zero_rounds (P : Kernel ι) (seed : Set ι) :
    pool P seed 0 = Finset.univ.filter (fun i => i ∈ seed) := rfl

theorem pool_mono (P : Kernel ι) (seed : Set ι) (n : ℕ) :
    pool P seed n ⊆ pool P seed (n + 1) := by
  intro i hi
  exact (mem_pool _ _ _ _).mpr (reachable_mono P seed n ((mem_pool _ _ _ _).mp hi))

theorem seeds_retained (P : Kernel ι) (seed : Set ι) (n : ℕ) :
    ∀ i ∈ seed, i ∈ pool P seed n := by
  induction n with
  | zero => intro i hi; exact (mem_pool P seed 0 i).mpr hi
  | succ n ih => intro i hi; exact pool_mono P seed n (ih i hi)

/-- Coverage is conditional on the dependencies being reachable in this graph.
It is not a proof that learned associations discover the right dependencies. -/
theorem covers_reachable_dependencies (P : Kernel ι) (seed : Set ι) (n : ℕ)
    (dependencies : Finset ι) (h : ∀ i ∈ dependencies, i ∈ reachable P seed n) :
    dependencies ⊆ pool P seed n := by
  intro i hi
  exact (mem_pool _ _ _ _).mpr (h i hi)

/-- The score view cannot introduce an unobserved premise. All raw sources
remain outside this selector's representation and ownership. -/
def rankedView (P : Kernel ι) (seed : Set ι) (n : ℕ) (keep : ι → Bool) : Finset ι :=
  (pool P seed n).filter fun i => keep i = true

theorem rankedView_subset (P : Kernel ι) (seed : Set ι) (n : ℕ) (keep : ι → Bool) :
    rankedView P seed n keep ⊆ pool P seed n := Finset.filter_subset _ _

/-- If a premise is absent from discovery, every ranking of that pool misses it. -/
theorem ranking_cannot_recover_missing (P : Kernel ι) (seed : Set ι) (n : ℕ)
    (keep : ι → Bool) (i : ι) (hi : i ∉ pool P seed n) :
    i ∉ rankedView P seed n keep := fun h => hi (rankedView_subset P seed n keep h)

end Mettapedia.CognitiveArchitecture.Attention.PremiseActivation
