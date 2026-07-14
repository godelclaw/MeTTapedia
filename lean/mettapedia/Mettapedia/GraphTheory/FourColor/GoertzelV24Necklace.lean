import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24Necklace

/-- In the canonical locked word, the blue/purple pair has exactly the two
singleton-color stubs `2` and `4` as its active support. -/
theorem cap5BadBoundaryWord2111_activeSupport_blue_purple :
    cap5ActiveSupport blue purple cap5BadBoundaryWord2111 =
      ({2, 4} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5ActiveSupport, cap5BadBoundaryWord2111, red, blue, purple]

/-- The five endpoint pairs in the locked-pentagon necklace. -/
def canonicalNecklaceSupports : Finset (Finset (Fin 5)) :=
  {{0, 3}, {1, 2}, {0, 4}, {1, 3}, {2, 4}}

/-- Number of necklace strands incident to a cap stub. -/
def necklaceIncidenceCount (i : Fin 5) : Nat :=
  (canonicalNecklaceSupports.filter fun support ↦ i ∈ support).card

/-- Endpoint graph of the five necklace strands. -/
def necklaceEndpointGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun i j ↦
    ({i, j} : Finset (Fin 5)) ∈ canonicalNecklaceSupports

theorem canonicalNecklaceSupports_card : canonicalNecklaceSupports.card = 5 := by
  decide

theorem canonicalNecklaceSupports_each_card_two :
    ∀ support ∈ canonicalNecklaceSupports, support.card = 2 := by
  decide

/-- Every cap spoke lies on exactly two of the five strands. -/
theorem necklaceIncidenceCount_eq_two (i : Fin 5) :
    necklaceIncidenceCount i = 2 := by
  fin_cases i <;> decide

/-- The endpoint graph spells the manuscript's closed necklace chain. -/
theorem necklaceEndpointGraph_closed_chain :
    necklaceEndpointGraph.Adj 0 4 ∧
    necklaceEndpointGraph.Adj 4 2 ∧
    necklaceEndpointGraph.Adj 2 1 ∧
    necklaceEndpointGraph.Adj 1 3 ∧
    necklaceEndpointGraph.Adj 3 0 := by
  unfold necklaceEndpointGraph canonicalNecklaceSupports
  decide

/-- The five strands form one connected endpoint union. -/
theorem necklaceEndpointGraph_connected : necklaceEndpointGraph.Connected := by
  unfold necklaceEndpointGraph canonicalNecklaceSupports
  decide

/-- Exceptional CAP5 component pairings, together with the forced
blue/purple singleton strand, are exactly the five necklace supports. The
component slots may occur in either order. -/
theorem necklaceSupports_eq_canonical_of_isExceptional
    (p : CAP5BadPairingSupports) (h : p.IsExceptional) :
    ({p.redBlue₁, p.redBlue₂, p.redPurple₁, p.redPurple₂,
        ({2, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) =
      canonicalNecklaceSupports := by
  rcases h with ⟨hredBlue, hredPurple⟩
  rcases hredBlue with hredBlue | hredBlue <;>
    rcases hredBlue with ⟨hredBlue₁, hredBlue₂⟩ <;>
    rcases hredPurple with hredPurple | hredPurple <;>
    rcases hredPurple with ⟨hredPurple₁, hredPurple₂⟩ <;>
    simp [hredBlue₁, hredBlue₂, hredPurple₁, hredPurple₂,
      canonicalNecklaceSupports] <;> decide

/-- Endpoint form of the Necklace Lemma from the component-cover interface:
if no immediate support switch repairs the locked word, the five recorded
component supports have the canonical necklace incidence. A graph-level
strand extraction must separately show that these supports come from the
corresponding connected Kempe strands. -/
theorem necklaceSupports_eq_canonical_of_componentCovers_of_not_hasRepair
    (p : CAP5BadPairingSupports) (hcovers : p.HasComponentCovers)
    (hlocked : ¬ p.HasRepair) :
    ({p.redBlue₁, p.redBlue₂, p.redPurple₁, p.redPurple₂,
        ({2, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) =
      canonicalNecklaceSupports := by
  apply necklaceSupports_eq_canonical_of_isExceptional p
  exact (CAP5BadPairingSupports.isExceptional_iff_not_hasRepair_of_componentCovers
    hcovers).2 hlocked

end GoertzelV24Necklace

end Mettapedia.GraphTheory.FourColor
