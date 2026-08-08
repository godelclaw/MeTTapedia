import Lean.Elab.Tactic.Omega

/-!
# Strand-end arithmetic for a totally closed v24 web

This module isolates the arithmetic in Addendum XXI of the source
manuscript.  A bichromatic strand in the annulus has either two inner ends,
one end on each boundary, or two outer ends.  The five-edge inner interface
contributes ten bichromatic strand-ends; an outer interface with `n` stubs
contributes `2 * n` ends.

Total closure says that every strand is inner-touching, so the outer--outer
count vanishes.  The equations then imply `n <= 5`.  Only after specializing
to `n = 5` do they imply the all-radial anatomy `(0, 10, 0)`.

The structure below records just the strand census and its two endpoint
equations.  A later semantic bridge must derive such a census from the
components of an actual closed web; no graph-theoretic or planar conclusion
is built into this arithmetic layer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebStrandCensus

/-- Endpoint census for the bichromatic strands of a five-edge-inner annular
interface. -/
structure StrandCensus where
  /-- Number of strands with two inner endpoints. -/
  innerInner : Nat
  /-- Number of radial strands, with one endpoint on each boundary. -/
  radial : Nat
  /-- Number of strands with two outer endpoints. -/
  outerOuter : Nat
  /-- Number of outer interface stubs. -/
  outerCount : Nat
  /-- The five inner stubs contribute two bichromatic ends apiece. -/
  inner_end_count : 2 * innerInner + radial = 10
  /-- Every outer stub likewise contributes two bichromatic ends. -/
  outer_end_count : radial + 2 * outerOuter = 2 * outerCount

namespace StrandCensus

/-- Total closure is the arithmetic assertion that no strand can have both
ends only on the outer boundary. -/
def TotallyClosed (census : StrandCensus) : Prop :=
  census.outerOuter = 0

/-- The exact all-radial anatomy observed at the five-stub boundary. -/
def AllRadial (census : StrandCensus) : Prop :=
  census.innerInner = 0 ∧ census.radial = 10 ∧ census.outerOuter = 0

/-- With total closure, every outer strand-end belongs to a radial strand. -/
theorem radial_eq_twice_outerCount (census : StrandCensus)
    (hclosed : census.TotallyClosed) :
    census.radial = 2 * census.outerCount := by
  have hinner := census.inner_end_count
  have houter := census.outer_end_count
  simp only [TotallyClosed] at hclosed
  omega

/-- The inner--inner count and the outer stub count exhaust the five inner
positions.  This is the subtraction-free form of
`k_2i = 5 - n_out`. -/
theorem innerInner_add_outerCount_eq_five (census : StrandCensus)
    (hclosed : census.TotallyClosed) :
    census.innerInner + census.outerCount = 5 := by
  have hinner := census.inner_end_count
  have houter := census.outer_end_count
  simp only [TotallyClosed] at hclosed
  omega

/-- Cubic closure's sharp arithmetic boundary: a totally closed web has at
most five outer stubs. -/
theorem outerCount_le_five (census : StrandCensus)
    (hclosed : census.TotallyClosed) :
    census.outerCount ≤ 5 := by
  have hinner := census.inner_end_count
  have houter := census.outer_end_count
  simp only [TotallyClosed] at hclosed
  omega

/-- The manuscript's displayed all-radial arithmetic, with natural-number
subtraction made safe by the separately proved bound. -/
theorem innerInner_eq_five_sub_outerCount (census : StrandCensus)
    (hclosed : census.TotallyClosed) :
    census.innerInner = 5 - census.outerCount := by
  have hinner := census.inner_end_count
  have houter := census.outer_end_count
  simp only [TotallyClosed] at hclosed
  omega

/-- Counting components rather than endpoints gives exactly
`5 + n_out` strands under total closure. -/
theorem total_strands_eq_five_add_outerCount (census : StrandCensus)
    (hclosed : census.TotallyClosed) :
    census.innerInner + census.radial + census.outerOuter =
      5 + census.outerCount := by
  have hinner := census.inner_end_count
  have houter := census.outer_end_count
  simp only [TotallyClosed] at hclosed
  omega

/-- At the boundary case `n_out = 5`, total closure forces all ten strands
to be radial.  No five-stub hypothesis is hidden in `StrandCensus`; it is an
explicit premise of this specialization. -/
theorem allRadial_of_totallyClosed_of_outerCount_eq_five
    (census : StrandCensus) (hclosed : census.TotallyClosed)
    (houter : census.outerCount = 5) :
    census.AllRadial := by
  have hinnerEnds := census.inner_end_count
  have houterEnds := census.outer_end_count
  simp only [TotallyClosed] at hclosed
  simp only [AllRadial]
  constructor
  · omega
  constructor
  · omega
  · exact hclosed

/-- Conversely, the all-radial anatomy can occur only at five outer stubs. -/
theorem outerCount_eq_five_of_allRadial (census : StrandCensus)
    (hradial : census.AllRadial) :
    census.outerCount = 5 := by
  have houterEnds := census.outer_end_count
  simp only [AllRadial] at hradial
  rcases hradial with ⟨_hinner, hradial, houter⟩
  omega

end StrandCensus

end GoertzelV24ClosedWebStrandCensus

end Mettapedia.GraphTheory.FourColor
