import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord

namespace Mettapedia.GraphTheory.FourColor

/-!
Boundary-level CAP5 reducibility interface.

The graph-level manuscript obligation is not that every CAP5 boundary word extends
immediately.  The bad `(2,1,1,1)` words need an outside-only Kempe move first.
This module packages the exact boundary endpoint that the later planar/Kempe
realizability proof must feed.
-/

/-- A CAP5 boundary word is solved at the boundary layer when it either extends
across the cap immediately, or some outside boundary action genuinely repairs it
into an extendable word. -/
def CAP5BoundaryWordSolved (w : CAP5BoundaryWord) : Prop :=
  CAP5WordExtendsAcrossCycle w ∨
    ∃ action : CAP5BoundaryAction, CAP5BoundaryActionRepairsWord action w

theorem cap5BoundaryWordSolved_of_extendsAcrossCycle
    {w : CAP5BoundaryWord} (h : CAP5WordExtendsAcrossCycle w) :
    CAP5BoundaryWordSolved w :=
  Or.inl h

theorem cap5BoundaryWordSolved_of_boundaryActionRepairsWord
    {w : CAP5BoundaryWord} {action : CAP5BoundaryAction}
    (h : CAP5BoundaryActionRepairsWord action w) :
    CAP5BoundaryWordSolved w :=
  Or.inr ⟨action, h⟩

/-- Good CAP5 block words are solved without a repair move. -/
theorem cap5BoundaryWordSolved_of_coloredBlock311
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasColoredBlock311 w) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_extendsAcrossCycle
    (cap5_extendsAcrossCycle_of_coloredBlock311 h)

/-- Bad CAP5 block words are solved once the graph-level proof supplies a genuine
boundary repair action. -/
theorem cap5BoundaryWordSolved_of_coloredBlock2111_of_repair
    {w : CAP5BoundaryWord}
    (_hbad : CAP5BoundaryWordHasColoredBlock2111 w)
    (hrepair : ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRepairsWord action w) :
    CAP5BoundaryWordSolved w :=
  Or.inr hrepair

/-- Boundary-layer form of the CAP5 reducibility split.  Under the parity shape
forced by a proper cubic coloring, it is enough to repair the bad
`(2,1,1,1)` branch; the good `(3,1,1)` branch extends immediately. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_odd_of_bad_repair
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w)
    (hbadRepair : CAP5BoundaryWordHasColoredBlock2111 w →
      ∃ action : CAP5BoundaryAction, CAP5BoundaryActionRepairsWord action w) :
    CAP5BoundaryWordSolved w := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact cap5BoundaryWordSolved_of_coloredBlock311 hgood
  · exact cap5BoundaryWordSolved_of_coloredBlock2111_of_repair hbad (hbadRepair hbad)

/-- Canonical bad CAP5 word: active component pairings plus exclusion of the
simultaneous exceptional pattern produce a boundary-level solution. -/
theorem cap5BadBoundaryWord2111_solved_of_activePairings_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hpair : p.HasActivePairings) (hnotExceptional : ¬ p.IsExceptional) :
    CAP5BoundaryWordSolved cap5BadBoundaryWord2111 := by
  rcases
    CAP5BadPairingSupports.exists_boundaryActionRepairsWord_of_activePairings_of_not_isExceptional
      hpair hnotExceptional with
    ⟨action, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Component-cover form of the canonical CAP5 boundary endpoint.  This is the
finite boundary target for the graph-level Kempe-component cover proof, after
the planar separator argument excludes the exceptional pairing. -/
theorem cap5BadBoundaryWord2111_solved_of_componentCovers_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hcovers : p.HasComponentCovers) (hnotExceptional : ¬ p.IsExceptional) :
    CAP5BoundaryWordSolved cap5BadBoundaryWord2111 := by
  rcases
    CAP5BadPairingSupports.exists_boundaryActionRepairsWord_of_componentCovers_of_not_isExceptional
      hcovers hnotExceptional with
    ⟨action, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

end Mettapedia.GraphTheory.FourColor
