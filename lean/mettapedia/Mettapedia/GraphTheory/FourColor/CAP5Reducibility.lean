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

/-- Transported-repair endpoint for an arbitrary normalized bad CAP5 word.  This is the
boundary-facing version of the manuscript's "up to cyclic rotation and color relabeling" clause:
once the graph-level proof supplies a transported repair type for the transported bad word, the
word is solved. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportRepair
    {w : CAP5BoundaryWord} {σ : Color ≃ Color} {n : Nat}
    (hσ0 : σ 0 = 0)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    {action : CAP5BoundaryAction}
    (hrepair : CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n) :
    CAP5BoundaryWordSolved w := by
  subst w
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord
    (cap5_boundaryActionRepairsWord_of_boundaryActionRealizesSomeTransportedRepairType_bad
      hσ0 hrepair)

/-- Any normalized `(2,1,1,1)` CAP5 word is solved once the graph-level proof supplies a
transported finite repair action for its particular rotation and color relabeling. -/
theorem cap5BoundaryWordSolved_of_block2111_of_transportRepair
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasBlock2111 w)
    (hrepair :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ action : CAP5BoundaryAction,
          CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n) :
    CAP5BoundaryWordSolved w := by
  rcases hbad with ⟨σ, n, hσ0, hw⟩
  rcases hrepair hσ0 hw with ⟨action, haction⟩
  exact cap5BoundaryWordSolved_of_eq_transportBad_of_transportRepair
    hσ0 hw (action := action) haction

/-- Colored block-`(2,1,1,1)` form of the transported-repair endpoint. -/
theorem cap5BoundaryWordSolved_of_coloredBlock2111_of_transportRepair
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasColoredBlock2111 w)
    (hrepair :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ action : CAP5BoundaryAction,
          CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_block2111_of_transportRepair
    (cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad) hrepair

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

/-- Transport-normalized boundary-layer form of the CAP5 reducibility split.  Under the parity
shape forced by a proper cubic coloring, the good branch extends immediately; for the bad branch,
it is enough for the graph-level proof to provide a transported repair type for the word's
particular cyclic/color normal form. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_odd_of_transport_bad_repair
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w)
    (hbadRepair :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ action : CAP5BoundaryAction,
          CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n) :
    CAP5BoundaryWordSolved w := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact cap5BoundaryWordSolved_of_coloredBlock311 hgood
  · exact cap5BoundaryWordSolved_of_coloredBlock2111_of_transportRepair hbad hbadRepair

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
