import Mettapedia.GraphTheory.FourColor.CAP5GraphBoundary
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.EdgeKempe

open scoped BigOperators

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

/-- Transported component-cover repair action for an arbitrary normalized bad CAP5 word.  This is
the graph-facing boundary endpoint once the outside Kempe-component argument supplies component
covers and excludes the simultaneous exceptional pairing pattern. -/
theorem exists_boundaryActionRepairsWord_usingTransportedSupport_of_eq_transportBad_of_componentCovers
    {w : CAP5BoundaryWord} {p : CAP5BadPairingSupports}
    (hcovers : p.HasComponentCovers) (hnotExceptional : ¬ p.IsExceptional)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    ∃ action : CAP5BoundaryAction,
      p.TransportedBoundaryActionUsesSupport σ n action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w := by
  subst w
  exact
    CAP5BadPairingSupports.exists_boundaryActionRepairsWord_usingTransportedSupport_of_componentCovers_of_not_isExceptional
        hcovers hnotExceptional hσ0 n

/-- Any normalized bad CAP5 word is solved once component-cover data supplies one of the finite
transported support repairs and the exceptional pairing pattern is excluded. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportComponentCovers
    {w : CAP5BoundaryWord} {p : CAP5BadPairingSupports}
    (hcovers : p.HasComponentCovers) (hnotExceptional : ¬ p.IsExceptional)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedSupport_of_eq_transportBad_of_componentCovers
        hcovers hnotExceptional hσ0 hw with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Block-`(2,1,1,1)` CAP5 words are solved if every cyclic/color normal form comes with
component-cover data whose simultaneous exceptional pattern is ruled out. -/
theorem cap5BoundaryWordSolved_of_block2111_of_transportComponentCovers
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ p : CAP5BadPairingSupports, p.HasComponentCovers ∧ ¬ p.IsExceptional) :
    CAP5BoundaryWordSolved w := by
  rcases hbad with ⟨σ, n, hσ0, hw⟩
  rcases hcomponentCovers hσ0 hw with ⟨p, hcovers, hnotExceptional⟩
  exact cap5BoundaryWordSolved_of_eq_transportBad_of_transportComponentCovers
    hcovers hnotExceptional hσ0 hw

/-- Colored block-`(2,1,1,1)` CAP5 words reduce to transported component-cover data. -/
theorem cap5BoundaryWordSolved_of_coloredBlock2111_of_transportComponentCovers
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasColoredBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ p : CAP5BadPairingSupports, p.HasComponentCovers ∧ ¬ p.IsExceptional) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_block2111_of_transportComponentCovers
    (cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad) hcomponentCovers

/-- Edge-set form of support use for a transported component-cover repair.  The graph/Kempe
layer should naturally produce finite edge supports; this predicate says that the boundary action
is the restriction of switching one of those edge supports. -/
def CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
    {E : Type*} [DecidableEq E]
    (boundaryEdge : Fin 5 → E)
    (redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset E)
    (σ : Color → Color) (action : CAP5BoundaryAction) : Prop :=
  action = cap5BoundaryActionOfEdgeSet boundaryEdge redBlue₁ (σ red) (σ blue) ∨
  action = cap5BoundaryActionOfEdgeSet boundaryEdge redBlue₂ (σ red) (σ blue) ∨
  action = cap5BoundaryActionOfEdgeSet boundaryEdge redPurple₁ (σ red) (σ purple) ∨
  action = cap5BoundaryActionOfEdgeSet boundaryEdge redPurple₂ (σ red) (σ purple)

/-- Structured graph-facing edge support data for one transported CAP5 bad-word presentation.
It keeps the finite edge supports, their induced transported boundary supports, and the finite
CAP5 component-cover facts together as a reusable obligation object. -/
structure CAP5TransportedEdgeComponentCoverCore
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (n : Nat) where
  redBlueEdge₁ : Finset E
  redBlueEdge₂ : Finset E
  redPurpleEdge₁ : Finset E
  redPurpleEdge₂ : Finset E
  redBlue₁ : Finset (Fin 5)
  redBlue₂ : Finset (Fin 5)
  redPurple₁ : Finset (Fin 5)
  redPurple₂ : Finset (Fin 5)
  hredBlue₁ :
    cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₁ =
      cap5RotateBoundarySupportN n redBlue₁
  hredBlue₂ :
    cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₂ =
      cap5RotateBoundarySupportN n redBlue₂
  hredPurple₁ :
    cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₁ =
      cap5RotateBoundarySupportN n redPurple₁
  hredPurple₂ :
    cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₂ =
      cap5RotateBoundarySupportN n redPurple₂
  hredBlue : CAP5BadRedBlueComponentCover redBlue₁ redBlue₂
  hredPurple : CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂

/-- The exceptional-pairing obstruction carried by transported edge component-cover core data. -/
def CAP5TransportedEdgeComponentCoverCore.IsExceptional
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n) : Prop :=
  CAP5BadExceptionalPairingPattern
    data.redBlue₁ data.redBlue₂ data.redPurple₁ data.redPurple₂

/-- One of the four normalized component supports lies on the finite CAP5 repair side. -/
def CAP5TransportedEdgeComponentCoverCore.HasBoundaryRepairSupport
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n) : Prop :=
  CAP5BadRedBlueRepairSupport data.redBlue₁ ∨
  CAP5BadRedBlueRepairSupport data.redBlue₂ ∨
  CAP5BadRedPurpleRepairSupport data.redPurple₁ ∨
  CAP5BadRedPurpleRepairSupport data.redPurple₂

/-- Boundary-support equations carried by the simultaneous exceptional CAP5 pairing after the
chosen cyclic transport.  This is the finite portal-pairing surface of the manuscript's
`(0,3),(1,2)` and `(0,4),(1,3)` exceptional annulus case. -/
def CAP5TransportedEdgeComponentCoverCore.HasExceptionalBoundarySupportPairings
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n) : Prop :=
  ((cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₁ =
        cap5RotateBoundarySupportN n ({0, 3} : Finset (Fin 5)) ∧
      cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₂ =
        cap5RotateBoundarySupportN n ({1, 2} : Finset (Fin 5))) ∨
    (cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₁ =
        cap5RotateBoundarySupportN n ({1, 2} : Finset (Fin 5)) ∧
      cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₂ =
        cap5RotateBoundarySupportN n ({0, 3} : Finset (Fin 5)))) ∧
  ((cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₁ =
        cap5RotateBoundarySupportN n ({0, 4} : Finset (Fin 5)) ∧
      cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₂ =
        cap5RotateBoundarySupportN n ({1, 3} : Finset (Fin 5))) ∨
    (cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₁ =
        cap5RotateBoundarySupportN n ({1, 3} : Finset (Fin 5)) ∧
      cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₂ =
        cap5RotateBoundarySupportN n ({0, 4} : Finset (Fin 5))))

/-- In core component-cover data, the finite boundary repair side is exactly the complement of
the simultaneous exceptional pairing. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasBoundaryRepairSupport_iff_not_isExceptional
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n) :
    data.HasBoundaryRepairSupport ↔ ¬ data.IsExceptional := by
  let p : CAP5BadPairingSupports :=
    { redBlue₁ := data.redBlue₁
      redBlue₂ := data.redBlue₂
      redPurple₁ := data.redPurple₁
      redPurple₂ := data.redPurple₂ }
  have hcovers : p.HasComponentCovers := ⟨data.hredBlue, data.hredPurple⟩
  simpa [p, CAP5TransportedEdgeComponentCoverCore.HasBoundaryRepairSupport,
    CAP5TransportedEdgeComponentCoverCore.IsExceptional,
    CAP5BadPairingSupports.HasRepair, CAP5BadPairingSupports.IsExceptional] using
    (CAP5BadPairingSupports.hasRepair_iff_not_isExceptional_of_componentCovers hcovers)

/-- The exceptional branch of core component-cover data exposes the exact transported boundary
support pairings needed by the subsequent annulus/Jordan-separator argument. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasExceptionalBoundarySupportPairings_of_isExceptional
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (h : data.IsExceptional) :
    data.HasExceptionalBoundarySupportPairings := by
  rcases h with ⟨hredBlue, hredPurple⟩
  constructor
  · rcases hredBlue with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by simpa [h₁] using data.hredBlue₁,
        by simpa [h₂] using data.hredBlue₂⟩
    · exact Or.inr ⟨by simpa [h₁] using data.hredBlue₁,
        by simpa [h₂] using data.hredBlue₂⟩
  · rcases hredPurple with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by simpa [h₁] using data.hredPurple₁,
        by simpa [h₂] using data.hredPurple₂⟩
    · exact Or.inr ⟨by simpa [h₁] using data.hredPurple₁,
        by simpa [h₂] using data.hredPurple₂⟩

/-- The four ordered exceptional CAP5 portal-pairing orientations left after the finite
one-move repair supports have been eliminated.  The names record whether the first stored
red/blue component is `{0,3}` or `{1,2}`, and whether the first stored red/purple component is
`{0,4}` or `{1,3}`. -/
inductive CAP5ExceptionalBoundarySupportOrientation where
  | redBlue03_redPurple04
  | redBlue03_redPurple13
  | redBlue12_redPurple04
  | redBlue12_redPurple13

/-- A transported core component-cover package realizes one of the four ordered exceptional
portal-pairing orientations. -/
def CAP5TransportedEdgeComponentCoverCore.RealizesExceptionalBoundarySupportOrientation
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (orientation : CAP5ExceptionalBoundarySupportOrientation) : Prop :=
  match orientation with
  | .redBlue03_redPurple04 =>
      cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₁ =
          cap5RotateBoundarySupportN n ({0, 3} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₂ =
          cap5RotateBoundarySupportN n ({1, 2} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₁ =
          cap5RotateBoundarySupportN n ({0, 4} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₂ =
          cap5RotateBoundarySupportN n ({1, 3} : Finset (Fin 5))
  | .redBlue03_redPurple13 =>
      cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₁ =
          cap5RotateBoundarySupportN n ({0, 3} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₂ =
          cap5RotateBoundarySupportN n ({1, 2} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₁ =
          cap5RotateBoundarySupportN n ({1, 3} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₂ =
          cap5RotateBoundarySupportN n ({0, 4} : Finset (Fin 5))
  | .redBlue12_redPurple04 =>
      cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₁ =
          cap5RotateBoundarySupportN n ({1, 2} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₂ =
          cap5RotateBoundarySupportN n ({0, 3} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₁ =
          cap5RotateBoundarySupportN n ({0, 4} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₂ =
          cap5RotateBoundarySupportN n ({1, 3} : Finset (Fin 5))
  | .redBlue12_redPurple13 =>
      cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₁ =
          cap5RotateBoundarySupportN n ({1, 2} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redBlueEdge₂ =
          cap5RotateBoundarySupportN n ({0, 3} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₁ =
          cap5RotateBoundarySupportN n ({1, 3} : Finset (Fin 5)) ∧
        cap5BoundarySupportOfEdges boundaryEdge data.redPurpleEdge₂ =
          cap5RotateBoundarySupportN n ({0, 4} : Finset (Fin 5))

/-- The transported exceptional support equations are exactly one of four ordered
portal-pairing orientations. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_exceptionalBoundarySupportOrientation_of_hasExceptionalBoundarySupportPairings
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (h : data.HasExceptionalBoundarySupportPairings) :
    ∃ orientation : CAP5ExceptionalBoundarySupportOrientation,
      data.RealizesExceptionalBoundarySupportOrientation orientation := by
  rcases h with ⟨hredBlue, hredPurple⟩
  rcases hredBlue with hredBlue | hredBlue <;>
    rcases hredPurple with hredPurple | hredPurple
  · exact ⟨.redBlue03_redPurple04, hredBlue.1, hredBlue.2, hredPurple.1, hredPurple.2⟩
  · exact ⟨.redBlue03_redPurple13, hredBlue.1, hredBlue.2, hredPurple.1, hredPurple.2⟩
  · exact ⟨.redBlue12_redPurple04, hredBlue.1, hredBlue.2, hredPurple.1, hredPurple.2⟩
  · exact ⟨.redBlue12_redPurple13, hredBlue.1, hredBlue.2, hredPurple.1, hredPurple.2⟩

/-- The exceptional branch of core component-cover data is a finite four-way portal-pairing case
split. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_exceptionalBoundarySupportOrientation_of_isExceptional
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (h : data.IsExceptional) :
    ∃ orientation : CAP5ExceptionalBoundarySupportOrientation,
      data.RealizesExceptionalBoundarySupportOrientation orientation :=
  exists_exceptionalBoundarySupportOrientation_of_hasExceptionalBoundarySupportPairings
    (hasExceptionalBoundarySupportPairings_of_isExceptional h)

/-- Finite form of the CAP5 move-realizability split for core edge component-cover data: either
one stored boundary component is already a one-move repair support, or the remaining branch is one
of four explicit exceptional portal-pairing orientations. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasBoundaryRepairSupport_or_exists_exceptionalBoundarySupportOrientation
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n) :
    data.HasBoundaryRepairSupport ∨
      ∃ orientation : CAP5ExceptionalBoundarySupportOrientation,
        data.RealizesExceptionalBoundarySupportOrientation orientation := by
  by_cases hexceptional : data.IsExceptional
  · exact Or.inr (exists_exceptionalBoundarySupportOrientation_of_isExceptional hexceptional)
  · exact Or.inl ((data.hasBoundaryRepairSupport_iff_not_isExceptional).2 hexceptional)

/-- The four side cases in the manuscript's exceptional CAP5 annulus argument, according to which
side of the first Jordan curve contains portals `p0` and `p4`.  This is still finite bookkeeping:
it does not assert that the corresponding curve exists in a graph embedding. -/
inductive CAP5ExceptionalAnnulusSideCase where
  | p0Inside_p4Outside
  | p0Outside_p4Inside
  | p0Inside_p4Inside
  | p0Outside_p4Outside

namespace CAP5ExceptionalAnnulusSideCase

/-- Boolean form of the manuscript's four-way side split: whether `p0` and `p4` lie on
the inside side of the first Jordan curve.  This is only the finite case distinction, not the
topological proof that either side contains the required graph pieces. -/
def ofPortalSides (p0Inside p4Inside : Bool) : CAP5ExceptionalAnnulusSideCase :=
  match p0Inside, p4Inside with
  | true, false => .p0Inside_p4Outside
  | false, true => .p0Outside_p4Inside
  | true, true => .p0Inside_p4Inside
  | false, false => .p0Outside_p4Outside

/-- Read off whether `p0` is on the inside side in a finite exceptional-annulus side case. -/
def p0Inside : CAP5ExceptionalAnnulusSideCase → Bool
  | .p0Inside_p4Outside => true
  | .p0Outside_p4Inside => false
  | .p0Inside_p4Inside => true
  | .p0Outside_p4Outside => false

/-- Read off whether `p4` is on the inside side in a finite exceptional-annulus side case. -/
def p4Inside : CAP5ExceptionalAnnulusSideCase → Bool
  | .p0Inside_p4Outside => false
  | .p0Outside_p4Inside => true
  | .p0Inside_p4Inside => true
  | .p0Outside_p4Outside => false

/-- The Boolean side data classify the finite exceptional-annulus side cases exactly. -/
theorem ofPortalSides_p0Inside_p4Inside (sideCase : CAP5ExceptionalAnnulusSideCase) :
    ofPortalSides sideCase.p0Inside sideCase.p4Inside = sideCase := by
  cases sideCase <;> rfl

/-- A conservative portal set for the small separator candidate in each exceptional-annulus side
case.  These are the CAP5 boundary portals touched by the manuscript's case split before the
topological/Jordan-curve-to-edge-cut conversion is attempted. -/
def separatorPortalSet : CAP5ExceptionalAnnulusSideCase → Finset (Fin 5)
  | .p0Inside_p4Outside => {0, 1, 2, 3}
  | .p0Outside_p4Inside => {1, 2, 3, 4}
  | .p0Inside_p4Inside => {0, 1, 3}
  | .p0Outside_p4Outside => {0, 1, 2, 4}

/-- Each finite side-case separator candidate uses at most four CAP5 portals. -/
theorem separatorPortalSet_card_le_four (sideCase : CAP5ExceptionalAnnulusSideCase) :
    sideCase.separatorPortalSet.card <= 4 := by
  cases sideCase <;> decide

/-- The finite side split generated from Boolean portal-side data always gives a separator
candidate using at most four portals. -/
theorem separatorPortalSet_ofPortalSides_card_le_four (p0Inside p4Inside : Bool) :
    (ofPortalSides p0Inside p4Inside).separatorPortalSet.card <= 4 :=
  separatorPortalSet_card_le_four (ofPortalSides p0Inside p4Inside)

end CAP5ExceptionalAnnulusSideCase

/-- Finite data handed to the later planar separator theorem: an exceptional orientation, an
annulus side case, and the corresponding small CAP5 portal set. -/
structure CAP5ExceptionalAnnulusSeparatorPortalCandidate where
  orientation : CAP5ExceptionalBoundarySupportOrientation
  sideCase : CAP5ExceptionalAnnulusSideCase
  portalSet : Finset (Fin 5)
  hportalSet : portalSet = sideCase.separatorPortalSet
  hcard_le_four : portalSet.card <= 4

/-- Constructor for the finite portal-set candidate attached to one exceptional orientation and
one annulus side case. -/
def CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase
    (orientation : CAP5ExceptionalBoundarySupportOrientation)
    (sideCase : CAP5ExceptionalAnnulusSideCase) :
    CAP5ExceptionalAnnulusSeparatorPortalCandidate where
  orientation := orientation
  sideCase := sideCase
  portalSet := sideCase.separatorPortalSet
  hportalSet := rfl
  hcard_le_four := CAP5ExceptionalAnnulusSideCase.separatorPortalSet_card_le_four sideCase

/-- Boundary-edge support candidate obtained by translating a finite separator-portal candidate
through the five CAP5 boundary edges.  This is the first graph-side finite object used by the
later separator theorem; it is not yet a proof that the support separates the graph cyclically. -/
structure CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) where
  portalCandidate : CAP5ExceptionalAnnulusSeparatorPortalCandidate
  edgeSupport : Finset E
  hedgeSupport : edgeSupport = portalCandidate.portalSet.image boundaryEdge
  hcard_le_four : edgeSupport.card <= 4

/-- Translate a separator-portal candidate into the corresponding finite set of CAP5 boundary
edges.  The cardinality bound survives even if two listed portals happen to name the same edge,
because image cardinality can only decrease. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E)
    (candidate : CAP5ExceptionalAnnulusSeparatorPortalCandidate) :
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge where
  portalCandidate := candidate
  edgeSupport := candidate.portalSet.image boundaryEdge
  hedgeSupport := rfl
  hcard_le_four := le_trans Finset.card_image_le candidate.hcard_le_four

/-- Canonical boundary-edge support candidate for one exceptional orientation and one annulus
side case.  This is the finite object the planar/Jordan micro-enumeration should realize as a
cyclic cut. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E)
    (orientation : CAP5ExceptionalBoundarySupportOrientation)
    (sideCase : CAP5ExceptionalAnnulusSideCase) :
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge :=
  ofPortalCandidate boundaryEdge
    (CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase orientation sideCase)

/-- Boolean-side version of the canonical exceptional-annulus boundary-edge candidate. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndPortalSides
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E)
    (orientation : CAP5ExceptionalBoundarySupportOrientation)
    (p0Inside p4Inside : Bool) :
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge :=
  ofOrientationAndSideCase boundaryEdge orientation
    (CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside)

/-- The boundary-edge support candidate only uses the five named CAP5 boundary edges. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.edgeSupport_subset_boundaryEdges
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge) :
    candidate.edgeSupport ⊆ (Finset.univ.image boundaryEdge : Finset E) := by
  intro e he
  rw [candidate.hedgeSupport] at he
  rcases Finset.mem_image.1 he with ⟨i, _hi, rfl⟩
  exact Finset.mem_image.2 ⟨i, by simp, rfl⟩

/-- Membership in a CAP5 boundary-edge support candidate is exactly membership in the image of
the finite separator-portal set under the boundary-edge map. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.mem_edgeSupport_iff_exists_portal
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (e : E) :
    e ∈ candidate.edgeSupport ↔
      ∃ i : Fin 5, i ∈ candidate.portalCandidate.portalSet ∧ boundaryEdge i = e := by
  rw [candidate.hedgeSupport]
  exact Finset.mem_image

/-- A boundary-edge support candidate has been promoted to the graph-level cyclic-cut target when
some small cyclic edge cut has exactly the candidate's finite edge support.  This predicate names
the planar/Jordan realization step without deriving it from the finite CAP5 bookkeeping alone. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.RealizesSmallCyclicEdgeCut
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (cut : SmallCyclicEdgeCut G) : Prop :=
  cut.edgeCut = candidate.edgeSupport

/-- Concrete realization data for a CAP5 boundary-edge support candidate.  This is the shape the
planar/Jordan layer should provide: a vertex side whose crossing edges are exactly the candidate
support, plus cycles on both sides. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.CyclicEdgeCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge) :=
  CyclicEdgeCutRealization G candidate.edgeSupport

/-- Build the cyclic-cut realization data for a CAP5 boundary-edge support candidate from the
direct path-separation interface expected of the planar/Jordan layer.  The listed candidate
support must consist of side-crossing edges, every walk crossing the side must contain a listed
candidate edge, and both sides must contain cycles. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_walk_separator
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hcandidate_crosses :
      ∀ e : G.edgeSet, e ∈ candidate.edgeSupport → EdgeCrossesVertexSide G side e)
    (hwalk_separator :
      ∀ {u v : V} (p : G.Walk u v), side u → ¬ side v →
        ∃ e : G.edgeSet, e ∈ candidate.edgeSupport ∧ (e : Sym2 V) ∈ p.edges)
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  CyclicEdgeCutRealization.of_walk_separator side hcandidate_crosses hwalk_separator
    hinside_cycle houtside_cycle

/-- Portal-language version of the direct walk-separator constructor.  This is the manuscript
shape of the CAP5/Sublemma 6.8 topological input: the named separator portals cross the chosen
side, and every walk between opposite sides contains one of those named boundary edges. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_portal_walk_separator
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hportal_crosses :
      ∀ i : Fin 5, i ∈ candidate.portalCandidate.portalSet →
        EdgeCrossesVertexSide G side (boundaryEdge i))
    (hportal_walk_separator :
      ∀ {u v : V} (p : G.Walk u v), side u → ¬ side v →
        ∃ i : Fin 5, i ∈ candidate.portalCandidate.portalSet ∧
          ((boundaryEdge i : G.edgeSet) : Sym2 V) ∈ p.edges)
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  candidate.cyclicEdgeCutRealizationData_of_walk_separator side
    (by
      intro e heSupport
      rcases (candidate.mem_edgeSupport_iff_exists_portal e).1 heSupport with
        ⟨i, hi, hboundary⟩
      subst e
      exact hportal_crosses i hi)
    (by
      intro u v p hu hv
      rcases hportal_walk_separator p hu hv with ⟨i, hi, hiEdges⟩
      exact ⟨boundaryEdge i,
        (candidate.mem_edgeSupport_iff_exists_portal (boundaryEdge i)).2 ⟨i, hi, rfl⟩,
        hiEdges⟩)
    hinside_cycle houtside_cycle

/-- Build CAP5 cyclic-cut realization data from the avoidance form of the planar/Jordan
separator theorem: every walk avoiding the candidate support must stay on the same side. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_walk_avoid_side_invariant
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hcandidate_crosses :
      ∀ e : G.edgeSet, e ∈ candidate.edgeSupport → EdgeCrossesVertexSide G side e)
    (hwalk_invariant :
      ∀ {u v : V} (p : G.Walk u v),
        (∀ e : G.edgeSet, e ∈ candidate.edgeSupport → (e : Sym2 V) ∉ p.edges) →
        (side u ↔ side v))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  CyclicEdgeCutRealization.of_walk_avoid_side_invariant side hcandidate_crosses
    hwalk_invariant hinside_cycle houtside_cycle

/-- Portal-language version of the CAP5 avoidance constructor.  It is enough for the planar/Jordan
layer to prove that every walk avoiding the named separator portals stays on one side; membership
in the finite edge support is then discharged through the candidate's image equation. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_portal_walk_avoid_side_invariant
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hcandidate_crosses :
      ∀ e : G.edgeSet, e ∈ candidate.edgeSupport → EdgeCrossesVertexSide G side e)
    (hportal_walk_invariant :
      ∀ {u v : V} (p : G.Walk u v),
        (∀ i : Fin 5, i ∈ candidate.portalCandidate.portalSet →
          ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) →
        (side u ↔ side v))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  candidate.cyclicEdgeCutRealizationData_of_walk_avoid_side_invariant side hcandidate_crosses
    (by
      intro u v p havoid
      exact hportal_walk_invariant p (by
        intro i hi heEdges
        exact havoid (boundaryEdge i)
          ((candidate.mem_edgeSupport_iff_exists_portal (boundaryEdge i)).2 ⟨i, hi, rfl⟩)
          heEdges))
    hinside_cycle houtside_cycle

/-- Build CAP5 cyclic-cut realization data from local edge classification: the candidate support
crosses the side, and every non-candidate edge preserves the side. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_edge_side_classification
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hcandidate_crosses :
      ∀ e : G.edgeSet, e ∈ candidate.edgeSupport → EdgeCrossesVertexSide G side e)
    (hnoncandidate_preserves :
      ∀ e : G.edgeSet, e ∉ candidate.edgeSupport →
        ∀ u v : V, u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) → (side u ↔ side v))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  CyclicEdgeCutRealization.of_edge_side_classification side hcandidate_crosses
    hnoncandidate_preserves hinside_cycle houtside_cycle

/-- Portal-language edge-classification constructor.  The planar/Jordan layer may prove that the
named separator portals cross the side and every edge outside their image preserves the side. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_portal_edge_side_classification
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hportal_crosses :
      ∀ i : Fin 5, i ∈ candidate.portalCandidate.portalSet →
        EdgeCrossesVertexSide G side (boundaryEdge i))
    (hnoncandidate_preserves :
      ∀ e : G.edgeSet, e ∉ candidate.edgeSupport →
        ∀ u v : V, u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) → (side u ↔ side v))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  candidate.cyclicEdgeCutRealizationData_of_edge_side_classification side
    (by
      intro e he
      rcases (candidate.mem_edgeSupport_iff_exists_portal e).1 he with ⟨i, hi, hboundary⟩
      subst e
      exact hportal_crosses i hi)
    hnoncandidate_preserves hinside_cycle houtside_cycle

/-- Build CAP5 cyclic-cut realization data from the exact local crossing classification: the
candidate support crosses the side, and every non-candidate edge does not cross it. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_edge_crossing_classification
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hcandidate_crosses :
      ∀ e : G.edgeSet, e ∈ candidate.edgeSupport → EdgeCrossesVertexSide G side e)
    (hnoncandidate_not_crosses :
      ∀ e : G.edgeSet, e ∉ candidate.edgeSupport → ¬ EdgeCrossesVertexSide G side e)
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  CyclicEdgeCutRealization.of_edge_crossing_classification side hcandidate_crosses
    hnoncandidate_not_crosses hinside_cycle houtside_cycle

/-- Portal-language exact crossing-edge constructor.  The planar/Jordan layer can target this
directly: named separator portals cross the side, and every edge outside their image does not. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_portal_edge_crossing_classification
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hportal_crosses :
      ∀ i : Fin 5, i ∈ candidate.portalCandidate.portalSet →
        EdgeCrossesVertexSide G side (boundaryEdge i))
    (hnoncandidate_not_crosses :
      ∀ e : G.edgeSet, e ∉ candidate.edgeSupport → ¬ EdgeCrossesVertexSide G side e)
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  candidate.cyclicEdgeCutRealizationData_of_edge_crossing_classification side
    (by
      intro e he
      rcases (candidate.mem_edgeSupport_iff_exists_portal e).1 he with ⟨i, hi, hboundary⟩
      subst e
      exact hportal_crosses i hi)
    hnoncandidate_not_crosses hinside_cycle houtside_cycle

/-- Direct separator consequence of non-candidate edge non-crossing: any walk crossing the chosen
side contains one of the named CAP5 separator boundary edges.  This is the graph-facing Sublemma
6.8 target after the planar/Jordan layer supplies a side for which edges outside the candidate
support do not cross. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.exists_portal_boundaryEdge_mem_walk_of_noncandidate_not_crosses
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop)
    (hnoncandidate_not_crosses :
      ∀ e : G.edgeSet, e ∉ candidate.edgeSupport → ¬ EdgeCrossesVertexSide G side e)
    {u v : V} (p : G.Walk u v) (hu : side u) (hv : ¬ side v) :
    ∃ i : Fin 5, i ∈ candidate.portalCandidate.portalSet ∧
      ((boundaryEdge i : G.edgeSet) : Sym2 V) ∈ p.edges := by
  rcases exists_mem_edgeCut_of_walk_endpoint_sides_of_edge_crossing_classification
      side hnoncandidate_not_crosses p hu hv with
    ⟨e, heSupport, heEdges⟩
  rcases (candidate.mem_edgeSupport_iff_exists_portal e).1 heSupport with
    ⟨i, hi, hboundary⟩
  subst e
  exact ⟨i, hi, heEdges⟩

/-- Portal form of the exact separator target.  For a CAP5 exceptional boundary support, saying
that every opposite-side walk hits one of the named portal boundary edges is equivalent to saying
that every non-candidate edge is non-crossing.  This is the local graph target the planar/Jordan
layer must supply for Sublemma 6.8. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.forall_portal_boundaryEdge_mem_walk_iff_noncandidate_not_crosses
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (side : V → Prop) :
    (∀ {u v : V} (p : G.Walk u v), side u → ¬ side v →
        ∃ i : Fin 5, i ∈ candidate.portalCandidate.portalSet ∧
          ((boundaryEdge i : G.edgeSet) : Sym2 V) ∈ p.edges) ↔
      (∀ e : G.edgeSet, e ∉ candidate.edgeSupport → ¬ EdgeCrossesVertexSide G side e) := by
  constructor
  · intro hwalk e hnot hcross
    rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
    rcases exists_walk_edges_eq_singleton_of_edge_endpoint_sides
        (G := G) (side := side) (e := e) hu hv hsu hsv with
      ⟨p, hpEdges⟩
    rcases hwalk p hsu hsv with ⟨i, hi, hiEdges⟩
    have hboundary_eq : boundaryEdge i = e := by
      apply Subtype.ext
      simpa [hpEdges] using hiEdges
    exact hnot ((candidate.mem_edgeSupport_iff_exists_portal e).2
      ⟨i, hi, hboundary_eq⟩)
  · intro hnoncandidate u v p hu hv
    exact candidate.exists_portal_boundaryEdge_mem_walk_of_noncandidate_not_crosses
      side hnoncandidate p hu hv

/-- If a finite CAP5 boundary-edge support candidate is realized by a graph-level small cyclic
edge cut, the cardinality bound transfers to that cut. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.exists_smallCyclicEdgeCut_of_realizes
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (hrealizes :
      ∃ cut : SmallCyclicEdgeCut G, candidate.RealizesSmallCyclicEdgeCut cut) :
    ∃ cut : SmallCyclicEdgeCut G,
      candidate.RealizesSmallCyclicEdgeCut cut ∧ cut.edgeCut.card <= 4 := by
  rcases hrealizes with ⟨cut, hcut⟩
  exact ⟨cut, hcut, by rw [hcut]; exact candidate.hcard_le_four⟩

/-- CAP5 support realization data gives the graph-level realized small cyclic cut expected by the
exceptional-annulus endpoint. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.exists_smallCyclicEdgeCut_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G)) :
    ∃ cut : SmallCyclicEdgeCut G,
      candidate.RealizesSmallCyclicEdgeCut cut ∧ cut.edgeCut.card <= 4 := by
  let cut := realization.toSmallCyclicEdgeCut candidate.hcard_le_four
  exact ⟨cut, rfl, candidate.hcard_le_four⟩

/-- Realization data gives the older existential realization interface.  This bridge lets legacy
CAP5 endpoints consume the stronger planar/Jordan target without weakening the topological
obligation. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.exists_realizesSmallCyclicEdgeCut_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G)) :
    ∃ cut : SmallCyclicEdgeCut G,
      candidate.RealizesSmallCyclicEdgeCut cut := by
  exact ⟨realization.toSmallCyclicEdgeCut candidate.hcard_le_four, rfl⟩

/-- Candidate-level separator consequence of the realization data: any walk crossing from one
realized side to the other must use an edge in the finite CAP5 boundary support candidate. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.exists_mem_edgeSupport_of_realizationData_walk_endpoint_sides
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G))
    {u v : V} (p : G.Walk u v) (hu : realization.side u) (hv : ¬ realization.side v) :
    ∃ e : G.edgeSet, e ∈ candidate.edgeSupport ∧ (e : Sym2 V) ∈ p.edges :=
  realization.exists_mem_edgeCut_of_walk_endpoint_sides p hu hv

/-- Portal-level separator consequence: when a realized CAP5 candidate separates two endpoints,
any walk between them contains one of the named boundary edges belonging to the candidate's portal
set. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.exists_portal_boundaryEdge_mem_walk_of_realizationData_endpoint_sides
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G))
    {u v : V} (p : G.Walk u v) (hu : realization.side u) (hv : ¬ realization.side v) :
    ∃ i : Fin 5, i ∈ candidate.portalCandidate.portalSet ∧
      ((boundaryEdge i : G.edgeSet) : Sym2 V) ∈ p.edges := by
  rcases candidate.exists_mem_edgeSupport_of_realizationData_walk_endpoint_sides
      realization p hu hv with
    ⟨e, heSupport, heEdges⟩
  rcases (candidate.mem_edgeSupport_iff_exists_portal e).1 heSupport with
    ⟨i, hi, hboundary⟩
  subst e
  exact ⟨i, hi, heEdges⟩

/-- Candidate-level invariance form: a walk avoiding the finite CAP5 boundary support candidate
cannot move between the two realized sides. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.side_iff_of_forall_not_mem_edgeSupport_of_realizationData_walk
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G))
    {u v : V} (p : G.Walk u v)
    (havoid : ∀ e : G.edgeSet, e ∈ candidate.edgeSupport → (e : Sym2 V) ∉ p.edges) :
    realization.side u ↔ realization.side v :=
  realization.side_iff_of_forall_not_mem_edgeCut_of_walk p havoid

/-- Portal-level invariance form: a walk that avoids every boundary edge named by the candidate's
separator portals cannot move between the two realized sides. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.side_iff_of_forall_not_mem_portalBoundaryEdge_of_realizationData_walk
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G))
    {u v : V} (p : G.Walk u v)
    (havoid : ∀ i : Fin 5, i ∈ candidate.portalCandidate.portalSet →
      ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) :
    realization.side u ↔ realization.side v :=
  candidate.side_iff_of_forall_not_mem_edgeSupport_of_realizationData_walk realization p
    (by
      intro e heSupport
      rcases (candidate.mem_edgeSupport_iff_exists_portal e).1 heSupport with
        ⟨i, hi, hboundary⟩
      simpa [hboundary] using havoid i hi)

/-- A realized CAP5 boundary-edge support candidate gives the forbidden small-cyclic-cut
existence form because the candidate support has cardinality at most four. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.hasCyclicEdgeCutOfSizeAtMostFour_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G)) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  realization.hasCyclicEdgeCutOfSizeAtMostFour candidate.hcard_le_four

/-- Under the no-small-cyclic-cut hypothesis, no CAP5 boundary-edge support candidate can be
realized as a cyclic cut. -/
theorem CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.false_of_noCyclicEdgeCut_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (realization : candidate.CyclicEdgeCutRealizationData (G := G)) :
    False :=
  hnoCut (candidate.hasCyclicEdgeCutOfSizeAtMostFour_of_realizationData realization)

/-- A bundled small cyclic edge cut whose support is exactly a CAP5 boundary-edge candidate gives
the realization-data form consumed by the sharper exceptional-annulus endpoint. -/
def CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.cyclicEdgeCutRealizationData_of_realizesSmallCyclicEdgeCut
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet}
    (candidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (cut : SmallCyclicEdgeCut G)
    (hcut : candidate.RealizesSmallCyclicEdgeCut cut) :
    candidate.CyclicEdgeCutRealizationData (G := G) :=
  cut.toCyclicEdgeCutRealization_of_edgeCut_eq hcut

/-- Once core component-cover data is in the exceptional branch, every annulus side case has a
finite separator-portal candidate using at most four CAP5 portals.  This is the finite input to the
later theorem that must turn an embedded annulus/Jordan curve into an actual cyclic edge cut. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_exceptionalAnnulusSeparatorPortalCandidate_of_isExceptional
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (sideCase : CAP5ExceptionalAnnulusSideCase)
    (h : data.IsExceptional) :
    ∃ candidate : CAP5ExceptionalAnnulusSeparatorPortalCandidate,
      data.RealizesExceptionalBoundarySupportOrientation candidate.orientation ∧
        candidate.sideCase = sideCase := by
  rcases exists_exceptionalBoundarySupportOrientation_of_isExceptional h with
    ⟨orientation, horientation⟩
  exact ⟨CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase
      orientation sideCase, horientation, rfl⟩

/-- Boolean portal-side form of the exceptional-annulus finite case split.  Once the topological
layer has determined on which side of the first Jordan curve `p0` and `p4` lie, exceptional core
component-cover data supplies the corresponding small separator-portal candidate. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_exceptionalAnnulusSeparatorPortalCandidate_of_isExceptional_of_portalSides
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional) :
    ∃ candidate : CAP5ExceptionalAnnulusSeparatorPortalCandidate,
      data.RealizesExceptionalBoundarySupportOrientation candidate.orientation ∧
        candidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
        candidate.portalSet =
          (CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside).separatorPortalSet ∧
        candidate.portalSet.card <= 4 := by
  rcases exists_exceptionalAnnulusSeparatorPortalCandidate_of_isExceptional
      (CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside) h with
    ⟨candidate, horientation, hsideCase⟩
  refine ⟨candidate, horientation, hsideCase, ?_, candidate.hcard_le_four⟩
  calc
    candidate.portalSet = candidate.sideCase.separatorPortalSet := candidate.hportalSet
    _ =
        (CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside).separatorPortalSet := by
          rw [hsideCase]

/-- Boundary-edge support form of the exceptional-annulus finite side split.  After the finite
portal-side case has been chosen, the candidate separator portals translate to at most four
actual CAP5 boundary edges.  The missing topological theorem must still prove that this edge
support is a cyclic separator in the ambient graph. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_exceptionalAnnulusBoundaryEdgeSupportCandidate_of_isExceptional_of_portalSides
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional) :
    ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
      data.RealizesExceptionalBoundarySupportOrientation
          edgeCandidate.portalCandidate.orientation ∧
        edgeCandidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
        edgeCandidate.edgeSupport =
          edgeCandidate.portalCandidate.portalSet.image boundaryEdge ∧
        edgeCandidate.edgeSupport.card <= 4 := by
  rcases exists_exceptionalAnnulusSeparatorPortalCandidate_of_isExceptional_of_portalSides
      p0Inside p4Inside h with
    ⟨candidate, horientation, hsideCase, _hportalSet, hcard⟩
  let edgeCandidate :=
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate boundaryEdge candidate
  exact ⟨edgeCandidate, horientation, hsideCase, rfl,
    le_trans Finset.card_image_le hcard⟩

/-- Graph-level endpoint for the exceptional CAP5 annulus branch.  Finite CAP5 data supplies the
candidate boundary-edge support; the topological realization input must identify that support with
a genuine small cyclic edge cut in the ambient graph. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_smallCyclicEdgeCutCandidate_of_isExceptional_of_portalSides
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
      data.RealizesExceptionalBoundarySupportOrientation
          edgeCandidate.portalCandidate.orientation ∧
        edgeCandidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut ∧ cut.edgeCut.card <= 4 := by
  rcases exists_exceptionalAnnulusBoundaryEdgeSupportCandidate_of_isExceptional_of_portalSides
      p0Inside p4Inside h with
    ⟨edgeCandidate, horientation, hsideCase, _hedgeSupport, hcard⟩
  rcases hrealizes edgeCandidate horientation hsideCase with ⟨cut, hcut⟩
  exact ⟨edgeCandidate, horientation, hsideCase, cut, hcut, by
    rw [hcut]
    exact hcard⟩

/-- Rich realization-data form of the exceptional-annulus topological obligation.  Instead of
asking the planar/Jordan layer to return an already-packaged `SmallCyclicEdgeCut`, it asks for the
side predicate, exact crossing-edge equality, and cycle witnesses that generate one. -/
def CAP5TransportedEdgeComponentCoverCore.HasExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) : Prop :=
  ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
    data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation →
    edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
    Nonempty (edgeCandidate.CyclicEdgeCutRealizationData (G := G))

/-- Existential realization-data form of the exceptional-annulus topological obligation.  This is
the weakest interface needed to contradict cyclic five-edge-connectivity: one compatible CAP5
boundary-edge candidate is realized as a cyclic edge cut. -/
def CAP5TransportedEdgeComponentCoverCore.HasSomeExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) : Prop :=
  ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
    data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation ∧
    edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
    Nonempty (edgeCandidate.CyclicEdgeCutRealizationData (G := G))

/-- Canonical realization-data obligation for the exceptional-annulus micro-enumeration.  For
each exceptional portal-pairing orientation realized by the component-cover data, realize the
canonical boundary-edge candidate for the selected `p0`/`p4` side case as a cyclic cut.  This is
weaker and more precise than realizing every compatible candidate. -/
def CAP5TransportedEdgeComponentCoverCore.HasCanonicalExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) : Prop :=
  ∀ orientation : CAP5ExceptionalBoundarySupportOrientation,
    data.RealizesExceptionalBoundarySupportOrientation orientation →
    Nonempty
      ((CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndPortalSides
          boundaryEdge orientation p0Inside p4Inside).CyclicEdgeCutRealizationData (G := G))

/-- Constructor for the existential realization-data obligation from one concrete candidate.  This
is the direct target shape for the planar/Jordan micro-enumeration: identify the candidate support
for the selected side case and provide the cyclic-cut realization data for that support. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_candidate
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (horientation :
      data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation)
    (hsideCase :
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside)
    (realization : edgeCandidate.CyclicEdgeCutRealizationData (G := G)) :
    data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside :=
  ⟨edgeCandidate, horientation, hsideCase, ⟨realization⟩⟩

/-- Canonical-candidate constructor for the existential realization-data obligation.  The later
topological proof can work orientation-by-orientation and only produce realization data for the
canonical candidate selected by the side case. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_orientationAndPortalSides
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (orientation : CAP5ExceptionalBoundarySupportOrientation)
    (horientation : data.RealizesExceptionalBoundarySupportOrientation orientation)
    (realization :
      ((CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndPortalSides
          boundaryEdge orientation p0Inside p4Inside).CyclicEdgeCutRealizationData (G := G))) :
    data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside :=
  data.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_candidate
    p0Inside p4Inside
    (CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndPortalSides
      boundaryEdge orientation p0Inside p4Inside)
    horientation rfl realization

/-- Realization data implies the older existential cut-realization interface. -/
theorem CAP5TransportedEdgeComponentCoverCore.realizesSmallCyclicEdgeCut_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
      data.RealizesExceptionalBoundarySupportOrientation
          edgeCandidate.portalCandidate.orientation →
      edgeCandidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
      ∃ cut : SmallCyclicEdgeCut G,
        edgeCandidate.RealizesSmallCyclicEdgeCut cut := by
  intro edgeCandidate horientation hsideCase
  rcases hrealizationData edgeCandidate horientation hsideCase with ⟨realization⟩
  exact edgeCandidate.exists_realizesSmallCyclicEdgeCut_of_realizationData
    realization

/-- The universal realization-data obligation supplies the weaker existential realization-data
obligation once the exceptional branch has selected a boundary-edge candidate. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside := by
  rcases exists_exceptionalAnnulusBoundaryEdgeSupportCandidate_of_isExceptional_of_portalSides
      p0Inside p4Inside h with
    ⟨edgeCandidate, horientation, hsideCase, _hedgeSupport, _hcard⟩
  exact ⟨edgeCandidate, horientation, hsideCase,
    hrealizationData edgeCandidate horientation hsideCase⟩

/-- The concrete small-cyclic-cut interface also supplies the sharper existential realization-data
obligation.  This is useful for the planar/Jordan layer: it can construct a `SmallCyclicEdgeCut`
with the candidate edge support, and this bridge turns that into the realization-data package used
by the graph-facing CAP5 endpoints. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_realizesSmallCyclicEdgeCut
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside := by
  rcases exists_exceptionalAnnulusBoundaryEdgeSupportCandidate_of_isExceptional_of_portalSides
      p0Inside p4Inside h with
    ⟨edgeCandidate, horientation, hsideCase, _hedgeSupport, _hcard⟩
  rcases hrealizes edgeCandidate horientation hsideCase with ⟨cut, hcut⟩
  exact ⟨edgeCandidate, horientation, hsideCase,
    ⟨edgeCandidate.cyclicEdgeCutRealizationData_of_realizesSmallCyclicEdgeCut cut hcut⟩⟩

/-- The canonical orientation-by-orientation realization obligation supplies the weaker
existential realization-data route once the exceptional branch has selected an orientation. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside := by
  rcases exists_exceptionalBoundarySupportOrientation_of_isExceptional h with
    ⟨orientation, horientation⟩
  rcases hcanonical orientation horientation with ⟨realization⟩
  exact
    data.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_orientationAndPortalSides
      p0Inside p4Inside orientation horientation realization

/-- Realization-data version of the graph-level exceptional-annulus endpoint. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_smallCyclicEdgeCutCandidate_of_isExceptional_of_portalSides_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
      data.RealizesExceptionalBoundarySupportOrientation
          edgeCandidate.portalCandidate.orientation ∧
        edgeCandidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut ∧ cut.edgeCut.card <= 4 :=
  exists_smallCyclicEdgeCutCandidate_of_isExceptional_of_portalSides
    p0Inside p4Inside h
    (data.realizesSmallCyclicEdgeCut_of_realizationData p0Inside p4Inside hrealizationData)

/-- Existential realization-data version of the graph-level exceptional-annulus endpoint. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_smallCyclicEdgeCutCandidate_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hrealizationData :
      data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
      data.RealizesExceptionalBoundarySupportOrientation
          edgeCandidate.portalCandidate.orientation ∧
        edgeCandidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut ∧ cut.edgeCut.card <= 4 := by
  rcases hrealizationData with ⟨edgeCandidate, horientation, hsideCase, ⟨realization⟩⟩
  rcases edgeCandidate.exists_smallCyclicEdgeCut_of_realizationData realization with
    ⟨cut, hcut, hcard⟩
  exact ⟨edgeCandidate, horientation, hsideCase, cut, hcut, hcard⟩

/-- Exceptional CAP5 annulus data plus the topological realization input produces the forbidden
small cyclic edge cut promised by the manuscript's annulus separator step. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasCyclicEdgeCutOfSizeAtMostFour_of_isExceptional_of_portalSides
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    HasCyclicEdgeCutOfSizeAtMostFour G := by
  rcases exists_smallCyclicEdgeCutCandidate_of_isExceptional_of_portalSides
      p0Inside p4Inside h hrealizes with
    ⟨_edgeCandidate, _horientation, _hsideCase, cut, _hcut, hcard⟩
  exact ⟨cut, hcard⟩

/-- Realization-data version of the forbidden small-cyclic-cut endpoint. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasCyclicEdgeCutOfSizeAtMostFour_of_isExceptional_of_portalSides_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  hasCyclicEdgeCutOfSizeAtMostFour_of_isExceptional_of_portalSides
    p0Inside p4Inside h
    (data.realizesSmallCyclicEdgeCut_of_realizationData p0Inside p4Inside hrealizationData)

/-- Existential realization-data version of the forbidden small-cyclic-cut endpoint. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasCyclicEdgeCutOfSizeAtMostFour_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hrealizationData :
      data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    HasCyclicEdgeCutOfSizeAtMostFour G := by
  rcases exists_smallCyclicEdgeCutCandidate_of_someExceptionalAnnulusCyclicCutRealizationData
      p0Inside p4Inside hrealizationData with
    ⟨_edgeCandidate, _horientation, _hsideCase, cut, _hcut, hcard⟩
  exact ⟨cut, hcard⟩

/-- Canonical orientation-by-orientation realization-data version of the forbidden
small-cyclic-cut endpoint. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasCyclicEdgeCutOfSizeAtMostFour_of_isExceptional_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  data.hasCyclicEdgeCutOfSizeAtMostFour_of_someExceptionalAnnulusCyclicCutRealizationData
    p0Inside p4Inside
    (data.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_canonicalRealizationData
      p0Inside p4Inside h hcanonical)

/-- Concrete-candidate realization-data version of the forbidden small-cyclic-cut endpoint. -/
theorem CAP5TransportedEdgeComponentCoverCore.hasCyclicEdgeCutOfSizeAtMostFour_of_candidate_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (horientation :
      data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation)
    (hsideCase :
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside)
    (realization : edgeCandidate.CyclicEdgeCutRealizationData (G := G)) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  data.hasCyclicEdgeCutOfSizeAtMostFour_of_someExceptionalAnnulusCyclicCutRealizationData
    p0Inside p4Inside
    (data.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_candidate
      p0Inside p4Inside edgeCandidate horientation hsideCase realization)

/-- Concrete-candidate realization-data contradiction under the no-small-cyclic-cut hypothesis. -/
theorem CAP5TransportedEdgeComponentCoverCore.false_of_noCyclicEdgeCut_of_candidate_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (horientation :
      data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation)
    (hsideCase :
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside)
    (realization : edgeCandidate.CyclicEdgeCutRealizationData (G := G)) :
    False :=
  hnoCut
    (data.hasCyclicEdgeCutOfSizeAtMostFour_of_candidate_realizationData
      p0Inside p4Inside edgeCandidate horientation hsideCase realization)

/-- Under a no-small-cyclic-cut hypothesis, the exceptional CAP5 annulus branch is impossible
once the planar/Jordan layer realizes each candidate support as an actual small cyclic edge cut. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_noCyclicEdgeCut_of_portalSides
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    ¬ data.IsExceptional := by
  intro hExceptional
  exact hnoCut
    (hasCyclicEdgeCutOfSizeAtMostFour_of_isExceptional_of_portalSides
      p0Inside p4Inside hExceptional hrealizes)

/-- Realization-data version of the no-small-cyclic-cut CAP5 obstruction. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_noCyclicEdgeCut_of_portalSides_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ¬ data.IsExceptional :=
  data.not_isExceptional_of_noCyclicEdgeCut_of_portalSides
    p0Inside p4Inside hnoCut
    (data.realizesSmallCyclicEdgeCut_of_realizationData p0Inside p4Inside hrealizationData)

/-- Existential realization-data version of the no-small-cyclic-cut CAP5 obstruction. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizationData :
      data.IsExceptional →
      data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ¬ data.IsExceptional := by
  intro hExceptional
  exact hnoCut
    (data.hasCyclicEdgeCutOfSizeAtMostFour_of_someExceptionalAnnulusCyclicCutRealizationData
      p0Inside p4Inside (hrealizationData hExceptional))

/-- Canonical orientation-by-orientation realization-data version of the no-small-cyclic-cut CAP5
obstruction. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_noCyclicEdgeCut_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    ¬ data.IsExceptional := by
  intro hExceptional
  exact hnoCut
    (data.hasCyclicEdgeCutOfSizeAtMostFour_of_isExceptional_of_canonicalRealizationData
      p0Inside p4Inside hExceptional hcanonical)

/-- Named cyclic-edge-connectivity form of the CAP5 exceptional-annulus obstruction. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_cyclicallyFiveEdgeConnected_of_portalSides
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    ¬ data.IsExceptional :=
  data.not_isExceptional_of_noCyclicEdgeCut_of_portalSides
    p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizes

/-- Realization-data version of the named cyclic-edge-connectivity CAP5 obstruction. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_cyclicallyFiveEdgeConnected_of_portalSides_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ¬ data.IsExceptional :=
  data.not_isExceptional_of_noCyclicEdgeCut_of_portalSides_of_realizationData
    p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizationData

/-- Existential realization-data version of the named cyclic-edge-connectivity CAP5 obstruction. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizationData :
      data.IsExceptional →
        data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ¬ data.IsExceptional :=
  data.not_isExceptional_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizationData

/-- Canonical orientation-by-orientation realization-data version of the named
cyclic-edge-connectivity CAP5 obstruction. -/
theorem CAP5TransportedEdgeComponentCoverCore.not_isExceptional_of_cyclicallyFiveEdgeConnected_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    ¬ data.IsExceptional :=
  data.not_isExceptional_of_noCyclicEdgeCut_of_canonicalRealizationData
    p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hcanonical

/-- Concrete-candidate realization-data contradiction under cyclic five-edge-connectivity. -/
theorem CAP5TransportedEdgeComponentCoverCore.false_of_cyclicallyFiveEdgeConnected_of_candidate_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge)
    (horientation :
      data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation)
    (hsideCase :
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside)
    (realization : edgeCandidate.CyclicEdgeCutRealizationData (G := G)) :
    False :=
  data.false_of_noCyclicEdgeCut_of_candidate_realizationData
    p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour edgeCandidate
    horientation hsideCase realization

/-- Full transported component-cover data is core component-cover data plus exclusion of the
simultaneous exceptional pattern.  The core form is the honest target before the planar separator
argument has ruled the exceptional branch out. -/
structure CAP5TransportedEdgeComponentCoverData
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (n : Nat) where
  redBlueEdge₁ : Finset E
  redBlueEdge₂ : Finset E
  redPurpleEdge₁ : Finset E
  redPurpleEdge₂ : Finset E
  redBlue₁ : Finset (Fin 5)
  redBlue₂ : Finset (Fin 5)
  redPurple₁ : Finset (Fin 5)
  redPurple₂ : Finset (Fin 5)
  hredBlue₁ :
    cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₁ =
      cap5RotateBoundarySupportN n redBlue₁
  hredBlue₂ :
    cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₂ =
      cap5RotateBoundarySupportN n redBlue₂
  hredPurple₁ :
    cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₁ =
      cap5RotateBoundarySupportN n redPurple₁
  hredPurple₂ :
    cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₂ =
      cap5RotateBoundarySupportN n redPurple₂
  hredBlue : CAP5BadRedBlueComponentCover redBlue₁ redBlue₂
  hredPurple : CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂
  hnotExceptional :
    ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂

/-- Forget the non-exceptional proof from full transported component-cover data. -/
def CAP5TransportedEdgeComponentCoverData.toCore
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5TransportedEdgeComponentCoverCore boundaryEdge n where
  redBlueEdge₁ := data.redBlueEdge₁
  redBlueEdge₂ := data.redBlueEdge₂
  redPurpleEdge₁ := data.redPurpleEdge₁
  redPurpleEdge₂ := data.redPurpleEdge₂
  redBlue₁ := data.redBlue₁
  redBlue₂ := data.redBlue₂
  redPurple₁ := data.redPurple₁
  redPurple₂ := data.redPurple₂
  hredBlue₁ := data.hredBlue₁
  hredBlue₂ := data.hredBlue₂
  hredPurple₁ := data.hredPurple₁
  hredPurple₂ := data.hredPurple₂
  hredBlue := data.hredBlue
  hredPurple := data.hredPurple

/-- Rebuild full transported component-cover data from core data after the exceptional branch is
excluded. -/
def CAP5TransportedEdgeComponentCoverData.ofCore
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hnotExceptional : ¬ data.IsExceptional) :
    CAP5TransportedEdgeComponentCoverData boundaryEdge n where
  redBlueEdge₁ := data.redBlueEdge₁
  redBlueEdge₂ := data.redBlueEdge₂
  redPurpleEdge₁ := data.redPurpleEdge₁
  redPurpleEdge₂ := data.redPurpleEdge₂
  redBlue₁ := data.redBlue₁
  redBlue₂ := data.redBlue₂
  redPurple₁ := data.redPurple₁
  redPurple₂ := data.redPurple₂
  hredBlue₁ := data.hredBlue₁
  hredBlue₂ := data.hredBlue₂
  hredPurple₁ := data.hredPurple₁
  hredPurple₂ := data.hredPurple₂
  hredBlue := data.hredBlue
  hredPurple := data.hredPurple
  hnotExceptional := by
    simpa [CAP5TransportedEdgeComponentCoverCore.IsExceptional] using hnotExceptional

/-- An edge-level color switch uses one of the four edge supports carried by a transported CAP5
component-cover package. -/
def CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (σ : Color → Color) (edgeSupport : Finset E) (a b : Color) : Prop :=
  (edgeSupport = data.redBlueEdge₁ ∧ a = σ red ∧ b = σ blue) ∨
  (edgeSupport = data.redBlueEdge₂ ∧ a = σ red ∧ b = σ blue) ∨
  (edgeSupport = data.redPurpleEdge₁ ∧ a = σ red ∧ b = σ purple) ∨
  (edgeSupport = data.redPurpleEdge₂ ∧ a = σ red ∧ b = σ purple)

/-- An edge-level color switch uses one of the four edge supports carried by a transported CAP5
component-cover package after the exceptional branch has already been excluded. -/
def CAP5TransportedEdgeSwitchUsesComponentCoverSupport
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (σ : Color → Color) (edgeSupport : Finset E) (a b : Color) : Prop :=
  (edgeSupport = data.redBlueEdge₁ ∧ a = σ red ∧ b = σ blue) ∨
  (edgeSupport = data.redBlueEdge₂ ∧ a = σ red ∧ b = σ blue) ∨
  (edgeSupport = data.redPurpleEdge₁ ∧ a = σ red ∧ b = σ purple) ∨
  (edgeSupport = data.redPurpleEdge₂ ∧ a = σ red ∧ b = σ purple)

/-- Full-data support use is the same support-use predicate on its core data. -/
theorem componentCoverCoreSupport_of_componentCoverDataSupport
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverData boundaryEdge n}
    {σ : Color → Color} {edgeSupport : Finset E} {a b : Color}
    (h :
      CAP5TransportedEdgeSwitchUsesComponentCoverSupport data σ edgeSupport a b) :
    CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport
      data.toCore σ edgeSupport a b := by
  simpa [CAP5TransportedEdgeSwitchUsesComponentCoverSupport,
    CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport,
    CAP5TransportedEdgeComponentCoverData.toCore] using h

/-- A finite edge support is realized by an interior edge-Kempe component and has even
incidence at every vertex.  This is the reusable graph-side certificate needed to ensure that a
CAP5 support switch preserves the zero-boundary equations. -/
def CAP5EdgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (C : E → Color) (edgeSupport : Finset E)
    (a b : Color) : Prop :=
  ∃ seed : V,
    edgeSupport = EdgeKempe.edgeKempeFinset D.incident D C seed a b ∧
    ∀ v : V,
      Even ((EdgeKempe.edgeKempeFinset D.incident D C seed a b ∩ D.incident v).card)

/-- A CAP5 support certified as an edge-Kempe component contains only the two switched colors. -/
theorem edgeSupport_forall_inTwoColors_of_edgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color}
    {edgeSupport : Finset E} {a b : Color}
    (hkempe : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b) :
    ∀ e ∈ edgeSupport, EdgeKempe.inTwoColors C a b e := by
  rcases hkempe with ⟨seed, hsupp, _heven⟩
  rw [hsupp]
  exact EdgeKempe.edgeKempeFinset_forall_inTwoColors D.incident D C seed a b

/-- A CAP5 support certified as an edge-Kempe component contains only interior edges. -/
theorem edgeSupport_forall_interior_of_edgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color}
    {edgeSupport : Finset E} {a b : Color}
    (hkempe : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b) :
    ∀ e ∈ edgeSupport, e ∉ D.boundaryEdges := by
  rcases hkempe with ⟨seed, hsupp, _heven⟩
  rw [hsupp]
  exact EdgeKempe.edgeKempeFinset_forall_interior D.incident D C seed a b

/-- A CAP5 support certified as an edge-Kempe component is disjoint from the boundary support. -/
theorem edgeSupport_disjoint_boundaryEdges_of_edgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color}
    {edgeSupport : Finset E} {a b : Color}
    (hkempe : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b) :
    Disjoint edgeSupport D.boundaryEdges := by
  rcases hkempe with ⟨seed, hsupp, _heven⟩
  rw [hsupp]
  exact EdgeKempe.edgeKempeFinset_disjoint_boundaryEdges D.incident D C seed a b

/-- A CAP5 support certified as an edge-Kempe component is contained in the two-color
over-approximation for the switched colors. -/
theorem edgeSupport_subset_overapprox_of_edgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color}
    {edgeSupport : Finset E} {a b : Color}
    (hkempe : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b) :
    edgeSupport ⊆ EdgeKempe.overapprox C a b := by
  rcases hkempe with ⟨seed, hsupp, _heven⟩
  rw [hsupp]
  exact EdgeKempe.edgeKempeFinset_subset_overapprox D.incident D C seed a b

/-- The four edge supports in a transported CAP5 component-cover package are all realized by
finite Kempe components with even vertex incidence. -/
def CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {n : Nat} (D : ZeroBoundaryData V E) (C : E → Color) (σ : Color → Color)
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n) : Prop :=
  CAP5EdgeSupportUsesKempeFinset D C data.redBlueEdge₁ (σ red) (σ blue) ∧
  CAP5EdgeSupportUsesKempeFinset D C data.redBlueEdge₂ (σ red) (σ blue) ∧
  CAP5EdgeSupportUsesKempeFinset D C data.redPurpleEdge₁ (σ red) (σ purple) ∧
  CAP5EdgeSupportUsesKempeFinset D C data.redPurpleEdge₂ (σ red) (σ purple)

/-- Structured transported CAP5 component-cover data whose four edge supports are already
certified as finite Kempe components.  This is the object the graph geometry layer should
construct: the component-cover data and its Kempe/even-incidence certificates travel together. -/
structure CAP5TransportedEdgeKempeComponentCoverData
    {V E : Type*} [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (C : E → Color) (σ : Color → Color)
    (boundaryEdge : Fin 5 → E) (n : Nat) where
  toEdgeComponentCoverData : CAP5TransportedEdgeComponentCoverData boundaryEdge n
  husesKempeFinsets :
    CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
      D C σ toEdgeComponentCoverData

/-- Forgetting the Kempe certificates from a transported edge-Kempe component-cover package
returns the ordinary transported edge component-cover data. -/
theorem CAP5TransportedEdgeKempeComponentCoverData.usesKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color} {σ : Color → Color}
    {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n) :
    CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
      D C σ data.toEdgeComponentCoverData :=
  data.husesKempeFinsets

/-- Seed-level certificate for turning transported CAP5 edge component-cover data into bundled
edge-Kempe component-cover data.  This is the shape the graph geometry layer should naturally
prove: each of the four CAP5 support sets is a concrete edge-Kempe component, and each such
component has even incidence at every vertex. -/
structure CAP5TransportedEdgeKempeSeeds
    {V E : Type*} [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (C : E → Color) (σ : Color → Color)
    {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n) where
  redBlueSeed₁ : V
  redBlueEdge₁_eq :
    data.redBlueEdge₁ =
      EdgeKempe.edgeKempeFinset D.incident D C redBlueSeed₁ (σ red) (σ blue)
  redBlueEven₁ :
    ∀ v : V,
      Even ((EdgeKempe.edgeKempeFinset D.incident D C redBlueSeed₁ (σ red) (σ blue) ∩
        D.incident v).card)
  redBlueSeed₂ : V
  redBlueEdge₂_eq :
    data.redBlueEdge₂ =
      EdgeKempe.edgeKempeFinset D.incident D C redBlueSeed₂ (σ red) (σ blue)
  redBlueEven₂ :
    ∀ v : V,
      Even ((EdgeKempe.edgeKempeFinset D.incident D C redBlueSeed₂ (σ red) (σ blue) ∩
        D.incident v).card)
  redPurpleSeed₁ : V
  redPurpleEdge₁_eq :
    data.redPurpleEdge₁ =
      EdgeKempe.edgeKempeFinset D.incident D C redPurpleSeed₁ (σ red) (σ purple)
  redPurpleEven₁ :
    ∀ v : V,
      Even ((EdgeKempe.edgeKempeFinset D.incident D C redPurpleSeed₁ (σ red) (σ purple) ∩
        D.incident v).card)
  redPurpleSeed₂ : V
  redPurpleEdge₂_eq :
    data.redPurpleEdge₂ =
      EdgeKempe.edgeKempeFinset D.incident D C redPurpleSeed₂ (σ red) (σ purple)
  redPurpleEven₂ :
    ∀ v : V,
      Even ((EdgeKempe.edgeKempeFinset D.incident D C redPurpleSeed₂ (σ red) (σ purple) ∩
        D.incident v).card)

/-- A seed-level CAP5/Kempe certificate gives the four support-level Kempe certificates used by
the reducibility endpoints. -/
theorem CAP5TransportedEdgeKempeSeeds.usesKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color} {σ : Color → Color}
    {boundaryEdge : Fin 5 → E} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverData boundaryEdge n}
    (seeds : CAP5TransportedEdgeKempeSeeds D C σ data) :
    CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets D C σ data := by
  exact
    ⟨⟨seeds.redBlueSeed₁, seeds.redBlueEdge₁_eq, seeds.redBlueEven₁⟩,
      ⟨seeds.redBlueSeed₂, seeds.redBlueEdge₂_eq, seeds.redBlueEven₂⟩,
      ⟨seeds.redPurpleSeed₁, seeds.redPurpleEdge₁_eq, seeds.redPurpleEven₁⟩,
      ⟨seeds.redPurpleSeed₂, seeds.redPurpleEdge₂_eq, seeds.redPurpleEven₂⟩⟩

/-- Constructor for bundled transported CAP5 edge-Kempe component-cover data from ordinary
component-cover data plus four explicit Kempe seeds. -/
def CAP5TransportedEdgeKempeComponentCoverData.ofSeeds
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color} {σ : Color → Color}
    {boundaryEdge : Fin 5 → E} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (seeds : CAP5TransportedEdgeKempeSeeds D C σ data) :
    CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n where
  toEdgeComponentCoverData := data
  husesKempeFinsets := seeds.usesKempeFinsets

/-- If a transported CAP5 repair uses one of the four supports in Kempe-certified component-cover
data, then that selected edge support is itself Kempe-certified. -/
theorem edgeSupportUsesKempeFinset_of_dataUsesKempeFinsets_of_uses
    {V E : Type*} [Fintype E] [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {n : Nat} {D : ZeroBoundaryData V E} {C : E → Color} {σ : Color → Color}
    {data : CAP5TransportedEdgeComponentCoverData boundaryEdge n}
    {edgeSupport : Finset E} {a b : Color}
    (hdata : CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets D C σ data)
    (huses : CAP5TransportedEdgeSwitchUsesComponentCoverSupport data σ edgeSupport a b) :
    CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b := by
  rcases hdata with ⟨hredBlue₁, hredBlue₂, hredPurple₁, hredPurple₂⟩
  rcases huses with huses | huses | huses | huses
  · rcases huses with ⟨hsupp, ha, hb⟩
    simpa [hsupp, ha, hb] using hredBlue₁
  · rcases huses with ⟨hsupp, ha, hb⟩
    simpa [hsupp, ha, hb] using hredBlue₂
  · rcases huses with ⟨hsupp, ha, hb⟩
    simpa [hsupp, ha, hb] using hredPurple₁
  · rcases huses with ⟨hsupp, ha, hb⟩
    simpa [hsupp, ha, hb] using hredPurple₂

/-- If a transported CAP5 repair uses one of the four supports in bundled edge-Kempe
component-cover data, then the selected edge support is itself Kempe-certified. -/
theorem edgeSupportUsesKempeFinset_of_edgeKempeComponentCoverData_of_uses
    {V E : Type*} [Fintype E] [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {n : Nat} {D : ZeroBoundaryData V E} {C : E → Color} {σ : Color → Color}
    {data : CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n}
    {edgeSupport : Finset E} {a b : Color}
    (huses :
      CAP5TransportedEdgeSwitchUsesComponentCoverSupport
        data.toEdgeComponentCoverData σ edgeSupport a b) :
    CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b :=
  edgeSupportUsesKempeFinset_of_dataUsesKempeFinsets_of_uses
    data.usesKempeFinsets huses

/-- Concrete edge-level repair outcome for a transported bad CAP5 boundary word.  It records
the transported normal form, the component-cover data used, and the actual edge switch whose
restricted boundary word extends across the cap. -/
structure CAP5EdgeSwitchRepairOutcome
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (C : E → Color) where
  σ : Color ≃ Color
  n : Nat
  hσ0 : σ 0 = 0
  data : CAP5TransportedEdgeComponentCoverData boundaryEdge n
  edgeSupport : Finset E
  a : Color
  b : Color
  huses : CAP5TransportedEdgeSwitchUsesComponentCoverSupport data σ edgeSupport a b
  hextends :
    CAP5WordExtendsAcrossCycle
      (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C))

/-- A repair outcome exposes the concrete edge switch whose restricted boundary word extends. -/
theorem exists_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcome
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {C : E → Color}
    (h : Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C)) :
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases h with ⟨outcome⟩
  exact ⟨outcome.edgeSupport, outcome.a, outcome.b, outcome.hextends⟩

/-- A repair outcome also retains the transported component-cover support that produced the
edge switch.  This is the provenance-preserving projection for later graph/Kempe extraction. -/
theorem exists_transportData_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcome
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E} {C : E → Color}
    (h : Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C)) :
    ∃ σ : Color ≃ Color, ∃ n : Nat,
    ∃ data : CAP5TransportedEdgeComponentCoverData boundaryEdge n,
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      σ 0 = 0 ∧
      CAP5TransportedEdgeSwitchUsesComponentCoverSupport data σ edgeSupport a b ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases h with ⟨outcome⟩
  exact
    ⟨outcome.σ, outcome.n, outcome.data, outcome.edgeSupport, outcome.a, outcome.b,
      outcome.hσ0, outcome.huses, outcome.hextends⟩

/-- The graph/Kempe certificate that a CAP5 edge-switch repair outcome is not an arbitrary edge
set switch: its support is a finite interior edge-Kempe component whose incidence is even at
every vertex. -/
def CAP5EdgeSwitchRepairOutcomeUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color}
    (D : ZeroBoundaryData V E) (outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C) : Prop :=
  ∃ seed : V,
    outcome.edgeSupport = EdgeKempe.edgeKempeFinset D.incident D C seed outcome.a outcome.b ∧
    ∀ v : V,
      Even ((EdgeKempe.edgeKempeFinset D.incident D C seed outcome.a outcome.b ∩
        D.incident v).card)

/-- Switching along a Kempe-certified finite edge support preserves the zero-boundary
equation. -/
theorem switch_isZeroBoundary_of_edgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color}
    {edgeSupport : Finset E} {a b : Color}
    (hC : D.isZeroBoundary C)
    (hkempe : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b) :
    D.isZeroBoundary (switch a b (edgeSupport : Set E) C) := by
  classical
  rcases hkempe with ⟨seed, hsupp, heven⟩
  rw [hsupp]
  exact EdgeKempe.switch_edgeKempeFinset_preserves_isZeroBoundary
    D C seed a b hC heven

/-- Switching along a Kempe-certified finite edge support preserves the full zero-boundary set:
vertex sums remain zero and boundary-edge colors remain zero. -/
theorem switch_mem_zeroBoundarySet_of_edgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} {C : E → Color}
    {edgeSupport : Finset E} {a b : Color}
    (hC : C ∈ D.zeroBoundarySet)
    (hkempe : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b) :
    switch a b (edgeSupport : Set E) C ∈ D.zeroBoundarySet := by
  classical
  rcases hkempe with ⟨seed, hsupp, heven⟩
  rw [hsupp]
  exact EdgeKempe.switch_edgeKempeFinset_mem_zeroBoundarySet
    D C seed a b hC heven

/-- A switch using one of the supports in bundled edge-Kempe component-cover data preserves the
zero-boundary equation. -/
theorem switch_isZeroBoundary_of_edgeKempeComponentCoverData_of_uses
    {V E : Type*} [Fintype E] [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {n : Nat} {D : ZeroBoundaryData V E} {C : E → Color} {σ : Color → Color}
    {data : CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n}
    {edgeSupport : Finset E} {a b : Color}
    (hC : D.isZeroBoundary C)
    (huses :
      CAP5TransportedEdgeSwitchUsesComponentCoverSupport
        data.toEdgeComponentCoverData σ edgeSupport a b) :
    D.isZeroBoundary (switch a b (edgeSupport : Set E) C) :=
  switch_isZeroBoundary_of_edgeSupportUsesKempeFinset hC
    (edgeSupportUsesKempeFinset_of_edgeKempeComponentCoverData_of_uses huses)

/-- A switch using one of the supports in bundled edge-Kempe component-cover data preserves the
full zero-boundary set. -/
theorem switch_mem_zeroBoundarySet_of_edgeKempeComponentCoverData_of_uses
    {V E : Type*} [Fintype E] [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {n : Nat} {D : ZeroBoundaryData V E} {C : E → Color} {σ : Color → Color}
    {data : CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n}
    {edgeSupport : Finset E} {a b : Color}
    (hC : C ∈ D.zeroBoundarySet)
    (huses :
      CAP5TransportedEdgeSwitchUsesComponentCoverSupport
        data.toEdgeComponentCoverData σ edgeSupport a b) :
    switch a b (edgeSupport : Set E) C ∈ D.zeroBoundarySet :=
  switch_mem_zeroBoundarySet_of_edgeSupportUsesKempeFinset hC
    (edgeSupportUsesKempeFinset_of_edgeKempeComponentCoverData_of_uses huses)

/-- If the selected support of a repair outcome is certified as a finite Kempe component, then
the whole repair outcome is Kempe-certified. -/
theorem switchRepairOutcomeUsesKempeFinset_of_edgeSupportUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color}
    {D : ZeroBoundaryData V E} {outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C}
    (h : CAP5EdgeSupportUsesKempeFinset D C outcome.edgeSupport outcome.a outcome.b) :
    CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome := by
  exact h

/-- A repair outcome inherits its Kempe certificate from the transported component-cover support
it actually uses.  This connects the CAP5 boundary support bookkeeping to the edge-Kempe
component layer without assuming that arbitrary edge switches preserve the zero-boundary
equations. -/
theorem switchRepairOutcomeUsesKempeFinset_of_dataUsesKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color}
    {D : ZeroBoundaryData V E} {outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C}
    (hdata :
      CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
        D C outcome.σ outcome.data) :
    CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome := by
  exact switchRepairOutcomeUsesKempeFinset_of_edgeSupportUsesKempeFinset
    (edgeSupportUsesKempeFinset_of_dataUsesKempeFinsets_of_uses hdata outcome.huses)

/-- A CAP5 repair outcome certified as a finite Kempe-component switch preserves the
zero-boundary equation of the edge coloring. -/
theorem switch_isZeroBoundary_of_switchRepairOutcomeUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color}
    {D : ZeroBoundaryData V E} {outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C}
    (hC : D.isZeroBoundary C)
    (hkempe : CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome) :
    D.isZeroBoundary
      (switch outcome.a outcome.b (outcome.edgeSupport : Set E) C) := by
  classical
  rcases hkempe with ⟨seed, hsupp, heven⟩
  rw [hsupp]
  exact EdgeKempe.switch_edgeKempeFinset_preserves_isZeroBoundary
    D C seed outcome.a outcome.b hC heven

/-- A CAP5 repair outcome certified as a finite Kempe-component switch preserves the full
zero-boundary set of the edge coloring. -/
theorem switch_mem_zeroBoundarySet_of_switchRepairOutcomeUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color}
    {D : ZeroBoundaryData V E} {outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C}
    (hC : C ∈ D.zeroBoundarySet)
    (hkempe : CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome) :
    switch outcome.a outcome.b (outcome.edgeSupport : Set E) C ∈ D.zeroBoundarySet := by
  exact switch_mem_zeroBoundarySet_of_edgeSupportUsesKempeFinset hC hkempe

/-- If a CAP5 repair outcome is certified as a finite Kempe-component switch, then it gives an
explicit edge switch that both preserves the zero-boundary equation and makes the CAP5 boundary
word extend. -/
theorem exists_isZeroBoundary_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcomeUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color} {D : ZeroBoundaryData V E}
    (h : Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C))
    (hC : D.isZeroBoundary C)
    (hkempe :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome) :
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      D.isZeroBoundary (switch a b (edgeSupport : Set E) C) ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases h with ⟨outcome⟩
  exact
    ⟨outcome.edgeSupport, outcome.a, outcome.b,
      switch_isZeroBoundary_of_switchRepairOutcomeUsesKempeFinset hC (hkempe outcome),
      outcome.hextends⟩

/-- If a CAP5 repair outcome is certified as a finite Kempe-component switch, then it gives an
explicit edge switch that stays inside the full zero-boundary set and makes the CAP5 boundary
word extend. -/
theorem exists_mem_zeroBoundarySet_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcomeUsesKempeFinset
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color} {D : ZeroBoundaryData V E}
    (h : Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C))
    (hC : C ∈ D.zeroBoundarySet)
    (hkempe :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome) :
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      switch a b (edgeSupport : Set E) C ∈ D.zeroBoundarySet ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases h with ⟨outcome⟩
  exact
    ⟨outcome.edgeSupport, outcome.a, outcome.b,
      switch_mem_zeroBoundarySet_of_switchRepairOutcomeUsesKempeFinset hC (hkempe outcome),
      outcome.hextends⟩

/-- Data-level Kempe-certified form of the repair-outcome projection.  The caller supplies
Kempe certificates for the transported component-cover data, and the theorem selects the one
used by the CAP5 repair outcome. -/
theorem exists_isZeroBoundary_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcomeDataUsesKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color} {D : ZeroBoundaryData V E}
    (h : Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C))
    (hC : D.isZeroBoundary C)
    (hkempeData :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets D C outcome.σ outcome.data) :
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      D.isZeroBoundary (switch a b (edgeSupport : Set E) C) ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  exact
    exists_isZeroBoundary_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcomeUsesKempeFinset
      h hC
      (fun outcome =>
        switchRepairOutcomeUsesKempeFinset_of_dataUsesKempeFinsets
          (hkempeData outcome))

/-- Data-level full-zero-boundary form of the repair-outcome projection.  The caller supplies
Kempe certificates for the transported component-cover data, and the selected switch remains in
`D.zeroBoundarySet`. -/
theorem exists_mem_zeroBoundarySet_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcomeDataUsesKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {boundaryEdge : Fin 5 → E} {C : E → Color} {D : ZeroBoundaryData V E}
    (h : Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C))
    (hC : C ∈ D.zeroBoundarySet)
    (hkempeData :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets D C outcome.σ outcome.data) :
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      switch a b (edgeSupport : Set E) C ∈ D.zeroBoundarySet ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  exact
    exists_mem_zeroBoundarySet_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcomeUsesKempeFinset
      h hC
      (fun outcome =>
        switchRepairOutcomeUsesKempeFinset_of_dataUsesKempeFinsets
          (hkempeData outcome))

/-- Raw support-cover repair action for an arbitrary transported bad CAP5 word.  This exposes the
actual support-carried boundary action, not just the solved-word conclusion. -/
theorem exists_boundaryActionRepairsWord_usingTransportedComponentCoverSupport_of_eq_transportBad_of_componentCoverSupports
    {w : CAP5BoundaryWord}
    {redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5)}
    (hredBlue : CAP5BadRedBlueComponentCover redBlue₁ redBlue₂)
    (hredPurple : CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂)
    (hnotExceptional :
      ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesComponentCoverSupport
        redBlue₁ redBlue₂ redPurple₁ redPurple₂ σ n action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w := by
  subst w
  exact
    exists_boundaryActionRepairsWord_usingTransportedComponentCoverSupport_of_componentCovers_of_notExceptional
      hredBlue hredPurple hnotExceptional hσ0 n

/-- Edge-support repair action for an arbitrary transported bad CAP5 word.  This is the
graph-facing version of the raw support-cover endpoint: it accepts four finite edge supports,
plus proofs that their restrictions to the five CAP5 boundary edges are the transported
component supports required by the finite CAP5 enumeration. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverSupports
    {E : Type*} [DecidableEq E]
    {w : CAP5BoundaryWord} (boundaryEdge : Fin 5 → E)
    {redBlueEdge₁ redBlueEdge₂ redPurpleEdge₁ redPurpleEdge₂ : Finset E}
    {redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5)}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (hredBlue₁ :
      cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₁ =
        cap5RotateBoundarySupportN n redBlue₁)
    (hredBlue₂ :
      cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₂ =
        cap5RotateBoundarySupportN n redBlue₂)
    (hredPurple₁ :
      cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₁ =
        cap5RotateBoundarySupportN n redPurple₁)
    (hredPurple₂ :
      cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₂ =
        cap5RotateBoundarySupportN n redPurple₂)
    (hredBlue : CAP5BadRedBlueComponentCover redBlue₁ redBlue₂)
    (hredPurple : CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂)
    (hnotExceptional :
      ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂)
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge redBlueEdge₁ redBlueEdge₂ redPurpleEdge₁ redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedComponentCoverSupport_of_eq_transportBad_of_componentCoverSupports
        hredBlue hredPurple hnotExceptional hσ0 hw with
    ⟨action, huses, hrealizes, hrepairs⟩
  rcases huses with huses | huses | huses | huses
  · subst action
    refine ⟨cap5BoundaryActionOfEdgeSet boundaryEdge redBlueEdge₁ (σ red) (σ blue), ?_, ?_, ?_⟩
    · exact Or.inl rfl
    · simpa [cap5BoundaryActionOfEdgeSet, hredBlue₁] using hrealizes
    · simpa [cap5BoundaryActionOfEdgeSet, hredBlue₁] using hrepairs
  · subst action
    refine ⟨cap5BoundaryActionOfEdgeSet boundaryEdge redBlueEdge₂ (σ red) (σ blue), ?_, ?_, ?_⟩
    · exact Or.inr (Or.inl rfl)
    · simpa [cap5BoundaryActionOfEdgeSet, hredBlue₂] using hrealizes
    · simpa [cap5BoundaryActionOfEdgeSet, hredBlue₂] using hrepairs
  · subst action
    refine ⟨cap5BoundaryActionOfEdgeSet boundaryEdge redPurpleEdge₁ (σ red) (σ purple), ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · simpa [cap5BoundaryActionOfEdgeSet, hredPurple₁] using hrealizes
    · simpa [cap5BoundaryActionOfEdgeSet, hredPurple₁] using hrepairs
  · subst action
    refine ⟨cap5BoundaryActionOfEdgeSet boundaryEdge redPurpleEdge₂ (σ red) (σ purple), ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr rfl))
    · simpa [cap5BoundaryActionOfEdgeSet, hredPurple₂] using hrealizes
    · simpa [cap5BoundaryActionOfEdgeSet, hredPurple₂] using hrepairs

/-- Edge-support repair-or-exceptional split for core transported component-cover data.  This is
the exact finite CAP5 move-realizability surface before the planar separator argument has excluded
the simultaneous exceptional pairing pattern. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_or_exceptional_of_eq_transportBad_of_componentCoverCore
    {E : Type*} [DecidableEq E]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → E}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    (∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w) ∨
    data.IsExceptional := by
  by_cases hnotExceptional : data.IsExceptional
  · exact Or.inr hnotExceptional
  · exact Or.inl
      (exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverSupports
        boundaryEdge hσ0 data.hredBlue₁ data.hredBlue₂ data.hredPurple₁ data.hredPurple₂
        data.hredBlue data.hredPurple
        (by
          simpa [CAP5TransportedEdgeComponentCoverCore.IsExceptional] using hnotExceptional)
        hw)

/-- Edge-support repair endpoint for core transported component-cover data, after the
planar/Jordan layer realizes the exceptional annulus branch as a forbidden small cyclic edge cut. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_or_exceptional_of_eq_transportBad_of_componentCoverCore
        hσ0 data hw with
    hrepair | hexceptional
  · exact hrepair
  · exact False.elim
      ((data.not_isExceptional_of_noCyclicEdgeCut_of_portalSides
          p0Inside p4Inside hnoCut hrealizes) hexceptional)

/-- Realization-data version of the core CAP5 repair endpoint under the no-small-cyclic-cut
obstruction. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w :=
  exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut
    hσ0 data hw p0Inside p4Inside hnoCut
    (data.realizesSmallCyclicEdgeCut_of_realizationData p0Inside p4Inside hrealizationData)

/-- Existential realization-data version of the core CAP5 repair endpoint under the
no-small-cyclic-cut obstruction. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizationData :
      data.IsExceptional →
        data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_or_exceptional_of_eq_transportBad_of_componentCoverCore
        hσ0 data hw with
    hrepair | hexceptional
  · exact hrepair
  · exact False.elim
      ((data.not_isExceptional_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
          p0Inside p4Inside hnoCut hrealizationData) hexceptional)

/-- Canonical orientation-by-orientation realization-data version of the core CAP5 repair
endpoint under the no-small-cyclic-cut obstruction. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w :=
  exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    hσ0 data hw p0Inside p4Inside hnoCut
    (fun hExceptional =>
      data.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_canonicalRealizationData
        p0Inside p4Inside hExceptional hcanonical)

/-- Named cyclic-edge-connectivity form of the CAP5 core repair endpoint. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w :=
  exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizes

/-- Realization-data version of the named cyclic-edge-connectivity core CAP5 repair endpoint. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w :=
  exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_realizationData
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizationData

/-- Existential realization-data version of the named cyclic-edge-connectivity core CAP5 repair
endpoint. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizationData :
      data.IsExceptional →
        data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w :=
  exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizationData

/-- Canonical orientation-by-orientation realization-data version of the named
cyclic-edge-connectivity core CAP5 repair endpoint. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w :=
  exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_canonicalRealizationData
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hcanonical

/-- Solved-boundary-word form of the core CAP5 endpoint under the no-small-cyclic-cut obstruction.
This is the boundary-layer conclusion once component covers are available and the exceptional
annulus branch has been ruled out by the graph-level cyclic-cut hypothesis. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut
        hσ0 data hw p0Inside p4Inside hnoCut hrealizes with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Realization-data version of the solved-boundary-word CAP5 endpoint under the
no-small-cyclic-cut obstruction. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_realizationData
        hσ0 data hw p0Inside p4Inside hnoCut hrealizationData with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Existential realization-data version of the solved-boundary-word CAP5 endpoint under the
no-small-cyclic-cut obstruction. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizationData :
      data.IsExceptional →
        data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
        hσ0 data hw p0Inside p4Inside hnoCut hrealizationData with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Canonical orientation-by-orientation realization-data version of the solved-boundary-word
CAP5 endpoint under the no-small-cyclic-cut obstruction. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_canonicalRealizationData
        hσ0 data hw p0Inside p4Inside hnoCut hcanonical with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Named cyclic-edge-connectivity form of the solved-boundary-word CAP5 endpoint. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizes :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∃ cut : SmallCyclicEdgeCut G,
          edgeCandidate.RealizesSmallCyclicEdgeCut cut) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizes

/-- Realization-data version of the named cyclic-edge-connectivity solved-boundary-word CAP5
endpoint. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_realizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizationData :
      data.HasExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut_of_realizationData
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizationData

/-- Existential realization-data version of the named cyclic-edge-connectivity solved-boundary-word
CAP5 endpoint. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizationData :
      data.IsExceptional →
        data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizationData

/-- Canonical orientation-by-orientation realization-data version of the named
cyclic-edge-connectivity solved-boundary-word CAP5 endpoint. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → G.edgeSet}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_noCyclicEdgeCut_of_canonicalRealizationData
    hσ0 data hw p0Inside p4Inside hcyclic.noCyclicEdgeCutOfSizeAtMostFour hcanonical

/-- Raw support-cover endpoint for an arbitrary transported bad CAP5 word.  This is the
interface a later graph/Kempe extraction should naturally target: it supplies the four boundary
supports directly, rather than first packaging them as `CAP5BadPairingSupports`. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportComponentCoverSupports
    {w : CAP5BoundaryWord}
    {redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5)}
    (hredBlue : CAP5BadRedBlueComponentCover redBlue₁ redBlue₂)
    (hredPurple : CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂)
    (hnotExceptional :
      ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedComponentCoverSupport_of_eq_transportBad_of_componentCoverSupports
        hredBlue hredPurple hnotExceptional hσ0 hw with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Edge-support endpoint for an arbitrary transported bad CAP5 word.  It packages the
edge-set support repair action into the boundary-layer solved predicate. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverSupports
    {E : Type*} [DecidableEq E]
    {w : CAP5BoundaryWord} (boundaryEdge : Fin 5 → E)
    {redBlueEdge₁ redBlueEdge₂ redPurpleEdge₁ redPurpleEdge₂ : Finset E}
    {redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5)}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (hredBlue₁ :
      cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₁ =
        cap5RotateBoundarySupportN n redBlue₁)
    (hredBlue₂ :
      cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₂ =
        cap5RotateBoundarySupportN n redBlue₂)
    (hredPurple₁ :
      cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₁ =
        cap5RotateBoundarySupportN n redPurple₁)
    (hredPurple₂ :
      cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₂ =
        cap5RotateBoundarySupportN n redPurple₂)
    (hredBlue : CAP5BadRedBlueComponentCover redBlue₁ redBlue₂)
    (hredPurple : CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂)
    (hnotExceptional :
      ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂)
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverSupports
        boundaryEdge hσ0 hredBlue₁ hredBlue₂ hredPurple₁ hredPurple₂
        hredBlue hredPurple hnotExceptional hw with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Structured-data form of the edge-support repair action endpoint for one transported bad
CAP5 word. -/
theorem exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverData
    {E : Type*} [DecidableEq E]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → E}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    ∃ action : CAP5BoundaryAction,
      CAP5TransportedBoundaryActionUsesEdgeComponentCoverSupport
        boundaryEdge data.redBlueEdge₁ data.redBlueEdge₂
          data.redPurpleEdge₁ data.redPurpleEdge₂ σ action ∧
      CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n ∧
      CAP5BoundaryActionRepairsWord action w :=
  exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverSupports
    boundaryEdge hσ0 data.hredBlue₁ data.hredBlue₂ data.hredPurple₁ data.hredPurple₂
    data.hredBlue data.hredPurple data.hnotExceptional hw

/-- Structured component-cover data yields an actual edge-level switch whose restricted CAP5
boundary word extends across the cap.  This is the concrete graph-facing form of the boundary
repair action. -/
theorem exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverData
    {E : Type*} [DecidableEq E]
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n) :
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      CAP5TransportedEdgeSwitchUsesComponentCoverSupport data σ edgeSupport a b ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverData
        hσ0 data hw with
    ⟨action, huses, _hrealizes, _hnotExtends, hextends⟩
  rcases huses with huses | huses | huses | huses
  · subst action
    refine ⟨data.redBlueEdge₁, σ red, σ blue, ?_, ?_⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
      simpa [hw]
        using hextends
  · subst action
    refine ⟨data.redBlueEdge₂, σ red, σ blue, ?_, ?_⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
      simpa [hw]
        using hextends
  · subst action
    refine ⟨data.redPurpleEdge₁, σ red, σ purple, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
      simpa [hw]
        using hextends
  · subst action
    refine ⟨data.redPurpleEdge₂, σ red, σ purple, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
      simpa [hw]
        using hextends

/-- Core component-cover data gives either a concrete transported edge switch whose boundary word
extends across the CAP5 cap, or the finite exceptional pairing pattern remains as the explicit
obstruction. -/
theorem exists_edgeSupport_switch_extendsAcrossCycle_or_exceptional_of_eq_transportBad_of_componentCoverCore
    {E : Type*} [DecidableEq E]
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n) :
    (∃ edgeSupport : Finset E, ∃ a b : Color,
      CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport data σ edgeSupport a b ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C))) ∨
    data.IsExceptional := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_or_exceptional_of_eq_transportBad_of_componentCoverCore
        hσ0 data hw with hrepair | hexceptional
  · rcases hrepair with ⟨action, huses, _hrealizes, _hnotExtends, hextends⟩
    rcases huses with huses | huses | huses | huses
    · subst action
      refine Or.inl ⟨data.redBlueEdge₁, σ red, σ blue, ?_, ?_⟩
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
        simpa [hw]
          using hextends
    · subst action
      refine Or.inl ⟨data.redBlueEdge₂, σ red, σ blue, ?_, ?_⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
        simpa [hw]
          using hextends
    · subst action
      refine Or.inl ⟨data.redPurpleEdge₁, σ red, σ purple, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
        simpa [hw]
          using hextends
    · subst action
      refine Or.inl ⟨data.redPurpleEdge₂, σ red, σ purple, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      · rw [← cap5BoundaryActionOfEdgeSet_apply_eq_boundaryWordOfEdges_switch]
        simpa [hw]
          using hextends
  · exact Or.inr hexceptional

/-- Core component-cover data plus the canonical annulus/Jordan cyclic-cut realization route gives
an actual edge switch whose restricted CAP5 boundary word extends.  This is the graph-facing
version of the exceptional-branch elimination: the finite CAP5 split may produce an exceptional
orientation, but the canonical realization data turns that orientation into a forbidden small
cyclic edge cut. -/
theorem exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.edgeSet → Color)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
      CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport data σ edgeSupport a b ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) := by
  rcases
      exists_edgeSupport_switch_extendsAcrossCycle_or_exceptional_of_eq_transportBad_of_componentCoverCore
        boundaryEdge C hσ0 data hw with
    hrepair | hexceptional
  · exact hrepair
  · exact False.elim
      ((data.not_isExceptional_of_noCyclicEdgeCut_of_canonicalRealizationData
          p0Inside p4Inside hnoCut hcanonical) hexceptional)

/-- Core component-cover data plus the actual exceptional-branch realization route gives an edge
switch whose restricted CAP5 boundary word extends.  This is the weakest graph-facing form: the
planar/Jordan layer only has to produce one compatible cyclic-cut realization when the finite CAP5
split really lands in the exceptional branch. -/
theorem exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.edgeSet → Color)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hnoCut : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hrealizationData :
      data.IsExceptional →
        data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
      CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport data σ edgeSupport a b ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) := by
  rcases
      exists_edgeSupport_switch_extendsAcrossCycle_or_exceptional_of_eq_transportBad_of_componentCoverCore
        boundaryEdge C hσ0 data hw with
    hrepair | hexceptional
  · exact hrepair
  · exact False.elim
      ((data.not_isExceptional_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
          p0Inside p4Inside hnoCut hrealizationData) hexceptional)

/-- Named cyclic-edge-connectivity form of the actual exceptional-branch graph-facing switch
endpoint. -/
theorem exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.edgeSet → Color)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrealizationData :
      data.IsExceptional →
        data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside) :
    ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
      CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport data σ edgeSupport a b ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) :=
  exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverCore_of_noCyclicEdgeCut_of_someExceptionalAnnulusCyclicCutRealizationData
    boundaryEdge C hσ0 data hw p0Inside p4Inside
    hcyclic.noCyclicEdgeCutOfSizeAtMostFour hrealizationData

/-- Named cyclic-edge-connectivity form of the graph-facing core CAP5 switch endpoint. -/
theorem exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.edgeSet → Color)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcanonical :
      data.HasCanonicalExceptionalAnnulusCyclicCutRealizationData (G := G)
        p0Inside p4Inside) :
    ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
      CAP5TransportedEdgeSwitchUsesComponentCoverCoreSupport data σ edgeSupport a b ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) :=
  exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
    boundaryEdge C hσ0 data hw p0Inside p4Inside hcyclic
    (fun hExceptional =>
      data.hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_canonicalRealizationData
        p0Inside p4Inside hExceptional hcanonical)

/-- Bundled edge-Kempe component-cover data for one transported bad CAP5 word gives an actual
edge switch that preserves zero-boundary and makes the restricted boundary word extend. -/
theorem exists_isZeroBoundary_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_edgeKempeComponentCoverData
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hCzero : D.isZeroBoundary C)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n)
    (hw :
      cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n) :
    ∃ edgeSupport : Finset E, ∃ a b : Color,
      D.isZeroBoundary (switch a b (edgeSupport : Set E) C) ∧
      CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases
      exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverData
        boundaryEdge C hσ0 data.toEdgeComponentCoverData hw with
    ⟨edgeSupport, a, b, huses, hextends⟩
  exact
    ⟨edgeSupport, a, b,
      switch_isZeroBoundary_of_edgeKempeComponentCoverData_of_uses hCzero huses,
      hextends⟩

/-- Structured-data form of the edge-support solved-word endpoint for one transported bad CAP5
word. -/
theorem cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E]
    {w : CAP5BoundaryWord} {boundaryEdge : Fin 5 → E}
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hw : w = cap5TransportedBadBoundaryWord σ n) :
    CAP5BoundaryWordSolved w := by
  rcases
      exists_boundaryActionRepairsWord_usingTransportedEdgeSupport_of_eq_transportBad_of_componentCoverData
        hσ0 data hw with
    ⟨_action, _huses, _hrealizes, hrepairs⟩
  exact cap5BoundaryWordSolved_of_boundaryActionRepairsWord hrepairs

/-- Block-`(2,1,1,1)` endpoint from transported edge-support component covers.  For every
normal-form presentation of the bad CAP5 boundary word, the graph/Kempe layer may provide four
finite edge supports plus their normalized boundary restrictions. -/
theorem cap5BoundaryWordSolved_of_block2111_of_transportEdgeComponentCoverSupports
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E)
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ redBlueEdge₁ redBlueEdge₂ redPurpleEdge₁ redPurpleEdge₂ : Finset E,
        ∃ redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5),
          cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₁ =
            cap5RotateBoundarySupportN n redBlue₁ ∧
          cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₂ =
            cap5RotateBoundarySupportN n redBlue₂ ∧
          cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₁ =
            cap5RotateBoundarySupportN n redPurple₁ ∧
          cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₂ =
            cap5RotateBoundarySupportN n redPurple₂ ∧
          CAP5BadRedBlueComponentCover redBlue₁ redBlue₂ ∧
          CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂ ∧
          ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂) :
    CAP5BoundaryWordSolved w := by
  rcases hbad with ⟨σ, n, hσ0, hw⟩
  rcases hcomponentCovers hσ0 hw with
    ⟨redBlueEdge₁, redBlueEdge₂, redPurpleEdge₁, redPurpleEdge₂,
      redBlue₁, redBlue₂, redPurple₁, redPurple₂,
      hredBlue₁, hredBlue₂, hredPurple₁, hredPurple₂,
      hredBlue, hredPurple, hnotExceptional⟩
  exact
    cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverSupports
      boundaryEdge hσ0 hredBlue₁ hredBlue₂ hredPurple₁ hredPurple₂
      hredBlue hredPurple hnotExceptional hw

/-- Colored block-`(2,1,1,1)` endpoint from transported edge-support component covers. -/
theorem cap5BoundaryWordSolved_of_coloredBlock2111_of_transportEdgeComponentCoverSupports
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E)
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasColoredBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ redBlueEdge₁ redBlueEdge₂ redPurpleEdge₁ redPurpleEdge₂ : Finset E,
        ∃ redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5),
          cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₁ =
            cap5RotateBoundarySupportN n redBlue₁ ∧
          cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₂ =
            cap5RotateBoundarySupportN n redBlue₂ ∧
          cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₁ =
            cap5RotateBoundarySupportN n redPurple₁ ∧
          cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₂ =
            cap5RotateBoundarySupportN n redPurple₂ ∧
          CAP5BadRedBlueComponentCover redBlue₁ redBlue₂ ∧
          CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂ ∧
          ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_block2111_of_transportEdgeComponentCoverSupports
    boundaryEdge (cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad) hcomponentCovers

/-- Structured-data form of the block-`(2,1,1,1)` edge-support endpoint. -/
theorem cap5BoundaryWordSolved_of_block2111_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved w := by
  rcases hbad with ⟨σ, n, hσ0, hw⟩
  exact cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverData
    hσ0 (hcomponentCovers hσ0 hw) hw

/-- Structured-data form of the colored block-`(2,1,1,1)` edge-support endpoint. -/
theorem cap5BoundaryWordSolved_of_coloredBlock2111_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasColoredBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_block2111_of_transportEdgeComponentCoverData
    (cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad) hcomponentCovers

/-- Block-`(2,1,1,1)` endpoint from raw component-cover supports.  This removes an
administrative record-construction step from the graph-facing obligation: for every transported
normal form, it is enough to supply the two red/blue supports, the two red/purple supports, their
cover facts, and the non-exceptional witness. -/
theorem cap5BoundaryWordSolved_of_block2111_of_transportComponentCoverSupports
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5),
          CAP5BadRedBlueComponentCover redBlue₁ redBlue₂ ∧
          CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂ ∧
          ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂) :
    CAP5BoundaryWordSolved w := by
  refine cap5BoundaryWordSolved_of_block2111_of_transportComponentCovers hbad ?_
  intro σ n hσ0 hw
  rcases hcomponentCovers hσ0 hw with
    ⟨redBlue₁, redBlue₂, redPurple₁, redPurple₂, hredBlue, hredPurple, hnotExceptional⟩
  let p : CAP5BadPairingSupports :=
    { redBlue₁ := redBlue₁
      redBlue₂ := redBlue₂
      redPurple₁ := redPurple₁
      redPurple₂ := redPurple₂ }
  refine ⟨p, ⟨hredBlue, hredPurple⟩, ?_⟩
  simpa [p, CAP5BadPairingSupports.IsExceptional] using hnotExceptional

/-- Colored block-`(2,1,1,1)` endpoint from raw component-cover supports. -/
theorem cap5BoundaryWordSolved_of_coloredBlock2111_of_transportComponentCoverSupports
    {w : CAP5BoundaryWord}
    (hbad : CAP5BoundaryWordHasColoredBlock2111 w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5),
          CAP5BadRedBlueComponentCover redBlue₁ redBlue₂ ∧
          CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂ ∧
          ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_block2111_of_transportComponentCoverSupports
    (cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad) hcomponentCovers

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

/-- Component-cover form of the transported CAP5 reducibility split.  Under the parity shape
forced by a proper cubic coloring, the good branch extends immediately; for the bad branch, it is
enough for the graph-level proof to supply transported component covers and rule out the
simultaneous exceptional pairing pattern. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_odd_of_transportComponentCovers
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ p : CAP5BadPairingSupports, p.HasComponentCovers ∧ ¬ p.IsExceptional) :
    CAP5BoundaryWordSolved w := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact cap5BoundaryWordSolved_of_coloredBlock311 hgood
  · exact cap5BoundaryWordSolved_of_coloredBlock2111_of_transportComponentCovers
      hbad hcomponentCovers

/-- Raw support-cover form of the transported CAP5 reducibility split.  Under the parity shape
forced by a proper cubic coloring, the graph/Kempe layer only has to produce four concrete
boundary support sets for each normalized bad-word presentation, prove that they cover the two
active color-pair supports, and exclude the simultaneous exceptional pattern. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_odd_of_transportComponentCoverSupports
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5),
          CAP5BadRedBlueComponentCover redBlue₁ redBlue₂ ∧
          CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂ ∧
          ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂) :
    CAP5BoundaryWordSolved w := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact cap5BoundaryWordSolved_of_coloredBlock311 hgood
  · exact cap5BoundaryWordSolved_of_coloredBlock2111_of_transportComponentCoverSupports
      hbad hcomponentCovers

/-- Edge-support form of the transported CAP5 reducibility split.  Under the parity shape
forced by a proper cubic coloring, it is enough for each transported bad-word presentation to
provide four finite edge supports whose boundary restrictions give non-exceptional CAP5
component covers. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_odd_of_transportEdgeComponentCoverSupports
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E)
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        ∃ redBlueEdge₁ redBlueEdge₂ redPurpleEdge₁ redPurpleEdge₂ : Finset E,
        ∃ redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5),
          cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₁ =
            cap5RotateBoundarySupportN n redBlue₁ ∧
          cap5BoundarySupportOfEdges boundaryEdge redBlueEdge₂ =
            cap5RotateBoundarySupportN n redBlue₂ ∧
          cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₁ =
            cap5RotateBoundarySupportN n redPurple₁ ∧
          cap5BoundarySupportOfEdges boundaryEdge redPurpleEdge₂ =
            cap5RotateBoundarySupportN n redPurple₂ ∧
          CAP5BadRedBlueComponentCover redBlue₁ redBlue₂ ∧
          CAP5BadRedPurpleComponentCover redPurple₁ redPurple₂ ∧
          ¬ CAP5BadExceptionalPairingPattern redBlue₁ redBlue₂ redPurple₁ redPurple₂) :
    CAP5BoundaryWordSolved w := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact cap5BoundaryWordSolved_of_coloredBlock311 hgood
  · exact cap5BoundaryWordSolved_of_coloredBlock2111_of_transportEdgeComponentCoverSupports
      boundaryEdge hbad hcomponentCovers

/-- Structured-data form of the edge-support transported CAP5 reducibility split. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_odd_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved w := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact cap5BoundaryWordSolved_of_coloredBlock311 hgood
  · exact cap5BoundaryWordSolved_of_coloredBlock2111_of_transportEdgeComponentCoverData
      hbad hcomponentCovers

/-- Sum-zero form of the edge-support transported CAP5 reducibility split.  For a nonzero CAP5
word, the zero total color sum is equivalent to the odd red/blue/purple parity shape, but this
form matches graph-side cubic cut equations more directly. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E}
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hsum : (∑ i : Fin 5, w i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved w :=
  cap5BoundaryWordSolved_of_nonzero_of_odd_of_transportEdgeComponentCoverData
    hnz (cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero hnz hsum)
    hcomponentCovers

/-- Sum-zero CAP5 reducibility split from core edge component-cover data using the weakest
exceptional-branch realization input.  The topological layer only has to realize a cyclic cut when
the selected transported component-cover package is actually exceptional. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hsum : (∑ i : Fin 5, w i) = 0)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hrealizationData :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw : w = cap5TransportedBadBoundaryWord σ n),
        (hcomponentCovers hσ0 hw).IsExceptional →
          (hcomponentCovers hσ0 hw).HasSomeExceptionalAnnulusCyclicCutRealizationData
            (G := G) p0Inside p4Inside) :
    CAP5BoundaryWordSolved w := by
  have hodd : CAP5BoundaryWordHasOddColorCounts w :=
    cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero hnz hsum
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact cap5BoundaryWordSolved_of_coloredBlock311 hgood
  · rcases cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad with
      ⟨σ, n, hσ0, hw⟩
    exact
      cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
        hσ0 (hcomponentCovers hσ0 hw) hw p0Inside p4Inside hcyclic
        (hrealizationData hσ0 hw)

/-- Sum-zero CAP5 reducibility split from core edge component-cover data.  Unlike
`CAP5TransportedEdgeComponentCoverData`, the core package may still be in the simultaneous
exceptional pairing branch; the canonical annulus/Jordan realization obligation eliminates that
branch under cyclic five-edge-connectivity. -/
theorem cap5BoundaryWordSolved_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hsum : (∑ i : Fin 5, w i) = 0)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        w = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hcanonical :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw : w = cap5TransportedBadBoundaryWord σ n),
        (hcomponentCovers hσ0 hw).HasCanonicalExceptionalAnnulusCyclicCutRealizationData
          (G := G) p0Inside p4Inside) :
    CAP5BoundaryWordSolved w := by
  exact
    cap5BoundaryWordSolved_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
      hnz hsum p0Inside p4Inside hcyclic hcomponentCovers
      (fun hσ0 hw hExceptional =>
        (hcomponentCovers hσ0 hw).hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_canonicalRealizationData
          p0Inside p4Inside hExceptional (hcanonical hσ0 hw))

/-- Graph-facing split for a CAP5 boundary word obtained from an edge coloring.  Under the
nonzero boundary and zero-sum equations, either the boundary word already extends across the cap,
or structured component-cover data produces a concrete edge-level switch whose restricted
boundary word extends. -/
theorem cap5BoundaryWordOfEdges_extends_or_switchRepairOutcome_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C) := by
  have hodd :
      CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
    cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero hnz hsum
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact Or.inl (cap5_extendsAcrossCycle_of_coloredBlock311 hgood)
  · rcases cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad with
      ⟨σ, n, hσ0, hw⟩
    let data : CAP5TransportedEdgeComponentCoverData boundaryEdge n :=
      hcomponentCovers hσ0 hw
    rcases
        exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverData
          boundaryEdge C hσ0 data hw with
      ⟨edgeSupport, a, b, huses, hextends⟩
    exact Or.inr ⟨
      { σ := σ
        n := n
        hσ0 := hσ0
        data := data
        edgeSupport := edgeSupport
        a := a
        b := b
        huses := huses
        hextends := hextends }⟩

/-- Edge-switch form of the graph-facing CAP5 split.  This erases the repair-outcome package
when downstream code only needs the actual switch that makes the boundary word extend. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset E, ∃ a b : Color,
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases
      cap5BoundaryWordOfEdges_extends_or_switchRepairOutcome_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
        boundaryEdge C hnz hsum hcomponentCovers with
    hextends | houtcome
  · exact Or.inl hextends
  · exact Or.inr
      (exists_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcome houtcome)

/-- Core-data graph-facing CAP5 split using the weakest exceptional-branch realization input.
Compared with the canonical orientation-by-orientation endpoint, this asks the planar/Jordan layer
only for one realized cyclic cut when the selected transported component-cover data is exceptional. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.edgeSet → Color)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hrealizationData :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n),
        (hcomponentCovers hσ0 hw).IsExceptional →
          (hcomponentCovers hσ0 hw).HasSomeExceptionalAnnulusCyclicCutRealizationData
            (G := G) p0Inside p4Inside) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) := by
  have hodd :
      CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
    cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero hnz hsum
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact Or.inl (cap5_extendsAcrossCycle_of_coloredBlock311 hgood)
  · rcases cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad with
      ⟨σ, n, hσ0, hw⟩
    let data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n :=
      hcomponentCovers hσ0 hw
    rcases
        exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
          boundaryEdge C hσ0 data hw p0Inside p4Inside hcyclic
          (hrealizationData hσ0 hw) with
      ⟨edgeSupport, a, b, _huses, hextends⟩
    exact Or.inr ⟨edgeSupport, a, b, hextends⟩

/-- Core-data graph-facing CAP5 split.  The bad branch may produce the simultaneous exceptional
pairing, but cyclic five-edge-connectivity plus canonical annulus/Jordan realization data rules it
out and still produces an actual finite edge-support switch. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_canonicalRealizationData
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.edgeSet → Color)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (hcanonical :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n),
        (hcomponentCovers hσ0 hw).HasCanonicalExceptionalAnnulusCyclicCutRealizationData
          (G := G) p0Inside p4Inside) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) := by
  exact
    cap5BoundaryWordOfEdges_extends_or_exists_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverCore_of_cyclicallyFiveEdgeConnected_of_someExceptionalAnnulusCyclicCutRealizationData
      boundaryEdge C hnz hsum p0Inside p4Inside hcyclic hcomponentCovers
      (fun hσ0 hw hExceptional =>
        (hcomponentCovers hσ0 hw).hasSomeExceptionalAnnulusCyclicCutRealizationData_of_isExceptional_of_canonicalRealizationData
          p0Inside p4Inside hExceptional (hcanonical hσ0 hw))

/-- Kempe-certified edge-switch form of the graph-facing CAP5 split.  The repair alternative is
now strong enough for the surrounding zero-boundary route: the switched coloring still satisfies
the vertex-sum equations. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hCzero : D.isZeroBoundary C)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempe :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset E, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set E) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  rcases
      cap5BoundaryWordOfEdges_extends_or_switchRepairOutcome_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
        boundaryEdge C hnz hsum hcomponentCovers with
    hextends | houtcome
  · exact Or.inl hextends
  · exact Or.inr
      (exists_isZeroBoundary_edgeSupport_switch_extendsAcrossCycle_of_switchRepairOutcomeUsesKempeFinset
        houtcome hCzero hkempe)

/-- Data-level Kempe-certified edge-switch form of the graph-facing CAP5 split.  Instead of
asking for an opaque proof about every repair outcome, this endpoint asks the graph layer to
certify that the four transported component-cover edge supports are finite Kempe components with
even incidence. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataUsesKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hCzero : D.isZeroBoundary C)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempeData :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets D C outcome.σ outcome.data) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset E, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set E) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    boundaryEdge C hCzero hnz hsum hcomponentCovers
    (fun outcome =>
      switchRepairOutcomeUsesKempeFinset_of_dataUsesKempeFinsets
        (hkempeData outcome))

/-- Direct data-level Kempe-certified edge-switch split.  This is the graph-facing obligation in
its most concrete form: for every transported bad CAP5 presentation, the component-cover data
returned by `hcomponentCovers` has four finite Kempe supports with even incidence.  The proof then
extracts the selected support and proves that the resulting switch preserves zero-boundary. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataWithKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hCzero : D.isZeroBoundary C)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempeCovers :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n),
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
          D C σ (hcomponentCovers hσ0 hw)) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset E, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set E) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  have hodd :
      CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
    cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero hnz hsum
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact Or.inl (cap5_extendsAcrossCycle_of_coloredBlock311 hgood)
  · rcases cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad with
      ⟨σ, n, hσ0, hw⟩
    let data : CAP5TransportedEdgeComponentCoverData boundaryEdge n :=
      hcomponentCovers hσ0 hw
    rcases
        exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverData
          boundaryEdge C hσ0 data hw with
      ⟨edgeSupport, a, b, huses, hextends⟩
    have hsupport : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b :=
      edgeSupportUsesKempeFinset_of_dataUsesKempeFinsets_of_uses
        (hkempeCovers hσ0 hw) huses
    exact Or.inr
      ⟨edgeSupport, a, b,
        switch_isZeroBoundary_of_edgeSupportUsesKempeFinset hCzero hsupport,
        hextends⟩

/-- Bundled-data form of the direct data-level Kempe-certified CAP5 split.  The caller supplies
one aligned object per transported bad CAP5 presentation, rather than separate component-cover
and Kempe-certificate functions. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeKempeComponentCoverData
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hCzero : D.isZeroBoundary C)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        (hσ0 : σ 0 = 0) →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset E, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set E) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataWithKempeFinsets
    boundaryEdge C hCzero hnz hsum
    (fun hσ0 hw => (hcomponentCovers hσ0 hw).toEdgeComponentCoverData)
    (fun hσ0 hw => (hcomponentCovers hσ0 hw).usesKempeFinsets)

/-- Direct data-level CAP5 split preserving the full zero-boundary set.  This is the
iteration-friendly form of the graph-facing CAP5 repair: the switched coloring remains in
`D.zeroBoundarySet`, not merely in the vertex-sum kernel. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_mem_zeroBoundarySet_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataWithKempeFinsets
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hCzero : C ∈ D.zeroBoundarySet)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempeCovers :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n),
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
          D C σ (hcomponentCovers hσ0 hw)) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset E, ∃ a b : Color,
        switch a b (edgeSupport : Set E) C ∈ D.zeroBoundarySet ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) := by
  have hodd :
      CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
    cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero hnz hsum
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
      hnz hodd with hgood | hbad
  · exact Or.inl (cap5_extendsAcrossCycle_of_coloredBlock311 hgood)
  · rcases cap5BoundaryWordHasBlock2111_of_coloredBlock2111 hbad with
      ⟨σ, n, hσ0, hw⟩
    let data : CAP5TransportedEdgeComponentCoverData boundaryEdge n :=
      hcomponentCovers hσ0 hw
    rcases
        exists_edgeSupport_switch_extendsAcrossCycle_of_eq_transportBad_of_componentCoverData
          boundaryEdge C hσ0 data hw with
      ⟨edgeSupport, a, b, huses, hextends⟩
    have hsupport : CAP5EdgeSupportUsesKempeFinset D C edgeSupport a b :=
      edgeSupportUsesKempeFinset_of_dataUsesKempeFinsets_of_uses
        (hkempeCovers hσ0 hw) huses
    exact Or.inr
      ⟨edgeSupport, a, b,
        switch_mem_zeroBoundarySet_of_edgeSupportUsesKempeFinset hCzero hsupport,
        hextends⟩

/-- Bundled-data form of the full-zero-boundary CAP5 split.  The graph geometry layer supplies
the transported edge-Kempe component-cover data directly; the repair branch stays inside
`D.zeroBoundarySet`. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_mem_zeroBoundarySet_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeKempeComponentCoverData
    {V E : Type*} [Fintype E] [DecidableEq E]
    {D : ZeroBoundaryData V E} (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hCzero : C ∈ D.zeroBoundarySet)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        (hσ0 : σ 0 = 0) →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset E, ∃ a b : Color,
        switch a b (edgeSupport : Set E) C ∈ D.zeroBoundarySet ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set E) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_mem_zeroBoundarySet_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataWithKempeFinsets
    boundaryEdge C hCzero hnz hsum
    (fun hσ0 hw => (hcomponentCovers hσ0 hw).toEdgeComponentCoverData)
    (fun hσ0 hw => (hcomponentCovers hσ0 hw).usesKempeFinsets)

/-- Manuscript-facing edge-switch split for a Tait edge coloring.  If the CAP5 boundary edges
enumerate a zero-boundary incidence set, then the restricted boundary word either extends across
the cap immediately or admits a concrete edge-level switch repair extracted from the supplied
component-cover data. -/
theorem cap5BoundaryWordOfEdges_extends_or_switchRepairOutcome_of_isTaitEdgeColoring_of_isZeroBoundary_at_of_transportEdgeComponentCoverData
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      Nonempty (CAP5EdgeSwitchRepairOutcome boundaryEdge C) :=
  cap5BoundaryWordOfEdges_extends_or_switchRepairOutcome_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    boundaryEdge C
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
      boundaryEdge C hinj hincident hzero)
    hcomponentCovers

/-- Manuscript-facing edge-switch endpoint with the repair package erased.  It states exactly
what the graph route can use next: either the original CAP5 boundary word extends, or an explicit
edge switch makes the restricted boundary word extend. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_edgeSupport_switch_extends_of_isTaitEdgeColoring_of_isZeroBoundary_at_of_transportEdgeComponentCoverData
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    boundaryEdge C
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
      boundaryEdge C hinj hincident hzero)
    hcomponentCovers

/-- Manuscript-facing Kempe-certified CAP5 repair endpoint.  The second branch exposes a
specific finite edge switch that preserves the zero-boundary equation and makes the CAP5 boundary
word extend across the cap. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_isTaitEdgeColoring_of_isZeroBoundary_at_of_transportEdgeComponentCoverData
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempe :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5EdgeSwitchRepairOutcomeUsesKempeFinset D outcome) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set G.edgeSet) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    boundaryEdge C hzero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
      boundaryEdge C hinj hincident hzero)
    hcomponentCovers hkempe

/-- Manuscript-facing data-level Kempe-certified CAP5 repair endpoint.  The graph layer supplies
Kempe/even-incidence certificates for the four transported component-cover supports; the endpoint
then chooses the support used by the CAP5 repair and returns a zero-boundary-preserving switch. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_isTaitEdgeColoring_of_isZeroBoundary_at_of_transportEdgeComponentCoverDataUsesKempeFinsets
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempeData :
      ∀ outcome : CAP5EdgeSwitchRepairOutcome boundaryEdge C,
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets D C outcome.σ outcome.data) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set G.edgeSet) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataUsesKempeFinsets
    boundaryEdge C hzero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
      boundaryEdge C hinj hincident hzero)
    hcomponentCovers hkempeData

/-- Manuscript-facing direct data-level Kempe-certified CAP5 endpoint.  The second branch is an
explicit finite edge switch preserving zero-boundary; the Kempe obligation is stated directly on
the component-cover data returned for each transported bad CAP5 presentation. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_isTaitEdgeColoring_of_isZeroBoundary_at_of_transportEdgeComponentCoverDataWithKempeFinsets
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempeCovers :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw : cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n),
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
          D C σ (hcomponentCovers hσ0 hw)) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set G.edgeSet) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataWithKempeFinsets
    boundaryEdge C hzero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
      boundaryEdge C hinj hincident hzero)
    hcomponentCovers hkempeCovers

/-- Manuscript-facing bundled-data CAP5 endpoint.  The graph geometry layer supplies the
transported edge-Kempe component-cover data directly; the theorem returns either immediate
extension or an explicit zero-boundary-preserving edge switch. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_isTaitEdgeColoring_of_isZeroBoundary_at_of_transportEdgeKempeComponentCoverData
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        (hσ0 : σ 0 = 0) →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeKempeComponentCoverData D C σ boundaryEdge n) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        D.isZeroBoundary (switch a b (edgeSupport : Set G.edgeSet) C) ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge (switch a b (edgeSupport : Set G.edgeSet) C)) :=
  cap5BoundaryWordOfEdges_extends_or_exists_isZeroBoundary_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeKempeComponentCoverData
    boundaryEdge C hzero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
      boundaryEdge C hinj hincident hzero)
    hcomponentCovers

/-- Manuscript-facing direct data-level CAP5 endpoint preserving the full zero-boundary set.  The
input coloring is a Tait edge coloring whose boundary incidence lies in `D.zeroBoundarySet`; the
repair branch returns a concrete Kempe switch that remains in the same full zero-boundary set, not
only in the single vertex equation. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_mem_zeroBoundarySet_edgeSupport_switch_extends_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at_of_transportEdgeComponentCoverDataWithKempeFinsets
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge (C : G.edgeSet → Color) =
          cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hkempeCovers :
      ∀ {σ : Color ≃ Color} {n : Nat}
        (hσ0 : σ 0 = 0)
        (hw :
          cap5BoundaryWordOfEdges boundaryEdge (C : G.edgeSet → Color) =
            cap5TransportedBadBoundaryWord σ n),
        CAP5TransportedEdgeComponentCoverDataUsesKempeFinsets
          D (C : G.edgeSet → Color) σ (hcomponentCovers hσ0 hw)) :
    CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (C : G.edgeSet → Color)) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        switch a b (edgeSupport : Set G.edgeSet) (C : G.edgeSet → Color) ∈
          D.zeroBoundarySet ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge
            (switch a b (edgeSupport : Set G.edgeSet) (C : G.edgeSet → Color))) :=
  cap5BoundaryWordOfEdges_extends_or_exists_mem_zeroBoundarySet_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverDataWithKempeFinsets
    boundaryEdge (C : G.edgeSet → Color) hzero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_mem_zeroBoundarySet_at
      boundaryEdge (C : G.edgeSet → Color) hinj hincident hzero)
    hcomponentCovers hkempeCovers

/-- Bundled-data version of the manuscript-facing full-zero-boundary CAP5 endpoint.  The graph
geometry layer supplies one Kempe-certified component-cover package for each transported bad CAP5
presentation; the theorem exposes the repair switch while preserving membership in
`D.zeroBoundarySet`. -/
theorem cap5BoundaryWordOfEdges_extends_or_exists_mem_zeroBoundarySet_edgeSupport_switch_extends_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at_of_transportEdgeKempeComponentCoverData
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        (hσ0 : σ 0 = 0) →
        cap5BoundaryWordOfEdges boundaryEdge (C : G.edgeSet → Color) =
          cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeKempeComponentCoverData
          D (C : G.edgeSet → Color) σ boundaryEdge n) :
    CAP5WordExtendsAcrossCycle
        (cap5BoundaryWordOfEdges boundaryEdge (C : G.edgeSet → Color)) ∨
      ∃ edgeSupport : Finset G.edgeSet, ∃ a b : Color,
        switch a b (edgeSupport : Set G.edgeSet) (C : G.edgeSet → Color) ∈
          D.zeroBoundarySet ∧
        CAP5WordExtendsAcrossCycle
          (cap5BoundaryWordOfEdges boundaryEdge
            (switch a b (edgeSupport : Set G.edgeSet) (C : G.edgeSet → Color))) :=
  cap5BoundaryWordOfEdges_extends_or_exists_mem_zeroBoundarySet_edgeSupport_switch_extends_of_nonzero_of_sum_zero_of_transportEdgeKempeComponentCoverData
    boundaryEdge (C : G.edgeSet → Color) hzero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_mem_zeroBoundarySet_at
      boundaryEdge (C : G.edgeSet → Color) hinj hincident hzero)
    hcomponentCovers

/-- Edge-coloring boundary restriction form of the structured CAP5 reducibility split.  This is
the graph-facing spelling: given an edge coloring `C`, solve the CAP5 boundary word obtained by
restricting `C` to the five boundary edges. -/
theorem cap5BoundaryWordOfEdges_solved_of_nonzero_of_odd_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hodd : CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C))
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordSolved_of_nonzero_of_odd_of_transportEdgeComponentCoverData
    hnz hodd hcomponentCovers

/-- Edge-coloring boundary restriction form using the graph-side boundary color-sum equation.
This is the preferred theorem target once the surrounding graph proof has established that the
five boundary edge colors are nonzero and sum to zero in `𝔽₂²`. -/
theorem cap5BoundaryWordOfEdges_solved_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hnz : CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C))
    (hsum : (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordSolved_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    hnz hsum hcomponentCovers

/-- Zero-boundary incidence form of the graph-facing CAP5 endpoint.  If the five boundary
edges enumerate a zero-boundary incidence set, the color-sum equation needed by the CAP5 parity
split follows from `D.isZeroBoundary C`. -/
theorem cap5BoundaryWordOfEdges_solved_of_forall_nonzero_of_isZeroBoundary_at_of_transportEdgeComponentCoverData
    {U E : Type*} [DecidableEq E] {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hC : ∀ i : Fin 5, C (boundaryEdge i) ≠ 0)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_solved_of_nonzero_of_sum_zero_of_transportEdgeComponentCoverData
    boundaryEdge C
    (cap5BoundaryWordOfEdges_isNonzero_of_forall_nonzero boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
      boundaryEdge C hinj hincident hzero)
    hcomponentCovers

/-- Full-zero-boundary-set form of the graph-facing CAP5 solved endpoint.  This exposes the
stronger invariant carried by `D.zeroBoundarySet` while using its vertex-sum component for the CAP5
cut equation. -/
theorem cap5BoundaryWordOfEdges_solved_of_forall_nonzero_of_mem_zeroBoundarySet_at_of_transportEdgeComponentCoverData
    {U E : Type*} [DecidableEq E] {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hC : ∀ i : Fin 5, C (boundaryEdge i) ≠ 0)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : C ∈ D.zeroBoundarySet)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_solved_of_forall_nonzero_of_isZeroBoundary_at_of_transportEdgeComponentCoverData
    boundaryEdge C hC hinj hincident hzero.1 hcomponentCovers

/-- Tait-coloring form of the zero-boundary CAP5 endpoint.  This is the manuscript-facing
interface: a Tait edge-coloring gives nonzero boundary colors, while the zero-boundary incidence
equation gives the CAP5 parity sum. -/
theorem cap5BoundaryWordOfEdges_solved_of_isTaitEdgeColoring_of_isZeroBoundary_at_of_transportEdgeComponentCoverData
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_solved_of_forall_nonzero_of_isZeroBoundary_at_of_transportEdgeComponentCoverData
    boundaryEdge C (fun i => hC (boundaryEdge i)) hinj hincident hzero hcomponentCovers

/-- Tait-coloring form of the full-zero-boundary CAP5 solved endpoint.  This is the strongest
manuscript-facing boundary-word solution surface when the surrounding graph proof carries the full
`D.zeroBoundarySet` invariant. -/
theorem cap5BoundaryWordOfEdges_solved_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at_of_transportEdgeComponentCoverData
    {V U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet)
    (hcomponentCovers :
      ∀ {σ : Color ≃ Color} {n : Nat},
        σ 0 = 0 →
        cap5BoundaryWordOfEdges boundaryEdge (C : G.edgeSet → Color) =
          cap5TransportedBadBoundaryWord σ n →
        CAP5TransportedEdgeComponentCoverData boundaryEdge n) :
    CAP5BoundaryWordSolved
      (cap5BoundaryWordOfEdges boundaryEdge (C : G.edgeSet → Color)) :=
  cap5BoundaryWordOfEdges_solved_of_forall_nonzero_of_mem_zeroBoundarySet_at_of_transportEdgeComponentCoverData
    boundaryEdge (C : G.edgeSet → Color) (fun i => hC (boundaryEdge i))
    hinj hincident hzero hcomponentCovers

/-- If an edge coloring restricts to a transported bad CAP5 boundary word, structured
edge-component-cover data supplies a boundary repair of that restricted word. -/
theorem cap5BoundaryWordOfEdges_solved_of_eq_transportBad_of_transportEdgeComponentCoverData
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) (C : E → Color)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverData boundaryEdge n)
    (hw :
      cap5BoundaryWordOfEdges boundaryEdge C = cap5TransportedBadBoundaryWord σ n) :
    CAP5BoundaryWordSolved (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordSolved_of_eq_transportBad_of_transportEdgeComponentCoverData
    hσ0 data hw

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
