import Mettapedia.GraphTheory.FourColor.GeneralTubeNodes
import Mettapedia.GraphTheory.FourColor.GeneralTubeExclusion

/-!
# No long corridor of bounded width, of any shapes

A chain of slabs of *arbitrary* shapes (`TubeAny`): each slab carries its own
(weak) shape check, and no relation between consecutive slabs is assumed beyond the
nesting of sides.  The exclusion argument of `GeneralTubeExclusion` used the
stabilisation of a fixed shape's relation only to make the accepted word sets
of two nested cuts equal; putting the word set itself into the pigeonhole
carrier removes that hypothesis.  Result: in a graph-backed least
counterexample, a chain of `n` slabs of width `k` with good connected innermost
side and connected outermost complement has
`n + 1 ≤ k!·k!·(6k+1)·2^(4^k)` (`TubeAny.le_of_tubeAny`).  Per-shape
stabilisation indices (`TubeOf.le_of_tubeOf`) sharpen the bound; they are not
needed for finiteness.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition
open GoertzelV24PhysicalClosedCountBridge
open GoertzelV24ClosedCountReplacement
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24NormalizedTaitSupport
open GoertzelV24NormalizedSeamState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24ShoreStateDescent
open GoertzelV24RawNooseCountPumping
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph

universe u

section Chain

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- a chain of slabs of arbitrary shapes, each carrying its shape check -/
inductive TubeAny (RS : RotationSystem.{u, u, u} V E) (k : Nat) [NeZero k] :
    (V → Prop) → Nat → Type (u + 1)
  | nil (inner : V → Prop) (e : Fin k ≃ BoundaryDart RS inner) : TubeAny RS k inner 0
  | cons {inner : V → Prop} {Vt It : Type u} [Nonempty Vt]
      {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} (hT : SlabShapeW T)
      (S : SlabOf RS T inner) {n : Nat} (rest : TubeAny RS k S.inner' n) :
      TubeAny RS k inner (n + 1)

namespace TubeAny

variable {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k]

def side : {inner : V → Prop} → {n : Nat} → TubeAny RS k inner n → Nat → (V → Prop)
  | inner, _, nil _ _, _ => inner
  | inner, _, cons _ _ _, 0 => inner
  | _, _, cons _ _ rest, r + 1 => rest.side r

noncomputable def sideEquiv : {inner : V → Prop} → {n : Nat} → (t : TubeAny RS k inner n) →
    (r : Nat) → Fin k ≃ BoundaryDart RS (t.side r)
  | _, _, nil _ e, _ => e
  | _, _, cons _ S _, 0 => S.inEquiv
  | _, _, cons _ _ rest, r + 1 => rest.sideEquiv r

end TubeAny

/-- a periodic chain is a chain -/
def TubeOf.toAny {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k] {Vt It : Type u}
    [Nonempty Vt] {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} (hT : SlabShape T) :
    {inner : V → Prop} → {n : Nat} → TubeOf RS T inner n → TubeAny RS k inner n
  | _, _, .nil inner e => .nil inner e
  | _, _, .cons S rest => .cons hT.toW S (rest.toAny hT)

theorem TubeOf.side_toAny {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k] {Vt It : Type u}
    [Nonempty Vt] {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} (hT : SlabShape T) :
    {inner : V → Prop} → {n : Nat} → (t : TubeOf RS T inner n) → ∀ r, (t.toAny hT).side r = t.side r
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _, 0 => rfl
  | _, _, .cons _ rest, r + 1 => rest.side_toAny hT r

/-- a chain with a weak shape check is a chain -/
def TubeOf.toAnyW {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k] {Vt It : Type u}
    [Nonempty Vt] {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} (hT : SlabShapeW T) :
    {inner : V → Prop} → {n : Nat} → TubeOf RS T inner n → TubeAny RS k inner n
  | _, _, .nil inner e => .nil inner e
  | _, _, .cons S rest => .cons hT S (rest.toAnyW hT)

theorem TubeOf.side_toAnyW {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k] {Vt It : Type u}
    [Nonempty Vt] {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} (hT : SlabShapeW T) :
    {inner : V → Prop} → {n : Nat} → (t : TubeOf RS T inner n) → ∀ r, (t.toAnyW hT).side r = t.side r
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _, 0 => rfl
  | _, _, .cons _ rest, r + 1 => rest.side_toAnyW hT r

end Chain

section Graph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
variable {rotation : SimpleGraphDartRotation.Data G} {k : Nat} [NeZero k]

namespace TubeAny

theorem goodSide_side : {inner : V → Prop} → {n : Nat} →
    (t : TubeAny rotation.toRotationSystem k inner n) → GoodSide (G := G) inner →
    ∀ r, r ≤ n → GoodSide (G := G) (t.side r)
  | _, _, nil _ _, h, _, _ => h
  | _, _, cons _ _ _, h, 0, _ => h
  | _, _, cons hT S rest, h, r + 1, hr => goodSide_side rest (S.goodSide_slab hT h) r (by omega)

theorem conn_side : {inner : V → Prop} → {n : Nat} →
    (t : TubeAny rotation.toRotationSystem k inner n) → GoodSide (G := G) inner →
    EdgeShoreConnected G (sideShore inner) →
    ∀ r, r ≤ n → EdgeShoreConnected G (sideShore (t.side r))
  | _, _, nil _ _, _, hc, _, _ => hc
  | _, _, cons _ _ _, _, hc, 0, _ => hc
  | _, _, cons hT S rest, hg, hc, r + 1, hr =>
    conn_side rest (S.goodSide_slab hT hg) (S.edgeShoreConnected_slab hT hg hc) r (by omega)

theorem cconn_side : {inner : V → Prop} → {n : Nat} →
    (t : TubeAny rotation.toRotationSystem k inner n) →
    EdgeShoreConnected G (ZigzagSlab.compShore (t.side n)) →
    ∀ r, r ≤ n → EdgeShoreConnected G (ZigzagSlab.compShore (t.side r))
  | _, _, nil _ _, hc, _, _ => hc
  | _, _, cons _ _ rest, hc, r + 1, hr => cconn_side rest hc r (by omega)
  | _, _, cons hT S rest, hc, 0, _ => by
    have h0 := cconn_side rest hc 0 (by omega)
    cases rest <;> exact S.edgeShoreConnected_comp_slab hT h0

theorem sideShore_ssubset_succ : {inner : V → Prop} → {n : Nat} →
    (t : TubeAny rotation.toRotationSystem k inner n) → ∀ r, r < n →
    sideShore (G := G) (t.side r) ⊂ sideShore (t.side (r + 1))
  | _, _, nil _ _, _, hr => absurd hr (Nat.not_lt_zero _)
  | _, _, cons hT S rest, 0, _ => by
    cases rest <;> exact S.sideShore_ssubset_inner' hT
  | _, _, cons _ _ rest, r + 1, hr => sideShore_ssubset_succ rest r (by omega)

theorem sideShore_ssubset_of_lt {inner : V → Prop} {n : Nat}
    (t : TubeAny rotation.toRotationSystem k inner n) (r : Nat) :
    ∀ r', r < r' → r' ≤ n → sideShore (G := G) (t.side r) ⊂ sideShore (t.side r')
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | r' + 1, h, hr' => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact (sideShore_ssubset_of_lt t r r' h (by omega)).trans
        (t.sideShore_ssubset_succ r' (by omega))
    · exact t.sideShore_ssubset_succ r (by omega)

end TubeAny

/-- the pigeonhole carrier: coordinates, hub rotation, phase, and the accepted words -/
abbrev CarrierW (k w : Nat) : Type u := Carrier.{u} k w × Set (Fin k → Color)

theorem card_color : Fintype.card Color = 4 := rfl

theorem card_carrierW (k w : Nat) :
    Fintype.card (CarrierW.{u} k w) =
      Nat.factorial k * (Nat.factorial k * (6 * w + 1)) * 2 ^ (4 ^ k) := by
  rw [Fintype.card_prod, card_carrier, Fintype.card_set, Fintype.card_fun, card_color,
    Fintype.card_fin]

/-- **Nested width-`k` nodes are few.**  A family of strictly nested majority nodes of
boundary width `k` in a graph-backed least counterexample has at most
`k!·k!·(6w+1)·2^(4^k)` members: the coordinates, hub rotation, phase and accepted
word set of a node take finitely many values, and two nested nodes with equal
values have equal card-phased state, which the splice lemma forbids. -/
theorem le_of_nested_nodes (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {w n : Nat} (nodes : Fin (n + 1) → LiteralShoreNode rotation k w)
    (e : ∀ r, Fin k ≃ BoundaryDart rotation.toRotationSystem (majorityRetainedKeep G (nodes r).shore))
    (hnested : ∀ r r' : Fin (n + 1), r < r' → (nodes r).shore ⊂ (nodes r').shore) :
    n + 1 ≤ Nat.factorial k * (Nat.factorial k * (6 * w + 1)) * 2 ^ (4 ^ k) := by
  by_contra hlt
  have hlt : Nat.factorial k * (Nat.factorial k * (6 * w + 1)) * 2 ^ (4 ^ k) < n + 1 :=
    Nat.lt_of_not_le hlt
  have hw : ∀ r : Fin (n + 1), boundaryWidth rotation (nodes r).shore = k := fun r =>
    boundaryWidth_eq_of_equiv rotation _ (e r)
  let f : Fin (n + 1) → CarrierW.{u} k w := fun r =>
    ((sigma rotation (nodes r).shore (hw _) rfl (e r),
      (normalizedState rotation (nodes r).shore (nodes r).innerOuter k (hw _)).hubRotation,
      shoreCardPhase w (nodes r).shore), sideWords (majorityRetainedKeep G (nodes r).shore) (e r))
  have hcard : Fintype.card (CarrierW.{u} k w) < Fintype.card (Fin (n + 1)) := by
    rw [card_carrierW, Fintype.card_fin]; exact hlt
  obtain ⟨j, j', hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hstate : ∀ a b : Fin (n + 1), f a = f b →
      (nodes a).cardPhasedState = (nodes b).cardPhasedState := by
    intro a b hab
    simp only [f, Prod.mk.injEq] at hab
    obtain ⟨⟨hσ, hhub, hphase⟩, hside⟩ := hab
    unfold LiteralShoreNode.cardPhasedState LiteralShoreNode.state
    rw [boundedNormalizedState_eq_of_width rotation _ _ _ (hw a),
      boundedNormalizedState_eq_of_width rotation _ _ _ (hw b), hphase]
    congr 2
    apply State.ext' hhub
    ext word
    rw [mem_support_iff_sideWords _ (nodes a).innerOuter (hw _) rfl (e a),
      mem_support_iff_sideWords _ (nodes b).innerOuter (hw _) rfl (e b), hσ, hside]
  rcases lt_or_gt_of_ne hne with hjj | hjj
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes j') (nodes j)
      (hnested _ _ hjj) (hstate j' j hf.symm)
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes j) (nodes j')
      (hnested _ _ hjj) (hstate j j' hf)

/-- **Nested good sides of width `k` are few**: the tube-free corridor lemma.  Any strictly
nested family of good sides with connected shores and connected complements, each of
boundary width `k`, has at most `k!·k!·(6k+1)·2^(4^k)` members. -/
theorem le_of_nested_sides (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hk2 : 2 ≤ k) {n : Nat} (side : Fin (n + 1) → (V → Prop))
    (e : ∀ r, Fin k ≃ BoundaryDart rotation.toRotationSystem (side r))
    (hgood : ∀ r, GoodSide (G := G) (side r))
    (hconn : ∀ r, EdgeShoreConnected G (sideShore (side r)))
    (hcconn : ∀ r, EdgeShoreConnected G (ZigzagSlab.compShore (side r)))
    (hnested : ∀ r r' : Fin (n + 1), r < r' → sideShore (G := G) (side r) ⊂ sideShore (side r')) :
    n + 1 ≤ Nat.factorial k * (Nat.factorial k * (6 * k + 1)) * 2 ^ (4 ^ k) := by
  let nodes : Fin (n + 1) → LiteralShoreNode rotation k k := fun r =>
    mkNode ⟨hgood r, hconn r, hcconn r⟩ (e r) hk2
  refine le_of_nested_nodes minimal nodes (fun r => (e r).trans (castBoundary ?_)) hnested
  exact (mkNode_keep _ _ _).symm

/-- **No long corridor of any shapes, on nodes.** -/
theorem le_of_tubeAny_nodes (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {w : Nat} {inner : V → Prop} {n : Nat}
    (t : TubeAny rotation.toRotationSystem k inner n)
    (nodes : Fin (n + 1) → LiteralShoreNode rotation k w)
    (hkeep : ∀ r : Fin (n + 1), majorityRetainedKeep G (nodes r).shore = t.side r)
    (hnested : ∀ r r' : Fin (n + 1), r < r' → (nodes r).shore ⊂ (nodes r').shore) :
    n + 1 ≤ Nat.factorial k * (Nat.factorial k * (6 * w + 1)) * 2 ^ (4 ^ k) :=
  le_of_nested_nodes minimal nodes (fun r => (t.sideEquiv r).trans (castBoundary (hkeep r).symm))
    hnested

/-- **No long corridor of any shapes, from base hypotheses.**  A chain of `n` slabs of
arbitrary shapes and width `k` in a graph-backed least counterexample, whose innermost
side is good with connected shore and whose outermost complement is connected, has
`n + 1 ≤ k!·k!·(6k+1)·2^(4^k)`. -/
theorem TubeAny.le_of_tubeAny (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hk2 : 2 ≤ k) {inner : V → Prop} {n : Nat}
    (t : TubeAny rotation.toRotationSystem k inner n)
    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))
    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n + 1 ≤ Nat.factorial k * (Nat.factorial k * (6 * k + 1)) * 2 ^ (4 ^ k) := by
  let nodes : Fin (n + 1) → LiteralShoreNode rotation k k := fun r =>
    mkNode ⟨t.goodSide_side hgood r (by omega), t.conn_side hgood hconn r (by omega),
      t.cconn_side hcconn r (by omega)⟩ (t.sideEquiv r) hk2
  exact le_of_tubeAny_nodes minimal t nodes (fun r => mkNode_keep _ _ _)
    (fun r r' hrr' => t.sideShore_ssubset_of_lt r r' hrr' (by omega))

/-- **No long periodic corridor of a weakly-shaped slab, without a table.**  The
stabilisation-free bound for chains of one shape whose layers may be disconnected. -/
theorem TubeOf.le_of_tubeOf_any {Vt It : Type u} [Nonempty Vt]
    {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} (hT : SlabShapeW T)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) (hk2 : 2 ≤ k)
    {inner : V → Prop} {n : Nat} (t : TubeOf rotation.toRotationSystem T inner n)
    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))
    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n + 1 ≤ Nat.factorial k * (Nat.factorial k * (6 * k + 1)) * 2 ^ (4 ^ k) :=
  TubeAny.le_of_tubeAny minimal hk2 (t.toAnyW hT) hgood hconn (by rwa [t.side_toAnyW hT])

end Graph

end TubeSlab
end Mettapedia.GraphTheory.FourColor
