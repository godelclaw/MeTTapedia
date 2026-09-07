import Mettapedia.GraphTheory.FourColor.SphericalMarkedCotreeChain
import Mettapedia.GraphTheory.FourColor.MarkedSeamState

/-!
# A full physical seam fixing designated crossing darts

Large bounded-dual-radius spherical maps supply a marked-free cotree chain.
Pigeonhole is applied to exact seam/support states together with the optional
positions of named ambient darts. The resulting physical seam fixes those
darts, has strict material between its shores, and feeds the existing
structural and zero-Count replacement constructors. Designated-hole data
and the global wall-free geometric transfer are separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24ConnectedEdgeShoreMajority GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24MajorityShoreStateDescent GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShorePhysicalReplacement GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphTaitBridge
open SphericalMarkedCotreeChain MarkedSeamState

noncomputable section
universe u v
attribute [local instance] Classical.propDecidable

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {M : Type v} [Fintype M]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Explicit size sufficient for a repeated marked seam state. -/
def vertexBound (h vertices darts : ℕ) : ℕ :=
  markedCotreeVertexBound h vertices (stateBound (2 * h + 1) darts)

/-- The supplied object names both literal shores, their common width, a
strict unmarked star, and the exact state equality including dart positions.
There is no supplied matching or supplied nested-chain hypothesis. -/
structure SeamPair (rotation : Data G) (marks : Finset V) (mark : M → G.Dart)
    (w : ℕ) where
  inner : LiteralShoreNode rotation w w
  outer : LiteralShoreNode rotation w w
  nested : inner.shore ⊂ outer.shore
  marks_constant : ∀ v ∈ marks,
    majorityVertexSide G inner.shore v ↔ majorityVertexSide G outer.shore v
  strictVertex : V
  strict_unmarked : strictVertex ∉ marks
  strict_star : ∀ e ∈ incidentEdgeFinset G strictVertex, e ∈ outer.shore \ inner.shore
  width : ℕ
  outerWidth : boundaryWidth rotation outer.shore = width
  innerWidth : boundaryWidth rotation inner.shore = width
  state_eq : ofShore rotation outer.shore outer.innerOuter mark width outerWidth =
    ofShore rotation inner.shore inner.innerOuter mark width innerWidth

/-- The marked geometric supplier followed by finite-state repetition.
Neither minimality nor non-colourability is a premise of the construction. -/
theorem exists_seamPair_of_large_card (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root : OrbitFace rotation.toRotationSystem) (h : ℕ)
    (marks : Finset V) (mark : M → G.Dart)
    (hradius : ∀ f, (orbitFaceDualGraph rotation).dist f root ≤ h)
    (hlarge : vertexBound h marks.card (Fintype.card M) < Fintype.card V) :
    Nonempty (SeamPair rotation marks mark (2 * h + 1)) := by
  let w := 2 * h + 1
  let n := stateBound w (Fintype.card M)
  obtain ⟨nodes, hnest, hmarks, hstar⟩ :=
    exists_marked_nodes_of_large_card rotation ambient htwo root h n marks hradius hlarge
  let literal := fun i => (nodes i).toLiteralOfSpherical rotation ambient
  let state := fun i => boundedOfShore rotation (literal i).shore
    (literal i).innerOuter mark w (literal i).widthBound
  have hcard : Fintype.card (Bounded.{u} M w) < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt (card_bounded_le (M := M) w) (Nat.lt_succ_self n)
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt state hcard
  have hordered : ∃ i j, i < j ∧ state j = state i := by
    rcases lt_or_gt_of_ne hne with hij | hij
    · exact ⟨i, j, hij, heq.symm⟩
    · exact ⟨j, i, hij, heq⟩
  obtain ⟨i, j, hij, heq⟩ := hordered
  obtain ⟨width, outerWidth, innerWidth, hs⟩ :=
    boundedOfShore_eq_elim rotation (literal j).shore (literal i).shore
      (literal j).innerOuter (literal i).innerOuter mark w
      (literal j).widthBound (literal i).widthBound heq
  obtain ⟨v, hv, _, _, hvs⟩ := hstar i j hij
  exact ⟨{
    inner := literal i
    outer := literal j
    nested := hnest i j hij
    marks_constant := fun v hv => (hmarks i v hv).trans (hmarks j v hv).symm
    strictVertex := v
    strict_unmarked := hv
    strict_star := hvs
    width := width
    outerWidth := outerWidth
    innerWidth := innerWidth
    state_eq := hs }⟩

namespace SeamPair
variable {rotation : Data G} {marks : Finset V} {mark : M → G.Dart} {w : ℕ}

/-- The seam is the actual matching used by physical replacement. -/
def matching (pair : SeamPair rotation marks mark w) :=
  replacementMatching rotation pair.outer.shore pair.inner.shore pair.width
    pair.outerWidth pair.innerWidth

/-- The literal smaller sewn map, before its structural certificate. -/
abbrev candidate (pair : SeamPair rotation marks mark w) :=
  replacementCandidate rotation pair.outer.shore pair.inner.shore
    pair.outer.outsideOuter pair.inner.innerOuter pair.width
    pair.outerWidth pair.innerWidth

/-- Forget only the sewn carrier tags; each dart keeps its ambient name. -/
def ambientDart (pair : SeamPair rotation marks mark w) : pair.candidate.D → G.Dart
  | Sum.inl (Sum.inl d) => d.val.val
  | Sum.inl (Sum.inr d) => d.val.val
  | Sum.inr (Sum.inl d) => d.val.val
  | Sum.inr (Sum.inr d) => d.val.val

omit [G.LocallyFinite] [Fintype M] in
/-- Every designated persistent crossing keeps its original ambient partner. -/
theorem matching_mark (pair : SeamPair rotation marks mark w)
    (b : BoundaryDart rotation.toRotationSystem (majorityDeletedKeep G pair.outer.shore))
    (m : M) (hb : rotation.toRotationSystem.alpha b.val.val = mark m) :
    (pair.matching b).val.val = rotation.toRotationSystem.alpha b.val.val :=
  replacementMatching_mark rotation pair.outer.shore pair.inner.shore
    pair.outer.innerOuter pair.inner.innerOuter mark pair.width
    pair.outerWidth pair.innerWidth pair.state_eq b m hb

omit [G.LocallyFinite] [Fintype M] in
theorem matching_symm_mark (pair : SeamPair rotation marks mark w)
    (b : BoundaryDart rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore))
    (m : M) (hb : b.val.val = mark m) :
    (pair.matching.symm b).val.val = rotation.toRotationSystem.alpha b.val.val :=
  replacementMatching_symm_mark rotation pair.outer.shore pair.inner.shore
    pair.outer.innerOuter pair.inner.innerOuter mark pair.width
    pair.outerWidth pair.innerWidth pair.state_eq b m hb

omit [G.LocallyFinite] [Fintype M] in
/-- On a designated family closed under ambient edge reversal, the actual
sewn map has exactly the original edge partners in both directions. Internal
edges are unchanged definitionally; seam edges use the two position lemmas. -/
theorem candidate_alpha_mark (pair : SeamPair rotation marks mark w)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (d : pair.candidate.D) (m : M) (hd : pair.ambientDart d = mark m) :
    pair.ambientDart (pair.candidate.alpha d) =
      rotation.toRotationSystem.alpha (pair.ambientDart d) := by
  rcases d with (d | d) | (d | d)
  · rfl
  · rfl
  · obtain ⟨m', hm'⟩ := hclosed m
    exact pair.matching_mark d m' ((congrArg rotation.toRotationSystem.alpha hd).trans hm')
  · exact pair.matching_symm_mark d m hd

omit [G.LocallyFinite] [Fintype M] in
/-- Endpoint marking keeps the named darts' vertices out of the removed
material; position equality independently fixes their crossing partners. -/
theorem mark_not_in_material (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (m : M) :
    ¬ (majorityVertexSide G pair.outer.shore (mark m).fst ∧
      ¬ majorityVertexSide G pair.inner.shore (mark m).fst) := by
  rintro ⟨ho, hi⟩
  exact hi ((pair.marks_constant _ (hmarks m)).mpr ho)

omit [G.LocallyFinite] [Fintype M] in
/-- Every named dart based at a marked vertex is actually present in the
smaller carrier. This rules out vacuous preservation by deleting the marks. -/
theorem mark_survives (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (m : M) :
    ∃ d : pair.candidate.D, pair.ambientDart d = mark m := by
  by_cases ho : majorityDeletedKeep G pair.outer.shore (mark m).fst
  · by_cases hp : majorityDeletedKeep G pair.outer.shore (mark m).snd
    · exact ⟨Sum.inl (Sum.inl ⟨⟨mark m, ho⟩, hp⟩), rfl⟩
    · exact ⟨Sum.inr (Sum.inl ⟨⟨mark m, ho⟩, hp⟩), rfl⟩
  · have hi : majorityRetainedKeep G pair.inner.shore (mark m).fst := by
      apply (majorityRetainedKeep_iff _ _).mpr
      apply (pair.marks_constant _ (hmarks m)).mpr
      simpa only [majorityDeletedKeep_iff, not_not] using ho
    by_cases hp : majorityRetainedKeep G pair.inner.shore (mark m).snd
    · exact ⟨Sum.inl (Sum.inr ⟨⟨mark m, hi⟩, hp⟩), rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨⟨mark m, hi⟩, hp⟩), rfl⟩

omit [G.LocallyFinite] [Fintype M] in
/-- Both ends of every named edge occur in the sewn map and are still paired
by its actual edge involution. The family can be the two darts of each frozen
edge; no assumption that frozen edges avoid the cut is needed. -/
theorem marked_edge_survives (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (m : M) :
    ∃ d : pair.candidate.D, pair.ambientDart d = mark m ∧
      pair.ambientDart (pair.candidate.alpha d) = rotation.toRotationSystem.alpha (mark m) := by
  obtain ⟨d, hd⟩ := pair.mark_survives hmarks m
  exact ⟨d, hd, (pair.candidate_alpha_mark hclosed d m hd).trans
    (congrArg rotation.toRotationSystem.alpha hd)⟩

/-- The existing constructor now receives the produced state equality and
strict star. The same physical object carries the named-dart seam law above. -/
def replacement (pair : SeamPair rotation marks mark w)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem) :
    StrictPhysicalReplacementData rotation pair.outer.shore pair.inner.shore
      pair.outer.outsideOuter pair.inner.innerOuter pair.width
      pair.outerWidth pair.innerWidth :=
  strictPhysicalReplacement_of_normalizedState_eq rotation ambient htwo hzero
    pair.outer.shore pair.inner.shore pair.nested.1
    pair.outer.shoreConnected pair.outer.complementConnected
    pair.outer.majorityNonempty pair.outer.complementNonempty
    pair.inner.shoreConnected pair.inner.complementConnected
    pair.inner.majorityNonempty pair.inner.complementNonempty
    pair.outer.outsideOuter pair.outer.innerOuter pair.inner.innerOuter pair.width
    pair.outerWidth pair.innerWidth (congrArg Prod.fst pair.state_eq)
    pair.outer.first pair.outer.second pair.outer.first_ne_second
    pair.strictVertex pair.strict_star

end SeamPair

/-- Bounded-dual-radius geometry constructs a strictly smaller spherical,
bridgeless cubic zero-Count map with the designated edge pairs still present.
This is the physical consumer of the finite positional refinement. -/
theorem exists_marked_replacement_of_large_card (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    (root : OrbitFace rotation.toRotationSystem) (h : ℕ)
    (marks : Finset V) (mark : M → G.Dart)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (hradius : ∀ f, (orbitFaceDualGraph rotation).dist f root ≤ h)
    (hlarge : vertexBound h marks.card (Fintype.card M) < Fintype.card V) :
    ∃ pair : SeamPair rotation marks mark (2 * h + 1),
      Nonempty (StrictPhysicalReplacementData rotation pair.outer.shore pair.inner.shore
        pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
      ∀ m, ∃ d : pair.candidate.D, pair.ambientDart d = mark m ∧
        pair.ambientDart (pair.candidate.alpha d) = rotation.toRotationSystem.alpha (mark m) := by
  obtain ⟨pair⟩ := exists_seamPair_of_large_card rotation ambient htwo root h marks mark hradius hlarge
  exact ⟨pair, ⟨pair.replacement ambient htwo hzero⟩,
    pair.marked_edge_survives hmarks hclosed⟩

end
end Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam
