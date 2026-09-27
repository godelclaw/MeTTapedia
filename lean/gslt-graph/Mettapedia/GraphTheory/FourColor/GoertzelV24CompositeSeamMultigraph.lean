import Mettapedia.GraphTheory.FourColor.GoertzelV24MultigraphTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationMultigraphAdapter
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition

/-!
# The composed rotation system is the glued multigraph

`composeRotationSystem` sews two open tangles along a matching of their boundary
darts and names the edges of the result by dart orbits.  `glue` sews two
multigraphs along ports and names the seam edges by the ports.  These are two
presentations of one graph, and this file exhibits the isomorphism between them:
an interior orbit of either side is that side's edge, and the orbit of a matched
pair of boundary darts is the seam edge at that port.

With the isomorphism in hand, the gluing lemmas land on the rotation system:
two connected boundary-essential sides with at least two ports compose to a
rotation system that is primal-connected and `EdgeBridgeFree`.  This is the
representation adapter the physical noose deletion consumes, for the two
properties the in-tree carrier can express.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CompositeSeamMultigraph

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24BoundaryEssentialGluing.Multigraph
open GoertzelV24MultigraphTransport
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationSpliceConstructor.RewiredDartSystem
open GoertzelV24RotationEdgeBridge
open GoertzelV24FaceDualConnectedness

noncomputable section

/-! ## A side, as a multigraph on its interior orbits -/

section Side

variable {V I B : Type*} [DecidableEq I]

/-- The interior edges of an open tangle: orbits of its interior involution. -/
def SideEdge (T : OpenTangleData V I B) : Type _ :=
  {pair : Sym2 I // ∃ d, pair = s(d, T.interiorAlpha d)}

/-- The interior edge through a dart. -/
def sideEdgeOf (T : OpenTangleData V I B) (d : I) : SideEdge T :=
  ⟨s(d, T.interiorAlpha d), ⟨d, rfl⟩⟩

theorem sideEdgeOf_alpha (T : OpenTangleData V I B) (d : I) :
    sideEdgeOf T (T.interiorAlpha d) = sideEdgeOf T d := by
  apply Subtype.ext
  change s(T.interiorAlpha d, T.interiorAlpha (T.interiorAlpha d)) = s(d, T.interiorAlpha d)
  rw [T.interiorAlpha_involutive]
  exact Sym2.eq_swap

/-- Every side edge is the edge of its chosen dart. -/
theorem sideEdgeOf_choose (T : OpenTangleData V I B) (e : SideEdge T) :
    sideEdgeOf T e.2.choose = e :=
  Subtype.ext e.2.choose_spec.symm

/-- The chosen dart of `sideEdgeOf d` is `d` or its flip. -/
theorem choose_sideEdgeOf (T : OpenTangleData V I B) (d : I) :
    (sideEdgeOf T d).2.choose = d ∨ (sideEdgeOf T d).2.choose = T.interiorAlpha d := by
  have h := (sideEdgeOf T d).2.choose_spec
  change s(d, T.interiorAlpha d) = s(_, T.interiorAlpha _) at h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Or.inl h1.symm
  · exact Or.inr h2.symm

/-- The side as a multigraph: each interior orbit joins the vertices of its two
darts. -/
def sideMultigraph (T : OpenTangleData V I B) : Multigraph V (SideEdge T) where
  fst e := T.interiorVert e.2.choose
  snd e := T.interiorVert (T.interiorAlpha e.2.choose)

/-- The endpoints of `sideEdgeOf d` are those of `d`, in one order or the
other. -/
theorem sideMultigraph_ends (T : OpenTangleData V I B) (d : I) :
    ((sideMultigraph T).fst (sideEdgeOf T d) = T.interiorVert d ∧
        (sideMultigraph T).snd (sideEdgeOf T d) = T.interiorVert (T.interiorAlpha d)) ∨
      ((sideMultigraph T).fst (sideEdgeOf T d) = T.interiorVert (T.interiorAlpha d) ∧
        (sideMultigraph T).snd (sideEdgeOf T d) = T.interiorVert d) := by
  rcases choose_sideEdgeOf T d with h | h
  · left
    exact ⟨by simp [sideMultigraph, h], by simp [sideMultigraph, h]⟩
  · right
    exact ⟨by simp [sideMultigraph, h], by simp [sideMultigraph, h, T.interiorAlpha_involutive]⟩

end Side

/-! ## The composite -/

section Composite

variable {V W I L J R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (left : OpenTangleData V I L) (right : OpenTangleData W J R) (matching : L ≃ R)

/-- The rewired dart system behind `composeRotationSystem`. -/
abbrev compositeDarts :=
  (left.composeData right matching).toRewiredDartSystem
    (left.composeData_interiorAlpha_involutive right matching)
    (left.composeData_interiorAlpha_fixfree right matching)
    (left.composeData_vert_rho right matching)
    (left.composeData_interior_no_self_loops right matching)
    (left.composeData_seam_no_self_loops right matching)

/-- The glued multigraph, with the right side's ports read through the
matching. -/
abbrev seamGlue : Multigraph (V ⊕ W) (SideEdge left ⊕ SideEdge right ⊕ L) :=
  glue (sideMultigraph left) (sideMultigraph right) left.boundaryVert
    (fun l => right.boundaryVert (matching l))

/-- Which glue edge a composite dart lies on. -/
def classify : MatchedSeam.Dart (I ⊕ J) L R → SideEdge left ⊕ SideEdge right ⊕ L
  | Sum.inl (Sum.inl i) => Sum.inl (sideEdgeOf left i)
  | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl (sideEdgeOf right j))
  | Sum.inr (Sum.inl l) => Sum.inr (Sum.inr l)
  | Sum.inr (Sum.inr r) => Sum.inr (Sum.inr (matching.symm r))

/-- Classification is constant on orbits. -/
theorem classify_alpha (d : MatchedSeam.Dart (I ⊕ J) L R) :
    classify left right matching ((compositeDarts left right matching).alpha d) =
      classify left right matching d := by
  rcases d with (i | j) | (l | r)
  · simp [classify, compositeDarts, MatchedSeam.Data.toRewiredDartSystem,
      composeData, sideEdgeOf_alpha]
  · simp [classify, compositeDarts, MatchedSeam.Data.toRewiredDartSystem,
      composeData, sideEdgeOf_alpha]
  · simp [classify, compositeDarts, MatchedSeam.Data.toRewiredDartSystem, composeData]
  · simp [classify, compositeDarts, MatchedSeam.Data.toRewiredDartSystem, composeData]

/-- The composite edge to glue edge map. -/
def toGlue (e : (compositeDarts left right matching).Edge) :
    SideEdge left ⊕ SideEdge right ⊕ L :=
  classify left right matching e.2.choose

/-- Every composite edge is the orbit of its chosen dart. -/
theorem edgeOf_choose (e : (compositeDarts left right matching).Edge) :
    (compositeDarts left right matching).edgeOf e.2.choose = e :=
  Subtype.ext e.2.choose_spec.symm

/-- `toGlue` reads any dart of the orbit. -/
theorem toGlue_edgeOf (d : MatchedSeam.Dart (I ⊕ J) L R) :
    toGlue left right matching ((compositeDarts left right matching).edgeOf d) =
      classify left right matching d := by
  unfold toGlue
  have h : s(d, (compositeDarts left right matching).alpha d) =
      s(((compositeDarts left right matching).edgeOf d).2.choose,
        (compositeDarts left right matching).alpha
          ((compositeDarts left right matching).edgeOf d).2.choose) :=
    ((compositeDarts left right matching).edgeOf d).2.choose_spec
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [← h1]
  · rw [← h2, classify_alpha]

/-- The glue edge to composite edge map. -/
def ofGlue : SideEdge left ⊕ SideEdge right ⊕ L → (compositeDarts left right matching).Edge
  | Sum.inl eh => (compositeDarts left right matching).edgeOf (Sum.inl (Sum.inl eh.2.choose))
  | Sum.inr (Sum.inl ek) =>
      (compositeDarts left right matching).edgeOf (Sum.inl (Sum.inr ek.2.choose))
  | Sum.inr (Sum.inr l) => (compositeDarts left right matching).edgeOf (Sum.inr (Sum.inl l))

theorem ofGlue_classify (d : MatchedSeam.Dart (I ⊕ J) L R) :
    ofGlue left right matching (classify left right matching d) =
      (compositeDarts left right matching).edgeOf d := by
  rcases d with (i | j) | (l | r)
  · simp only [classify, ofGlue]
    rcases choose_sideEdgeOf left i with h | h
    · rw [h]
    · rw [h]
      have := (compositeDarts left right matching).edgeOf_alpha (Sum.inl (Sum.inl i))
      simpa [compositeDarts, MatchedSeam.Data.toRewiredDartSystem, composeData] using this
  · simp only [classify, ofGlue]
    rcases choose_sideEdgeOf right j with h | h
    · rw [h]
    · rw [h]
      have := (compositeDarts left right matching).edgeOf_alpha (Sum.inl (Sum.inr j))
      simpa [compositeDarts, MatchedSeam.Data.toRewiredDartSystem, composeData] using this
  · rfl
  · simp only [classify, ofGlue]
    have := (compositeDarts left right matching).edgeOf_alpha (Sum.inr (Sum.inr r))
    simpa [compositeDarts, MatchedSeam.Data.toRewiredDartSystem, composeData] using this

/-- **The edge equivalence.** -/
def edgeEquiv : (compositeDarts left right matching).Edge ≃ SideEdge left ⊕ SideEdge right ⊕ L where
  toFun := toGlue left right matching
  invFun := ofGlue left right matching
  left_inv e := by
    rw [← edgeOf_choose left right matching e, toGlue_edgeOf, ofGlue_classify]
  right_inv x := by
    rcases x with eh | ek | l
    · simp only [ofGlue]
      rw [toGlue_edgeOf]
      simp [classify, sideEdgeOf_choose]
    · simp only [ofGlue]
      rw [toGlue_edgeOf]
      simp [classify, sideEdgeOf_choose]
    · simp only [ofGlue]
      rw [toGlue_edgeOf]
      rfl

/-- The composed rotation system, as in `composeRotationSystem`. -/
abbrev compositeRS : RotationSystem (V ⊕ W) (compositeDarts left right matching).Edge :=
  (compositeDarts left right matching).toRotationSystem

theorem compositeRS_eq :
    compositeRS left right matching = left.composeRotationSystem right matching := rfl

/-- The endpoints of an edge, relative to any dart of its orbit. -/
theorem ends_of_edgeOf {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) {d : RS.D} {e : E} (hd : RS.edgeOf d = e) :
    ((toMultigraph RS).fst e = RS.vertOf d ∧ (toMultigraph RS).snd e = RS.vertOf (RS.alpha d)) ∨
      ((toMultigraph RS).fst e = RS.vertOf (RS.alpha d) ∧ (toMultigraph RS).snd e = RS.vertOf d) := by
  rcases eq_someDart_or RS e hd with h | h
  · left
    rw [toMultigraph_fst, toMultigraph_snd, ← h]
    exact ⟨rfl, rfl⟩
  · right
    rw [toMultigraph_fst, toMultigraph_snd, h, RS.alpha_involutive]
    exact ⟨rfl, rfl⟩

/-- Two unordered pairs that both equal `{a, b}` equal each other. -/
theorem pair_match {X : Type*} {x y x' y' a b : X}
    (hc : (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (hg : (x' = a ∧ y' = b) ∨ (x' = b ∧ y' = a)) :
    (x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- **Endpoints agree across the edge map**, dart by dart. -/
theorem iso_ends (d : MatchedSeam.Dart (I ⊕ J) L R) :
    ((seamGlue left right matching).fst
        (toGlue left right matching ((compositeDarts left right matching).edgeOf d)) =
        (toMultigraph (compositeRS left right matching)).fst
          ((compositeDarts left right matching).edgeOf d) ∧
      (seamGlue left right matching).snd
        (toGlue left right matching ((compositeDarts left right matching).edgeOf d)) =
        (toMultigraph (compositeRS left right matching)).snd
          ((compositeDarts left right matching).edgeOf d)) ∨
    ((seamGlue left right matching).fst
        (toGlue left right matching ((compositeDarts left right matching).edgeOf d)) =
        (toMultigraph (compositeRS left right matching)).snd
          ((compositeDarts left right matching).edgeOf d) ∧
      (seamGlue left right matching).snd
        (toGlue left right matching ((compositeDarts left right matching).edgeOf d)) =
        (toMultigraph (compositeRS left right matching)).fst
          ((compositeDarts left right matching).edgeOf d)) := by
  rw [toGlue_edgeOf]
  have hc := ends_of_edgeOf (compositeRS left right matching) (d := d) rfl
  rcases d with (i | j) | (l | r)
  · -- an interior edge of the left side
    refine pair_match hc ?_
    rcases sideMultigraph_ends left i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨?_, ?_⟩
      · change Sum.inl ((sideMultigraph left).fst (sideEdgeOf left i)) =
          Sum.inl (left.interiorVert i)
        rw [h1]
      · change Sum.inl ((sideMultigraph left).snd (sideEdgeOf left i)) =
          Sum.inl (left.interiorVert (left.interiorAlpha i))
        rw [h2]
    · refine Or.inr ⟨?_, ?_⟩
      · change Sum.inl ((sideMultigraph left).fst (sideEdgeOf left i)) =
          Sum.inl (left.interiorVert (left.interiorAlpha i))
        rw [h1]
      · change Sum.inl ((sideMultigraph left).snd (sideEdgeOf left i)) =
          Sum.inl (left.interiorVert i)
        rw [h2]
  · -- an interior edge of the right side
    refine pair_match hc ?_
    rcases sideMultigraph_ends right j with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨?_, ?_⟩
      · change Sum.inr ((sideMultigraph right).fst (sideEdgeOf right j)) =
          Sum.inr (right.interiorVert j)
        rw [h1]
      · change Sum.inr ((sideMultigraph right).snd (sideEdgeOf right j)) =
          Sum.inr (right.interiorVert (right.interiorAlpha j))
        rw [h2]
    · refine Or.inr ⟨?_, ?_⟩
      · change Sum.inr ((sideMultigraph right).fst (sideEdgeOf right j)) =
          Sum.inr (right.interiorVert (right.interiorAlpha j))
        rw [h1]
      · change Sum.inr ((sideMultigraph right).snd (sideEdgeOf right j)) =
          Sum.inr (right.interiorVert j)
        rw [h2]
  · -- a seam edge, read from its left dart
    exact pair_match hc (Or.inl ⟨rfl, rfl⟩)
  · -- a seam edge, read from its right dart
    refine pair_match hc (Or.inr ⟨rfl, ?_⟩)
    change Sum.inr (right.boundaryVert (matching (matching.symm r))) =
      Sum.inr (right.boundaryVert r)
    rw [Equiv.apply_symm_apply]

/-- **The isomorphism** between the composed rotation system's multigraph and the
glued multigraph. -/
def compositeIso :
    Iso (toMultigraph (compositeRS left right matching)) (seamGlue left right matching) where
  vert := Equiv.refl _
  edge := edgeEquiv left right matching
  ends := by
    intro e
    rw [← edgeOf_choose left right matching e]
    generalize e.2.choose = d
    simpa [edgeEquiv] using iso_ends left right matching d

/-! ## The adapter, delivered -/

/-- **The composed rotation system is bridge-free** when both sides are connected
and boundary-essential and there are at least two ports. -/
theorem edgeBridgeFree_composeRotationSystem
    (hH : (sideMultigraph left).Connected) (hK : (sideMultigraph right).Connected)
    (hHess : BoundaryEssential (sideMultigraph left) left.boundaryVert)
    (hKess : BoundaryEssential (sideMultigraph right) (fun l => right.boundaryVert (matching l)))
    {p₀ q₀ : L} (hpq : p₀ ≠ q₀) :
    EdgeBridgeFree (left.composeRotationSystem right matching) := by
  rw [← compositeRS_eq]
  refine (bridgeless_iff_edgeBridgeFree _).1 ?_
  exact (compositeIso left right matching).symm.bridgeless_of
    (glue_bridgeless hH hK hHess hKess hpq)

/-- **The composed rotation system is primal-connected** when both sides are
connected and there is a port. -/
theorem primalConnected_composeRotationSystem [Nonempty V]
    (hH : (sideMultigraph left).Connected) (hK : (sideMultigraph right).Connected) (p₀ : L) :
    (rotationPrimalGraph (left.composeRotationSystem right matching)).Connected := by
  rw [← compositeRS_eq]
  refine primalConnected_of_connected _ ?_
  exact (compositeIso left right matching).symm.connected_of (glue_connected hH hK p₀)

end Composite

end

end GoertzelV24CompositeSeamMultigraph

end Mettapedia.GraphTheory.FourColor
