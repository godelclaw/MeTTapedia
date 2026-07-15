import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpaceEquality
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PlanarBondBoundaryOrder

open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open GoertzelV24RotationVertexCutProfile
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A predicate invariant under one permutation step is constant on every
permutation cycle. The step hypothesis is needed only on the selected cycle. -/
theorem predicate_eq_of_sameCycle_of_step_eq
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (predicate : A -> Prop) (root : A)
    (hstep : forall point, perm.SameCycle root point ->
      predicate point = predicate (perm point))
    {point : A} (hpoint : perm.SameCycle root point) :
    predicate root = predicate point := by
  rcases hpoint with ⟨power, hpower⟩
  have hpowers : perm.SameCycle root ((perm ^ power) root) /\
      predicate root = predicate ((perm ^ power) root) := by
    exact zpow_induction_left (g := perm)
      (P := fun permutation =>
        perm.SameCycle root (permutation root) /\
          predicate root = predicate (permutation root))
      ⟨Equiv.Perm.SameCycle.refl perm root, rfl⟩
      (fun permutation hinduction => by
        have hnextCycle := hinduction.1.trans
          (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
            perm (permutation root))
        refine ⟨?_, ?_⟩
        · simpa [Equiv.Perm.mul_apply] using hnextCycle
        · simpa [Equiv.Perm.mul_apply] using
            hinduction.2.trans (hstep (permutation root) hinduction.1))
      (fun permutation hinduction => by
        have hpreviousCycle := hinduction.1.trans
          (Mettapedia.GraphTheory.EquivPermSameCycle.step_right_inv
            perm (permutation root))
        have hpreviousStep := hstep (perm.symm (permutation root))
          hpreviousCycle
        refine ⟨?_, ?_⟩
        · simpa [Equiv.Perm.mul_apply] using hpreviousCycle
        · have hpreviousEq :
              predicate (perm.symm (permutation root)) =
                predicate (permutation root) := by
            simpa using hpreviousStep
          simpa [Equiv.Perm.mul_apply] using
            hinduction.2.trans hpreviousEq.symm)
      power
  rw [hpower] at hpowers
  exact hpowers.2

/-- Every dart occurrence of a quotient face is based on the selected vertex
side. -/
def OrbitFaceAllOnSide
    (RS : RotationSystem V E) (side : V -> Prop) (face : OrbitFace RS) : Prop :=
  forall dart, dart ∈ orbitFaceDarts RS face -> side (RS.vertOf dart)

/-- Quotient faces lying entirely on the selected vertex side. -/
noncomputable def orbitFacesAllOnSide
    (RS : RotationSystem V E) (side : V -> Prop) : Finset (OrbitFace RS) := by
  classical
  exact Finset.univ.filter (OrbitFaceAllOnSide RS side)

@[simp]
theorem mem_orbitFacesAllOnSide_iff
    (RS : RotationSystem V E) (side : V -> Prop) (face : OrbitFace RS) :
    face ∈ orbitFacesAllOnSide RS side <-> OrbitFaceAllOnSide RS side face := by
  classical
  simp [orbitFacesAllOnSide]

/-- If a quotient face is untouched by the side cut, its side predicate is
constant on the whole facial cycle. -/
theorem side_eq_on_orbitFace_of_not_mem_transitionFaces
    (RS : RotationSystem V E) (deleted : Finset V) (face : OrbitFace RS)
    (hnotTouched : face ∉ cutSideTransitionFaces RS deleted)
    {left right : RS.D}
    (hleft : left ∈ orbitFaceDarts RS face)
    (hright : right ∈ orbitFaceDarts RS face) :
    deletedRegionKeep deleted (RS.vertOf left) =
      deletedRegionKeep deleted (RS.vertOf right) := by
  have hnoTransitions : orbitFaceSideTransitionDarts RS
      (deletedRegionKeep deleted) face = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.1
    simpa using hnotTouched
  have hstep : forall point, RS.phi.SameCycle left point ->
      deletedRegionKeep deleted (RS.vertOf point) =
        deletedRegionKeep deleted (RS.vertOf (RS.phi point)) := by
    intro point hpoint
    by_contra hne
    have hpointFace : dartOrbitFace RS point = face := by
      have hleftFace := (mem_orbitFaceDarts_iff RS face left).1 hleft
      have hsameFace : dartOrbitFace RS point = dartOrbitFace RS left := by
        apply Quotient.sound
        exact hpoint.symm
      exact hsameFace.trans hleftFace
    have hmem : point ∈ orbitFaceSideTransitionDarts RS
        (deletedRegionKeep deleted) face :=
      (mem_orbitFaceSideTransitionDarts_iff RS
        (deletedRegionKeep deleted) face point).2 ⟨hpointFace, hne⟩
    rw [hnoTransitions] at hmem
    simp at hmem
  apply predicate_eq_of_sameCycle_of_step_eq RS.phi
    (fun dart => deletedRegionKeep deleted (RS.vertOf dart)) left hstep
  have hleftFace := (mem_orbitFaceDarts_iff RS face left).1 hleft
  have hrightFace := (mem_orbitFaceDarts_iff RS face right).1 hright
  have hquotient : dartOrbitFace RS left = dartOrbitFace RS right :=
    hleftFace.trans hrightFace.symm
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) left =
    Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) right at hquotient
  rw [Quotient.eq] at hquotient
  exact hquotient

/-- An untouched quotient face lies wholly on exactly one of the two vertex
sides. -/
theorem allOnSide_or_allOffSide_of_not_mem_transitionFaces
    (RS : RotationSystem V E) (deleted : Finset V) (face : OrbitFace RS)
    (hnotTouched : face ∉ cutSideTransitionFaces RS deleted) :
    OrbitFaceAllOnSide RS (deletedRegionKeep deleted) face \/
      OrbitFaceAllOnSide RS
        (fun vertex => Not (deletedRegionKeep deleted vertex)) face := by
  rcases exists_dartOrbitFace_eq RS face with ⟨root, hrootFace⟩
  have hrootMem : root ∈ orbitFaceDarts RS face :=
    (mem_orbitFaceDarts_iff RS face root).2 hrootFace
  by_cases hrootSide : deletedRegionKeep deleted (RS.vertOf root)
  · left
    intro dart hdart
    have heq := side_eq_on_orbitFace_of_not_mem_transitionFaces
      RS deleted face hnotTouched hrootMem hdart
    exact heq.mp hrootSide
  · right
    intro dart hdart hdartSide
    have heq := side_eq_on_orbitFace_of_not_mem_transitionFaces
      RS deleted face hnotTouched hrootMem hdart
    exact hrootSide (heq.mpr hdartSide)

/-- A touched face cannot lie entirely on the retained side. -/
theorem cutSideTransitionFaces_disjoint_allOnSide
    (RS : RotationSystem V E) (deleted : Finset V) :
    Disjoint (cutSideTransitionFaces RS deleted)
      (orbitFacesAllOnSide RS (deletedRegionKeep deleted)) := by
  rw [Finset.disjoint_left]
  intro face htouched hall
  rcases (mem_cutSideTransitionFaces_iff RS deleted face).1 htouched with
    ⟨dart, hdartTransition⟩
  have hdartData := (mem_orbitFaceSideTransitionDarts_iff RS
    (deletedRegionKeep deleted) face dart).1 hdartTransition
  have hallData := (mem_orbitFacesAllOnSide_iff RS
    (deletedRegionKeep deleted) face).1 hall
  have hcurrent := hallData dart
    ((mem_orbitFaceDarts_iff RS face dart).2 hdartData.1)
  have hnextFace : dartOrbitFace RS (RS.phi dart) = face := by
    have hstepFace : dartOrbitFace RS (RS.phi dart) =
        dartOrbitFace RS dart := by
      change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) (RS.phi dart) =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) dart
      apply Quotient.sound
      exact (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        RS.phi dart).symm
    exact hstepFace.trans hdartData.1
  have hnext := hallData (RS.phi dart)
    ((mem_orbitFaceDarts_iff RS face (RS.phi dart)).2 hnextFace)
  exact hdartData.2 (propext ⟨fun _ => hnext, fun _ => hcurrent⟩)

/-- A touched face cannot lie entirely on the deleted side. -/
theorem cutSideTransitionFaces_disjoint_allOffSide
    (RS : RotationSystem V E) (deleted : Finset V) :
    Disjoint (cutSideTransitionFaces RS deleted)
      (orbitFacesAllOnSide RS
        (fun vertex => Not (deletedRegionKeep deleted vertex))) := by
  rw [Finset.disjoint_left]
  intro face htouched hall
  rcases (mem_cutSideTransitionFaces_iff RS deleted face).1 htouched with
    ⟨dart, hdartTransition⟩
  have hdartData := (mem_orbitFaceSideTransitionDarts_iff RS
    (deletedRegionKeep deleted) face dart).1 hdartTransition
  have hallData := (mem_orbitFacesAllOnSide_iff RS
    (fun vertex => Not (deletedRegionKeep deleted vertex)) face).1 hall
  have hcurrent := hallData dart
    ((mem_orbitFaceDarts_iff RS face dart).2 hdartData.1)
  have hnextFace : dartOrbitFace RS (RS.phi dart) = face := by
    have hstepFace : dartOrbitFace RS (RS.phi dart) =
        dartOrbitFace RS dart := by
      change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) (RS.phi dart) =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) dart
      apply Quotient.sound
      exact (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        RS.phi dart).symm
    exact hstepFace.trans hdartData.1
  have hnext := hallData (RS.phi dart)
    ((mem_orbitFaceDarts_iff RS face (RS.phi dart)).2 hnextFace)
  apply hdartData.2
  apply propext
  constructor <;> intro h
  · exact (hcurrent h).elim
  · exact (hnext h).elim

/-- No nonempty quotient face can lie entirely on both complementary vertex
sides. -/
theorem allOnSide_disjoint_allOffSide
    (RS : RotationSystem V E) (deleted : Finset V) :
    Disjoint (orbitFacesAllOnSide RS (deletedRegionKeep deleted))
      (orbitFacesAllOnSide RS
        (fun vertex => Not (deletedRegionKeep deleted vertex))) := by
  rw [Finset.disjoint_left]
  intro face hon hoff
  rcases exists_dartOrbitFace_eq RS face with ⟨dart, hdartFace⟩
  have hdartMem : dart ∈ orbitFaceDarts RS face :=
    (mem_orbitFaceDarts_iff RS face dart).2 hdartFace
  exact ((mem_orbitFacesAllOnSide_iff RS
      (fun vertex => Not (deletedRegionKeep deleted vertex)) face).1 hoff
      dart hdartMem)
    ((mem_orbitFacesAllOnSide_iff RS
      (deletedRegionKeep deleted) face).1 hon dart hdartMem)

/-- Touched, retained-only, and deleted-only quotient faces form a disjoint
partition of every ambient face occurrence. -/
theorem transition_union_allOnSide_union_allOffSide_eq_univ
    (RS : RotationSystem V E) (deleted : Finset V) :
    cutSideTransitionFaces RS deleted ∪
        orbitFacesAllOnSide RS (deletedRegionKeep deleted) ∪
      orbitFacesAllOnSide RS
        (fun vertex => Not (deletedRegionKeep deleted vertex)) =
      Finset.univ := by
  classical
  ext face
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  by_cases htouched : face ∈ cutSideTransitionFaces RS deleted
  · exact Or.inl (Or.inl htouched)
  · rcases allOnSide_or_allOffSide_of_not_mem_transitionFaces
      RS deleted face htouched with hon | hoff
    · exact Or.inl (Or.inr ((mem_orbitFacesAllOnSide_iff RS
        (deletedRegionKeep deleted) face).2 hon))
    · exact Or.inr ((mem_orbitFacesAllOnSide_iff RS
        (fun vertex => Not (deletedRegionKeep deleted vertex)) face).2 hoff)

/-- Cardinal form of the computed three-way quotient-face partition. -/
theorem card_transition_add_allOnSide_add_allOffSide_eq_faces
    (RS : RotationSystem V E) (deleted : Finset V) :
    (cutSideTransitionFaces RS deleted).card +
        (orbitFacesAllOnSide RS (deletedRegionKeep deleted)).card +
      (orbitFacesAllOnSide RS
        (fun vertex => Not (deletedRegionKeep deleted vertex))).card =
      Fintype.card (OrbitFace RS) := by
  have hfirstDisjoint : Disjoint (cutSideTransitionFaces RS deleted)
      (orbitFacesAllOnSide RS (deletedRegionKeep deleted)) :=
    cutSideTransitionFaces_disjoint_allOnSide RS deleted
  have hsecondDisjoint : Disjoint
      (cutSideTransitionFaces RS deleted ∪
        orbitFacesAllOnSide RS (deletedRegionKeep deleted))
      (orbitFacesAllOnSide RS
        (fun vertex => Not (deletedRegionKeep deleted vertex))) := by
    rw [Finset.disjoint_union_left]
    exact ⟨cutSideTransitionFaces_disjoint_allOffSide RS deleted,
      allOnSide_disjoint_allOffSide RS deleted⟩
  rw [← Finset.card_union_of_disjoint hfirstDisjoint,
    ← Finset.card_union_of_disjoint hsecondDisjoint,
    transition_union_allOnSide_union_allOffSide_eq_univ,
    Finset.card_univ]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A pure quotient face uses only edges whose two endpoints lie on the
selected vertex side. -/
theorem orbitFaceBoundary_endpoints_on_side
    (data : Data G) (side : V -> Prop)
    (face : OrbitFace data.toRotationSystem)
    (hpure : OrbitFaceAllOnSide data.toRotationSystem side face)
    (edge : G.edgeSet)
    (hedge : edge ∈ orbitFaceBoundary data.toRotationSystem face) :
    forall vertex, vertex ∈ (edge.1 : Sym2 V) -> side vertex := by
  rcases (mem_orbitFaceBoundary_iff data.toRotationSystem face edge).1 hedge with
    ⟨dart, hdartFace, hdartEdge⟩
  have hdartMem : dart ∈ orbitFaceDarts data.toRotationSystem face :=
    hdartFace
  have hphiFace : dartOrbitFace data.toRotationSystem
      (data.toRotationSystem.phi dart) = face := by
    have hstep : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.phi dart) =
          dartOrbitFace data.toRotationSystem dart := by
      apply Quotient.sound
      exact (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        data.toRotationSystem.phi dart).symm
    exact hstep.trans
      ((mem_orbitFaceDarts_iff data.toRotationSystem face dart).1 hdartFace)
  have hphiMem : data.toRotationSystem.phi dart ∈
      orbitFaceDarts data.toRotationSystem face :=
    (mem_orbitFaceDarts_iff data.toRotationSystem face _).2 hphiFace
  have hleft : side (data.toRotationSystem.vertOf dart) :=
    hpure dart hdartMem
  have hright :
      side (data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart)) := by
    rw [← data.toRotationSystem.vert_phi_eq_vert_alpha dart]
    exact hpure _ hphiMem
  intro vertex hvertex
  have hedgeValue : (edge.1 : Sym2 V) = dart.edge := by
    exact congrArg Subtype.val hdartEdge.symm
  rw [hedgeValue] at hvertex
  rcases (Sym2.mem_iff.1 hvertex) with hvertex | hvertex
  · rwa [hvertex]
  · rwa [hvertex]

/-- The vertices selected by a side predicate. -/
abbrev SideVertex (side : V -> Prop) :=
  ↑({vertex | side vertex} : Set V)

/-- Inclusion of an induced side edge into the ambient graph edge carrier. -/
def inducedSideEdgeEmbedding
    (G : SimpleGraph V) (side : V -> Prop) :
    (G.induce {vertex | side vertex}).edgeSet ↪ G.edgeSet :=
  (SimpleGraph.Embedding.induce
    (G := G) {vertex | side vertex}).mapEdgeSet

@[simp]
theorem inducedSideEdgeEmbedding_val
    (G : SimpleGraph V) (side : V -> Prop)
    (edge : (G.induce {vertex | side vertex}).edgeSet) :
    ((inducedSideEdgeEmbedding G side edge).1 : Sym2 V) =
      Sym2.map Subtype.val edge.1 := by
  rfl

@[simp]
theorem mem_inducedSideEdgeEmbedding_iff
    (G : SimpleGraph V) (side : V -> Prop)
    (vertex : SideVertex side)
    (edge : (G.induce {vertex | side vertex}).edgeSet) :
    vertex.1 ∈ ((inducedSideEdgeEmbedding G side edge).1 : Sym2 V) ↔
      vertex ∈ (edge.1 : Sym2 (SideVertex side)) := by
  rw [inducedSideEdgeEmbedding_val]
  induction edge.1 using Sym2.inductionOn with
  | _ left right =>
      rw [Sym2.map_mk]
      rw [Sym2.mem_iff, Sym2.mem_iff]
      constructor
      · rintro (heq | heq)
        · exact Or.inl (Subtype.ext heq)
        · exact Or.inr (Subtype.ext heq)
      · rintro (heq | heq)
        · exact Or.inl (congrArg Subtype.val heq)
        · exact Or.inr (congrArg Subtype.val heq)

/-- Restriction of a pure ambient facial boundary to the induced side. -/
def inducedSideFaceBoundaryIndicator
    (data : Data G) (side : V -> Prop)
    (face : OrbitFace data.toRotationSystem) :
    (G.induce {vertex | side vertex}).edgeSet -> F2 :=
  fun edge => orbitFaceBoundaryIndicator data face
    (inducedSideEdgeEmbedding G side edge)

@[simp]
theorem inducedSideFaceBoundaryIndicator_apply
    (data : Data G) (side : V -> Prop)
    (face : OrbitFace data.toRotationSystem)
    (edge : (G.induce {vertex | side vertex}).edgeSet) :
    inducedSideFaceBoundaryIndicator data side face edge =
      if inducedSideEdgeEmbedding G side edge ∈
          orbitFaceBoundary data.toRotationSystem face
        then 1 else 0 := by
  rfl

/-- Restricting a pure two-sided facial boundary to its induced side gives a
cycle of the induced graph. -/
theorem inducedSideFaceBoundaryIndicator_mem_f2CycleSpace
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (side : V -> Prop) [Fintype (SideVertex side)]
    (face : OrbitFace data.toRotationSystem)
    (hpure : OrbitFaceAllOnSide data.toRotationSystem side face) :
    inducedSideFaceBoundaryIndicator data side face ∈
      f2CycleSpace (G.induce {vertex | side vertex}) := by
  classical
  let H := G.induce {vertex | side vertex}
  letI : Fintype H.edgeSet := SimpleGraph.fintypeEdgeSet H
  letI : DecidableEq H.edgeSet := Subtype.instDecidableEq
  rw [f2CycleSpace, LinearMap.mem_ker]
  funext vertex
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    f2IncidenceMatrix, inducedSideFaceBoundaryIndicator_apply]
  change (∑ edge : H.edgeSet,
    (if vertex ∈ (edge.1 : Sym2 (SideVertex side)) then 1 else 0) *
      (if inducedSideEdgeEmbedding G side edge ∈
          orbitFaceBoundary data.toRotationSystem face
        then 1 else 0)) = 0
  let inducedIncidentBoundary := Finset.univ.filter fun edge : H.edgeSet =>
    vertex ∈ (edge.1 : Sym2 (SideVertex side)) ∧
      inducedSideEdgeEmbedding G side edge ∈
        orbitFaceBoundary data.toRotationSystem face
  let ambientIncidentBoundary :=
    data.toRotationSystem.incidentEdges vertex.1 ∩
      orbitFaceBoundary data.toRotationSystem face
  have hcard : inducedIncidentBoundary.card =
      ambientIncidentBoundary.card := by
    refine Finset.card_bij
      (fun edge _ => inducedSideEdgeEmbedding G side edge) ?_ ?_ ?_
    · intro edge hedge
      have hedgeData := (Finset.mem_filter.1 hedge).2
      apply Finset.mem_inter.2
      refine ⟨?_, hedgeData.2⟩
      rw [mem_toRotationSystem_incidentEdges_iff]
      exact (mem_inducedSideEdgeEmbedding_iff G side vertex edge).2
        hedgeData.1
    · intro left _ right _ heq
      exact (inducedSideEdgeEmbedding G side).injective heq
    · intro ambient hambient
      have hambientData := Finset.mem_inter.1 hambient
      have hendpoints := orbitFaceBoundary_endpoints_on_side
        data side face hpure ambient hambientData.2
      rcases ambient with ⟨edge, hedge⟩
      induction edge using Sym2.inductionOn with
      | _ left right =>
          let leftSide : SideVertex side :=
            ⟨left, hendpoints left (by simp)⟩
          let rightSide : SideVertex side :=
            ⟨right, hendpoints right (by simp)⟩
          have hadj : G.Adj left right :=
            (SimpleGraph.mem_edgeSet G).1 hedge
          let induced : H.edgeSet :=
            ⟨s(leftSide, rightSide), hadj⟩
          have hmap : inducedSideEdgeEmbedding G side induced =
              (⟨s(left, right), hedge⟩ : G.edgeSet) := by
            apply Subtype.ext
            rfl
          refine ⟨induced, ?_, hmap⟩
          apply Finset.mem_filter.2
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · apply (mem_inducedSideEdgeEmbedding_iff
              G side vertex induced).1
            rw [hmap]
            exact (mem_toRotationSystem_incidentEdges_iff
              data vertex.1 _).1 hambientData.1
          · exact hmap.symm ▸ hambientData.2
  calc
    (∑ edge : H.edgeSet,
      (if vertex ∈ (edge.1 : Sym2 (SideVertex side)) then 1 else 0) *
        (if inducedSideEdgeEmbedding G side edge ∈
            orbitFaceBoundary data.toRotationSystem face
          then 1 else 0)) =
        ∑ edge : H.edgeSet,
          if vertex ∈ (edge.1 : Sym2 (SideVertex side)) ∧
              inducedSideEdgeEmbedding G side edge ∈
                orbitFaceBoundary data.toRotationSystem face
            then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro edge _
      split_ifs <;> simp_all
    _ = (inducedIncidentBoundary.card : F2) := by
      exact Finset.sum_boole _ _
    _ = (ambientIncidentBoundary.card : F2) := by rw [hcard]
    _ = 0 := by
      exact (incidentEdges_inter_orbitFaceBoundary_card_even
        data.toRotationSystem htwoSided face vertex.1).natCast_zmod_two

/-- Quotient faces lying wholly on an induced vertex side. -/
abbrev PureSideFace (data : Data G) (side : V -> Prop) :=
  {face : OrbitFace data.toRotationSystem //
    OrbitFaceAllOnSide data.toRotationSystem side face}

noncomputable instance pureSideFaceFintype
    (data : Data G) (side : V -> Prop) :
    Fintype (PureSideFace data side) :=
  Fintype.ofInjective (fun face : PureSideFace data side => face.1)
    Subtype.val_injective

noncomputable instance pureSideFaceDecidableEq
    (data : Data G) (side : V -> Prop) :
    DecidableEq (PureSideFace data side) :=
  Classical.decEq _

/-- Extend coefficients on pure-side faces by zero to all ambient quotient
faces. -/
def extendPureSideFaceCoefficients
    (data : Data G) (side : V -> Prop)
    (coefficients : PureSideFace data side -> F2) :
    OrbitFace data.toRotationSystem -> F2 :=
  fun face => if hpure : face ∈
      orbitFacesAllOnSide data.toRotationSystem side
    then coefficients ⟨face,
      (mem_orbitFacesAllOnSide_iff data.toRotationSystem side face).1 hpure⟩
    else 0

/-- The ambient boundary of zero-extended pure-face coefficients is exactly
the sum over the pure-face subtype. -/
theorem orbitFaceBoundaryLinearMap_extendPureSideFaceCoefficients_apply
    (data : Data G) (side : V -> Prop)
    (coefficients : PureSideFace data side -> F2) (edge : G.edgeSet) :
    orbitFaceBoundaryLinearMap data.toRotationSystem
        (extendPureSideFaceCoefficients data side coefficients) edge =
      ∑ face : PureSideFace data side,
        if edge ∈ orbitFaceBoundary data.toRotationSystem face.1
          then coefficients face else 0 := by
  classical
  rw [orbitFaceBoundaryLinearMap_apply]
  let pure := orbitFacesAllOnSide data.toRotationSystem side
  calc
    (∑ face : OrbitFace data.toRotationSystem,
        if edge ∈ orbitFaceBoundary data.toRotationSystem face
          then extendPureSideFaceCoefficients data side coefficients face
          else 0) =
        ∑ face ∈ pure,
          if edge ∈ orbitFaceBoundary data.toRotationSystem face
            then extendPureSideFaceCoefficients
              data side coefficients face else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ pure)
      intro face _ hnotPure
      simp [extendPureSideFaceCoefficients, pure, hnotPure]
    _ = ∑ face : PureSideFace data side,
        if edge ∈ orbitFaceBoundary data.toRotationSystem face.1
          then extendPureSideFaceCoefficients
            data side coefficients face.1 else 0 := by
      rw [Finset.sum_subtype pure (fun face => by
        exact mem_orbitFacesAllOnSide_iff
          data.toRotationSystem side face)]
    _ = ∑ face : PureSideFace data side,
        if edge ∈ orbitFaceBoundary data.toRotationSystem face.1
          then coefficients face else 0 := by
      apply Finset.sum_congr rfl
      intro face _
      split_ifs with hedge
      · simp [extendPureSideFaceCoefficients,
          (mem_orbitFacesAllOnSide_iff
            data.toRotationSystem side face.1).2 face.2]
      · rfl

/-- A pure facial cycle as an element of the induced graph's cycle space. -/
def inducedSideFaceCycle
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (side : V -> Prop) [Fintype (SideVertex side)]
    (face : PureSideFace data side) :
    f2CycleSpace (G.induce {vertex | side vertex}) :=
  ⟨inducedSideFaceBoundaryIndicator data side face.1,
    inducedSideFaceBoundaryIndicator_mem_f2CycleSpace
      data htwoSided side face.1 face.2⟩

/-- If at least one ambient face is not pure on the selected side, all
pure-side facial cycles are linearly independent in the induced cycle
space. The proof uses the unique all-face relation in the connected facial
dual. -/
theorem linearIndependent_inducedSideFaceCycle
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (side : V -> Prop) [Fintype (SideVertex side)]
    (hnotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem side) :
    LinearIndependent F2
      (inducedSideFaceCycle data htwoSided side) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hsum face
  let extended :=
    extendPureSideFaceCoefficients data side coefficients
  have hkernel : extended ∈ LinearMap.ker
      (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [LinearMap.mem_ker]
    funext edge
    rw [orbitFaceBoundaryLinearMap_extendPureSideFaceCoefficients_apply]
    simp only [Pi.zero_apply]
    by_cases hinternal : forall vertex,
        vertex ∈ (edge.1 : Sym2 V) -> side vertex
    · rcases edge with ⟨edge, hedge⟩
      induction edge using Sym2.inductionOn with
      | _ left right =>
          let leftSide : SideVertex side :=
            ⟨left, hinternal left (by simp)⟩
          let rightSide : SideVertex side :=
            ⟨right, hinternal right (by simp)⟩
          have hadj : G.Adj left right :=
            (SimpleGraph.mem_edgeSet G).1 hedge
          let induced :
              (G.induce {vertex | side vertex}).edgeSet :=
            ⟨s(leftSide, rightSide), hadj⟩
          have hmap : inducedSideEdgeEmbedding G side induced =
              (⟨s(left, right), hedge⟩ : G.edgeSet) := by
            apply Subtype.ext
            rfl
          have hsumVal := congrArg
            (Submodule.subtype
              (f2CycleSpace (G.induce {vertex | side vertex}))) hsum
          simp only [map_sum, map_smul, map_zero] at hsumVal
          change (∑ pureFace : PureSideFace data side,
            coefficients pureFace •
              inducedSideFaceBoundaryIndicator data side pureFace.1) =
                0 at hsumVal
          have hsumAt := congrFun hsumVal induced
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Pi.zero_apply] at hsumAt
          simp only [inducedSideFaceBoundaryIndicator_apply,
            mul_ite, mul_one, mul_zero] at hsumAt
          rw [hmap] at hsumAt
          exact hsumAt
    · apply Finset.sum_eq_zero
      intro pureFace _
      by_cases hedgeFace : edge ∈
          orbitFaceBoundary data.toRotationSystem pureFace.1
      · exfalso
        apply hinternal
        exact orbitFaceBoundary_endpoints_on_side
          data side pureFace.1 pureFace.2 edge hedgeFace
      · simp [hedgeFace]
  have hconstant :=
    (mem_ker_orbitFaceBoundaryLinearMap_iff_constant
      data.toRotationSystem htwoSided hdual extended).1 hkernel
  rcases hnotPure with ⟨outsideFace, houtsideFace⟩
  have houtsideZero : extended outsideFace = 0 := by
    simp [extended, extendPureSideFaceCoefficients, houtsideFace]
  have hfaceMem : face.1 ∈
      orbitFacesAllOnSide data.toRotationSystem side :=
    (mem_orbitFacesAllOnSide_iff
      data.toRotationSystem side face.1).2 face.2
  have hfaceValue : extended face.1 = coefficients face := by
    simp [extended, extendPureSideFaceCoefficients, hfaceMem]
  calc
    coefficients face = extended face.1 := hfaceValue.symm
    _ = extended outsideFace := hconstant face.1 outsideFace
    _ = 0 := houtsideZero

/-- Pure-side faces are canonically the elements of the computed pure-face
finset. -/
def pureSideFaceEquivAllOnSideFinset
    (data : Data G) (side : V -> Prop) :
    PureSideFace data side ≃
      ↑(orbitFacesAllOnSide data.toRotationSystem side) where
  toFun face := ⟨face.1,
    (mem_orbitFacesAllOnSide_iff
      data.toRotationSystem side face.1).2 face.2⟩
  invFun face := ⟨face.1,
    (mem_orbitFacesAllOnSide_iff
      data.toRotationSystem side face.1).1 face.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Cardinality of the pure-side face subtype. -/
theorem card_pureSideFace
    (data : Data G) (side : V -> Prop) :
    Fintype.card (PureSideFace data side) =
      (orbitFacesAllOnSide data.toRotationSystem side).card := by
  rw [Fintype.card_congr (pureSideFaceEquivAllOnSideFinset data side)]
  exact Fintype.card_coe _

/-- Ambient graph edges whose two endpoints both satisfy the selected side
predicate, represented on the ambient `Sym2` edge carrier. -/
noncomputable def graphEdgesAllOnSide
    (G : SimpleGraph V) (side : V -> Prop) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset ∩ (Finset.univ.filter side).sym2

@[simp]
theorem mem_graphEdgesAllOnSide_iff
    (G : SimpleGraph V) (side : V -> Prop) (edge : Sym2 V) :
    edge ∈ graphEdgesAllOnSide G side <->
      edge ∈ G.edgeSet /\ (forall vertex, vertex ∈ edge -> side vertex) := by
  classical
  simp [graphEdgesAllOnSide, Finset.mem_sym2_iff,
    SimpleGraph.mem_edgeFinset]

/-- Values of the endpoint-computed crossing-edge subtype on the ambient
`Sym2` carrier. -/
noncomputable def graphCrossingEdgeValues
    (data : Data G) (deleted : Finset V) : Finset (Sym2 V) := by
  classical
  exact (vertexSetCrossingEdges data.toRotationSystem deleted).image
    Subtype.val

@[simp]
theorem mem_graphCrossingEdgeValues_iff
    (data : Data G) (deleted : Finset V) (edge : Sym2 V) :
    edge ∈ graphCrossingEdgeValues data deleted <->
      ∃ hedge : edge ∈ G.edgeSet,
        (⟨edge, hedge⟩ : G.edgeSet) ∈
          vertexSetCrossingEdges data.toRotationSystem deleted := by
  classical
  constructor
  · intro hedge
    rcases Finset.mem_image.1 hedge with ⟨crossing, hcrossing, hvalue⟩
    let hedgeSet : edge ∈ G.edgeSet := hvalue ▸ crossing.2
    refine ⟨hedgeSet, ?_⟩
    have heq : crossing = (⟨edge, hedgeSet⟩ : G.edgeSet) :=
      Subtype.ext hvalue
    rwa [← heq]
  · rintro ⟨hedge, hcrossing⟩
    exact Finset.mem_image.2
      ⟨⟨edge, hedge⟩, hcrossing, rfl⟩

/-- The ambient graph edge set is the disjoint union of retained-internal,
deleted-internal, and crossing edges. -/
theorem allOnSide_union_allOffSide_union_crossing_eq_edgeFinset
    (data : Data G) (deleted : Finset V) :
    graphEdgesAllOnSide G (deletedRegionKeep deleted) ∪
        graphEdgesAllOnSide G
          (fun vertex => Not (deletedRegionKeep deleted vertex)) ∪
      graphCrossingEdgeValues data deleted = G.edgeFinset := by
  classical
  ext edge
  constructor
  · simp only [Finset.mem_union]
    rintro ((hretained | hdeleted) | hcrossing)
    · exact SimpleGraph.mem_edgeFinset.2
        ((mem_graphEdgesAllOnSide_iff G _ edge).1 hretained).1
    · exact SimpleGraph.mem_edgeFinset.2
        ((mem_graphEdgesAllOnSide_iff G _ edge).1 hdeleted).1
    · rcases (mem_graphCrossingEdgeValues_iff data deleted edge).1
        hcrossing with ⟨hedge, _⟩
      exact SimpleGraph.mem_edgeFinset.2 hedge
  · intro hedge
    have hedgeSet : edge ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.1 hedge
    rw [Finset.mem_union, Finset.mem_union]
    induction edge using Sym2.inductionOn with
    | _ left right =>
        have hadj : G.Adj left right := hedgeSet
        by_cases hleft : left ∈ deleted <;>
          by_cases hright : right ∈ deleted
        · left
          right
          apply (mem_graphEdgesAllOnSide_iff G _ s(left, right)).2
          refine ⟨hadj, ?_⟩
          intro vertex hvertex
          rcases (Sym2.mem_iff.1 hvertex) with rfl | rfl
          · simpa [deletedRegionKeep] using hleft
          · simpa [deletedRegionKeep] using hright
        · right
          apply (mem_graphCrossingEdgeValues_iff data deleted
            s(left, right)).2
          refine ⟨hadj, ?_⟩
          rw [mem_simpleGraph_vertexSetCrossingEdges_iff]
          exact ⟨left, right, by simp, by simp, hleft, hright⟩
        · right
          apply (mem_graphCrossingEdgeValues_iff data deleted
            s(left, right)).2
          refine ⟨hadj, ?_⟩
          rw [mem_simpleGraph_vertexSetCrossingEdges_iff]
          exact ⟨right, left, by simp, by simp, hright, hleft⟩
        · left
          left
          apply (mem_graphEdgesAllOnSide_iff G _ s(left, right)).2
          refine ⟨hadj, ?_⟩
          intro vertex hvertex
          rcases (Sym2.mem_iff.1 hvertex) with rfl | rfl
          · simpa [deletedRegionKeep] using hleft
          · simpa [deletedRegionKeep] using hright

/-- Retained-internal and deleted-internal edge supports are disjoint. -/
theorem graphEdgesAllOnSide_disjoint_allOffSide
    (G : SimpleGraph V) (deleted : Finset V) :
    Disjoint (graphEdgesAllOnSide G (deletedRegionKeep deleted))
      (graphEdgesAllOnSide G
        (fun vertex => Not (deletedRegionKeep deleted vertex))) := by
  rw [Finset.disjoint_left]
  intro edge hretained hdeleted
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hleftRetained :=
        ((mem_graphEdgesAllOnSide_iff G _ s(left, right)).1 hretained).2
          left (by simp)
      exact (((mem_graphEdgesAllOnSide_iff G _ s(left, right)).1 hdeleted).2
        left (by simp)) hleftRetained

/-- No internal retained edge is a crossing edge. -/
theorem graphEdgesAllOnSide_disjoint_crossing
    (data : Data G) (deleted : Finset V) :
    Disjoint (graphEdgesAllOnSide G (deletedRegionKeep deleted))
      (graphCrossingEdgeValues data deleted) := by
  rw [Finset.disjoint_left]
  intro edge hretained hcrossing
  rcases (mem_graphCrossingEdgeValues_iff data deleted edge).1
      hcrossing with ⟨hedge, hcrossingEdge⟩
  rw [mem_simpleGraph_vertexSetCrossingEdges_iff] at hcrossingEdge
  rcases hcrossingEdge with
    ⟨inner, outer, hinner, houter, hinnerDeleted, _⟩
  have hinnerRetained :=
    ((mem_graphEdgesAllOnSide_iff G _ edge).1 hretained).2 inner hinner
  exact hinnerRetained hinnerDeleted

/-- No internal deleted edge is a crossing edge. -/
theorem graphEdgesAllOffSide_disjoint_crossing
    (data : Data G) (deleted : Finset V) :
    Disjoint
      (graphEdgesAllOnSide G
        (fun vertex => Not (deletedRegionKeep deleted vertex)))
      (graphCrossingEdgeValues data deleted) := by
  rw [Finset.disjoint_left]
  intro edge hdeleted hcrossing
  rcases (mem_graphCrossingEdgeValues_iff data deleted edge).1
      hcrossing with ⟨hedge, hcrossingEdge⟩
  rw [mem_simpleGraph_vertexSetCrossingEdges_iff] at hcrossingEdge
  rcases hcrossingEdge with
    ⟨inner, outer, hinner, houter, _, houterNotDeleted⟩
  have houterDeleted :=
    ((mem_graphEdgesAllOnSide_iff G _ edge).1 hdeleted).2 outer houter
  exact houterNotDeleted (by simpa [deletedRegionKeep] using houterDeleted)

/-- Cardinal form of the computed three-way edge partition. -/
theorem card_allOnSide_add_allOffSide_add_crossing_eq_edges
    (data : Data G) (deleted : Finset V) :
    (graphEdgesAllOnSide G (deletedRegionKeep deleted)).card +
        (graphEdgesAllOnSide G
          (fun vertex => Not (deletedRegionKeep deleted vertex))).card +
      (vertexSetCrossingEdges data.toRotationSystem deleted).card =
      Fintype.card G.edgeSet := by
  have hfirstDisjoint := graphEdgesAllOnSide_disjoint_allOffSide G deleted
  have hsecondDisjoint : Disjoint
      (graphEdgesAllOnSide G (deletedRegionKeep deleted) ∪
        graphEdgesAllOnSide G
          (fun vertex => Not (deletedRegionKeep deleted vertex)))
      (graphCrossingEdgeValues data deleted) := by
    rw [Finset.disjoint_union_left]
    exact ⟨graphEdgesAllOnSide_disjoint_crossing data deleted,
      graphEdgesAllOffSide_disjoint_crossing data deleted⟩
  have hcrossingCard : (graphCrossingEdgeValues data deleted).card =
      (vertexSetCrossingEdges data.toRotationSystem deleted).card := by
    exact Finset.card_image_iff.mpr Subtype.val_injective.injOn
  have hedgeCard : G.edgeFinset.card = Fintype.card G.edgeSet := by
    simp [SimpleGraph.edgeFinset]
  rw [← hcrossingCard,
    ← Finset.card_union_of_disjoint hfirstDisjoint,
    ← Finset.card_union_of_disjoint hsecondDisjoint,
    allOnSide_union_allOffSide_union_crossing_eq_edgeFinset,
    hedgeCard]

/-- Number of ambient vertices satisfying a selected side predicate. -/
noncomputable def sideVertexCount (side : V -> Prop) : Nat := by
  classical
  exact (Finset.univ.filter side).card

/-- A vertex side and its complement partition the ambient vertex carrier. -/
theorem sideVertexCount_add_complement
    (side : V -> Prop) :
    sideVertexCount side + sideVertexCount (fun vertex => Not (side vertex)) =
      Fintype.card V := by
  classical
  let retained := Finset.univ.filter side
  let deleted := Finset.univ.filter (fun vertex => Not (side vertex))
  have hdisjoint : Disjoint retained deleted := by
    rw [Finset.disjoint_left]
    simp [retained, deleted]
  have hunion : retained ∪ deleted = (Finset.univ : Finset V) := by
    ext vertex
    simp [retained, deleted, Classical.em]
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcard
  have hretainedCount : sideVertexCount side = retained.card := by
    unfold sideVertexCount
    apply congrArg Finset.card
    ext vertex
    simp [retained]
  have hdeletedCount :
      sideVertexCount (fun vertex => Not (side vertex)) = deleted.card := by
    unfold sideVertexCount
    apply congrArg Finset.card
    ext vertex
    simp [deleted]
  convert hcard.symm using 1
  · rw [hretainedCount, hdeletedCount]
  · simp

/-- The computed side vertex count is the cardinality of the induced
vertex carrier. -/
theorem sideVertexCount_eq_card_sideVertex
    (side : V -> Prop) [Fintype (SideVertex side)] :
    sideVertexCount side = Fintype.card (SideVertex side) := by
  classical
  let filtered := Finset.univ.filter side
  let equivalence : SideVertex side ≃ ↑filtered :=
    { toFun := fun vertex => ⟨vertex.1, by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa only [Set.mem_setOf_eq] using vertex.2⟩
      invFun := fun vertex => ⟨vertex.1, by
        simpa only [Set.mem_setOf_eq] using
          (Finset.mem_filter.1 vertex.2).2⟩
      left_inv := fun vertex => Subtype.ext rfl
      right_inv := fun vertex => Subtype.ext rfl }
  have hcount : sideVertexCount side = filtered.card := by
    unfold sideVertexCount
    apply congrArg Finset.card
    ext vertex
    simp [filtered]
  have hequiv := Fintype.card_congr equivalence
  have hfiltered := Fintype.card_coe filtered
  omega

/-- The computed ambient internal-edge finset has the same size as the
edge carrier of the induced side graph. -/
theorem card_graphEdgesAllOnSide_eq_card_inducedEdgeSet
    (G : SimpleGraph V) (side : V -> Prop)
    [Fintype (SideVertex side)]
    [Fintype (G.induce {vertex | side vertex}).edgeSet] :
    (graphEdgesAllOnSide G side).card =
      Fintype.card (G.induce {vertex | side vertex}).edgeSet := by
  classical
  let toInternal : (G.induce {vertex | side vertex}).edgeSet ->
      ↑(graphEdgesAllOnSide G side) :=
    fun edge => ⟨(inducedSideEdgeEmbedding G side edge).1,
      (mem_graphEdgesAllOnSide_iff G side _).2 ⟨
        (inducedSideEdgeEmbedding G side edge).2,
        fun vertex hvertex => by
          rw [inducedSideEdgeEmbedding_val] at hvertex
          rcases (Sym2.mem_map.1 hvertex) with
            ⟨source, _hsource, hsource⟩
          rw [← hsource]
          exact source.2⟩⟩
  have hinjective : Function.Injective toInternal := by
    intro left right heq
    apply (inducedSideEdgeEmbedding G side).injective
    apply Subtype.ext
    exact congrArg (fun edge => edge.1) heq
  have hsurjective : Function.Surjective toInternal := by
    rintro ⟨ambient, hambient⟩
    have hambientData :=
      (mem_graphEdgesAllOnSide_iff G side ambient).1 hambient
    induction ambient using Sym2.inductionOn with
    | _ left right =>
        let leftSide : SideVertex side :=
          ⟨left, hambientData.2 left (by simp)⟩
        let rightSide : SideVertex side :=
          ⟨right, hambientData.2 right (by simp)⟩
        have hadj : G.Adj left right :=
          (SimpleGraph.mem_edgeSet G).1 hambientData.1
        let induced : (G.induce {vertex | side vertex}).edgeSet :=
          ⟨s(leftSide, rightSide), hadj⟩
        refine ⟨induced, ?_⟩
        rfl
  let equivalence : (G.induce {vertex | side vertex}).edgeSet ≃
      ↑(graphEdgesAllOnSide G side) :=
    Equiv.ofBijective toInternal ⟨hinjective, hsurjective⟩
  have hequiv := Fintype.card_congr equivalence
  have hinternalCard := Fintype.card_coe (graphEdgesAllOnSide G side)
  omega

/-- A connected induced side satisfies the exact cycle-rank inequality
needed by the spherical cut arithmetic. -/
theorem pureSideFace_cycleRankBound_of_connected
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (side : V -> Prop)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (hnotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem side) :
    (orbitFacesAllOnSide data.toRotationSystem side).card +
        sideVertexCount side ≤
      (graphEdgesAllOnSide G side).card + 1 := by
  classical
  let H : SimpleGraph (SideVertex side) :=
    G.induce {vertex | side vertex}
  have hHConnected : H.Connected := hsideConnected
  letI : Fintype H.edgeSet := SimpleGraph.fintypeEdgeSet H
  letI : DecidableEq H.edgeSet := Subtype.instDecidableEq
  have hlinear := linearIndependent_inducedSideFaceCycle
    data htwoSided hdual side hnotPure
  have hrank := hlinear.fintype_card_le_finrank
  rw [finrank_f2CycleSpace_eq H hHConnected] at hrank
  have hfaces := card_pureSideFace data side
  have hvertices := sideVertexCount_eq_card_sideVertex side
  have hedges := card_graphEdgesAllOnSide_eq_card_inducedEdgeSet G side
  let edgeEquivalence :
      (G.induce {vertex | side vertex}).edgeSet ≃ H.edgeSet := Equiv.refl _
  have hedgeTypes := Fintype.card_congr edgeEquivalence
  have hvertexPositive : 0 < Fintype.card (SideVertex side) :=
    Fintype.card_pos_iff.mpr hHConnected.nonempty
  have hspanningTreeBound :
      Fintype.card (SideVertex side) ≤ Fintype.card H.edgeSet + 1 := by
    simpa only [Nat.card_eq_fintype_card] using
      hHConnected.card_vert_le_card_edgeSet_add_one
  have hcycleRankDefined :
      Fintype.card (SideVertex side) - 1 ≤ Fintype.card H.edgeSet := by
    omega
  omega

/-- In a connected graph, any nontrivial vertex bipartition has an actual
edge crossing from the selected side to its complement. -/
theorem exists_adjacent_crossing_of_connected
    (hconnected : G.Connected) (side : V -> Prop)
    (hside : ∃ vertex, side vertex)
    (hoffSide : ∃ vertex, Not (side vertex)) :
    ∃ left right, G.Adj left right ∧ side left ∧ Not (side right) := by
  by_contra hnoCrossing
  push Not at hnoCrossing
  rcases hside with ⟨start, hstart⟩
  rcases hoffSide with ⟨finish, hfinish⟩
  rcases hconnected start finish with ⟨walk⟩
  have hpropagate : forall {left right},
      (path : G.Walk left right) -> side left -> side right := by
    intro left right path hleft
    induction path with
    | nil => exact hleft
    | @cons first second last hadj tail ih =>
        exact ih (hnoCrossing first second hadj hleft)
  exact hfinish (hpropagate walk hstart)

/-- A nontrivial cut in a connected graph-backed rotation has a computed
quotient face containing a side-changing dart. -/
theorem cutSideTransitionFaces_nonempty_of_connected
    (data : Data G) (deleted : Finset V) (hconnected : G.Connected)
    (hretained : ∃ vertex, deletedRegionKeep deleted vertex)
    (hdeleted : ∃ vertex, Not (deletedRegionKeep deleted vertex)) :
    (cutSideTransitionFaces data.toRotationSystem deleted).Nonempty := by
  rcases exists_adjacent_crossing_of_connected hconnected
      (deletedRegionKeep deleted) hretained hdeleted with
    ⟨left, right, hadj, hleft, hright⟩
  let dart : data.toRotationSystem.D :=
    ⟨(left, right), hadj⟩
  let face := dartOrbitFace data.toRotationSystem dart
  refine ⟨face, (mem_cutSideTransitionFaces_iff
    data.toRotationSystem deleted face).2 ?_⟩
  refine ⟨dart, (mem_orbitFaceSideTransitionDarts_iff
    data.toRotationSystem (deletedRegionKeep deleted) face dart).2 ⟨rfl, ?_⟩⟩
  rw [data.toRotationSystem.vert_phi_eq_vert_alpha]
  change deletedRegionKeep deleted left ≠ deletedRegionKeep deleted right
  intro heq
  exact hright (heq.mp hleft)

/-- The two connected-side cycle-rank inequalities, together with spherical
Euler data, force at least one touched face for every crossing edge. This is
the numerical heart of the planar bond/dual-cycle theorem. -/
theorem crossingEdges_le_transitionFaces_of_sideCycleRankBounds
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hretainedRank :
      (orbitFacesAllOnSide data.toRotationSystem
          (deletedRegionKeep deleted)).card +
        sideVertexCount (deletedRegionKeep deleted) <=
      (graphEdgesAllOnSide G (deletedRegionKeep deleted)).card + 1)
    (hdeletedRank :
      (orbitFacesAllOnSide data.toRotationSystem
          (fun vertex => Not (deletedRegionKeep deleted vertex))).card +
        sideVertexCount
          (fun vertex => Not (deletedRegionKeep deleted vertex)) <=
      (graphEdgesAllOnSide G
          (fun vertex => Not (deletedRegionKeep deleted vertex))).card + 1) :
    (vertexSetCrossingEdges data.toRotationSystem deleted).card <=
      (cutSideTransitionFaces data.toRotationSystem deleted).card := by
  have hfaces := card_transition_add_allOnSide_add_allOffSide_eq_faces
    data.toRotationSystem deleted
  have hedges := card_allOnSide_add_allOffSide_add_crossing_eq_edges
    data deleted
  have hvertices := sideVertexCount_add_complement
    (deletedRegionKeep deleted)
  have heuler := hsphere.euler
  have heulerNat : Fintype.card V +
      Fintype.card (OrbitFace data.toRotationSystem) =
        Fintype.card G.edgeSet + 2 := by
    omega
  omega

/-- Under the actual two connected-side cycle-rank inequalities, every
ambient face changes side at most twice. -/
theorem cutFacesHaveAtMostTwoTransitions_of_sideCycleRankBounds
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hretainedRank :
      (orbitFacesAllOnSide data.toRotationSystem
          (deletedRegionKeep deleted)).card +
        sideVertexCount (deletedRegionKeep deleted) <=
      (graphEdgesAllOnSide G (deletedRegionKeep deleted)).card + 1)
    (hdeletedRank :
      (orbitFacesAllOnSide data.toRotationSystem
          (fun vertex => Not (deletedRegionKeep deleted vertex))).card +
        sideVertexCount
          (fun vertex => Not (deletedRegionKeep deleted vertex)) <=
      (graphEdgesAllOnSide G
          (fun vertex => Not (deletedRegionKeep deleted vertex))).card + 1) :
    CutFacesHaveAtMostTwoTransitionDarts data.toRotationSystem deleted := by
  apply cutFacesHaveAtMostTwoTransitions_of_crossingEdges_le_touchedFaces
  exact crossingEdges_le_transitionFaces_of_sideCycleRankBounds
    data deleted hsphere hretainedRank hdeletedRank

/-- Consequently the two actually computed capped boundary orders have
opposite orientation under the same cycle-rank hypotheses. -/
theorem retained_boundarySuccessor_eq_deleted_inverse_of_sideCycleRankBounds
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hretainedRank :
      (orbitFacesAllOnSide data.toRotationSystem
          (deletedRegionKeep deleted)).card +
        sideVertexCount (deletedRegionKeep deleted) <=
      (graphEdgesAllOnSide G (deletedRegionKeep deleted)).card + 1)
    (hdeletedRank :
      (orbitFacesAllOnSide data.toRotationSystem
          (fun vertex => Not (deletedRegionKeep deleted vertex))).card +
        sideVertexCount
          (fun vertex => Not (deletedRegionKeep deleted vertex)) <=
      (graphEdgesAllOnSide G
          (fun vertex => Not (deletedRegionKeep deleted vertex))).card + 1) :
    retainedRegionBoundarySuccessor data.toRotationSystem
        (deletedRegionKeep deleted) =
      (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹ := by
  apply retained_boundarySuccessor_eq_deleted_boundarySuccessor_inv_of_cutFacesUnique
  apply cutFacesHaveUniqueRetainedBoundaryDart_of_atMostTwoTransitions
  exact cutFacesHaveAtMostTwoTransitions_of_sideCycleRankBounds
    data deleted hsphere hretainedRank hdeletedRank

/-- For a connected spherical graph-backed rotation whose two cut sides are
connected, the computed retained and deleted boundary orders have opposite
orientation. No cut-face uniqueness or cycle-rank inequality is assumed. -/
theorem retained_boundarySuccessor_eq_deleted_inverse_of_connected_sides
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected) :
    retainedRegionBoundarySuccessor data.toRotationSystem
        (deletedRegionKeep deleted) =
      (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹ := by
  rcases hretainedConnected.nonempty with ⟨retainedVertex⟩
  rcases hdeletedConnected.nonempty with ⟨deletedVertex⟩
  have hretained : ∃ vertex, deletedRegionKeep deleted vertex :=
    ⟨retainedVertex.1, by
      simpa only [Set.mem_setOf_eq] using retainedVertex.2⟩
  have hdeleted : ∃ vertex,
      Not (deletedRegionKeep deleted vertex) :=
    ⟨deletedVertex.1, by
      simpa only [Set.mem_setOf_eq] using deletedVertex.2⟩
  rcases cutSideTransitionFaces_nonempty_of_connected
      data deleted hconnected hretained hdeleted with
    ⟨touchedFace, htouchedFace⟩
  have hretainedNotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem
        (deletedRegionKeep deleted) := by
    refine ⟨touchedFace, ?_⟩
    intro hpure
    exact (Finset.disjoint_left.1
      (cutSideTransitionFaces_disjoint_allOnSide
        data.toRotationSystem deleted)) htouchedFace hpure
  have hdeletedNotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => Not (deletedRegionKeep deleted vertex)) := by
    refine ⟨touchedFace, ?_⟩
    intro hpure
    exact (Finset.disjoint_left.1
      (cutSideTransitionFaces_disjoint_allOffSide
        data.toRotationSystem deleted)) htouchedFace hpure
  have hretainedRank := pureSideFace_cycleRankBound_of_connected
    data htwoSided hdual (deletedRegionKeep deleted)
      hretainedConnected hretainedNotPure
  have hdeletedRank := pureSideFace_cycleRankBound_of_connected
    data htwoSided hdual
      (fun vertex => Not (deletedRegionKeep deleted vertex))
      hdeletedConnected hdeletedNotPure
  exact retained_boundarySuccessor_eq_deleted_inverse_of_sideCycleRankBounds
    data deleted hsphere hretainedRank hdeletedRank

/-- The full facial-dual connectedness premise is itself computed from
connectedness of the graph and the stored cyclic vertex rotations. -/
theorem retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected) :
    retainedRegionBoundarySuccessor data.toRotationSystem
        (deletedRegionKeep deleted) =
      (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹ := by
  have hprimal :
      (rotationPrimalGraph data.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  have hdual := orbitFaceInteriorDual_connected
    data.toRotationSystem hsphere.cubic hprimal hrotation
  exact retained_boundarySuccessor_eq_deleted_inverse_of_connected_sides
    data deleted hsphere htwoSided hdual hconnected
      hretainedConnected hdeletedConnected

end

end GoertzelV24PlanarBondBoundaryOrder

end Mettapedia.GraphTheory.FourColor
