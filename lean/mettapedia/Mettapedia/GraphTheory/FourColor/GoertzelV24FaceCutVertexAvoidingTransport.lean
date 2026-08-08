import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Exact-cut transport along a vertex-avoiding walk

The existing trail transport specializes to cubic vertices.  A framed
annular cellulation has mixed degrees, but the L8 comparison path is disjoint
from the candidate chord wall at the vertex level.  At such a vertex every
incident edge avoids the cut, so exact-cut labels can be transported through
an arbitrary cyclic rotation fiber, regardless of its cardinality.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FaceCutVertexAvoidingTransport

open GoertzelV24FaceCutTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- At one genuinely cyclic vertex, exact-cut labels agree on any two dart
sides when every edge incident to that vertex avoids the cut. -/
theorem labels_eq_of_same_vertex_of_all_edges_not_cut
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {A : Type*} (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (first second : RS.D)
    (hbase : RS.vertOf second = RS.vertOf first)
    (hnot : ∀ dart : RS.D,
      RS.vertOf dart = RS.vertOf first → ¬cut (RS.edgeOf dart)) :
    labels (dartOrbitFace RS first) =
      labels (dartOrbitFace RS second) := by
  rcases hrotation first second hbase.symm with ⟨power, hpower⟩
  have hpowers :
      RS.vertOf ((RS.rho ^ power) first) = RS.vertOf first ∧
        labels (dartOrbitFace RS first) =
          labels (dartOrbitFace RS ((RS.rho ^ power) first)) := by
    exact zpow_induction_left (g := RS.rho)
      (P := fun permutation =>
        RS.vertOf (permutation first) = RS.vertOf first ∧
          labels (dartOrbitFace RS first) =
            labels (dartOrbitFace RS (permutation first)))
      (by simp)
      (fun permutation hinduction => by
        constructor
        · exact (RS.vert_rho (permutation first)).trans hinduction.1
        · exact hinduction.2.trans
            (labels_eq_rho_of_not_cut RS labels cut hexact
              (permutation first) (hnot _ hinduction.1)))
      (fun permutation hinduction => by
        have hvertex :
            RS.vertOf (RS.rho.symm (permutation first)) =
              RS.vertOf first := by
          calc
            RS.vertOf (RS.rho.symm (permutation first)) =
                RS.vertOf (RS.rho (RS.rho.symm (permutation first))) :=
              (RS.vert_rho (RS.rho.symm (permutation first))).symm
            _ = RS.vertOf (permutation first) := by simp
            _ = RS.vertOf first := hinduction.1
        constructor
        · exact hvertex
        · have hstep := labels_eq_rho_of_not_cut RS labels cut hexact
            (RS.rho.symm (permutation first)) (hnot _ hvertex)
          have hstep' :
              labels (dartOrbitFace RS
                (RS.rho.symm (permutation first))) =
                labels (dartOrbitFace RS (permutation first)) := by
            simpa using hstep
          exact hinduction.2.trans hstep'.symm)
      power
  rw [hpower] at hpowers
  exact hpowers.2

/-- The vertex compatibility followed by consecutive graph darts. -/
def FaceCutWalkStep (RS : RotationSystem V E)
    (first second : RS.D) : Prop :=
  RS.vertOf second = RS.vertOf (RS.alpha first)

/-- A nonempty dart chain whose based vertices avoid a cut transports the
exact-cut label from its first dart side to the opposite side of its last
dart.  Edge repetition is harmless; only vertex-level avoidance is used. -/
theorem labels_eq_head_alpha_getLast_of_vertexAvoidingDartChain
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {A : Type*} (labels : OrbitFace RS → A) (cut : E → Prop)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        cut (RS.edgeOf dart))
    (darts : List RS.D) (hne : darts ≠ [])
    (hchain : darts.IsChain (FaceCutWalkStep RS))
    (hnot : ∀ based ∈ darts, ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf based →
        ¬cut (RS.edgeOf incident)) :
    labels (dartOrbitFace RS (darts.head hne)) =
      labels (dartOrbitFace RS
        (RS.alpha (darts.getLast hne))) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hresult :
      labels (dartOrbitFace RS first) =
        labels (dartOrbitFace RS
          (RS.alpha ((first :: rest).getLast (by simp)))) := by
    induction rest generalizing first with
    | nil =>
        exact labels_eq_alpha_of_not_cut RS labels cut hexact first
          (hnot first (by simp) first rfl)
    | cons second rest ih =>
        have hstep : FaceCutWalkStep RS first second := hchain.rel
        have htail : (second :: rest).IsChain (FaceCutWalkStep RS) :=
          hchain.of_cons
        have hnotFirst : ¬cut (RS.edgeOf first) :=
          hnot first (by simp) first rfl
        have hnotAtSecond : ∀ incident : RS.D,
            RS.vertOf incident = RS.vertOf second →
              ¬cut (RS.edgeOf incident) := by
          intro incident hincident
          exact hnot second (by simp) incident hincident
        have hturn := labels_eq_of_same_vertex_of_all_edges_not_cut
          RS hrotation labels cut hexact (RS.alpha first) second
            hstep (fun incident hincident =>
              hnotAtSecond incident (hincident.trans hstep.symm))
        have htailLabels := ih second (by simp) htail (by
          intro based hbased incident hincident
          exact hnot based (by simp [hbased]) incident hincident)
        calc
          labels (dartOrbitFace RS first) =
              labels (dartOrbitFace RS (RS.alpha first)) :=
            labels_eq_alpha_of_not_cut RS labels cut hexact first hnotFirst
          _ = labels (dartOrbitFace RS second) := hturn
          _ = labels (dartOrbitFace RS
                (RS.alpha ((second :: rest).getLast (by simp)))) :=
            htailLabels
          _ = labels (dartOrbitFace RS
                (RS.alpha ((first :: second :: rest).getLast (by simp)))) := by
            simp
  simpa using hresult

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Graph-walk form of vertex-avoiding exact-cut transport. -/
theorem walk_labels_eq_firstDart_alpha_lastDart_of_vertices_avoid_cut
    (graphData : Data G)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    {start finish : V} (walk : G.Walk start finish)
    (hnil : ¬walk.Nil)
    (hnot : ∀ based ∈ walk.darts, ∀ incident : G.Dart,
      incident.fst = based.fst →
        ¬cut (graphData.toRotationSystem.edgeOf incident)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (walk.firstDart hnil)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha (walk.lastDart hnil))) := by
  have hdartsNe : walk.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hnil
  have hchain : walk.darts.IsChain
      (FaceCutWalkStep graphData.toRotationSystem) := by
    apply walk.isChain_dartAdj_darts.imp
    intro first second hadj
    change second.fst = first.symm.fst
    exact hadj.symm
  have hlabels :=
    labels_eq_head_alpha_getLast_of_vertexAvoidingDartChain
      graphData.toRotationSystem hrotation labels cut hexact
        walk.darts hdartsNe hchain hnot
  have hfirstLabel := congrArg
    (fun dart : G.Dart =>
      labels (dartOrbitFace graphData.toRotationSystem dart))
    (walk.firstDart_eq_head_darts hnil)
  have hlastLabel := congrArg
    (fun dart : G.Dart => labels (dartOrbitFace graphData.toRotationSystem
      (graphData.toRotationSystem.alpha dart)))
    (walk.getLast_darts_eq_lastDart hdartsNe)
  exact hfirstLabel.trans (hlabels.trans hlastLabel)

end GoertzelV24FaceCutVertexAvoidingTransport

end Mettapedia.GraphTheory.FourColor
