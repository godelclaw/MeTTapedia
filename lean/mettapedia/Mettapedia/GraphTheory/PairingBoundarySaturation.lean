import Mettapedia.Combinatorics.Matching.Pairing
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Saturating paired boundary components

Let a graph carry a displayed boundary whose points are paired through graph
components.  Given a selected part of the boundary, the corresponding
pairing saturation contains

* every selected boundary point; and
* the whole graph component of a selected pair when both endpoints of that
  pair are selected.

Consequently an edge of the graph can leave the saturated side only at a
selected boundary point whose partner is not selected.  This is the generic
set-theoretic fact behind sweep interfaces: completed returns disappear into
the saturated side, while open returns are the only remaining graph exits.
-/

namespace Mettapedia.GraphTheory

open MatchingParity
open SimpleGraph

universe u v

variable {V : Type u} {B : Type v} {H : SimpleGraph V}

/-- The side obtained by retaining selected boundary points and filling every
component whose paired boundary endpoints are both selected. -/
def pairingBoundarySaturation
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop) :
    V → Prop :=
  fun vertex =>
    (∃ boundary, selected boundary ∧ embed boundary = vertex) ∨
      ∃ boundary, selected boundary ∧
        selected (pairing.partner boundary) ∧
        H.Reachable (embed boundary) vertex

theorem pairingBoundarySaturation_boundary
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop)
    {boundary : B} (hselected : selected boundary) :
    pairingBoundarySaturation (H := H) embed pairing selected
      (embed boundary) :=
  Or.inl ⟨boundary, hselected, rfl⟩

/-- A component whose two paired boundary endpoints are selected is wholly
contained in the saturation. -/
theorem pairingBoundarySaturation_of_reachable
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop)
    {boundary : B} (hselected : selected boundary)
    (hpartner : selected (pairing.partner boundary)) {vertex : V}
    (hreachable : H.Reachable (embed boundary) vertex) :
    pairingBoundarySaturation (H := H) embed pairing selected vertex :=
  Or.inr ⟨boundary, hselected, hpartner, hreachable⟩

/-- Filling whole components whose paired boundary endpoints are selected
preserves connectedness of a connected selected boundary skeleton.  The
component graph may be a subgraph of the ambient graph: its paths are lifted
to the ambient graph and remain inside the saturation by construction. -/
theorem induce_pairingBoundarySaturation_connected
    [DecidableEq V]
    {G : SimpleGraph V}
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop)
    (hHG : H ≤ G)
    (hboundaryConnected :
      (G.induce (fun vertex => ∃ boundary, selected boundary ∧
        embed boundary = vertex)).Connected) :
    (G.induce
      (pairingBoundarySaturation (H := H) embed pairing selected)).Connected := by
  have hsub : ∀ vertex,
      (∃ boundary, selected boundary ∧ embed boundary = vertex) →
        pairingBoundarySaturation (H := H) embed pairing selected vertex := by
    intro vertex hvertex
    exact Or.inl hvertex
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  rcases hboundaryConnected.nonempty with ⟨root⟩
  refine ⟨⟨root.1, hsub root.1 root.2⟩, ?_⟩
  intro vertex
  rcases vertex.2 with hboundary | hcomponent
  · have hrootBoundary :
        (G.induce (fun point => ∃ boundary, selected boundary ∧
          embed boundary = point)).Reachable root
            ⟨vertex.1, hboundary⟩ :=
      hboundaryConnected.preconnected root ⟨vertex.1, hboundary⟩
    exact hrootBoundary.map (G.induceHomOfLE hsub).toHom
  · rcases hcomponent with
      ⟨boundary, hselected, hpartnerSelected, hreachable⟩
    have hboundaryMem :
        (∃ point, selected point ∧ embed point = embed boundary) :=
      ⟨boundary, hselected, rfl⟩
    have hrootBoundary :
        (G.induce (fun point => ∃ boundary, selected boundary ∧
          embed boundary = point)).Reachable root
            ⟨embed boundary, hboundaryMem⟩ :=
      hboundaryConnected.preconnected root ⟨embed boundary, hboundaryMem⟩
    have hrootBoundaryMapped :=
      hrootBoundary.map (G.induceHomOfLE hsub).toHom
    rcases hreachable with ⟨walk⟩
    let ambientWalk := walk.mapLe hHG
    have hall : ∀ point ∈ ambientWalk.support,
        pairingBoundarySaturation (H := H) embed pairing selected point := by
      intro point hpoint
      have hpointH : point ∈ walk.support := by
        simpa only [ambientWalk, SimpleGraph.Walk.support_mapLe_eq_support]
          using hpoint
      exact Or.inr ⟨boundary, hselected, hpartnerSelected,
        (walk.takeUntil point hpointH).reachable⟩
    have hcomponentInduced :
        (G.induce
          (pairingBoundarySaturation (H := H) embed pairing selected)).Reachable
            ⟨embed boundary, hsub _ hboundaryMem⟩ vertex := by
      exact ⟨ambientWalk.induce
        {point |
          pairingBoundarySaturation (H := H) embed pairing selected point}
        hall⟩
    exact hrootBoundaryMapped.trans hcomponentInduced

/-- Any graph edge leaving the saturated side leaves from an open selected
boundary endpoint.  No degree or planarity assumption is needed for this
local statement. -/
theorem exists_open_boundary_of_adj_saturation_exit
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop)
    {inside outside : V} (hadj : H.Adj inside outside)
    (hinside : pairingBoundarySaturation (H := H) embed pairing selected inside)
    (houtside : ¬ pairingBoundarySaturation (H := H) embed pairing selected outside) :
    ∃ boundary : B,
      selected boundary ∧ ¬ selected (pairing.partner boundary) ∧
        embed boundary = inside := by
  rcases hinside with ⟨boundary, hselected, hembed⟩ |
    ⟨boundary, hselected, hpartner, hreachable⟩
  · refine ⟨boundary, hselected, ?_, hembed⟩
    intro hpartner
    apply houtside
    exact pairingBoundarySaturation_of_reachable embed pairing selected
      hselected hpartner (by simpa [hembed] using hadj.reachable)
  · exact False.elim (houtside
      (pairingBoundarySaturation_of_reachable embed pairing selected
        hselected hpartner (hreachable.trans hadj.reachable)))

/-- Symmetric form for an unoriented crossing edge: its endpoint inside the
saturation is the image of an open selected boundary point. -/
theorem exists_open_boundary_of_edge_crosses_pairingBoundarySaturation
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop)
    {left right : V} (hadj : H.Adj left right)
    (hcrosses :
      (pairingBoundarySaturation (H := H) embed pairing selected left ∧
          ¬ pairingBoundarySaturation (H := H) embed pairing selected right) ∨
        (pairingBoundarySaturation (H := H) embed pairing selected right ∧
          ¬ pairingBoundarySaturation (H := H) embed pairing selected left)) :
    ∃ boundary : B,
      selected boundary ∧ ¬ selected (pairing.partner boundary) ∧
        (embed boundary = left ∨ embed boundary = right) := by
  rcases hcrosses with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · rcases exists_open_boundary_of_adj_saturation_exit embed pairing selected
        hadj hleft hright with ⟨boundary, hselected, hopen, heq⟩
    exact ⟨boundary, hselected, hopen, Or.inl heq⟩
  · rcases exists_open_boundary_of_adj_saturation_exit embed pairing selected
        hadj.symm hright hleft with ⟨boundary, hselected, hopen, heq⟩
    exact ⟨boundary, hselected, hopen, Or.inr heq⟩

/-- Boundary points selected on only one end of their displayed pair. -/
def PairingBoundaryOpenEndpoint
    (pairing : Pairing B) (selected : B → Prop) :=
  {boundary : B // selected boundary ∧ ¬ selected (pairing.partner boundary)}

/-- Oriented graph edges leaving a pairing-saturated side. -/
def PairingBoundaryExitDart
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop) :=
  {dart : H.Dart //
    pairingBoundarySaturation (H := H) embed pairing selected dart.fst ∧
      ¬ pairingBoundarySaturation (H := H) embed pairing selected dart.snd}

/-- If every displayed boundary point has degree one, distinct outgoing darts
of the saturated side have distinct open boundary endpoints.  Thus the number
of graph exits is bounded by the number of genuinely open displayed pairs. -/
theorem card_pairingBoundaryExitDart_le_openEndpoint
    [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    [DecidableRel H.Adj]
    (embed : B → V) (pairing : Pairing B) (selected : B → Prop)
    (hdegree : ∀ boundary, H.degree (embed boundary) = 1) :
    Nat.card (PairingBoundaryExitDart (H := H) embed pairing selected) ≤
      Nat.card (PairingBoundaryOpenEndpoint pairing selected) := by
  classical
  let boundaryOf
      (dart : PairingBoundaryExitDart (H := H) embed pairing selected) : B :=
    Classical.choose (exists_open_boundary_of_adj_saturation_exit
      (H := H) embed pairing selected dart.1.adj dart.2.1 dart.2.2)
  have boundaryOf_spec
      (dart : PairingBoundaryExitDart (H := H) embed pairing selected) :
      selected (boundaryOf dart) ∧
        ¬ selected (pairing.partner (boundaryOf dart)) ∧
        embed (boundaryOf dart) = dart.1.fst :=
    Classical.choose_spec (exists_open_boundary_of_adj_saturation_exit
      (H := H) embed pairing selected dart.1.adj dart.2.1 dart.2.2)
  let toOpen :
      PairingBoundaryExitDart (H := H) embed pairing selected →
        PairingBoundaryOpenEndpoint pairing selected :=
    fun dart => ⟨boundaryOf dart, (boundaryOf_spec dart).1,
      (boundaryOf_spec dart).2.1⟩
  have hinjective : Function.Injective toOpen := by
    intro left right heq
    have hboundary : boundaryOf left = boundaryOf right :=
      congrArg Subtype.val heq
    have hleftFst : embed (boundaryOf left) = left.1.fst :=
      (boundaryOf_spec left).2.2
    have hrightFst : embed (boundaryOf right) = right.1.fst :=
      (boundaryOf_spec right).2.2
    have hfst : left.1.fst = right.1.fst := by
      rw [← hleftFst, hboundary, hrightFst]
    rcases SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
        (hdegree (boundaryOf left)) with
      ⟨neighbor, _hadjNeighbor, hunique⟩
    have hleftAdj : H.Adj (embed (boundaryOf left)) left.1.snd := by
      simpa only [hleftFst] using left.1.adj
    have hrightAdj : H.Adj (embed (boundaryOf left)) right.1.snd := by
      rw [hboundary]
      simpa only [hrightFst] using right.1.adj
    have hleftSnd : left.1.snd = neighbor :=
      hunique left.1.snd hleftAdj
    have hrightSnd : right.1.snd = neighbor :=
      hunique right.1.snd hrightAdj
    have hsnd : left.1.snd = right.1.snd :=
      hleftSnd.trans hrightSnd.symm
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext hfst hsnd
  letI : Finite (PairingBoundaryOpenEndpoint pairing selected) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Nat.card_le_card_of_injective toOpen hinjective

end Mettapedia.GraphTheory
