import Mettapedia.GraphTheory.FourColor.FacePathExtension
import Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch

/-!
# Component-switch repair of short facial steps

The old colouring is changed by the existing physical Kempe operation,
then extended across the actual exposed path. The exact test retains
which attachment vertices the component meets. Switching at both ends
preserves the extension test. For the specified repair pair, switching
at only the first end repairs a failed one-edge or two-edge addition.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceKempeRepair

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open FaceRegionShelling FaceRegionComplement PhysicalForkCodeCut
open PermutationSingleExitArc FaceExposedBoundary FaceExposedPath
open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)

/-- Extension preserves the specified old assignment, which may itself
be the result of a physical component switch. -/
def Extends (S R : Region data) (a : G.edgeSet → Fin 3) : Prop :=
  ∃ d : G.edgeSet → Fin 3,
    Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) d ∧
      ∀ x ∈ edges data.toRotationSystem S.faces, d x = a x

variable {S R : Region data} (e : Event S R)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)
variable (b : Arc
  (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
  (exposedDarts data e outer))
variable (C : (IncidenceKempeSwitch.graph data.toRotationSystem.endpoints
  (edges data.toRotationSystem S.faces)).Coloring (Fin 3))

/-- The previous classification in the exact colouring representation used
by the component switch. The missing colours have their full profile meaning. -/
theorem extension_iff (m n : Fin 3)
    (hm : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).first ↔ q = m)
    (hn : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).last ↔ q = n) :
    Extends data S R C ↔
      ((exposedEdges data e).card = 1 ∧ m = n) ∨
        ((exposedEdges data e).card = 2 ∧ m ≠ n) ∨ 3 ≤ (exposedEdges data e).card := by
  rw [Extends, FaceColourTransfer.extension_iff data e outer ambient ho b C (proper _ _ C)]
  change (∃ c, (path data e outer ambient ho b).Consecutive c ∧
    (path data e outer ambient ho b).EndpointCompatible (edges data.toRotationSystem S.faces) C c) ↔ _
  rw [(path data e outer ambient ho b).endpoint_extension_iff _ C m n hm hn,
    path_length data e outer ambient ho b]

/-- Exact extension after a specified physical switch, including every
choice of contact at the two attachment vertices. -/
theorem switched_extension_iff (r s : Fin 3)
    (K : (C.bicoloredSubgraph r s).ConnectedComponent) (m n : Fin 3)
    (hm : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).first ↔ q = m)
    (hn : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).last ↔ q = n) :
    Extends data S R (C.swapOnKempeComponent r s K) ↔
      ((exposedEdges data e).card = 1 ∧
        (if Touches C r s K (path data e outer ambient ho b).first then Equiv.swap r s m else m) =
        (if Touches C r s K (path data e outer ambient ho b).last then Equiv.swap r s n else n)) ∨
      ((exposedEdges data e).card = 2 ∧
        (if Touches C r s K (path data e outer ambient ho b).first then Equiv.swap r s m else m) ≠
        (if Touches C r s K (path data e outer ambient ho b).last then Equiv.swap r s n else n)) ∨
      3 ≤ (exposedEdges data e).card :=
  extension_iff data e outer ambient ho b (C.swapOnKempeComponent r s K) _ _
    (missing_switch C r s K hm) (missing_switch C r s K hn)

/-- A switch touching both attachment vertices, or neither, leaves the
extension test unchanged. It cannot fix an already failed short step. -/
theorem same_contact_preserves_extension (r s : Fin 3)
    (K : (C.bicoloredSubgraph r s).ConnectedComponent)
    (hcontact : Touches C r s K (path data e outer ambient ho b).first ↔
      Touches C r s K (path data e outer ambient ho b).last) :
    Extends data S R (C.swapOnKempeComponent r s K) ↔ Extends data S R C := by
  obtain ⟨m, n, hm, hn⟩ := FacePathExtension.endpoint_colours data e outer ambient ho b C (proper _ _ C)
  rw [switched_extension_iff data e outer ambient ho b C r s K m n hm hn,
    extension_iff data e outer ambient ho b C m n hm hn]
  by_cases hfirst : Touches C r s K (path data e outer ambient ho b).first
  · have hlast := hcontact.mp hfirst
    have hne : Equiv.swap r s m ≠ Equiv.swap r s n ↔ m ≠ n :=
      not_congr (Equiv.swap r s).injective.eq_iff
    simp only [hfirst, hlast, ite_true, (Equiv.swap r s).injective.eq_iff, hne]
  · have hlast : ¬ Touches C r s K (path data e outer ambient ho b).last :=
      fun h => hfirst (hcontact.mpr h)
    simp only [hfirst, hlast, ite_false]

/-- For a failed one-edge step, swapping its two different missing colours
in the component through the first end succeeds exactly when it avoids the other. -/
theorem one_edge_switch_iff (r s : Fin 3)
    (K : (C.bicoloredSubgraph r s).ConnectedComponent) (hne : r ≠ s)
    (hr : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).first ↔ q = r)
    (hs : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).last ↔ q = s)
    (hlen : (exposedEdges data e).card = 1)
    (hfirst : Touches C r s K (path data e outer ambient ho b).first) :
    Extends data S R (C.swapOnKempeComponent r s K) ↔
      ¬ Touches C r s K (path data e outer ambient ho b).last := by
  rw [switched_extension_iff data e outer ambient ho b C r s K r s hr hs]
  by_cases hlast : Touches C r s K (path data e outer ambient ho b).last <;>
    simp [hlen, hfirst, hlast, hne.symm]

/-- For a failed two-edge step, both missing colours are `r`. Swapping
`r` with a distinct colour in the first component succeeds exactly on separation. -/
theorem two_edge_switch_iff (r s : Fin 3)
    (K : (C.bicoloredSubgraph r s).ConnectedComponent) (hne : r ≠ s)
    (hr : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).first ↔ q = r)
    (hs : ∀ q, q ∉ profile data.toRotationSystem.endpoints
      (edges data.toRotationSystem S.faces) C (path data e outer ambient ho b).last ↔ q = r)
    (hlen : (exposedEdges data e).card = 2)
    (hfirst : Touches C r s K (path data e outer ambient ho b).first) :
    Extends data S R (C.swapOnKempeComponent r s K) ↔
      ¬ Touches C r s K (path data e outer ambient ho b).last := by
  rw [switched_extension_iff data e outer ambient ho b C r s K r r hr hs]
  by_cases hlast : Touches C r s K (path data e outer ambient ho b).last <;>
    simp [hlen, hfirst, hlast, hne.symm]

include ambient in
/-- Every failed facial extension supplies its own repair pair and physical
component. Separation is exactly success for that switch; contact at the
other end supplies a literal two-colour walk through the old patch. -/
theorem exists_component_test (hfail : ¬ Extends data S R C) :
    ∃ p : OrderedEdgePath.Path data.toRotationSystem.endpoints (exposedEdges data e),
      p.length = (exposedEdges data e).card ∧
      ∃ r s : Fin 3, r ≠ s ∧
        ∃ K : (C.bicoloredSubgraph r s).ConnectedComponent,
          Touches C r s K p.first ∧
          (Extends data S R (C.swapOnKempeComponent r s K) ↔ ¬ Touches C r s K p.last) ∧
          (Touches C r s K p.last →
            ∃ x y : C.bicoloredSet r s,
              p.first ∈ data.toRotationSystem.endpoints x.val ∧
              p.last ∈ data.toRotationSystem.endpoints y.val ∧
              ∃ w : (C.bicoloredSubgraph r s).Walk x y,
                ∀ z ∈ w.support, z.val ∈ edges data.toRotationSystem S.faces) := by
  obtain ⟨oR, hR, _, _⟩ := Region.realizes ambient R
  obtain ⟨arc⟩ := exists_exposed_arc data e oR ambient hR
  let p := path data e oR ambient hR arc
  have hlength : p.length = (exposedEdges data e).card := path_length data e oR ambient hR arc
  obtain ⟨m, n, hm, hn⟩ := FacePathExtension.endpoint_colours
    data e oR ambient hR arc C (proper _ _ C)
  have htest := extension_iff data e oR ambient hR arc C m n hm hn
  have hshort : (exposedEdges data e).card = 1 ∨ (exposedEdges data e).card = 2 := by
    have hpos := p.positive
    have hnot : ¬ 3 ≤ (exposedEdges data e).card :=
      fun h => hfail (htest.mpr (Or.inr (Or.inr h)))
    omega
  rcases hshort with hlen | hlen
  · have hne : m ≠ n := fun h => hfail (htest.mpr (Or.inl ⟨hlen, h⟩))
    obtain ⟨K, hK⟩ := exists_component_touches_of_missing C m n hm hne
    refine ⟨p, hlength, m, n, hne, K, hK,
      one_edge_switch_iff data e oR ambient hR arc C m n K hne hm hn hlen hK, ?_⟩
    exact fun h => exists_walk_of_touches C m n K hK h
  · have hmn : m = n := by
      by_contra h
      exact hfail (htest.mpr (Or.inr (Or.inl ⟨hlen, h⟩)))
    subst n
    obtain ⟨s, hsm, _⟩ := Fin.exists_ne_and_ne_of_two_lt m m (by decide)
    obtain ⟨K, hK⟩ := exists_component_touches_of_missing C m s hm hsm.symm
    refine ⟨p, hlength, m, s, hsm.symm, K, hK,
      two_edge_switch_iff data e oR ambient hR arc C m s K hsm.symm hm hn hlen hK, ?_⟩
    exact fun h => exists_walk_of_touches C m s K hK h

end
end Mettapedia.GraphTheory.FourColor.FaceKempeRepair
