import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgeTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedMapEulerBound
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarDualStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Bridgeless spherical rotation maps have two-sided faces

The permutation-level bridge theorem was already available, but the map
class used by the compositional route stores bridge-freeness as connectivity
of the primal graph after deleting an edge.  This file supplies the missing
semantic adapter between those two formulations.

For a dart `d`, strip the transposition through `d` from the edge involution.
The resulting permutation fixes the two deleted darts and agrees with the
old involution everywhere else.  Bridge-freeness makes the edge-deleted
primal graph connected, so the vertex rotation together with the remaining
edge transpositions acts transitively on darts.  If the two sides of the
deleted edge belonged to one face, the Euler split/merge theorem would force
at least two such word components, a contradiction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BridgelessFaceTwoSided

open Equiv Equiv.Perm
open GoertzelV24BridgeTwoSided
open GoertzelV24ConnectedMapEulerBound
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InvolutionEdgeList
open GoertzelV24MapEulerBound
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24RotationEdgeBridge
open GoertzelV24StellarDualStructure
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WordReachability

noncomputable section

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] in
/-- Removing one two-cycle from an involution leaves an involution. -/
theorem strip_involutive (alpha : Perm D) (dart : D)
    (hinvolutive : Function.Involutive alpha) :
    Function.Involutive (Equiv.swap dart (alpha dart) * alpha) := by
  intro current
  by_cases hleft : current = dart
  · subst current
    rw [strip_apply_left alpha dart, strip_apply_left alpha dart]
  by_cases hright : current = alpha dart
  · subst current
    rw [strip_apply_right alpha dart hinvolutive,
      strip_apply_right alpha dart hinvolutive]
  · rw [strip_apply_of_ne alpha dart current hinvolutive hleft hright]
    have halphaLeft : alpha current ≠ dart := by
      intro heq
      apply hright
      have := congrArg alpha heq
      simpa [hinvolutive current] using this
    have halphaRight : alpha current ≠ alpha dart := by
      intro heq
      exact hleft (alpha.injective heq)
    rw [strip_apply_of_ne alpha dart (alpha current) hinvolutive
      halphaLeft halphaRight, hinvolutive current]

/-- Deleting a bridge-free edge from a connected rotation map leaves its
primal vertex graph connected. -/
theorem edgeDeletedPrimalGraph_connected
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hfree : EdgeBridgeFree RS) (removed : E) :
    (edgeDeletedPrimalGraph RS removed).Connected := by
  refine { nonempty := hconnected.nonempty, preconnected := ?_ }
  intro left right
  obtain ⟨walk⟩ := hconnected.preconnected left right
  induction walk with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons first middle last hadj tail ih =>
      obtain ⟨dart, hfirst, hmiddle⟩ :=
        (rotationPrimalGraph_adj_iff RS).1 hadj
      have hstep : (edgeDeletedPrimalGraph RS removed).Reachable first middle := by
        by_cases hedge : RS.edgeOf dart = removed
        · have hreach := hfree dart
          rw [hedge] at hreach
          simpa [hfirst, hmiddle] using hreach
        · exact (SimpleGraph.Adj.reachable
            ⟨dart, hedge, hfirst, hmiddle⟩)
      exact hstep.trans ih

/-- A walk in the edge-deleted primal graph lifts to word reachability for
the vertex rotation and the stripped edge involution. -/
theorem wordReachable_of_edgeDeletedPrimalWalk
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    (removedDart : RS.D)
    {leftVertex rightVertex : V}
    (walk : (edgeDeletedPrimalGraph RS (RS.edgeOf removedDart)).Walk
      leftVertex rightVertex) :
    let stripped := Equiv.swap removedDart (RS.alpha removedDart) * RS.alpha
    let generators := RS.rho :: swapGenerators (edgeList stripped)
    ∀ (left right : RS.D),
      RS.vertOf left = leftVertex → RS.vertOf right = rightVertex →
        WordReachable generators left right := by
  dsimp
  let stripped := Equiv.swap removedDart (RS.alpha removedDart) * RS.alpha
  let generators := RS.rho :: swapGenerators (edgeList stripped)
  have hstripInv : Function.Involutive stripped :=
    strip_involutive RS.alpha removedDart RS.alpha_involutive
  have rotate : ∀ {left right : RS.D},
      RS.vertOf left = RS.vertOf right →
        WordReachable generators left right := by
    intro left right hvertex
    obtain ⟨power, hpower⟩ := exists_nat_pow_apply_eq
      (hrotation left right hvertex)
    have hreach := wordReachable_pow
      (L := generators) (List.mem_cons_self) left power
    rwa [hpower] at hreach
  induction walk with
  | nil =>
      intro left right hleft hright
      exact rotate (hleft.trans hright.symm)
  | @cons first middle last hadj tail ih =>
      intro left right hleft hright
      obtain ⟨crossing, hedge, hfirst, hmiddle⟩ := hadj
      have hcrossingLeft : crossing ≠ removedDart := by
        intro heq
        apply hedge
        simp [heq]
      have hcrossingRight : crossing ≠ RS.alpha removedDart := by
        intro heq
        apply hedge
        simpa [heq] using RS.edge_alpha removedDart
      have hrotate : WordReachable generators left crossing :=
        rotate (hleft.trans hfirst.symm)
      have hcross : WordReachable generators crossing (RS.alpha crossing) := by
        have hreach := wordReachable_swapProduct RS.rho
          (edgeList stripped) crossing
        rw [swapProduct_edgeList stripped hstripInv] at hreach
        rw [strip_apply_of_ne RS.alpha removedDart crossing
          RS.alpha_involutive hcrossingLeft hcrossingRight] at hreach
        exact hreach
      exact hrotate.trans (hcross.trans
        (ih (RS.alpha crossing) right hmiddle hright))

/-- Bridge-freeness gives one word component after stripping any edge. -/
theorem wordOrbitCount_stripped_eq_one
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (hfree : EdgeBridgeFree RS) (dart : RS.D) :
    wordOrbitCount
      (RS.rho :: swapGenerators
        (edgeList (Equiv.swap dart (RS.alpha dart) * RS.alpha))) = 1 := by
  have hdeleted := edgeDeletedPrimalGraph_connected RS hconnected hfree
    (RS.edgeOf dart)
  unfold wordOrbitCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk _ RS.outer, ?_⟩
  intro component
  induction component using Quotient.inductionOn with
  | h current =>
      apply Quotient.sound
      obtain ⟨walk⟩ := hdeleted (RS.vertOf current) (RS.vertOf RS.outer)
      exact wordReachable_of_edgeDeletedPrimalWalk RS hrotation dart walk
        current RS.outer rfl rfl

/-- Stripping one edge from a fixed-point-free edge involution leaves one
fewer transposition in its canonical edge list. -/
theorem length_edgeList_strip_add_one
    (RS : RotationSystem V E) (dart : RS.D) :
    (edgeList (Equiv.swap dart (RS.alpha dart) * RS.alpha)).length + 1 =
      Fintype.card E := by
  let stripped := Equiv.swap dart (RS.alpha dart) * RS.alpha
  have hstripInv : Function.Involutive stripped :=
    strip_involutive RS.alpha dart RS.alpha_involutive
  have hlength := two_mul_length_edgeList_eq_card_movedFinset
    stripped hstripInv
  have hmoved := card_movedFinset_strip_add_two RS.alpha dart
    RS.alpha_involutive (RS.alpha_fixfree dart)
  have hfull : movedFinset RS.alpha = Finset.univ := by
    ext current
    simp [movedFinset, RS.alpha_fixfree]
  rw [hfull, Finset.card_univ] at hmoved
  dsimp [stripped] at hlength
  have hdarts := RS.card_darts_eq_twice_card_edges
  omega

/-- **Bridgeless spherical maps have two-sided faces.**  This is the
rotation-system consumer form of the permutation bridge theorem. -/
theorem orbitFacesTwoSided_of_edgeBridgeFree
    (RS : RotationSystem V E)
    (hspherical : OrbitSphericalCubicMapData RS)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (hfree : EdgeBridgeFree RS) :
    OrbitFacesTwoSided RS := by
  intro dart hsame
  let stripped := Equiv.swap dart (RS.alpha dart) * RS.alpha
  let rest := edgeList stripped
  have hstripInv : Function.Involutive stripped :=
    strip_involutive RS.alpha dart RS.alpha_involutive
  have hleft : swapProduct rest dart = dart := by
    rw [swapProduct_edgeList stripped hstripInv]
    exact strip_apply_left RS.alpha dart
  have hright : swapProduct rest (RS.alpha dart) = RS.alpha dart := by
    rw [swapProduct_edgeList stripped hstripInv]
    exact strip_apply_right RS.alpha dart RS.alpha_involutive
  have hproduct : Equiv.swap dart (RS.alpha dart) * swapProduct rest =
      RS.alpha := by
    rw [swapProduct_edgeList stripped hstripInv]
    simp [stripped]
  have hsurjective : Function.Surjective RS.vertOf := by
    intro vertex
    have hcard := hspherical.cubic vertex
    have hnonempty : (RS.dartsAt vertex).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.card_empty] at hcard
      omega
    obtain ⟨located, hlocated⟩ := hnonempty
    exact ⟨located, (Finset.mem_filter.1 hlocated).2⟩
  have hrho := orbitCount_rho_eq_card_vertex RS hrotation hsurjective
  have hphi := orbitCount_phi_eq_card_orbitFace RS
  have hrest := length_edgeList_strip_add_one RS dart
  have heulerNat :
      Fintype.card V + Fintype.card (OrbitFace RS) = Fintype.card E + 2 := by
    have := hspherical.euler
    omega
  have hsphere :
      orbitCount RS.rho +
          orbitCount (RS.rho *
            (Equiv.swap dart (RS.alpha dart) * swapProduct rest)) =
        rest.length + 3 := by
    rw [hproduct]
    change orbitCount RS.rho + orbitCount RS.phi = rest.length + 3
    rw [hrho, hphi]
    dsimp [rest, stripped] at hrest ⊢
    omega
  have hcomponents := two_le_components_of_sameCycle RS.rho rest
    (RS.alpha_fixfree dart).symm hleft hright
    (edgeList_fst_ne_snd stripped) hsphere (by
      have hsameCycle : RS.phi.SameCycle dart (RS.alpha dart) :=
        Quotient.exact hsame
      simpa [RotationSystem.phi, hproduct] using hsameCycle)
  have hone := wordOrbitCount_stripped_eq_one RS hconnected hrotation
    hfree dart
  change 2 ≤ wordOrbitCount
    (RS.rho :: swapGenerators (edgeList stripped)) at hcomponents
  rw [hone] at hcomponents
  omega

/-- The complete cap-stable class supplies two-sidedness with no additional
hypothesis. -/
theorem BridgelessSphericalCubicMapData.orbitFacesTwoSided
    (RS : RotationSystem V E) (data : BridgelessSphericalCubicMapData RS) :
    OrbitFacesTwoSided RS :=
  orbitFacesTwoSided_of_edgeBridgeFree RS data.spherical
    data.primalConnected data.vertexRotationCyclic data.edgeBridgeFree

end

end GoertzelV24BridgelessFaceTwoSided

end Mettapedia.GraphTheory.FourColor
