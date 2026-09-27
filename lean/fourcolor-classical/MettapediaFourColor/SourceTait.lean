import MettapediaFourColor.ClassicalAssembly
import MettapediaFourColor.HypermapDictionary
import MettapediaFourColor.HypermapTransport
import Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT
import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgelessFaceTwoSided

/-!
# Classical face colours give witnesses for source construction routes

The classical Klein-group difference of the two incident face colours gives
a nonzero colour on each literal edge. At a cubic vertex these three colours
are distinct. This is the usual face-colouring/Tait-colouring implication;
parallel edges and the source's cyclic orders are retained.

The geometric dictionary supplies the reference planarity and bridgelessness
hypotheses from the existing spherical map class. The resulting colouring
then inhabits the previously constructed, geometry-faithful GSLT route.
The catalogue and discharging obligations remain explicit inputs.
-/

namespace FourColor.SourceConstruction

open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.Hypermap.Reference
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceDualConnectedness
open GoertzelV24StellarDualStructure GoertzelV24ConnectedMapEulerBound
open GoertzelV24BridgelessFaceTwoSided
open GoertzelV24RotationDartColoring
open VertexCodeCyclicEncoder SourceVertexCodeTrace
open TubeSlab.VertexTransfer

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem.{u, u, u} V E)

/-- The exact reference hypermap on the original dart carrier. -/
def sourceMap : Hypermap RS.D :=
  toReference (Mettapedia.GraphTheory.Hypermap.ofRotationSystem RS)

/-- A fixed identification of the four reference colours with the source palette. -/
def palette : Color ↪ Mettapedia.GraphTheory.FourColor.Color where
  toFun
    | .c0 => 0
    | .c1 => red
    | .c2 => blue
    | .c3 => purple
  inj' := by decide +kernel

@[simp] theorem palette_zero : palette 0 = 0 := rfl

/-- The unoriented difference of the two face colours at a dart. -/
def dartTrace (k : RS.D → Color) (d : RS.D) : Color := k d + k (RS.alpha d)

theorem dartTrace_alpha (k : RS.D → Color) (d : RS.D) :
    dartTrace RS k (RS.alpha d) = dartTrace RS k d := by
  simp only [dartTrace, RS.alpha_involutive, add_comm]

variable {RS}

theorem faceColor_rho {k : RS.D → Color} (hk : (sourceMap RS).Coloring k) (d : RS.D) :
    k (RS.rho d) = k (RS.alpha d) := by
  have h := hk.face (RS.alpha d)
  change k (RS.phi (RS.alpha d)) = k (RS.alpha d) at h
  simpa only [RotationSystem.phi_apply, RS.alpha_involutive] using h

theorem rho_three (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS) (d : RS.D) :
    RS.rho (RS.rho (RS.rho d)) = d :=
  congrArg Subtype.val (rot_three hc hcyc (⟨d, rfl⟩ : At RS (RS.vertOf d)))

theorem dartTrace_ne_rho (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    {k : RS.D → Color} (hk : (sourceMap RS).Coloring k) (d : RS.D) :
    dartTrace RS k d ≠ dartTrace RS k (RS.rho d) := by
  intro h
  simp only [dartTrace, ← faceColor_rho hk] at h
  have hends : k d = k (RS.rho (RS.rho d)) :=
    add_right_cancel (h.trans (add_comm _ _))
  apply hk.edge (RS.rho (RS.rho d))
  change k (RS.alpha (RS.rho (RS.rho d))) = k (RS.rho (RS.rho d))
  rw [← faceColor_rho hk, rho_three hc hcyc]
  exact hends

/-- Distinct incident darts have distinct edge differences. Cubicity and
one cyclic order per vertex are the only structural inputs. -/
theorem dartTrace_ne_of_sameVertex
    (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    {k : RS.D → Color} (hk : (sourceMap RS).Coloring k)
    {d d' : RS.D} (hvertex : RS.vertOf d = RS.vertOf d') (hne : d ≠ d') :
    dartTrace RS k d ≠ dartTrace RS k d' := by
  let a : At RS (RS.vertOf d) := ⟨d, rfl⟩
  have hsurj : Function.Surjective (cyc a) :=
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨cyc_injective hc hcyc a, by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using
          (card_at (v := RS.vertOf d) hc).symm⟩).2
  obtain ⟨i, hi⟩ := hsurj ⟨d', hvertex.symm⟩
  have hd' := congrArg Subtype.val hi
  fin_cases i
  · exact (hne hd').elim
  · change RS.rho d = d' at hd'
    rw [← hd']
    exact dartTrace_ne_rho hc hcyc hk d
  · change RS.rho (RS.rho d) = d' at hd'
    rw [← hd']
    have h := (dartTrace_ne_rho hc hcyc hk (RS.rho (RS.rho d))).symm
    simpa only [rho_three hc hcyc] using h

/-- A face colouring produces a proper colouring of the original edge carrier. -/
def taitColoring (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    {k : RS.D → Color} (hk : (sourceMap RS).Coloring k) :
    RS.EdgeColoring Mettapedia.GraphTheory.FourColor.Color :=
  edgeColoringOfDartColor RS (fun d => palette (dartTrace RS k d))
    (fun d => congrArg palette (dartTrace_alpha RS k d))
    (fun hv hn heq => dartTrace_ne_of_sameVertex hc hcyc hk hv hn (palette.injective heq))

theorem taitColoring_nonzero (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    {k : RS.D → Color} (hk : (sourceMap RS).Coloring k) :
    RS.IsTaitEdgeColoring (taitColoring hc hcyc hk) := by
  apply edgeColoringOfDartColor_isTait RS _
    (fun d => congrArg palette (dartTrace_alpha RS k d))
    (fun hv hn heq => dartTrace_ne_of_sameVertex hc hcyc hk hv hn (palette.injective heq))
  intro d he
  rw [← palette_zero] at he
  have hz := palette.injective he
  exact hk.edge d ((Color.add_eq_zero_iff.mp hz).symm)

theorem taitColoring_dart (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    {k : RS.D → Color} (hk : (sourceMap RS).Coloring k) (d : RS.D) :
    taitColoring hc hcyc hk (RS.edgeOf d) = palette (k d + k (RS.alpha d)) :=
  edgeColoringOfDartColor_edgeOf RS _
    (fun d => congrArg palette (dartTrace_alpha RS k d))
    (fun hv hn heq => dartTrace_ne_of_sameVertex hc hcyc hk hv hn (palette.injective heq)) d

/-- The source's labelled Euler equation becomes the exact hypermap planarity condition. -/
theorem sourceMap_planar (hclass : BridgelessSphericalCubicMapData RS) :
    (sourceMap RS).Planar := by
  apply (planar_iff _).mpr
  have hs : Function.Surjective RS.vertOf := fun v =>
    ⟨(SourceVertexCodeTrace.root hclass.spherical.cubic v).val,
      (SourceVertexCodeTrace.root hclass.spherical.cubic v).property⟩
  have hv := GoertzelV24StellarDualStructure.orbitCount_rho_eq_card_vertex
    RS hclass.vertexRotationCyclic hs
  have he := orbitCount_alpha_eq_card_edge RS
  have hf := GoertzelV24StellarDualStructure.orbitCount_phi_eq_card_orbitFace RS
  have hd := RS.card_darts_eq_twice_card_edges
  have hn := hypermap_compCount_eq_one_of_primalConnected
    RS hclass.primalConnected hclass.vertexRotationCyclic
  change Mettapedia.GraphTheory.Hypermap.eulerDefect
    (Mettapedia.GraphTheory.Hypermap.ofRotationSystem RS) = 0
  rw [Mettapedia.GraphTheory.Hypermap.eulerDefect,
    Mettapedia.GraphTheory.Hypermap.eulerLhs_eq_orbit_sum,
    Mettapedia.GraphTheory.Hypermap.eulerRhs_eq_card_add_two_mul_compCount,
    Mettapedia.GraphTheory.Hypermap.ofRotationSystem_edge,
    Mettapedia.GraphTheory.Hypermap.orbitCount_node,
    Mettapedia.GraphTheory.Hypermap.ofRotationSystem_face, hv, he, hf, hd, hn]
  have := hclass.spherical.euler
  omega

theorem sourceMap_bridgeless (hclass : BridgelessSphericalCubicMapData RS) :
    (sourceMap RS).Bridgeless := by
  intro d hsame
  exact GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
    RS hclass d (Quotient.sound hsame)

/-- The classical reconstruction supplies the actual Tait colouring required
by the source route, on finite dart carriers in any universe. -/
theorem taitColorable_of_unavoidability
    (noCounterexample : ∀ {D : Type} [Finite D] (H : Hypermap D),
      ¬ H.MinimalCounterExample)
    (hclass : BridgelessSphericalCubicMapData RS) : RotationSystemTaitColorable RS := by
  obtain ⟨k, hk⟩ := Hypermap.fourColorable_of_small_unavoidability
    noCounterexample (sourceMap RS) ⟨sourceMap_planar hclass, sourceMap_bridgeless hclass⟩
  exact ⟨taitColoring hclass.spherical.cubic hclass.vertexRotationCyclic hk,
    taitColoring_nonzero hclass.spherical.cubic hclass.vertexRotationCyclic hk⟩

/-- Every complete valid sweep admits a compatible choice of colours.
This does not require each partial colouring to extend at the next step. -/
theorem supported_sweep_of_unavoidability
    (noCounterexample : ∀ {D : Type} [Finite D] (H : Hypermap D),
      ¬ H.MinimalCounterExample)
    (hclass : BridgelessSphericalCubicMapData RS)
    (order : List V) (hn : order.Nodup) (hne : order ≠ [])
    (hcover : ∀ v, visited order v) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (encodeClosed hclass.spherical.cubic
        hclass.vertexRotationCyclic order hn hne hcover).trace) Fin.elim0 Fin.elim0 :=
  (SourceConstructionGSLT.encoded_support_iff hclass.spherical.cubic
    hclass.vertexRotationCyclic order hn hne hcover).mpr
    (taitColorable_of_unavoidability noCounterexample hclass)

/-- Every map in the source class has a geometry-faithful construction with
compatible colouring witnesses, once the classical obligations are supplied. -/
theorem supported_construction_of_unavoidability
    (noCounterexample : ∀ {D : Type} [Finite D] (H : Hypermap D),
      ¬ H.MinimalCounterExample)
    (hclass : BridgelessSphericalCubicMapData RS) :
    ∃ trace : VertexCodeTrace.Trace 0,
      Nonempty (VertexCodeSourceGeometry.Model trace.realize
        (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      Fintype.card trace.Vertex = Fintype.card V ∧
      VertexConstructionGSLT.colouring.Supports (VertexConstructionGSLT.route trace)
        Fin.elim0 Fin.elim0 := by
  obtain ⟨trace, model, cardinality, support⟩ := SourceConstructionGSLT.class_represented hclass
  exact ⟨trace, model, cardinality, support.mpr
    (taitColorable_of_unavoidability noCounterexample hclass)⟩

#print axioms taitColoring_dart
#print axioms sourceMap_planar
#print axioms sourceMap_bridgeless
#print axioms supported_construction_of_unavoidability

end
end FourColor.SourceConstruction
