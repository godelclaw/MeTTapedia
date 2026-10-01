import MettapediaFourColor.TwoDiamondSplitRepair
import MettapediaFourColor.ConfigurationTable
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness
import MettapediaFourColor.PhysicalKempeBoundary
import MettapediaFourColor.OpenTangleKempeRepair
import MettapediaFourColor.TwoDiamondCompositionGSLT

/-!
# The shared-tip pair of diamonds as an actual cubic disk

Configuration 3 has twenty cubic vertices, twenty-six internal edges and
eight outward half-edges. Its incidence and rotation maps are checked against
the entire reference construction. Face differences reconstruct genuine
colourings while retaining the two diamonds' common tip.

The repair law is transported from configuration 6. It uses that existing
certificate and no independent configuration 3 certificate.
-/

namespace FourColor.TwoDiamondTangle

open ConfigurationTable
open Color KempeBoundarySplit

abbrev graph := TwoDiamondConfigurations.graph003
abbrev boundary := TwoDiamondConfigurations.boundary003
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition
open Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

abbrev Dart := Fin 52 ⊕ Fin 8

def index : Dart ≃ Fin 60 where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr i => ⟨52 + i.val, by omega⟩
  invFun i := if h : i.val < 52 then .inl ⟨i.val, h⟩
    else .inr ⟨i.val - 52, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertexCodes : String := "!\"\"##$%&&!&''#()*++($,,--*'..,%//.)001122/+33034424-\"!%1)(*$"
def rotationCodes : String := "V#U.$5W+(!);,%ZC[K2/\\>6T81-B<7'J@=YNDGXRHA3OLEMSPIQ9\"*?F04:&"
def inverseCodes : String := "*U\"%.\\?)+V(-;$4Y:3KZ&7>9T[,=B6WAJ<0ENXFIR@2MODLQSHP8#!'GC/15"
def leftCodes : String := "\"/!/!.#-#//-/.&,'*',(.()(*.-.)-$-)%,%+$+$),*,++*+))*\"#$%&'(!"
def rightCodes : String := "/\"/!.!-#/#-/./,&*','.()(*(-.).$-)-,%+%+$)$*,+,*+)+*)!\"#$%&'("
def alphaCodes : String := "\"!$#&%('*),+.-0/21436587:9<;>=@?BADCFEHGJILKNMPORQTS"

def vertex (d : Dart) : Fin 20 := lookupBase 33 vertexCodes (index d)
def left (d : Dart) : Fin 15 := lookupBase 33 leftCodes (index d)
def right (d : Dart) : Fin 15 := lookupBase 33 rightCodes (index d)

def rotate (s : String) (d : Dart) : Dart :=
  index.symm (lookupBase 33 s (index d))

def rho : Equiv.Perm Dart where
  toFun := rotate rotationCodes
  invFun := rotate inverseCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alpha : Equiv.Perm (Fin 52) where
  toFun := lookupBase 33 alphaCodes
  invFun := lookupBase 33 alphaCodes
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Literal cyclic orders and half-edges of the twenty-vertex cubic piece. -/
def piece : OpenTangleData (Fin 20) (Fin 52) (Fin 8) where
  interiorVert i := vertex (.inl i)
  boundaryVert i := vertex (.inr i)
  interiorAlpha := alpha
  interiorAlpha_involutive := by decide +kernel
  interiorAlpha_fixfree := by decide +kernel
  rho := rho
  vert_rho := by decide +kernel
  interior_no_self_loops := by decide +kernel
  outer := .inr 0

@[simp] theorem piece_vertex (d : Dart) : piece.vertOf d = vertex d := by
  cases d <;> rfl

def original (d : Dart) : Fin 68 := lookupBase 33 "#$'()*/01234569:?@ABCDEFGHIJKLMNOPQRSTWXYZ[\\]^_`abcd%\".U;8>+" (index d)

/-- The source is exactly the darts off the actual reference perimeter. -/
theorem original_selected : Function.Injective original ∧
    (∀ d, original d ∉ TwoDiamondConfigurations.ring003) ∧
    (∀ d : Fin 68, d ∉ TwoDiamondConfigurations.ring003 → ∃ x, original x = d) := by
  decide +kernel

/-- The embedding preserves the literal cubic rotation and internal reversal. -/
theorem original_incidence :
    (∀ d, original (rho d) = TwoDiamondConfigurations.table003.map.node (original d)) ∧
    (∀ i, original (.inl (alpha i)) =
      TwoDiamondConfigurations.table003.map.edge (original (.inl i))) ∧
    (∀ d, left d = TwoDiamondConfigurations.vertex003 (original d) ∧
      right d = TwoDiamondConfigurations.vertex003
        (TwoDiamondConfigurations.table003.map.edge (original d))) := by
  decide +kernel

def referenceDart (d : Dart) : (cfmap cf003).Dart :=
  TwoDiamondConfigurations.realization003.numbering.symm (original d)

/-- The literal source embeds in the original reference construction,
preserving actual vertex rotations and internal edge identities. -/
theorem reference_embedding : Function.Injective referenceDart ∧
    (∀ d, referenceDart (rho d) = (cfmap cf003).map.node (referenceDart d)) ∧
    (∀ i, referenceDart (.inl (alpha i)) =
      (cfmap cf003).map.edge (referenceDart (.inl i))) := by
  let R := TwoDiamondConfigurations.realization003
  have node (d : (cfmap cf003).Dart) : R.numbering ((cfmap cf003).map.node d) =
      TwoDiamondConfigurations.table003.map.node (R.numbering d) := by
    have h := congrArg (fun H => H.node (R.numbering d)) R.map_eq
    simpa only [Hypermap.relabel_node, Equiv.symm_apply_apply] using h
  have edge (d : (cfmap cf003).Dart) : R.numbering ((cfmap cf003).map.edge d) =
      TwoDiamondConfigurations.table003.map.edge (R.numbering d) := by
    have h := congrArg (fun H => H.edge (R.numbering d)) R.map_eq
    simpa only [Hypermap.relabel_edge, Equiv.symm_apply_apply] using h
  refine ⟨R.numbering.symm.injective.comp original_selected.1, ?_, ?_⟩
  · intro d
    apply R.numbering.injective
    change R.numbering (R.numbering.symm (original (rho d))) =
      R.numbering ((cfmap cf003).map.node (R.numbering.symm (original d)))
    rw [node, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact original_incidence.1 d
  · intro i
    apply R.numbering.injective
    change R.numbering (R.numbering.symm (original (.inl (alpha i)))) =
      R.numbering ((cfmap cf003).map.edge (R.numbering.symm (original (.inl i))))
    rw [edge, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact original_incidence.2.1 i

private theorem edge_faces : ∀ i : Fin 52,
    left (.inl (alpha i)) = right (.inl i) ∧
      right (.inl (alpha i)) = left (.inl i) := by
  decide +kernel

private theorem face_adjacent : ∀ d : Dart, graph.Adj (left d) (right d) := by
  decide +kernel

/-- Distinct incident edges share one face; their other two faces are adjacent. -/
private theorem incident_faces : ∀ d e : Dart, vertex d = vertex e → d ≠ e →
    (left d = left e ∧ graph.Adj (right d) (right e)) ∨
    (left d = right e ∧ graph.Adj (right d) (left e)) ∨
    (right d = left e ∧ graph.Adj (left d) (right e)) ∨
    (right d = right e ∧ graph.Adj (left d) (left e)) := by
  decide +kernel

def referenceColour (k : graph.Coloring Color) (d : Dart) : Color :=
  k (left d) + k (right d)

theorem referenceColour_proper (k : graph.Coloring Color) {d e : Dart}
    (hv : vertex d = vertex e) (hne : d ≠ e) :
    referenceColour k d ≠ referenceColour k e := by
  intro h
  change k (left d) + k (right d) = k (left e) + k (right e) at h
  rcases incident_faces d e hv hne with ⟨he, ha⟩ | ⟨he, ha⟩ | ⟨he, ha⟩ | ⟨he, ha⟩
  · rw [he] at h
    exact k.valid ha (add_left_cancel h)
  · rw [he, add_comm (k (left e))] at h
    exact k.valid ha (add_left_cancel h)
  · rw [he, add_comm (k (left d))] at h
    exact k.valid ha (add_left_cancel h)
  · rw [he] at h
    exact k.valid ha (add_right_cancel h)

/-- Reuse the common exact identification of the two Klein palettes. -/
abbrev palette := PhysicalKempeBoundary.palette

def colouring (k : graph.Coloring Color) :
    Dart → Mettapedia.GraphTheory.FourColor.Color := fun d => palette (referenceColour k d)

/-- Colourings reconstruct on actual darts, respecting every internal edge and vertex. -/
theorem colouring_valid (k : graph.Coloring Color) :
    OpenTangleClosedWitness.IsColor piece (colouring k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply congrArg palette
    change k (left (.inl (alpha i))) + k (right (.inl (alpha i))) =
      k (left (.inl i)) + k (right (.inl i))
    rw [(edge_faces i).1, (edge_faces i).2, add_comm]
  · intro d e hv hn h
    exact referenceColour_proper k (by simpa using hv) hn (palette.injective h)
  · intro d h
    have hz : referenceColour k d = 0 := palette.injective h
    exact k.valid (face_adjacent d) (Color.add_eq_zero_iff.mp hz)

/-- Boundary extraction commutes with the graph-to-tangle reconstruction. -/
theorem boundary_reference (k : graph.Coloring Color) :
    (List.finRange 8).map (fun i => referenceColour k (.inr i)) =
      trace (boundary.map k) := by
  change _ = trace [k 0, k 1, k 2, k 3, k 4, k 5, k 6, k 7]
  rw [trace_cons]
  change [k 1 + k 0, k 2 + k 1, k 3 + k 2, k 4 + k 3,
    k 5 + k 4, k 6 + k 5, k 7 + k 6, k 0 + k 7] =
    [k 0 + k 1, k 1 + k 2, k 2 + k 3, k 3 + k 4,
      k 4 + k 5, k 5 + k 6, k 6 + k 7, k 7 + k 0]
  simp only [add_comm]

theorem boundary_colouring (k : graph.Coloring Color) :
    (List.finRange 8).map (fun i => colouring k (.inr i)) =
      (trace (boundary.map k)).map palette := by
  rw [← boundary_reference, List.map_map]
  rfl

/-- Reuse the integrated shared-tip repair transferred from configuration 6. -/
theorem repair : Repairs (GraphTrace graph boundary) 8 := by
  intro et hlen hzero hsum Q hQ hold
  obtain ⟨es, hs, ho⟩ := TwoDiamondSplitRepair.transferred_repair et hlen hzero hsum Q hQ hold
  exact ⟨es, (TwoDiamondConfigurations.reducibilityTrace003 es).mp hs, ho⟩

theorem compatible_colouring {Q : List Color → Prop} (hQ : KempeClosed Q)
    (et : List Color) (hlen : et.length = 8) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : Q et) :
    ∃ k : graph.Coloring Color, Q (trace (boundary.map k)) := by
  obtain ⟨es, ⟨k, rfl⟩, hk⟩ := repair et hlen hzero hsum Q hQ hold
  exact ⟨k, hk⟩

/-- The shared eight-port profile reconstructs genuine open-piece witnesses. -/
theorem open_repair : Repairs (OpenTangleKempeRepair.Trace piece (Equiv.refl _)) 8 := by
  intro et hlen hzero hsum Q hQ hold
  obtain ⟨k, hk⟩ := compatible_colouring hQ et hlen hzero hsum hold
  exact ⟨trace (boundary.map k), ⟨colouring k, colouring_valid k, boundary_colouring k⟩, hk⟩

noncomputable def jointColour (p : TwoDiamondConfigurations.Plan003 Color) :=
  colouring ((TwoDiamondConfigurations.planEquiv003 Color).symm p)

/-- The existing GSLT assembly and the physical piece use the same joint
choice. Boundary extraction retains exactly its original exterior colours. -/
theorem joint_construction (p : TwoDiamondConfigurations.Plan003 Color) :
    (TwoDiamondCompositionGSLT.semantics .three).Supports TwoDiamondCompositionGSLT.route p
      (TwoDiamondCompositionGSLT.assembled .three p) ∧
    OpenTangleClosedWitness.IsColor piece (jointColour p) ∧
    (List.finRange 8).map (fun i => jointColour p (.inr i)) =
      (trace ((List.finRange 8).map p.1)).map palette := by
  refine ⟨⟨TwoDiamondCompositionGSLT.witness .three p⟩,
    colouring_valid _, ?_⟩
  change (List.finRange 8).map (fun i => colouring
    ((TwoDiamondConfigurations.planEquiv003 Color).symm p) (.inr i)) = _
  rw [boundary_colouring]
  have ports : (List.finRange 8).map
      (fun i => TwoDiamondConfigurations.graphIso003 (.inl i)) = boundary := by
    decide +kernel
  have hb : boundary.map ((TwoDiamondConfigurations.planEquiv003 Color).symm p) =
      (List.finRange 8).map p.1 := by
    rw [← ports, List.map_map]
    apply List.map_congr_left
    intro i _
    exact TwoDiamondConfigurations.reconstruct_boundary003 Color p i
  rw [hb]

end FourColor.TwoDiamondTangle
