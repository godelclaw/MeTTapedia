import MettapediaFourColor.TwoDiamondTangle
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler
import Mettapedia.GraphTheory.FourColor.SmallCutConnectedBridgeless
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-!
# Intrinsic geometry of the shared-tip diamond disk

The genuine twenty-vertex piece is cubic, rotation-cyclic, connected and
bridgeless. Its eight ordered first-return arcs form one boundary cycle,
and its Euler mass is four. Alternate paths are short incidence witnesses,
not colour certificates.
-/

namespace FourColor.TwoDiamondTangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph
open OpenTangleMarkedFace OpenTanglePortReplacement OpenTangleReplacementEuler
open GoertzelV24CompositeSeamCubic PermutationFirstReturnRestriction
open ConfigurationTable

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem cubic : OpenIsCubic piece := by
  unfold OpenIsCubic
  decide +kernel

theorem rotation_cyclic : OpenRotationCyclic piece := by
  intro d e hv
  have finite : ∀ d e : Dart, vertex d = vertex e →
      ∃ n : Fin 3, (rho ^ n.val) d = e := by decide +kernel
  obtain ⟨n,hn⟩ := finite d e (by simpa only [piece_vertex] using hv)
  exact ⟨n.val, by rw [zpow_natCast]; exact hn⟩

def vertexOrder : Fin 20 ≃ Fin 20 where
  toFun := lookupBase 33 "!\"&#%'$/.,2-14*03+)("
  invFun := lookupBase 33 "!\"$'%#&43/2*,)(0-+1."
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem piece_connected : (sideMultigraph piece).Connected := by
  have down : ∀ v : Fin 20, v ≠ 0 → ∃ i : Fin 52,
      piece.interiorVert i = vertexOrder v ∧
        vertexOrder.symm (piece.interiorVert (piece.interiorAlpha i)) < v := by decide +kernel
  have root (v : Fin 20) : (sideMultigraph piece).Reach (vertexOrder v) (vertexOrder 0) := by
    induction v using Fin.strong_induction_on with
    | h v ih =>
      by_cases hv : v = 0
      · subst v; exact .refl
      · obtain ⟨i, hi, hj⟩ := down v hv
        have hs : (sideMultigraph piece).Step (vertexOrder v)
            (piece.interiorVert (piece.interiorAlpha i)) := by
          refine ⟨sideEdgeOf piece i, not_false, ?_⟩
          simpa only [hi] using sideMultigraph_ends piece i
        have hr := ih _ hj
        rw [Equiv.apply_symm_apply] at hr
        exact (Relation.ReflTransGen.single hs).trans hr
  intro u v
  change Relation.ReflTransGen (sideMultigraph piece).Step u v
  simpa only [Equiv.apply_symm_apply] using
    (root (vertexOrder.symm u)).trans (reach_symm (root (vertexOrder.symm v)))

def alternateLength : Fin 52 → Fin 6 := lookupBase 33 "%%%%%%%%%%%%%%%%%%%%%%&&%%%%%%%%%%%%%%%%&&%%%%%%%%%%"

def alternateDart (i : Fin 52) (j : Fin 6) : Fin 52 :=
  lookupBase 33 "*+-$$$#.,)))\"*+---.,)!!!.;=6665><---?A<,,,+;B@@@+-$\"\"\"!#.,,,(?A<<<-$\"***,)!###$\"*+++4KMDDDCNL333:TPLLLKOS999KMD000/CNLLL&.;===><-%%%>BJRSSTQIA==TPL2221KOSSS,(?AAA=6&...<-%5556&.;;;'+;BBBA<,(((@'+;;;<,(???04KMMMNL3///NOQHHHGRPMMMFNOQQQRPMEEERS8>BBA=7TQQ2:TPPPMD0444L3/CCCD04KKKL2:TTTQHFNNNPMEGGGHFNOOOPL2:::91KOOO" (⟨6*i.val+j.val, by omega⟩ : Fin 312)

def alternateVertex (i : Fin 52) (j : ℕ) : Fin 20 :=
  lookupBase 33 "!&'#\"\"\"\"#'&!!!\"!&'####'&!\"\"\"#'.,$$$$,.'###%/.'&&&&'./%%%&'#\"!!!!\"#'&&&&%/.''''#\"!&&&'&!\"####\"!&'''(+30))))03+(((*-43++++34-***+30)(((()03+++$#'.,,,,.'#$$$,./24---42/.,,-43+****+34---'&%/....,$#'''.'#$,,,,$#'...%&'.////.'&%%%/%&'....'&%///)(+300003+()))034211112430001034222243011124-,.///.,-422+*-433330)(+++3+()0000)(+3333+*-44442103334301222210344443+*----*+3444" (⟨7*i.val+j%7, by have := Nat.mod_lt j (by decide : 0 < 7); omega⟩ : Fin 364)

private theorem alternate_certificate : ∀ i : Fin 52,
    alternateVertex i 0 = piece.interiorVert i ∧
    alternateVertex i (alternateLength i).val =
      piece.interiorVert (piece.interiorAlpha i) ∧
    ∀ j : Fin 6, j < alternateLength i →
      alternateDart i j ≠ i ∧ alternateDart i j ≠ piece.interiorAlpha i ∧
      piece.interiorVert (alternateDart i j) = alternateVertex i j.val ∧
      piece.interiorVert (piece.interiorAlpha (alternateDart i j)) =
        alternateVertex i (j.val+1) := by decide +kernel

private theorem sideEdge_ne {i j : Fin 52} (hi : j ≠ i)
    (ha : j ≠ piece.interiorAlpha i) : sideEdgeOf piece j ≠ sideEdgeOf piece i := by
  intro h
  have he := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp he with ⟨he, _⟩ | ⟨he, _⟩
  · exact hi he
  · exact ha he

theorem piece_bridgeless : (sideMultigraph piece).Bridgeless := by
  intro e he
  let i : Fin 52 := e.property.choose
  have walk : ∀ j : ℕ, ∀ hj : j ≤ (alternateLength i).val,
      (sideMultigraph piece).ReachAvoiding (sideEdgeOf piece i)
        (piece.interiorVert i) (alternateVertex i j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [(alternate_certificate i).1]
      exact .refl
    | succ j ih =>
      intro hj
      let jj : Fin 6 := ⟨j, by have := (alternateLength i).isLt; omega⟩
      have hc := (alternate_certificate i).2.2 jj (by change j < (alternateLength i).val; omega)
      have hs : (sideMultigraph piece).StepAvoiding (· = sideEdgeOf piece i)
          (alternateVertex i j) (alternateVertex i (j+1)) := by
        refine ⟨sideEdgeOf piece (alternateDart i jj), sideEdge_ne hc.1 hc.2.1, ?_⟩
        simpa only [hc.2.2.1, hc.2.2.2] using
          sideMultigraph_ends piece (alternateDart i jj)
      exact (ih (by omega)).tail hs
  have h := walk (alternateLength i).val (le_refl _)
  rw [(alternate_certificate i).2.1, sideEdgeOf_choose] at h
  exact he h

private instance boundaryDecidable {I B : Type*} (d : I ⊕ B) :
    Decidable (SerialTangleFaceTransfer.Boundary d) := by
  cases d <;> unfold SerialTangleFaceTransfer.Boundary <;> infer_instance

/-- The eight return arcs have lengths two, three, four, three, two, three,
four and three, as read from the actual reference dart rotations. -/
theorem piece_returnCode : returnCode piece = finRotate 8 := by
  let time : Fin 8 → Fin 5 := lookupBase 33 "#$%$#$%$"
  have h : ∀ i : Fin 8, 0 < (time i).val ∧
      (openPhi piece ^ (time i).val) (.inr i) = .inr (i+1) ∧
      ∀ j : Fin 5, 0 < j.val → j.val < (time i).val →
        ¬ SerialTangleFaceTransfer.Boundary ((openPhi piece ^ j.val) (.inr i)) := by
    decide +kernel
  apply Equiv.ext
  intro i
  rw [finRotate_apply]
  change SerialTangleFaceCode.boundaryCoordinate (Fin 52) (Fin 8)
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm (openPhi piece)
      SerialTangleFaceTransfer.Boundary ⟨.inr i,trivial⟩) = i+1
  have hr : ReturnArc (openPhi piece) SerialTangleFaceTransfer.Boundary
      (.inr i) (.inr (i+1)) (time i).val := by
    refine ⟨(h i).1, (h i).2.1, ?_⟩
    intro n hn hlt
    exact (h i).2.2 ⟨n, lt_trans hlt (time i).isLt⟩ hn hlt
  exact congrArg (SerialTangleFaceCode.boundaryCoordinate (Fin 52) (Fin 8))
    (nextHit_eq_of_returnArc (openPhi piece) SerialTangleFaceTransfer.Boundary
      ⟨.inr i,trivial⟩ ⟨.inr (i+1),trivial⟩ hr)

theorem piece_face_count : (openPhi piece).partition.parts.card = 8 := by decide +kernel

theorem piece_eulerMass : eulerMass piece = 4 := by
  unfold eulerMass
  rw [piece_face_count]
  norm_num

end FourColor.TwoDiamondTangle
