import Mettapedia.GraphTheory.FourColor.PaddedCycleCapImmersion
import Mettapedia.GraphTheory.FourColor.PartialCubicDartRoutes

/-!
# Separation of the face-derived forty-vertex pentagonal cap

The finite certificate transports both darts together until a short
path or distinct cubic slots excludes their equality. Cyclic translation
reduces the check to one source sector. It checks geometry, not colourings.
Actual face closure supplies an interpretation before separation is known.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap.PentagonalSeparation

open PartialCubicDartSeparation

abbrev Vertex := PaddedCycleCap.Vertex 5
abbrev Slot := PartialDiagram.Slot 5

def shift (k : Fin 5) (v : Vertex) : Vertex := (v.1+k,v.2)
def shiftSlot (k : Fin 5) (d : Slot) : Slot := (shift k d.1,d.2)

set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

def flat (d : Slot) : ℕ := 3*(8*d.1.1.val+d.1.2.val)+d.2.val
def unflat (i : Fin 120) : Slot :=
  ((⟨i.val/24,by omega⟩,⟨i.val/3%8,Nat.mod_lt _ (by decide)⟩),
    ⟨i.val%3,Nat.mod_lt _ (by decide)⟩)

/-- Two ASCII hex digits encode each reversal; zero denotes a port. -/
def flipCodes : String := "6219056B0307060A0E081C147709100F1300110C1615250002311D0B1B1F1E222620342C172128272B0029242E2D3D001A4935233337363A3E384C442F39403F4300413C4645550032614D3B4B4F4E525650645C475158575B0059545E5D6D004A0165536367666A6E6804745F69706F7300716C76750D00"

def hexNibble (b : UInt8) : ℕ :=
  if 65 ≤ b.toNat then b.toNat-55 else b.toNat-48

def flip (d : Slot) : Option Slot :=
  let k := 2*flat d
  let n := 16*hexNibble (flipCodes.toUTF8[k]?.getD 48) +
    hexNibble (flipCodes.toUTF8[k+1]?.getD 48)
  if n = 0 then none else some (unflat ⟨(n-1)%120,Nat.mod_lt _ (by decide)⟩)

/-- The compact presentation has exactly the original internal reversals,
including all ten missing boundary reversals. -/
theorem flip_eq : ∀ d : Slot, flip d = PartialDiagram.flip 5 d := by decide

def diagram : Diagram Vertex where
  rotate := PartialDiagram.rotate 5
  flip := flip
  flip_reverse := fun d e he => by
    rw [flip_eq] at he ⊢
    exact PartialDiagram.flip_reverse 5 d e he

theorem shift_rotate (k : Fin 5) (d : Slot) :
    shiftSlot k (diagram.rotate d) = diagram.rotate (shiftSlot k d) := rfl

/-- Missing boundary reversals remain missing under cyclic translation. -/
theorem shift_flip : ∀ (k : Fin 5) (d : Slot),
    Option.map (shiftSlot k) (diagram.flip d) = diagram.flip (shiftSlot k d) := by decide

/-- Four ASCII hex digits encode each binary route. The highest bit is
its terminal sentinel; lower bits are the simultaneous operations in
execution order. Zero denotes an unused equal-vertex row. Eight flat
blocks bound the amount of data reduced by each fixed-kind certificate. -/
private def routeCodes0 : String := "0000000000000001000100010001000100010001000100010001000100010001000100010001000100010006000C0006000100010001000100010001000100010001000100010001000100010001000600340006000600030006000600190006000100010001000100010001000100010001000100010001000600030032001A0003000600060003000D00030003001A00010001000100010001000100010001000100010001000100060003000300030003006400010001000100030003000C000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001"
private def routeCodes1 : String := "0001000100010000000000000001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010006000C00060006000C000C001A000C000600060064000C001A003400320001000100010001000100010006003400060006001900060006001A0032001A006900320006001A0032001A0019003200010001000100010001000100060003000600010001000100060003000D000600030032000600030003000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001"
private def routeCodes2 : String := "0001000100010001000100010000000000000001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010006000C00060006001900060019003400060001000100010006000300060003006500060019000300CA001A0019003200190069001A001A001900650019000D00CA00010001000100060003000D00030003003500190003000D001A0019000D0019000D006400C90003000300190003000C000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001"
private def routeCodes3 : String := "000100010001000100010001000100010001000000000000000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001001A000C0006000100010001000100010001001A003200060006006900060006006A0006001A00340032001A00190032001A00690032000100010001000600030032001A006500060006000300D2001A00190065001A001900CA001A0019000D001A00030064000100010001000600030003000100010001000100010001001A0003000300030003000C000100010001000100010001"
private def routeCodes4 : String := "000100010001000100010001000100010001000100010001000000000000000100010001000100010001000100010001000100010001000100010001000100010001001A000C000600010001000100CA000C00060006000C003200CA003400320006000C0006000600340006001A00340032001A00690032001A034A003200CA019400D200CA006A00D200CA006900D2000600190006000600190034001A001900320006000300D4001A00190654001A001900D200CA0019000300060003064A000100010001000600060003000100010001000100010001000100010001000100010001000100010001000100010001"
private def routeCodes5 : String := "00010001000100010001000100010001000100010001000100010001000100000000000000010001000100010001000100010001000100010001000100010001000100030006000600010001000100010001000100060069000600190D29000600030032000600060019000600190032001A001A00650032001A00690032006901A900CA00CA006900D20329006500D2001A00030006001A001900650019000D00CA001A0019000D00CA0069006500690065035200CA0019000D001A0003194A00060003000D001A0003000300060003000300010001000100CA00030003000100010001000100010001000100010001"
private def routeCodes6 : String := "0001000100010001000100010001000100010001000100010001000100010001000100010000000000000001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010352000C00060001000100010006000C000600C9000C0006001A0034003200C9000C003200CA0034003200320329003400CA019400D2000600340006000600190032001A00690032001A0019003200D2006900D400CA006900D20032001A0652001A001900D20006000300060006000600190006000300320001000100010006001A00030006000300D2000100010001000100010001"
private def routeCodes7 : String := "000600030003000100010001000100010001000100010001000100010001000100010001000100010001000000000000000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000300060006000100010001001900060006001A003200060006032A0006001A0CA50006001A00690032006A01A500CA0003000D0006001A0019003200190065001A001A001900D200CA006900D2032A006900CA00CA00690065006A0069034A000600030032001A0019000D001A0003000D001A0003000300CA0019000D001900031952034900030003000100010001"

def routeCodes (a : Fin 8) : String :=
  match a.val with
  | 0 => routeCodes0
  | 1 => routeCodes1
  | 2 => routeCodes2
  | 3 => routeCodes3
  | 4 => routeCodes4
  | 5 => routeCodes5
  | 6 => routeCodes6
  | _ => routeCodes7

def routeOffset (b : Fin 8) (delta : Fin 5) (s : Fin 3) : ℕ :=
  4 * ((delta.val*8+b.val)*3+s.val)

def routeCode (a b : Fin 8) (delta : Fin 5) (s : Fin 3) : ℕ :=
  let k := routeOffset b delta s
  4096*hexNibble ((routeCodes a).toUTF8[k]?.getD 48) +
    256*hexNibble ((routeCodes a).toUTF8[k+1]?.getD 48) +
     16*hexNibble ((routeCodes a).toUTF8[k+2]?.getD 48) +
        hexNibble ((routeCodes a).toUTF8[k+3]?.getD 48)


private theorem routes_kind_0 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(0 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 0 b delta s) 14
      ((0,0),0) ((delta,b),s) = true := by decide

private theorem routes_kind_1 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(1 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 1 b delta s) 14
      ((0,1),0) ((delta,b),s) = true := by decide

private theorem routes_kind_2 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(2 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 2 b delta s) 14
      ((0,2),0) ((delta,b),s) = true := by decide

private theorem routes_kind_3 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(3 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 3 b delta s) 14
      ((0,3),0) ((delta,b),s) = true := by decide

private theorem routes_kind_4 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(4 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 4 b delta s) 14
      ((0,4),0) ((delta,b),s) = true := by decide

private theorem routes_kind_5 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(5 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 5 b delta s) 14
      ((0,5),0) ((delta,b),s) = true := by decide

private theorem routes_kind_6 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(6 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 6 b delta s) 14
      ((0,6),0) ((delta,b),s) = true := by decide

private theorem routes_kind_7 : ∀ (b : Fin 8) (delta : Fin 5),
    (0,(7 : Fin 8)) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode 7 b delta s) 14
      ((0,7),0) ((delta,b),s) = true := by decide

/-- Every unequal normalized vertex pair is separated in all three
relative slot phases. The checker retains both corners of a four-path.
The fixed first-kind split bounds the kernel's computation depth. -/
theorem certified_routes : ∀ (a b : Fin 8) (delta : Fin 5),
    (0,a) ≠ (delta,b) → ∀ s : Fin 3,
    diagram.routeCheck (routeCode a b delta s) 14
      ((0,a),0) ((delta,b),s) = true := by
  intro a
  fin_cases a
  · exact routes_kind_0
  · exact routes_kind_1
  · exact routes_kind_2
  · exact routes_kind_3
  · exact routes_kind_4
  · exact routes_kind_5
  · exact routes_kind_6
  · exact routes_kind_7


variable {V : Type*} {G : SimpleGraph V}
  (F : Realization diagram G)

/-- The same partial operation diagram realizes the actual graph after a
cyclic coordinate shift; no information about the shared dart is dropped. -/
def shiftedRealization (k : Fin 5) : Realization diagram G where
  vertex := F.vertex ∘ shift k
  dart := F.dart ∘ shiftSlot k
  fst := fun d => F.fst (shiftSlot k d)
  slots_injective := fun v => F.slots_injective (shift k v)
  slots_surjective := fun v d hd => F.slots_surjective (shift k v) d hd
  rotation := F.rotation
  rotate_eq := fun d => by
    change F.dart (shiftSlot k (diagram.rotate d)) = _
    rw [shift_rotate]
    exact F.rotate_eq (shiftSlot k d)
  flip_eq := fun d e he => by
    apply F.flip_eq (shiftSlot k d) (shiftSlot k e)
    rw [← shift_flip,he]
    rfl

theorem normalized_vertex_ne (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) (a b : Fin 8) (delta : Fin 5)
    (hne : (0,a) ≠ (delta,b)) : F.vertex (0,a) ≠ F.vertex (delta,b) := by
  intro he
  obtain ⟨s,hs⟩ := F.slots_surjective (delta,b) (F.dart ((0,a),0))
    ((F.fst _).trans he)
  exact F.routeCheck_sound ht hf (routeCode a b delta s) (certified_routes a b delta hne s) hs.symm

/-- No size, source minimality, final-port exposure or exterior hypothesis
is supplied to this geometric separation theorem. -/
theorem vertex_injective (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) : Function.Injective F.vertex := by
  intro u v he
  by_contra hn
  have hu : shift u.1 (0,u.2) = u := by simp [shift]
  have hv : shift u.1 (v.1-u.1,v.2) = v := by simp [shift]
  have hne : (0,u.2) ≠ (v.1-u.1,v.2) := by
    intro h
    apply hn
    simpa only [hu,hv] using congrArg (shift u.1) h
  apply normalized_vertex_ne (shiftedRealization F u.1) ht hf u.2 v.2 (v.1-u.1) hne
  change F.vertex (shift u.1 (0,u.2)) = F.vertex (shift u.1 (v.1-u.1,v.2))
  simpa only [hu,hv] using he

noncomputable section
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (rotation : SimpleGraphDartRotation.Data G) (root : G.Dart)

local instance capSeparationEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance capSeparationEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Local face lengths realize the entire diagram, and ambient girth
forces forty distinct actual vertices. No local embedding is assumed. -/
theorem actual_vertex_injective
    (hC : PhysicalForkCodeFaces.Cubic3 rotation.toRotationSystem)
    (hfaces : FaceTraversal.FaceLengths rotation.toRotationSystem 5 root)
    (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) :
    Function.Injective (FaceTraversal.vertex rotation.toRotationSystem 5 root) := by
  let F := PartialDiagram.realization 5 rotation root hC hfaces
  let F' : Realization diagram G := {
    vertex := F.vertex
    dart := F.dart
    fst := F.fst
    slots_injective := F.slots_injective
    slots_surjective := F.slots_surjective
    rotation := F.rotation
    rotate_eq := F.rotate_eq
    flip_eq := fun d e he => F.flip_eq d e ((flip_eq d).symm.trans he) }
  exact vertex_injective F' ht hf

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap.PentagonalSeparation
