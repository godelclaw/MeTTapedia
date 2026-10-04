import MettapediaFourColor.StripParentFan
import MettapediaFourColor.KempeChordExchange

/-!
# Two successful source repairs through different parent interfaces

Each parent uses the uniform one-chord exchange law and two explicit source
colourings. Both repairs then pass through the same fan transport theorem.
These are two input classes against arbitrary Kempe-closed exteriors, not
complete parent or D0099 reducibility.
-/

namespace FourColor.StripParentFanExample

open Color KempeBoundarySplit KempeBoundaryFan StripParentFan BoundaryFanRepair

def parentWord : Bool → List Color
  | false => [c1,c2,c3,c1,c2,c1,c1,c1,c1,c2,c1]
  | true => [c3,c1,c1,c1,c2,c1,c1,c2,c1,c1,c2]

def childWord : Bool → List Color
  | false => [c2,c1,c3,c1,c2,c1,c1,c1,c1,c2,c1]
  | true => [c1,c3,c1,c1,c2,c1,c1,c2,c1,c1,c2]

def data : Bool → String
  | false => "010102320233211302010103231230213302"
  | true => "010132310122301223010123201023031221"

def colour (side : Bool) (i : Fin 2) (v : Fin 18) : Color :=
  ![c0,c1,c2,c3] ⟨((data side).toUTF8[18 * i.val + v.val]?.getD 48).toNat % 4,
    Nat.mod_lt _ (by decide)⟩

theorem proper : ∀ side i u v,
    (parent side).Adj u v → colour side i u ≠ colour side i v := by decide +kernel

def colouring (side : Bool) (i : Fin 2) : (parent side).Coloring Color :=
  .mk (colour side i) (fun h => proper side i _ _ h)

def anchor (side : Bool) : ℕ := if side then 0 else 4

theorem active : ∀ side, anchor side ≤ (parentWord side).length ∧
    (((parentWord side).rotate (anchor side)).headD 0).hi = true := by decide +kernel

theorem answer_witness : ∀ side,
    ∀ word ∈ KempeChordExchange.answers (parentWord side) (anchor side),
      ∃ i : Fin 2, word = trace
        ((oldPorts (left side) (middle side) (right side) (rest side)).map (colour side i)) := by
  decide +kernel

/-- No matching table: one uniform chord theorem supplies one of two witnesses. -/
theorem parent_repair (side : Bool) :
    KempeCoclosure (GraphTrace (parent side)
      (oldPorts (left side) (middle side) (right side) (rest side))) (parentWord side) := by
  intro outside closed start
  obtain ⟨_, gram, hm, all⟩ := closed _ start
  obtain ⟨word, member, hw⟩ := KempeChordExchange.answer_exists _ _ _
    (active side).1 (active side).2 hm
  obtain ⟨i, rfl⟩ := answer_witness side word member
  exact ⟨_, ⟨colouring side i, rfl⟩, all _ hw⟩

/-- The two graph decompositions consume genuine parent repairs and rebuild D0099. -/
theorem source_repair (side : Bool) :
    KempeCoclosure (GraphTrace TriangleStripAnchors.input0099.graph
      (TriangleStripAnchors.input0099.boundary.rotate (shift side))) (childWord side) := by
  cases side
  · exact StripParentFan.source_repair false [c3,c1,c2,c1,c1,c1,c1,c2,c1]
      (show Related c2 c1 c1 c2 from by decide) (parent_repair false)
  · exact StripParentFan.source_repair true [c1,c1,c2,c1,c1,c2,c1,c1,c2]
      (show Related c1 c3 c3 c1 from by decide) (parent_repair true)

end FourColor.StripParentFanExample
