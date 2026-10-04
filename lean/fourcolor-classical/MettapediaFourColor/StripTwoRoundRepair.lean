import MettapediaFourColor.KempeFiniteDecoder
import MettapediaFourColor.StripMajorityRepair
import MettapediaFourColor.KempeChordExchange

/-!
# Two composed source repairs with one exterior retained

Five matching layouts give a bounded inverse bridge for the two existing
D0099 inputs. Their repairs then consume the uniform majority theorem in
any Kempe-closed exterior. A third input uses an anchor exchange followed,
only when necessary, by one of those majority repairs. Four additional
full colourings witness the direct first-step outcomes.

The composition uses the same exterior predicate throughout. No full-source
repair, geometric occurrence supply or strict graph reduction is claimed.
-/

namespace FourColor.StripTwoRoundRepair

open Color KempeMatchingChromogram KempeBoundarySplit

def mate : Fin 5 → Fin 11 → Fin 11 :=
  ![![0,1,2,5,4,3,7,6,9,8,10],
    ![0,1,2,5,4,3,9,8,7,6,10],
    ![0,1,2,7,4,6,5,3,9,8,10],
    ![0,1,2,9,4,6,5,8,7,3,10],
    ![0,1,2,9,4,8,7,6,5,3,10]]

theorem mates_valid : ∀ s j,
    Function.Involutive (mate j) ∧ Noncrossing (mate j) ∧
      ∀ i, mate j i = i ↔ StripIntervalRepair.word s i = c1 := by
  unfold Function.Involutive
  decide +kernel

theorem five_parses : ∀ s,
    (KempeFiniteDecoder.parses [] (List.ofFn (StripIntervalRepair.word s))).length = 5 := by
  decide +kernel

theorem decode_check : ∀ s, ∀ w ∈
    KempeFiniteDecoder.parses [] (List.ofFn (StripIntervalRepair.word s)),
      ∃ j : Fin 5, gram (mate j) (StripIntervalRepair.word s) = w := by
  decide +kernel

/-- An inverse for these two inputs, not for arbitrary chromograms. -/
theorem decode (s : Bool) (w : Chromogram)
    (hw : matchg [] (List.ofFn (StripIntervalRepair.word s)) w) :
    ∃ j : Fin 5, gram (mate j) (StripIntervalRepair.word s) = w :=
  decode_check s w ((KempeFiniteDecoder.mem_parses _ _ _).mpr hw)

abbrev Terminal := GraphTrace TriangleStripAnchors.input0099.graph
  TriangleStripAnchors.input0099.boundary

/-- The existing majority law now answers the chromogram chosen by any
Kempe-closed exterior; every output is an actual source colouring. -/
theorem majority_coclosure (s : Bool) :
    KempeCoclosure Terminal (List.ofFn (StripIntervalRepair.word s)) := by
  intro outside hout hold
  obtain ⟨_, w, hw, hall⟩ := hout _ hold
  obtain ⟨j, rfl⟩ := decode s w hw
  obtain ⟨hinv, hnc, hf⟩ := mates_valid s j
  obtain ⟨k, hk⟩ := StripMajorityRepair.source_repair s (mate j) hinv hnc hf
  exact ⟨_, ⟨k, rfl⟩, hall _ hk⟩

def input : List Color := [c1,c1,c1,c2,c1,c2,c3,c2,c1,c1,c1]

def data : String := "0132013023110321023010101302311032120301013230231132013020101320310223012213"

def colour (j : Fin 4) (v : Fin 19) : Color :=
  ![c0,c1,c2,c3] ⟨(data.toUTF8[19 * j.val + v.val]?.getD 48).toNat % 4,
    Nat.mod_lt _ (by decide)⟩

theorem proper : ∀ j u v, TriangleStripAnchors.input0099.graph.Adj u v →
    colour j u ≠ colour j v := by decide +kernel

def colouring (j : Fin 4) : TriangleStripAnchors.input0099.graph.Coloring Color :=
  .mk (colour j) (fun h => proper j _ _ h)

/-- Colour normalization changes no boundary positions. The sole indirect
outcome is exactly the previously certified second majority input. -/
theorem answers : ∀ t ∈ KempeChordExchange.answers (input.map EdgePerm.e321) 9,
    (∃ j : Fin 4, t.map EdgePerm.e321 =
      trace (TriangleStripAnchors.input0099.boundary.map (colour j))) ∨
    t.map EdgePerm.e321 = List.ofFn (StripIntervalRepair.word true) := by
  decide +kernel

/-- One anchor step, then at most one majority step, in the same exterior. -/
theorem source_repair : KempeCoclosure Terminal input := by
  intro outside hout hold
  have hnormal := (hout input hold).1 EdgePerm.e321
  obtain ⟨_, w, hw, hall⟩ := hout _ hnormal
  obtain ⟨t, ht, hm⟩ := KempeChordExchange.answer_exists
    (input.map EdgePerm.e321) 9 w (by decide) (by decide) hw
  have hback := (hout t (hall t hm)).1 EdgePerm.e321
  rcases answers t ht with ⟨j, hj⟩ | hj
  · exact ⟨_, ⟨colouring j, rfl⟩, hj ▸ hback⟩
  · exact majority_coclosure true outside hout (hj ▸ hback)

end FourColor.StripTwoRoundRepair
