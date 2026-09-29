import MettapediaFourColor.KempeAnswerComposition
import MettapediaFourColor.KempeBoundarySplit
import Mathlib.Tactic.FinCases

/-!
# Joint boundary repair for a pentagonal lobe patch

The literal triangulated disk has six boundary vertices and six interior
vertices. Its dual cubic patch consists of a pentagon and an eleven-edge
surrounding cycle. Twenty-two terminal trace representatives have explicit
colouring witnesses. Nine other representatives descend in two rounds using
the reference's proved chromogram-cover rule.

The theorem quantifies over every Kempe-closed exterior predicate. The finite
identification with an extracted lobe is checked separately by a program;
this file does not prove that geometric adapter, a strict closed-map reduction,
or coverage of arbitrary planar graphs. No catalogue certificate is imported.
-/

namespace FourColor.PentagonalLobePatch

open Color KempeAnswerComposition KempeBoundarySplit

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def readColor (s : String) (i : ℕ) : Color :=
  match (s.toUTF8[i]?.getD 48).toNat with
  | 49 => c1 | 50 => c2 | 51 => c3 | _ => c0

def decode (s : String) : List Color :=
  (List.range 6).map (readColor s)

def words (s : String) : List (List Color) :=
  (List.range ((s.toUTF8.size + 1) / 7)).map fun i =>
    (List.range 6).map fun j => readColor s (7 * i + j)

def terminalCodes : String :=
  "111122 111212 111221 112121 112211 112222 112233 121112 121211 121222 121332 122111 122212 122221 122313 122331 123123 123132 123213 123231 123312 123321"

def allCodes : String :=
  "111111 111122 111212 111221 112112 112121 112211 112222 112233 112323 112332 121112 121121 121211 121222 121233 121323 121332 122111 122122 122133 122212 122221 122313 122331 123123 123132 123213 123231 123312 123321"

private theorem terminals_eq : words terminalCodes = [
    decode "111122", decode "111212", decode "111221", decode "112121", decode "112211", decode "112222", decode "112233", decode "121112", decode "121211", decode "121222", decode "121332", decode "122111", decode "122212", decode "122221", decode "122313", decode "122331", decode "123123", decode "123132", decode "123213", decode "123231", decode "123312", decode "123321"] := by
  decide +kernel

private theorem allCodes_eq : words allCodes = [
    decode "111111", decode "111122", decode "111212", decode "111221", decode "112112", decode "112121", decode "112211", decode "112222", decode "112233", decode "112323", decode "112332", decode "121112", decode "121121", decode "121211", decode "121222", decode "121233", decode "121323", decode "121332", decode "122111", decode "122122", decode "122133", decode "122212", decode "122221", decode "122313", decode "122331", decode "123123", decode "123132", decode "123213", decode "123231", decode "123312", decode "123321"] := by
  decide +kernel

variable {P : List Color → Prop}
variable (terminal : ∀ et ∈ words terminalCodes, P et)

include terminal

private theorem repair_111111 : KempeCoclosure P (decode "111111") := by
  apply kempeCoclosure_of_map .e213
  apply of_answers (words "222233 222332 223322")
  · decide +kernel
  intro t ht
  change t ∈ [decode "222233", decode "222332", decode "223322"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "111122")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "111221")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "112211")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_112112 : KempeCoclosure P (decode "112112") := by
  apply kempeCoclosure_of_map .e231
  apply of_answers (words "222323 223333 223232")
  · decide +kernel
  intro t ht
  change t ∈ [decode "222323", decode "223333", decode "223232"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "111212")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "112222")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "112121")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_112323 : KempeCoclosure P (decode "112323") := by
  apply kempeCoclosure_of_map .e213
  apply of_answers (words "221212 231213")
  · decide +kernel
  intro t ht
  change t ∈ [decode "221212", decode "231213"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "112121")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "123132")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_112332 : KempeCoclosure P (decode "112332") := by
  apply kempeCoclosure_of_map .e231
  apply of_answers (words "222112 232113")
  · decide +kernel
  intro t ht
  change t ∈ [decode "222112", decode "232113"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "111221")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "121332")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_121121 : KempeCoclosure P (decode "121121") := by
  apply kempeCoclosure_of_map .e231
  apply of_answers (words "223232 233323 223322")
  · decide +kernel
  intro t ht
  change t ∈ [decode "223232", decode "233323", decode "223322"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "112121")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "122212")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "112211")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_121233 : KempeCoclosure P (decode "121233") := by
  apply kempeCoclosure_of_map .e213
  apply of_answers (words "212122 213123")
  · decide +kernel
  intro t ht
  change t ∈ [decode "212122", decode "213123"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "121211")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "123213")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_122122 : KempeCoclosure P (decode "122122") := by
  apply kempeCoclosure_of_map .e231
  apply of_answers (words "222233 232322 222323")
  · decide +kernel
  intro t ht
  change t ∈ [decode "222233", decode "232322", decode "222323"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "111122")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "121211")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "111212")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_122133 : KempeCoclosure P (decode "122133") := by
  apply kempeCoclosure_of_map .e213
  apply of_answers (words "211222 211323")
  · decide +kernel
  intro t ht
  change t ∈ [decode "211222", decode "211323"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "122111")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "122313")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

private theorem repair_121323 : KempeCoclosure P (decode "121323") := by
  apply kempeCoclosure_of_map .e123
  apply of_answers (words "121233 121332")
  · decide +kernel
  intro t ht
  change t ∈ [decode "121233", decode "121332"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "121233")
    exact repair_121233 terminal
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "121332")
    exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

theorem represented_repair (et : List Color) (h : et ∈ words allCodes) :
    KempeCoclosure P et := by
  rw [allCodes_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact repair_111111 terminal
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact repair_112112 terminal
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact repair_112323 terminal
  · exact repair_112332 terminal
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact repair_121121 terminal
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact repair_121233 terminal
  · exact repair_121323 terminal
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact repair_122122 terminal
  · exact repair_122133 terminal
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))
  · exact of_mem (terminal _ (by rw [terminals_eq]; decide +kernel))

omit terminal in
private theorem normalize : ∀ a b c d e f : Color,
    (0 : Color) ∉ [a,b,c,d,e,f] → [a,b,c,d,e,f].sum = 0 →
      ∃ g : EdgePerm, [a,b,c,d,e,f].map g ∈ words allCodes := by
  decide +kernel

/-- A single repair argument for all proper six-port inputs and closed exteriors. -/
theorem boundary_repair : Repairs P 6 := by
  intro et hlen hzero hsum

  rcases et with _ | ⟨a, et⟩
  · simp at hlen

  rcases et with _ | ⟨b, et⟩
  · simp at hlen

  rcases et with _ | ⟨c, et⟩
  · simp at hlen

  rcases et with _ | ⟨d, et⟩
  · simp at hlen

  rcases et with _ | ⟨e, et⟩
  · simp at hlen

  rcases et with _ | ⟨f, et⟩
  · simp at hlen

  have ht : et = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
  subst et
  obtain ⟨g, hg⟩ := normalize a b c d e f hzero hsum
  exact kempeCoclosure_of_map g (represented_repair terminal _ hg)

omit terminal

/-- Adjacency of the actual twelve-vertex disk, in row-major order. -/

def adjacency : String :=
  "010001000010101000010010010100110000001010100100000101000101100010000011001100011100011000101010000000110111000110101001110001011001000011001110"

def graph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel fun u v =>
    (adjacency.toUTF8[12 * u.val + v.val]?.getD 48) = 49

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def boundary : List (Fin 12) := [0,1,2,3,4,5]

def colouringCodes : String :=
  "010102320231 010132320231 010131321032 010231320132 010201120332 010202120331 010203130321 013232102031 013201021332 013202102331 013212021330 013101021332 013132021230 013131021230 013123201320 013121021330 013013103220 013012102330 013023201320 013021102330 013032120231 013031103220"

def assignment (i : Fin 22) (v : Fin 12) : Color :=
  readColor colouringCodes (13 * i.val + v.val)

private theorem assignment_valid : ∀ i : Fin 22, ∀ u v,
    graph.Adj u v → assignment i u ≠ assignment i v := by
  decide +kernel

def colouring (i : Fin 22) : graph.Coloring Color :=
  SimpleGraph.Coloring.mk (assignment i) (fun {_ _} h => assignment_valid i _ _ h)

private theorem terminal_witness : ∀ et ∈ words terminalCodes,
    ∃ i : Fin 22, et = trace (boundary.map (assignment i)) := by
  decide +kernel

/-- Every terminal answer has a genuine colouring of the literal graph. -/
theorem terminal_supported : ∀ et ∈ words terminalCodes,
    GraphTrace graph boundary et := by
  intro et ht
  obtain ⟨i, hi⟩ := terminal_witness et ht
  exact ⟨colouring i, hi⟩

/-- Repair ends in an actual graph-colouring witness, preserving the exterior
predicate on the entire boundary word. -/
theorem repair : Repairs (GraphTrace graph boundary) 6 :=
  boundary_repair terminal_supported

/-- Exact shared-boundary conclusion, with the chosen colouring retained. -/
theorem compatible_colouring {Q : List Color → Prop} (hQ : KempeClosed Q)
    (et : List Color) (hlen : et.length = 6) (hzero : (0 : Color) ∉ et)
    (hsum : et.sum = 0) (hold : Q et) :
    ∃ k : graph.Coloring Color, Q (trace (boundary.map k)) := by
  obtain ⟨es, ⟨k, rfl⟩, hk⟩ := repair et hlen hzero hsum Q hQ hold
  exact ⟨k, hk⟩

end FourColor.PentagonalLobePatch
