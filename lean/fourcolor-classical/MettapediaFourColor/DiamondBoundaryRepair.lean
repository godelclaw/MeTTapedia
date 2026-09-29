import MettapediaFourColor.KempeAnswerComposition

/-!
# A joint boundary repair law for coupled diamond insertions

The law depends only on an eight-port boundary relation and twenty-three
terminal traces. Ten finite Kempe steps establish repair of all admissible
joint traces. The proof retains the coupling between the two insertions and
quantifies over every Kempe-closed exterior predicate. It imports no catalogue
configuration, colouring table, or configuration certificate.
-/

namespace FourColor.DiamondBoundaryRepair

open Color KempeAnswerComposition

/-- Read a colour digit from a compact byte string. -/
def colorAt (s : String) (i : ℕ) : Color :=
  match (s.toUTF8[i]?.getD 48).toNat with
  | 49 => c1 | 50 => c2 | 51 => c3 | _ => c0

def wordAt (s : String) (i : ℕ) : List Color :=
  (List.range 8).map fun j => colorAt s (9 * i + j)

/-- An eight-colour word; adjacent words are separated by one byte. -/
def decode (s : String) : List Color := wordAt s 0

def words (s : String) : List (List Color) :=
  (List.range ((s.toUTF8.size + 1) / 9)).map (wordAt s)

/-- Terminal traces whose actual colouring witnesses are supplied by a consumer. -/
def terminalCodes : String :=
  "11112233 11121112 11121121 11122212 11122221 11123321 \
  11211112 11211121 11211323 11212122 11212212 11212221 \
  11213312 11221133 11221212 11222233 11223311 11223333 \
  11232113 11232232 11233332 12131213 12321232"

/-- The eighteen colour-permutation classes of the coupled boundary condition. -/
def startCodes : String :=
  "11121112 11121121 11122212 11122221 11123312 11123321 \
  11211112 11211121 11212212 11212221 11213312 11213321 \
  11231123 11231132 11232223 11232232 11233323 11233332"

set_option maxRecDepth 32768 in
private theorem terminalCodes_eq : words terminalCodes = [
    decode "11112233", decode "11121112", decode "11121121", decode "11122212",
    decode "11122221", decode "11123321", decode "11211112", decode "11211121",
    decode "11211323", decode "11212122", decode "11212212", decode "11212221",
    decode "11213312", decode "11221133", decode "11221212", decode "11222233",
    decode "11223311", decode "11223333", decode "11232113", decode "11232232",
    decode "11233332", decode "12131213", decode "12321232"] := by
  decide +kernel

set_option maxRecDepth 32768 in
private theorem startCodes_eq : words startCodes = [
    decode "11121112", decode "11121121", decode "11122212", decode "11122221",
    decode "11123312", decode "11123321", decode "11211112", decode "11211121",
    decode "11212212", decode "11212221", decode "11213312", decode "11213321",
    decode "11231123", decode "11231132", decode "11232223", decode "11232232",
    decode "11233323", decode "11233332"] := by
  decide +kernel

variable {P : List Color → Prop}
variable (terminal : ∀ et ∈ words terminalCodes, P et)

include terminal

private theorem repair_11123312 : KempeCoclosure P (decode "11123312") := by
  apply kempeCoclosure_of_map .e231
  apply of_answers (words "22221133 22231132 22321123")
  · decide +kernel
  intro t ht
  change t ∈ [decode "22221133", decode "22231132", decode "22321123"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "11112233")
    exact of_mem (terminal (decode "11112233") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "11123321")
    exact of_mem (terminal (decode "11123321") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "11213312")
    exact of_mem (terminal (decode "11213312") (by rw [terminalCodes_eq]; decide +kernel))

private theorem repair_11213321 : KempeCoclosure P (decode "11213321") := by
  apply kempeCoclosure_of_map .e231
  apply of_answers (words "22231132 22321123 22331122")
  · decide +kernel
  intro t ht
  change t ∈ [decode "22231132", decode "22321123", decode "22331122"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "11123321")
    exact of_mem (terminal (decode "11123321") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "11213312")
    exact of_mem (terminal (decode "11213312") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "11223311")
    exact of_mem (terminal (decode "11223311") (by rw [terminalCodes_eq]; decide +kernel))

private theorem repair_11232223 : KempeCoclosure P (decode "11232223") := by
  apply kempeCoclosure_of_map .e123
  apply of_answers (words "11223333 11232232 11233332")
  · decide +kernel
  intro t ht
  change t ∈ [decode "11223333", decode "11232232", decode "11233332"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11223333")
    exact of_mem (terminal (decode "11223333") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11232232")
    exact of_mem (terminal (decode "11232232") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11233332")
    exact of_mem (terminal (decode "11233332") (by rw [terminalCodes_eq]; decide +kernel))

private theorem repair_11233323 : KempeCoclosure P (decode "11233323") := by
  apply kempeCoclosure_of_map .e123
  apply of_answers (words "11222233 11232232 11233332")
  · decide +kernel
  intro t ht
  change t ∈ [decode "11222233", decode "11232232", decode "11233332"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11222233")
    exact of_mem (terminal (decode "11222233") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11232232")
    exact of_mem (terminal (decode "11232232") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11233332")
    exact of_mem (terminal (decode "11233332") (by rw [terminalCodes_eq]; decide +kernel))

private theorem repair_11213123 : KempeCoclosure P (decode "11213123") := by
  apply kempeCoclosure_of_map .e213
  apply of_answers (words "22122313 23132313 22123312")
  · decide +kernel
  intro t ht
  change t ∈ [decode "22122313", decode "23132313", decode "22123312"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "11211323")
    exact of_mem (terminal (decode "11211323") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "12321232")
    exact of_mem (terminal (decode "12321232") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "11213321")
    exact repair_11213321 terminal

private theorem repair_11231213 : KempeCoclosure P (decode "11231213") := by
  apply kempeCoclosure_of_map .e231
  apply of_answers (words "22313221 23212321 22213321")
  · decide +kernel
  intro t ht
  change t ∈ [decode "22313221", decode "23212321", decode "22213321"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "11232113")
    exact of_mem (terminal (decode "11232113") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e312
    change KempeCoclosure P (decode "12131213")
    exact of_mem (terminal (decode "12131213") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "11123312")
    exact repair_11123312 terminal

private theorem repair_11213132 : KempeCoclosure P (decode "11213132") := by
  apply kempeCoclosure_of_map .e123
  apply of_answers (words "11212122 11213123")
  · decide +kernel
  intro t ht
  change t ∈ [decode "11212122", decode "11213123"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11212122")
    exact of_mem (terminal (decode "11212122") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11213123")
    exact repair_11213123 terminal

private theorem repair_11231312 : KempeCoclosure P (decode "11231312") := by
  apply kempeCoclosure_of_map .e123
  apply of_answers (words "11221212 11231213")
  · decide +kernel
  intro t ht
  change t ∈ [decode "11221212", decode "11231213"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11221212")
    exact of_mem (terminal (decode "11221212") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11231213")
    exact repair_11231213 terminal

private theorem repair_11231132 : KempeCoclosure P (decode "11231132") := by
  apply kempeCoclosure_of_map .e213
  apply of_answers (words "22133331 22123231 22132321")
  · decide +kernel
  intro t ht
  change t ∈ [decode "22133331", decode "22123231", decode "22132321"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "11233332")
    exact of_mem (terminal (decode "11233332") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "11213132")
    exact repair_11213132 terminal
  · apply kempeCoclosure_of_map .e213
    change KempeCoclosure P (decode "11231312")
    exact repair_11231312 terminal

private theorem repair_11231123 : KempeCoclosure P (decode "11231123") := by
  apply kempeCoclosure_of_map .e123
  apply of_answers (words "11221133 11231132")
  · decide +kernel
  intro t ht
  change t ∈ [decode "11221133", decode "11231132"] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11221133")
    exact of_mem (terminal (decode "11221133") (by rw [terminalCodes_eq]; decide +kernel))
  · apply kempeCoclosure_of_map .e123
    change KempeCoclosure P (decode "11231132")
    exact repair_11231132 terminal

set_option maxRecDepth 32768 in
theorem start_repair {et : List Color} (h : et ∈ words startCodes) :
    KempeCoclosure P et := by
  rw [startCodes_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_mem (terminal (decode "11121112") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11121121") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11122212") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11122221") (by rw [terminalCodes_eq]; decide +kernel))
  · exact repair_11123312 terminal
  · exact of_mem (terminal (decode "11123321") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11211112") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11211121") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11212212") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11212221") (by rw [terminalCodes_eq]; decide +kernel))
  · exact of_mem (terminal (decode "11213312") (by rw [terminalCodes_eq]; decide +kernel))
  · exact repair_11213321 terminal
  · exact repair_11231123 terminal
  · exact repair_11231132 terminal
  · exact repair_11232223 terminal
  · exact of_mem (terminal (decode "11232232") (by rw [terminalCodes_eq]; decide +kernel))
  · exact repair_11233323 terminal
  · exact of_mem (terminal (decode "11233332") (by rw [terminalCodes_eq]; decide +kernel))

omit terminal in
private theorem normalize_three : ∀ a b y : Color,
    a ≠ b → y ≠ a → y ≠ b →
    ∃ g : EdgePerm, g (a + b) = c1 ∧ g (a + y) = c2 := by
  decide +kernel

omit terminal in
set_option maxRecDepth 32768 in
private theorem normalize_remaining : ∀ x z w : Color,
    (x ≠ c0 ∧ z ≠ c1 ∧ w ≠ c0 ∧ w ≠ c1) →
    ∃ g : EdgePerm, (trace [c0, x, c0, c2, c1, z, c1, w]).map g ∈ words startCodes := by
  decide +kernel

omit terminal in
/-- Translate and permute three distinct colours; only three choices remain. -/
theorem normalize (a b x y z w : Color)
    (h : a ≠ b ∧ x ≠ a ∧ z ≠ b ∧ y ≠ a ∧ y ≠ b ∧ w ≠ a ∧ w ≠ b) :
    ∃ g : EdgePerm, (trace [a, x, a, y, b, z, b, w]).map g ∈ words startCodes := by
  obtain ⟨hab, hxa, hzb, hya, hyb, hwa, hwb⟩ := h
  obtain ⟨g, hb, hy⟩ := normalize_three a b y hab hya hyb
  let f : Color → Color := fun c => g (a + c)
  have hf : Function.Injective f := fun _ _ he => add_left_cancel (g.apply_injective he)
  have hfa : f a = c0 := by simp only [f, add_self, EdgePerm.apply_zero]; rfl
  have hfb : f b = c1 := hb
  have hfy : f y = c2 := hy
  have hx' : f x ≠ f a := fun he => hxa (hf he)
  have hz' : f z ≠ f b := fun he => hzb (hf he)
  have hwa' : f w ≠ f a := fun he => hwa (hf he)
  have hwb' : f w ≠ f b := fun he => hwb (hf he)
  obtain ⟨g', hg'⟩ := normalize_remaining (f x) (f z) (f w)
    ⟨hfa ▸ hx', hfb ▸ hz', hfa ▸ hwa', hfb ▸ hwb'⟩
  have ht : (trace [a, x, a, y, b, z, b, w]).map g =
      trace [c0, f x, c0, c2, c1, f z, c1, f w] := by
    calc
      _ = trace (([a, x, a, y, b, z, b, w].map (a + ·)).map g) := by
        rw [trace_map, trace_map_add]
      _ = trace [f a, f x, f a, f y, f b, f z, f b, f w] := rfl
      _ = _ := by rw [hfa, hfb, hfy]
  refine ⟨g' * g, ?_⟩
  rw [← map_map_edgePerm, ht]
  exact hg'

/-- One boundary law, for every admissible assignment and every exterior.
The consumer supplies actual colourings for the terminal patterns. -/
theorem repair (a b x y z w : Color)
    (h : a ≠ b ∧ x ≠ a ∧ z ≠ b ∧ y ≠ a ∧ y ≠ b ∧ w ≠ a ∧ w ≠ b) :
    KempeCoclosure P (trace [a, x, a, y, b, z, b, w]) := by
  obtain ⟨g, hg⟩ := normalize a b x y z w h
  exact kempeCoclosure_of_map g (start_repair terminal hg)

end FourColor.DiamondBoundaryRepair
