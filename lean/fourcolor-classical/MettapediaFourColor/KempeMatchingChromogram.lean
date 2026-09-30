import MettapediaFourColor.KempeMatchingStack

/-!
# Exact translation of component matchings at arbitrary width

A noncrossing component matching retains which boundary changes must be made
together. Its chromogram records the same joint choices, including the parity
of the two endpoint colours. The difference of two matching traces selects a
union of complete components. The stack proof is uniform in the boundary size.
-/

namespace FourColor.KempeMatchingChromogram

open Color

abbrev Ports := Fin 6

variable {n : ℕ}

def Noncrossing (mate : Fin n → Fin n) : Prop :=
  ∀ i j, ¬ ((min i.val (mate i).val < min j.val (mate j).val ∧
    min j.val (mate j).val < max i.val (mate i).val ∧
    max i.val (mate i).val < max j.val (mate j).val) ∨
    (min j.val (mate j).val < min i.val (mate i).val ∧
    min i.val (mate i).val < max j.val (mate j).val ∧
    max j.val (mate j).val < max i.val (mate i).val))

instance (mate : Fin n → Fin n) : Decidable (Noncrossing mate) := by
  unfold Noncrossing
  infer_instance

def layout (mate : Fin n → Fin n) : List Slot :=
  List.ofFn fun i => if mate i = i then .fixed
    else if i < mate i then .opening else .closing

/-- All choices of the active colours, with inactive ports fixed to `c1`. -/
def word (mate : Fin n → Fin n) (bits : Fin n → Bool) : Fin n → Color :=
  fun i => if mate i = i then .c1 else if bits i then .c3 else .c2

def gram (mate : Fin n → Fin n) (c : Fin n → Color) : Chromogram :=
  List.ofFn fun i => if mate i = i then .skip else if i < mate i then .push
    else if c i = c (mate i) then .pop0 else .pop1

theorem shape_gram (mate : Fin n → Fin n) (c : Fin n → Color) :
    shape (gram mate c) = layout mate := by
  simp only [shape, gram, layout, List.map_ofFn]
  congr 1
  funext i
  by_cases h : mate i = i
  · simp [h]
  by_cases h' : i < mate i
  · simp [h, h']
  by_cases h'' : c i = c (mate i) <;> simp [h, h', h'']

/-- Extend a finite matching by fixed points beyond its boundary. -/
def liftMate (mate : Fin n → Fin n) (i : ℕ) : ℕ :=
  if hi : i < n then (mate ⟨i, hi⟩).val else i

def liftBits (bits : Fin n → Bool) (i : ℕ) : Bool :=
  if hi : i < n then bits ⟨i, hi⟩ else false

theorem liftMate_bound (mate : Fin n → Fin n) (i : ℕ) (hi : i < n) :
    liftMate mate i < n := by
  simp only [liftMate, dite_eq_left hi]
  exact (mate ⟨i, hi⟩).isLt

theorem liftMate_involutive (mate : Fin n → Fin n)
    (hinv : ∀ i, mate (mate i) = i) : Function.Involutive (liftMate mate) := by
  intro i
  by_cases hi : i < n
  · simp only [liftMate, dite_eq_left hi, dite_eq_left (mate ⟨i, hi⟩).isLt, Fin.eta,
      hinv ⟨i, hi⟩, Fin.val_mk]
  · simp only [liftMate, dite_eq_right hi]

theorem liftMate_noncrossing (mate : Fin n → Fin n) (hplanar : Noncrossing mate) :
    Mettapedia.GraphTheory.NoncrossingMatchingStack.Noncrossing (liftMate mate) := by
  intro a b hab hba hamb
  have ha : a < n := by
    by_contra ha
    simp only [liftMate, dite_eq_right ha] at hba
    omega
  have hb : b < n := lt_trans hba (liftMate_bound mate a ha)
  simp only [liftMate, dite_eq_left ha, dite_eq_left hb] at hba hamb
  have hfa : a ≤ (mate ⟨a, ha⟩).val := by omega
  have hfb : b ≤ (mate ⟨b, hb⟩).val := by omega
  apply hplanar ⟨a, ha⟩ ⟨b, hb⟩
  left
  simpa only [Fin.val_mk, min_eq_left hfa, max_eq_right hfa,
    min_eq_left hfb, max_eq_right hfb] using And.intro hab (And.intro hba hamb)

theorem read_word (mate : Fin n → Fin n) (bits : Fin n → Bool) :
    Stack.read (Stack.word (liftMate mate) (liftBits bits)) 0 n =
      List.ofFn (word mate bits) := by
  rw [Stack.read_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [Stack.word, word, liftMate, liftBits, Fin.ext_iff]

theorem read_gram (mate : Fin n → Fin n) (bits : Fin n → Bool) :
    Stack.read (Stack.symbol (liftMate mate) (Stack.word (liftMate mate) (liftBits bits)))
        0 n = gram mate (word mate bits) := by
  rw [Stack.read_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [Stack.symbol, Stack.word, word, liftMate, liftBits, Fin.ext_iff]

theorem read_layout (mate : Fin n → Fin n) :
    Stack.read (Stack.slot (liftMate mate)) 0 n = layout mate := by
  rw [Stack.read_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [Stack.slot, liftMate, Fin.ext_iff]

theorem read_bits (bits : Fin n → Bool) :
    Stack.read (liftBits bits) 0 n = List.ofFn bits := by
  rw [Stack.read_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [liftBits]

/-- One construction covers all finite widths, including the empty boundary.
Every accepted mask retains the original matching's shared choices. -/
theorem translation (mate : Fin n → Fin n)
    (hinv : ∀ i, mate (mate i) = i) (hplanar : Noncrossing mate)
    (bits : Fin n → Bool) :
    matchg [] (List.ofFn (word mate bits)) (gram mate (word mate bits)) ∧
      (paired [] (List.ofFn bits) (layout mate) → ∀ i, bits i = bits (mate i)) := by
  have hi := liftMate_involutive mate hinv
  have hn := liftMate_noncrossing mate hplanar
  refine ⟨?_, ?_⟩
  · simpa only [read_word, read_gram] using
      Stack.accepted hi hn (liftBits bits) n (liftMate_bound mate)
  · intro hp i
    have hm := Stack.mask_constant hi hn (liftBits bits) n (liftMate_bound mate)
      (by simpa only [read_bits, read_layout] using hp) i.val i.isLt
    simpa only [liftBits, liftMate, dite_eq_left i.isLt, Fin.eta,
      dite_eq_left (mate i).isLt] using hm

end FourColor.KempeMatchingChromogram
