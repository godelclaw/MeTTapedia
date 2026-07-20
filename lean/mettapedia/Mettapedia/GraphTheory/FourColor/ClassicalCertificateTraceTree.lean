import Mathlib.Tactic.FinCases
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceTree

/-- The three nonzero elements of the Tait color group, used as trace-tree
branch labels. -/
inductive TraceSymbol where
  | red
  | blue
  | purple
  deriving DecidableEq, Repr

instance : Fintype TraceSymbol where
  elems := {.red, .blue, .purple}
  complete := by
    intro symbol
    cases symbol <;> simp

namespace TraceSymbol

/-- Interpretation of a trace symbol in the existing `𝔽₂²` color algebra. -/
def toColor : TraceSymbol → Color
  | .red => FourColor.red
  | .blue => FourColor.blue
  | .purple => FourColor.purple

@[simp] theorem toColor_red : TraceSymbol.red.toColor = FourColor.red := rfl
@[simp] theorem toColor_blue : TraceSymbol.blue.toColor = FourColor.blue := rfl
@[simp] theorem toColor_purple :
    TraceSymbol.purple.toColor = FourColor.purple := rfl

theorem toColor_ne_zero (symbol : TraceSymbol) :
    symbol.toColor ≠ 0 := by
  cases symbol <;> simp [toColor]

theorem toColor_injective : Function.Injective toColor := by
  intro left right heq
  cases left <;> cases right
  · rfl
  · exact (FourColor.red_ne_blue heq).elim
  · exact (FourColor.red_ne_purple heq).elim
  · exact (FourColor.red_ne_blue heq.symm).elim
  · rfl
  · exact (FourColor.blue_ne_purple heq).elim
  · exact (FourColor.red_ne_purple heq.symm).elim
  · exact (FourColor.blue_ne_purple heq.symm).elim
  · rfl

/-- Every nonzero Tait color has a unique trace symbol. -/
theorem existsUnique_toColor_eq (color : Color) (hnonzero : color ≠ 0) :
    ∃! symbol : TraceSymbol, symbol.toColor = color := by
  rcases color with ⟨first, second⟩
  fin_cases first <;> fin_cases second
  · exact (hnonzero rfl).elim
  · refine ⟨TraceSymbol.blue, rfl, ?_⟩
    intro symbol heq
    exact toColor_injective heq
  · refine ⟨TraceSymbol.red, rfl, ?_⟩
    intro symbol heq
    exact toColor_injective heq
  · refine ⟨TraceSymbol.purple, rfl, ?_⟩
    intro symbol heq
    exact toColor_injective heq

theorem map_toColor_injective :
    Function.Injective (List.map toColor) := by
  intro left right heq
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at heq
      | cons otherHead otherTail =>
          simp only [List.map_cons, List.cons.injEq] at heq
          rw [toColor_injective heq.1, ih heq.2]

/-- A nonzero color word has a unique spelling over trace symbols. -/
theorem existsUnique_word_toColor_eq (colors : List Color)
    (hnonzero : ∀ color ∈ colors, color ≠ 0) :
    ∃! symbols : List TraceSymbol,
      symbols.map toColor = colors := by
  induction colors with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      intro symbols heq
      cases symbols <;> simp_all
  | cons color colors ih =>
      obtain ⟨symbol, hsymbol, hsymbolUnique⟩ :=
        existsUnique_toColor_eq color (hnonzero color (by simp))
      obtain ⟨symbols, hsymbols, hsymbolsUnique⟩ := ih (by
        intro other hmem
        exact hnonzero other (by simp [hmem]))
      refine ⟨symbol :: symbols, by simp [hsymbol, hsymbols], ?_⟩
      intro candidate hcand
      cases candidate with
      | nil => simp at hcand
      | cons candidateHead candidateTail =>
          simp only [List.map_cons, List.cons.injEq] at hcand
          rw [hsymbolUnique candidateHead hcand.1,
            hsymbolsUnique candidateTail hcand.2]

end TraceSymbol

/-- A compact ternary trie of normalized nonzero boundary-color words. -/
inductive TraceTree where
  | empty
  | leaf
  | node (red blue purple : TraceTree)
  deriving DecidableEq, Repr

namespace TraceTree

/-- Select the subtree indexed by a nonzero color. -/
def child : TraceTree → TraceSymbol → TraceTree
  | .node red _ _, .red => red
  | .node _ blue _, .blue => blue
  | .node _ _ purple, .purple => purple
  | _, _ => .empty

/-- Exact word-membership test. -/
def accepts : TraceTree → List TraceSymbol → Bool
  | .empty, _ => false
  | .leaf, [] => true
  | .leaf, _ :: _ => false
  | .node _ _ _, [] => false
  | tree@(.node _ _ _), symbol :: rest => tree.child symbol |>.accepts rest

/-- A singleton trace tree. -/
def singleton : List TraceSymbol → TraceTree
  | [] => .leaf
  | .red :: rest => .node (singleton rest) .empty .empty
  | .blue :: rest => .node .empty (singleton rest) .empty
  | .purple :: rest => .node .empty .empty (singleton rest)

theorem accepts_singleton_iff (target word : List TraceSymbol) :
    (singleton target).accepts word = true ↔ word = target := by
  induction target generalizing word with
  | nil =>
      cases word <;> simp [singleton, accepts]
  | cons symbol rest ih =>
      cases symbol <;> cases word with
      | nil => simp [singleton, accepts]
      | cons head tail =>
          cases head <;> simp [singleton, accepts, child, ih]

/-- Structural disjointness of two trace tries. -/
def disjoint : TraceTree → TraceTree → Bool
  | .leaf, .leaf => false
  | .node leftRed leftBlue leftPurple,
      .node rightRed rightBlue rightPurple =>
      disjoint leftRed rightRed && disjoint leftBlue rightBlue &&
        disjoint leftPurple rightPurple
  | _, _ => true

theorem disjoint_sound : ∀ (left right : TraceTree),
    left.disjoint right = true →
      ∀ word, ¬ (left.accepts word = true ∧ right.accepts word = true)
  | .empty, right, _, word => by simp [accepts]
  | .leaf, .empty, _, word => by simp [accepts]
  | .leaf, .leaf, hdisjoint, _ => by simp [disjoint] at hdisjoint
  | .leaf, .node _ _ _, _, word => by
      cases word <;> simp [accepts]
  | .node _ _ _, .empty, _, word => by simp [accepts]
  | .node _ _ _, .leaf, _, word => by
      cases word <;> simp [accepts]
  | .node leftRed leftBlue leftPurple,
      .node rightRed rightBlue rightPurple, hdisjoint, word => by
      simp only [disjoint, Bool.and_eq_true] at hdisjoint
      rcases hdisjoint with ⟨⟨hred, hblue⟩, hpurple⟩
      cases word with
      | nil => simp [accepts]
      | cons symbol rest =>
          cases symbol with
          | red =>
              simpa [accepts, child] using
                disjoint_sound leftRed rightRed hred rest
          | blue =>
              simpa [accepts, child] using
                disjoint_sound leftBlue rightBlue hblue rest
          | purple =>
              simpa [accepts, child] using
                disjoint_sound leftPurple rightPurple hpurple rest

theorem exists_common_word_of_disjoint_eq_false : ∀ (left right : TraceTree),
    left.disjoint right = false →
      ∃ word, left.accepts word = true ∧ right.accepts word = true
  | .empty, _, hdisjoint => by simp [disjoint] at hdisjoint
  | .leaf, .empty, hdisjoint => by simp [disjoint] at hdisjoint
  | .leaf, .leaf, _ => ⟨[], by simp [accepts]⟩
  | .leaf, .node _ _ _, hdisjoint => by simp [disjoint] at hdisjoint
  | .node _ _ _, .empty, hdisjoint => by simp [disjoint] at hdisjoint
  | .node _ _ _, .leaf, hdisjoint => by simp [disjoint] at hdisjoint
  | .node leftRed leftBlue leftPurple,
      .node rightRed rightBlue rightPurple, hdisjoint => by
      simp only [disjoint,
        Bool.and_eq_false_eq_eq_false_or_eq_false] at hdisjoint
      rcases hdisjoint with hfirst | hpurple
      · rcases hfirst with hred | hblue
        · obtain ⟨word, hleft, hright⟩ :=
            exists_common_word_of_disjoint_eq_false leftRed rightRed hred
          exact ⟨.red :: word, by simpa [accepts, child] using hleft,
            by simpa [accepts, child] using hright⟩
        · obtain ⟨word, hleft, hright⟩ :=
            exists_common_word_of_disjoint_eq_false leftBlue rightBlue hblue
          exact ⟨.blue :: word, by simpa [accepts, child] using hleft,
            by simpa [accepts, child] using hright⟩
      · obtain ⟨word, hleft, hright⟩ :=
          exists_common_word_of_disjoint_eq_false
            leftPurple rightPurple hpurple
        exact ⟨.purple :: word, by simpa [accepts, child] using hleft,
          by simpa [accepts, child] using hright⟩

/-- The structural test reflects exact disjointness of represented word sets. -/
theorem disjoint_eq_true_iff (left right : TraceTree) :
    left.disjoint right = true ↔
      ∀ word, ¬ (left.accepts word = true ∧ right.accepts word = true) := by
  constructor
  · exact left.disjoint_sound right
  · intro hsemantic
    cases hcheck : left.disjoint right with
    | true => rfl
    | false =>
        obtain ⟨word, hleft, hright⟩ :=
          exists_common_word_of_disjoint_eq_false left right hcheck
        exact (hsemantic word ⟨hleft, hright⟩).elim

/-- Semantic acceptance of a word in the existing four-color algebra. -/
def AcceptsColorWord (tree : TraceTree) (colors : List Color) : Prop :=
  ∃ symbols, symbols.map TraceSymbol.toColor = colors ∧
    tree.accepts symbols = true

theorem no_common_color_word_of_disjoint
    {left right : TraceTree} (hdisjoint : left.disjoint right = true)
    (colors : List Color) :
    ¬ (left.AcceptsColorWord colors ∧ right.AcceptsColorWord colors) := by
  rintro ⟨⟨leftWord, hleftColor, hleft⟩,
    ⟨rightWord, hrightColor, hright⟩⟩
  have hword : leftWord = rightWord :=
    TraceSymbol.map_toColor_injective
      (hleftColor.trans hrightColor.symm)
  subst rightWord
  exact left.disjoint_sound right hdisjoint leftWord ⟨hleft, hright⟩

end TraceTree

/-- A compact reducibility-overlap certificate.  Later layers construct the
first tree from contract colorings and the second from the Kempe co-closure. -/
structure DisjointTraceCertificate where
  contractTree : TraceTree
  kempeTree : TraceTree
  deriving DecidableEq, Repr

namespace DisjointTraceCertificate

def checker (certificate : DisjointTraceCertificate) : Bool :=
  certificate.contractTree.disjoint certificate.kempeTree

theorem no_common_trace_of_checker_true
    (certificate : DisjointTraceCertificate)
    (haccepted : certificate.checker = true) (word : List TraceSymbol) :
    ¬ (certificate.contractTree.accepts word = true ∧
      certificate.kempeTree.accepts word = true) :=
  (TraceTree.disjoint_eq_true_iff _ _).1 haccepted word

end DisjointTraceCertificate

end ClassicalCertificateTraceTree

end Mettapedia.GraphTheory.FourColor
