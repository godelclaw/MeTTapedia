import Mettapedia.OSLF.MeTTaIL.Orientation
import Mathlib.GroupTheory.CoprodI
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Data words with variables, and their normal form

A datum of an oriented language is a word over literals and data variables: `g`, `δ`, `w · w'`,
`w⁻¹`. Two open words are equal when the group laws and the multiplication of the data group `G`
make them equal, which is equality in the free product `G ∗ F(V)` of `G` with the free group on the
variables (Meredith, "Group-valued data, a chaos constant, and an equivariant COMM", §6, the cost of
the word problem). With the data group computable, that equality is decided by a normal form:
constants between variables multiplied out, adjacent powers of one variable merged, trivial letters
dropped.

- `letters`: a data word as a list of letters, a constant of `G` or a power `δ^n`;
- `reduce`: the reduced list; `reduce_reduced` and `eval_reduce`: it is reduced and denotes the same
  element of `G ∗ F(V)`;
- `reduce_eq_iff`: two letter lists reduce alike exactly when they denote the same element, by the
  uniqueness of reduced words in a free product (`Monoid.CoprodI.Word.equiv`);
- `wordNormal`: a data word written in normal form; `wordNormal_eq_iff`: two words have the same
  normal form exactly when they are equal in `G ∗ F(V)`; `wordNormal_closed`: on a word without
  variables it is the canonical word of the element it reads.

The free product is the intended equality, not equality under every value of the variables: in an
abelian `G` the words `g · δ` and `δ · g` agree for every value of `δ` and are still different words
of `G ∗ F(V)`, as the group laws alone do not commute a variable past a literal.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

/-- A data variable: a bound one, by its index, or a free one, by its name. -/
inductive DataVar where
  | bound (index : Nat)
  | free (name : String)
  deriving DecidableEq, Repr

/-- The summands of the free product `G ∗ F(V)`: the data group at `none`, and one infinite cyclic
group for each variable. -/
def Summand (G : Type) : Option DataVar → Type
  | none => G
  | some _ => Multiplicative ℤ

instance summandGroup (G : Type) [Group G] : (i : Option DataVar) → Group (Summand G i)
  | none => (inferInstance : Group G)
  | some _ => (inferInstance : Group (Multiplicative ℤ))

instance summandDecidableEq (G : Type) [DecidableEq G] : (i : Option DataVar) → DecidableEq (Summand G i)
  | none => (inferInstance : DecidableEq G)
  | some _ => (inferInstance : DecidableEq (Multiplicative ℤ))

/-- The free product of the data group with the free group on the data variables. -/
abbrev FreeData (G : Type) [Group G] := Monoid.CoprodI (Summand G)

variable {G : Type} [Group G] [DecidableEq G]

/-! ## Letters -/

/-- A letter of a data word: an element of the data group, or a power of a variable. -/
inductive Letter (G : Type) where
  | const (g : G)
  | power (var : DataVar) (exponent : ℤ)

namespace Letter

/-- The summand a letter belongs to. -/
def index : Letter G → Option DataVar
  | .const _ => none
  | .power var _ => some var

/-- A letter as an element of its summand. -/
def sigma : Letter G → Σ i, Summand G i
  | .const g => ⟨none, g⟩
  | .power var exponent => ⟨some var, Multiplicative.ofAdd exponent⟩

/-- The element of the free product a letter denotes. -/
def eval (letter : Letter G) : FreeData G := Monoid.CoprodI.of letter.sigma.2

/-- A trivial letter: the unit, or a zeroth power. -/
def isOne : Letter G → Bool
  | .const g => decide (g = 1)
  | .power _ exponent => decide (exponent = 0)

/-- The inverse letter. -/
def inv : Letter G → Letter G
  | .const g => .const g⁻¹
  | .power var exponent => .power var (-exponent)

omit [Group G] [DecidableEq G] in
theorem sigma_fst (letter : Letter G) : letter.sigma.1 = letter.index := by
  cases letter <;> rfl

omit [DecidableEq G] in
theorem eval_inv (letter : Letter G) : letter.inv.eval = letter.eval⁻¹ := by
  cases letter with
  | const g => exact (map_inv (Monoid.CoprodI.of (M := Summand G) (i := none)) g)
  | power var exponent =>
    exact (map_inv (Monoid.CoprodI.of (M := Summand G) (i := some var)) (Multiplicative.ofAdd exponent))

theorem eval_one {letter : Letter G} (trivial : letter.isOne = true) : letter.eval = 1 := by
  cases letter with
  | const g =>
    have : g = 1 := by simpa [isOne] using trivial
    subst this
    exact map_one (Monoid.CoprodI.of (M := Summand G) (i := none))
  | power var exponent =>
    have : exponent = 0 := by simpa [isOne] using trivial
    subst this
    exact map_one (Monoid.CoprodI.of (M := Summand G) (i := some var))

theorem sigma_ne_one {letter : Letter G} (notTrivial : letter.isOne = false) : letter.sigma.2 ≠ 1 := by
  cases letter with
  | const g =>
    have nontrivial : ¬ g = 1 := by simpa [isOne] using notTrivial
    exact nontrivial
  | power var exponent =>
    simp only [isOne, decide_eq_false_iff_not] at notTrivial
    simp only [sigma]
    intro equal
    exact notTrivial (ofAdd_eq_one.mp equal)

omit [Group G] [DecidableEq G] in
theorem sigma_injective : Function.Injective (sigma : Letter G → Σ i, Summand G i) := by
  intro first second same
  cases first with
  | const g =>
    cases second with
    | const h => exact congrArg Letter.const (eq_of_heq (Sigma.mk.inj same).2)
    | power w m => exact absurd (Sigma.mk.inj same).1 (by simp)
  | power v n =>
    cases second with
    | const h => exact absurd (Sigma.mk.inj same).1 (by simp)
    | power w m =>
      obtain ⟨index, value⟩ := Sigma.mk.inj same
      obtain rfl : v = w := Option.some.inj index
      exact congrArg (Letter.power v) (Multiplicative.ofAdd.injective (eq_of_heq value))

end Letter

/-- The element of the free product a list of letters denotes. -/
def evalLetters (letters : List (Letter G)) : FreeData G := (letters.map Letter.eval).prod

omit [DecidableEq G] in
@[simp] theorem evalLetters_nil : evalLetters ([] : List (Letter G)) = 1 := rfl

omit [DecidableEq G] in
@[simp] theorem evalLetters_cons (letter : Letter G) (letters : List (Letter G)) :
    evalLetters (letter :: letters) = letter.eval * evalLetters letters := by
  simp [evalLetters]

omit [DecidableEq G] in
theorem evalLetters_append (left right : List (Letter G)) :
    evalLetters (left ++ right) = evalLetters left * evalLetters right := by
  simp [evalLetters]

/-- The inverse of a list of letters: inverse letters in reverse order. -/
def invertLetters (letters : List (Letter G)) : List (Letter G) := (letters.map Letter.inv).reverse

omit [DecidableEq G] in
theorem evalLetters_invert (letters : List (Letter G)) :
    evalLetters (invertLetters letters) = (evalLetters letters)⁻¹ := by
  induction letters with
  | nil => simp [invertLetters]
  | cons letter rest ih =>
    simp only [invertLetters, List.map_cons, List.reverse_cons] at ih ⊢
    rw [evalLetters_append, ih]
    simp only [evalLetters_cons, evalLetters_nil, mul_one, Letter.eval_inv, mul_inv_rev]

/-! ## Reduction -/

/-- Put a nontrivial letter in front of a reduced list, merging it with a first letter of the same
summand. -/
def merge : Letter G → List (Letter G) → List (Letter G)
  | .const g, .const h :: rest => if g * h = 1 then rest else .const (g * h) :: rest
  | .power v n, .power w m :: rest =>
      if v = w then (if n + m = 0 then rest else .power v (n + m) :: rest) else .power v n :: .power w m :: rest
  | letter, rest => letter :: rest

/-- Put a letter in front of a reduced list. -/
def push (letter : Letter G) (rest : List (Letter G)) : List (Letter G) :=
  if letter.isOne then rest else merge letter rest

/-- **The reduced list of letters.** -/
def reduce (letters : List (Letter G)) : List (Letter G) := letters.foldr push []

/-- A reduced list: no trivial letter, and no two adjacent letters of one summand. -/
def Reduced (letters : List (Letter G)) : Prop :=
  (∀ letter ∈ letters, letter.isOne = false) ∧ letters.IsChain fun a b => a.index ≠ b.index

theorem Reduced.tail {letter : Letter G} {rest : List (Letter G)} (reduced : Reduced (letter :: rest)) :
    Reduced rest :=
  ⟨fun other member => reduced.1 other (List.mem_cons_of_mem _ member), reduced.2.tail⟩

theorem Reduced.cons {letter : Letter G} {rest : List (Letter G)} (reduced : Reduced rest)
    (notTrivial : letter.isOne = false) (differs : ∀ first ∈ rest.head?, letter.index ≠ first.index) :
    Reduced (letter :: rest) := by
  refine ⟨fun other member => ?_, ?_⟩
  · rcases List.mem_cons.mp member with rfl | inside
    · exact notTrivial
    · exact reduced.1 other inside
  · cases rest with
    | nil => exact List.isChain_singleton _
    | cons first others => exact List.isChain_cons_cons.mpr ⟨differs first rfl, reduced.2⟩

theorem eval_merge (letter : Letter G) (rest : List (Letter G)) :
    evalLetters (merge letter rest) = letter.eval * evalLetters rest := by
  match letter, rest with
  | .const g, .const h :: rest =>
    have product : (Letter.const g).eval * (Letter.const h).eval = (Letter.const (g * h)).eval :=
      (map_mul (Monoid.CoprodI.of (M := Summand G) (i := none)) g h).symm
    simp only [merge]
    split
    · rename_i trivial
      rw [evalLetters_cons, ← mul_assoc, product, trivial]
      rw [show (Letter.const (1 : G)).eval = 1 from map_one (Monoid.CoprodI.of (M := Summand G) (i := none)),
        one_mul]
    · rw [evalLetters_cons, evalLetters_cons, ← mul_assoc, product]
  | .power v n, .power w m :: rest =>
    simp only [merge]
    split
    · rename_i same
      subst same
      have product : (Letter.power v n : Letter G).eval * (Letter.power v m).eval = (Letter.power v (n + m)).eval := by
        have key := map_mul (Monoid.CoprodI.of (M := Summand G) (i := some v))
          (show Summand G (some v) from Multiplicative.ofAdd n) (show Summand G (some v) from Multiplicative.ofAdd m)
        exact key.symm.trans rfl
      split
      · rename_i trivial
        rw [evalLetters_cons, ← mul_assoc, product, trivial]
        rw [show (Letter.power v (0 : ℤ) : Letter G).eval = 1 from
          map_one (Monoid.CoprodI.of (M := Summand G) (i := some v)), one_mul]
      · rw [evalLetters_cons, evalLetters_cons, ← mul_assoc, product]
    · rfl
  | .const g, [] => rfl
  | .const g, .power w m :: rest => rfl
  | .power v n, [] => rfl
  | .power v n, .const h :: rest => rfl

theorem eval_push (letter : Letter G) (rest : List (Letter G)) :
    evalLetters (push letter rest) = letter.eval * evalLetters rest := by
  unfold push
  split
  · rename_i trivial
    rw [Letter.eval_one trivial, one_mul]
  · exact eval_merge letter rest

theorem merge_reduced {letter : Letter G} {rest : List (Letter G)} (notTrivial : letter.isOne = false)
    (reduced : Reduced rest) : Reduced (merge letter rest) := by
  match letter, rest, reduced with
  | .const g, .const h :: rest, reduced =>
    simp only [merge]
    split
    · exact reduced.tail
    · rename_i nontrivial
      refine reduced.tail.cons (by simpa [Letter.isOne] using nontrivial) fun first member => ?_
      have chain := reduced.2
      cases rest with
      | nil => cases member
      | cons second others =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at member
        subst member
        have adjacent := List.rel_of_isChain_cons_cons chain
        exact adjacent
  | .power v n, .power w m :: rest, reduced =>
    simp only [merge]
    split
    · rename_i same
      split
      · exact reduced.tail
      · rename_i nontrivial
        refine reduced.tail.cons (by simpa [Letter.isOne] using nontrivial) fun first member => ?_
        have chain := reduced.2
        cases rest with
        | nil => cases member
        | cons second others =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at member
          subst member
          subst same
          have adjacent := List.rel_of_isChain_cons_cons chain
          exact adjacent
    · rename_i differs
      exact reduced.cons notTrivial fun first member => by
        cases member
        simpa [Letter.index] using differs
  | .const g, [], reduced => exact reduced.cons notTrivial fun first member => by cases member
  | .const g, .power w m :: rest, reduced =>
    exact reduced.cons notTrivial fun first member => by cases member; simp [Letter.index]
  | .power v n, [], reduced => exact reduced.cons notTrivial fun first member => by cases member
  | .power v n, .const h :: rest, reduced =>
    exact reduced.cons notTrivial fun first member => by cases member; simp [Letter.index]

theorem push_reduced (letter : Letter G) {rest : List (Letter G)} (reduced : Reduced rest) :
    Reduced (push letter rest) := by
  unfold push
  split
  · exact reduced
  · rename_i notTrivial
    exact merge_reduced (by simpa using notTrivial) reduced

theorem reduce_reduced (letters : List (Letter G)) : Reduced (reduce letters) := by
  induction letters with
  | nil => exact ⟨fun _ member => (by cases member), List.isChain_nil⟩
  | cons letter rest ih => exact push_reduced letter ih

theorem eval_reduce (letters : List (Letter G)) : evalLetters (reduce letters) = evalLetters letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
    simp only [reduce, List.foldr_cons] at ih ⊢
    rw [eval_push, ih, evalLetters_cons]

/-- A reduced list is its own reduction. -/
theorem reduce_of_reduced : ∀ {letters : List (Letter G)}, Reduced letters → reduce letters = letters
  | [], _ => rfl
  | letter :: rest, reduced => by
    have tail := reduce_of_reduced reduced.tail
    simp only [reduce, List.foldr_cons] at tail ⊢
    rw [tail]
    unfold push
    rw [if_neg (by simp [reduced.1 letter List.mem_cons_self])]
    have chain := reduced.2
    match letter, rest, chain with
    | .const g, [], _ => rfl
    | .const g, .const h :: _, chain => exact absurd rfl (List.rel_of_isChain_cons_cons chain)
    | .const g, .power w m :: _, _ => rfl
    | .power v n, [], _ => rfl
    | .power v n, .const h :: _, _ => rfl
    | .power v n, .power w m :: _, chain =>
      have differs : v ≠ w := by simpa [Letter.index] using List.rel_of_isChain_cons_cons chain
      simp [merge, differs]

/-! ## Uniqueness, from the reduced words of a free product -/

/-- A reduced list as a reduced word of the free product. -/
def toWord (letters : List (Letter G)) (reduced : Reduced letters) : Monoid.CoprodI.Word (Summand G) where
  toList := letters.map Letter.sigma
  ne_one := by
    intro entry member
    obtain ⟨letter, inside, rfl⟩ := List.mem_map.mp member
    exact Letter.sigma_ne_one (reduced.1 letter inside)
  chain_ne := by
    refine (List.isChain_map Letter.sigma).mpr ?_
    refine reduced.2.imp fun a b differs => ?_
    rwa [Letter.sigma_fst, Letter.sigma_fst]

theorem prod_toWord (letters : List (Letter G)) (reduced : Reduced letters) :
    (toWord letters reduced).prod = evalLetters letters := by
  simp only [Monoid.CoprodI.Word.prod, toWord, List.map_map, evalLetters]
  rfl

/-- **Two reduced lists denoting the same element are equal.** -/
theorem eq_of_reduced {first second : List (Letter G)} (firstReduced : Reduced first) (secondReduced : Reduced second)
    (same : evalLetters first = evalLetters second) : first = second := by
  have words : toWord first firstReduced = toWord second secondReduced := by
    apply Monoid.CoprodI.Word.equiv.symm.injective
    change (toWord first firstReduced).prod = (toWord second secondReduced).prod
    rw [prod_toWord, prod_toWord, same]
  have lists := congrArg Monoid.CoprodI.Word.toList words
  exact (List.map_injective_iff.mpr Letter.sigma_injective) lists

/-- **Two letter lists reduce alike exactly when they denote the same element of `G ∗ F(V)`.** -/
theorem reduce_eq_iff (first second : List (Letter G)) :
    reduce first = reduce second ↔ evalLetters first = evalLetters second := by
  constructor
  · intro same
    rw [← eval_reduce first, ← eval_reduce second, same]
  · intro same
    apply eq_of_reduced (reduce_reduced first) (reduce_reduced second)
    rw [eval_reduce, eval_reduce, same]

/-! ## Data words -/

variable (decl : OrientationDecl)

/-- **A data word as letters**: the unit, inverses and products of the declaration, the constants
the reading knows, and variables. Anything else is not a data word. -/
def letters (constant : String → Option G) : Pattern → Option (List (Letter G))
  | .bvar index => some [.power (.bound index) 1]
  | .fvar name => some [.power (.free name) 1]
  | .apply label [] => if label = decl.unit then some [] else (constant label).map fun g => [.const g]
  | .apply label [argument] =>
      if label = decl.inverse then (letters constant argument).map invertLetters else none
  | .apply label [left, right] =>
      if label = decl.multiply then
        match letters constant left, letters constant right with
        | some x, some y => some (x ++ y)
        | _, _ => none
      else none
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- A power of a variable as a word. -/
def powerWord (var : Pattern) : Nat → Pattern
  | 0 => .apply decl.unit []
  | 1 => var
  | n + 2 => .apply decl.multiply [var, powerWord var (n + 1)]

/-- A variable as a pattern. -/
def DataVar.pattern : DataVar → Pattern
  | .bound index => .bvar index
  | .free name => .fvar name

variable (reading : DataReading decl G)

/-- A letter as a word. -/
def Letter.render : Letter G → Pattern
  | .const g => reading.write g
  | .power var (.ofNat n) => powerWord decl var.pattern n
  | .power var (.negSucc n) => .apply decl.inverse [powerWord decl var.pattern (n + 1)]

/-- A list of letters as a right-nested product; the empty list is the unit's canonical word. -/
def renderWord : List (Letter G) → Pattern
  | [] => reading.write 1
  | [letter] => letter.render decl reading
  | letter :: rest => .apply decl.multiply [letter.render decl reading, renderWord rest]

/-- **A data word in normal form**: its letters reduced and written out; anything that is not a
data word is left as it is. -/
def wordNormal (datum : Pattern) : Pattern :=
  match letters decl reading.constant datum with
  | some found => renderWord decl reading (reduce found)
  | none => datum


/-! ## Correctness of the normal form -/

variable {decl reading}

/-- The element of the free product a constant of the data group denotes. -/
abbrev constEval (x : G) : FreeData G := Monoid.CoprodI.of (M := Summand G) (i := none) x

/-- The element of the free product a power of a variable denotes. -/
abbrev powerEval (v : DataVar) (n : ℤ) : FreeData G :=
  Monoid.CoprodI.of (M := Summand G) (i := some v) (Multiplicative.ofAdd n)

omit [DecidableEq G] in
theorem constEval_mul (x y : G) : constEval (x * y) = constEval x * constEval y :=
  map_mul (Monoid.CoprodI.of (M := Summand G) (i := none)) x y

omit [DecidableEq G] in
theorem powerEval_add (v : DataVar) (n m : ℤ) : powerEval (G := G) v (n + m) = powerEval v n * powerEval v m :=
  map_mul (Monoid.CoprodI.of (M := Summand G) (i := some v)) (Multiplicative.ofAdd n) (Multiplicative.ofAdd m)

omit [DecidableEq G] in
theorem powerEval_neg (v : DataVar) (n : ℤ) : powerEval (G := G) v (-n) = (powerEval v n)⁻¹ :=
  map_inv (Monoid.CoprodI.of (M := Summand G) (i := some v)) (Multiplicative.ofAdd n)

omit [DecidableEq G] in
theorem powerEval_zero (v : DataVar) : powerEval (G := G) v 0 = 1 :=
  map_one (Monoid.CoprodI.of (M := Summand G) (i := some v))

omit [DecidableEq G] in
/-- **A word the reading reads has letters denoting what it reads.** -/
theorem letters_of_read (constant : String → Option G) : ∀ (datum : Pattern) {x : G},
    read decl constant datum = some x →
      ∃ found, letters decl constant datum = some found ∧ evalLetters found = constEval x
  | .apply label [], x, readOk => by
    rw [read] at readOk
    rw [letters]
    by_cases unit : label = decl.unit
    · rw [if_pos unit] at readOk ⊢
      cases readOk
      exact ⟨[], rfl, (map_one (Monoid.CoprodI.of (M := Summand G) (i := none))).symm⟩
    · rw [if_neg unit] at readOk ⊢
      rw [readOk]
      exact ⟨[.const x], rfl, by
        simp only [evalLetters, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; rfl⟩
  | .apply label [argument], x, readOk => by
    rw [read] at readOk
    rw [letters]
    by_cases inverse : label = decl.inverse
    · rw [if_pos inverse] at readOk ⊢
      obtain ⟨y, inner, rfl⟩ := Option.map_eq_some_iff.mp readOk
      obtain ⟨found, parsed, value⟩ := letters_of_read constant argument inner
      refine ⟨invertLetters found, by rw [parsed]; rfl, ?_⟩
      rw [evalLetters_invert, value]
      exact (map_inv (Monoid.CoprodI.of (M := Summand G) (i := none)) y).symm
    · rw [if_neg inverse] at readOk
      cases readOk
  | .apply label [left, right], x, readOk => by
    rw [read] at readOk
    rw [letters]
    by_cases multiply : label = decl.multiply
    · rw [if_pos multiply] at readOk ⊢
      split at readOk
      · rename_i y z leftRead rightRead
        cases readOk
        obtain ⟨leftFound, leftParsed, leftValue⟩ := letters_of_read constant left leftRead
        obtain ⟨rightFound, rightParsed, rightValue⟩ := letters_of_read constant right rightRead
        refine ⟨leftFound ++ rightFound, by rw [leftParsed, rightParsed], ?_⟩
        rw [evalLetters_append, leftValue, rightValue, constEval_mul]
      · cases readOk
    · rw [if_neg multiply] at readOk
      cases readOk
  | .apply label (first :: second :: third :: rest), x, readOk => by simp [read] at readOk
  | .bvar index, x, readOk => by simp [read] at readOk
  | .fvar name, x, readOk => by simp [read] at readOk
  | .lambda binder body, x, readOk => by simp [read] at readOk
  | .multiLambda arity binders body, x, readOk => by simp [read] at readOk
  | .subst body replacement, x, readOk => by simp [read] at readOk
  | .collection kind elements rest, x, readOk => by simp [read] at readOk
termination_by datum => sizeOf datum
decreasing_by all_goals sizeOf_pattern_dec

omit [DecidableEq G] in
theorem letters_powerWord (v : DataVar) : ∀ n : Nat,
    ∃ found, letters decl reading.constant (powerWord decl v.pattern n) = some found ∧
      evalLetters found = powerEval v n
  | 0 => ⟨[], by simp [powerWord, letters], (powerEval_zero v).symm⟩
  | 1 => ⟨[.power v 1], by cases v <;> simp [powerWord, letters, DataVar.pattern],
      by simp only [evalLetters, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; rfl⟩
  | n + 2 => by
    obtain ⟨found, parsed, value⟩ := letters_powerWord v (n + 1)
    refine ⟨.power v 1 :: found, ?_, ?_⟩
    · rw [powerWord, letters, if_pos rfl, parsed]
      cases v <;> simp [letters, DataVar.pattern]
    · rw [evalLetters_cons, value]
      have : ((n + 2 : Nat) : ℤ) = 1 + ((n + 1 : Nat) : ℤ) := by push_cast; omega
      rw [this, powerEval_add]
      rfl

omit [DecidableEq G] in
/-- **Writing letters out and reading them back gives the same element.** -/
theorem letters_render (letter : Letter G) :
    ∃ found, letters decl reading.constant (letter.render decl reading) = some found ∧
      evalLetters found = letter.eval := by
  match letter with
  | .const g =>
    obtain ⟨found, parsed, value⟩ := letters_of_read reading.constant (reading.write g) (reading.read_write g)
    exact ⟨found, parsed, value⟩
  | .power v (.ofNat n) =>
    obtain ⟨found, parsed, value⟩ := letters_powerWord (reading := reading) v n
    exact ⟨found, parsed, value⟩
  | .power v (.negSucc n) =>
    obtain ⟨found, parsed, value⟩ := letters_powerWord (reading := reading) v (n + 1)
    refine ⟨invertLetters found, ?_, ?_⟩
    · simp only [Letter.render]
      rw [letters, if_pos rfl, parsed]
      rfl
    · rw [evalLetters_invert, value]
      have : Int.negSucc n = -((n + 1 : Nat) : ℤ) := rfl
      simp only [Letter.eval, Letter.sigma]
      rw [this]
      exact (powerEval_neg v _).symm

omit [DecidableEq G] in
theorem letters_renderWord : ∀ found : List (Letter G),
    ∃ again, letters decl reading.constant (renderWord decl reading found) = some again ∧
      evalLetters again = evalLetters found
  | [] => by
    obtain ⟨again, parsed, value⟩ := letters_of_read reading.constant (reading.write 1) (reading.read_write 1)
    exact ⟨again, parsed, value.trans (map_one (Monoid.CoprodI.of (M := Summand G) (i := none)))⟩
  | [letter] => by
    obtain ⟨again, parsed, value⟩ := letters_render (reading := reading) letter
    exact ⟨again, parsed, by rw [value, evalLetters_cons, evalLetters_nil, mul_one]⟩
  | letter :: second :: rest => by
    obtain ⟨front, frontParsed, frontValue⟩ := letters_render (reading := reading) letter
    obtain ⟨back, backParsed, backValue⟩ := letters_renderWord (second :: rest)
    refine ⟨front ++ back, ?_, ?_⟩
    · show letters decl reading.constant
          (.apply decl.multiply [letter.render decl reading, renderWord decl reading (second :: rest)]) =
        some (front ++ back)
      rw [letters, if_pos rfl, frontParsed, backParsed]
    · simp only [evalLetters_append, frontValue, backValue, evalLetters_cons]

/-- **Two data words have the same normal form exactly when they are equal in `G ∗ F(V)`.** -/
theorem wordNormal_eq_iff {first second : Pattern} {firstLetters secondLetters : List (Letter G)}
    (firstParsed : letters decl reading.constant first = some firstLetters)
    (secondParsed : letters decl reading.constant second = some secondLetters) :
    wordNormal decl reading first = wordNormal decl reading second ↔
      evalLetters firstLetters = evalLetters secondLetters := by
  unfold wordNormal
  rw [firstParsed, secondParsed]
  dsimp only
  constructor
  · intro same
    obtain ⟨firstAgain, firstAgainParsed, firstValue⟩ := letters_renderWord (reading := reading) (reduce firstLetters)
    obtain ⟨secondAgain, secondAgainParsed, secondValue⟩ :=
      letters_renderWord (reading := reading) (reduce secondLetters)
    rw [same, secondAgainParsed, Option.some.injEq] at firstAgainParsed
    rw [← eval_reduce firstLetters, ← eval_reduce secondLetters, ← firstValue, ← secondValue, firstAgainParsed]
  · intro same
    rw [(reduce_eq_iff firstLetters secondLetters).mpr same]

/-- **On a word the reading reads, the normal form is the canonical word of what it reads.** -/
theorem wordNormal_closed {datum : Pattern} {x : G} (readOk : read decl reading.constant datum = some x) :
    wordNormal decl reading datum = reading.write x := by
  obtain ⟨found, parsed, value⟩ := letters_of_read reading.constant datum readOk
  unfold wordNormal
  rw [parsed]
  dsimp only
  by_cases trivial : x = 1
  · subst trivial
    have empty : reduce found = [] := by
      apply eq_of_reduced (reduce_reduced found) ⟨fun _ member => (by cases member), List.isChain_nil⟩
      rw [eval_reduce, value]
      exact map_one (Monoid.CoprodI.of (M := Summand G) (i := none))
    rw [empty]
    rfl
  · have single : reduce found = [.const x] := by
      apply eq_of_reduced (reduce_reduced found)
        ⟨fun other member => by
          rw [List.mem_singleton] at member
          subst member
          simpa [Letter.isOne] using trivial, List.isChain_singleton _⟩
      rw [eval_reduce, value]
      simp only [evalLetters, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rfl
    rw [single]
    rfl

/-- **The normal form is idempotent** on data words. -/
theorem wordNormal_idem {datum : Pattern} {found : List (Letter G)}
    (parsed : letters decl reading.constant datum = some found) :
    wordNormal decl reading (wordNormal decl reading datum) = wordNormal decl reading datum := by
  obtain ⟨again, againParsed, value⟩ := letters_renderWord (reading := reading) (reduce found)
  have normalParsed : letters decl reading.constant (wordNormal decl reading datum) = some again := by
    unfold wordNormal
    rw [parsed]
    exact againParsed
  apply (wordNormal_eq_iff normalParsed parsed).mpr
  rw [value, eval_reduce]

end Mettapedia.OSLF.MeTTaIL.Orientation
