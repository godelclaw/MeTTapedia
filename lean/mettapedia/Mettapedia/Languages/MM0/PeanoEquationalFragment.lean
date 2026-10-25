import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# The equational fragment of `peano.mm0` in the MM0 kernel

`peano.mm0` is the Peano arithmetic of the MM0 distribution. This module states
the part of it that equational reasoning about numerals, sums and products
needs, as tables of the Lean model of the MM0 kernel (`Kernel.Derives`,
`Kernel.ProofWitness.check`):

* the sorts `wff` (strict, provable) and `nat`;
* the term constructors `im`, `not`, `eq`, `d0`, `suc`, `add`, `mul`;
* a theorem table (`baseEntries`) whose every entry is, word for word, either
  an axiom of `peano.mm0` or a public theorem of an MM0 file that extends it.
  Each entry carries its native name, so that the table can be printed and
  compared with the native specification. `table extra` extends the table by
  further declarations.

On these tables:

* **Guest terms** (`PTerm`) and their encoding (`encode`), typed in the
  context of their variables (`encode_typed`).
* **Proof witnesses for the equality structure**: reflexivity, symmetry,
  transitivity, the congruences of `suc`, `add` and `mul`, and instances of
  table entries (`checks_refl`, `checks_symm`, `checks_trans`, `checks_suc`,
  `checks_add`, `checks_mul`, `checks_instance`). Each is a finite
  `ProofWitness` that the kernel model accepts; `nodeCount` is its size.
* **The standard model** (`derives_sound`). Everything the base table derives
  holds in the natural numbers. So the base table derives neither `1 + 0 = 0`
  nor `suc 0 = 0` (`not_derives_one_add_zero_eq_zero`,
  `not_derives_suc_zero_eq_zero`).
* **Printers** for MM0 surface syntax, MM1 proof terms and MMU headers.

The native numerals `d1`, ..., `d10` and the definition `ne` are not part of
the fragment: numerals are iterated `suc`, and the fragment has no
definitions, so its MM0 conversion is syntactic identity (`converts_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.PeanoEquationalFragment

open Mettapedia.Languages.MM0.Kernel

/-! ## Guest terms -/

/-- First-order Peano terms over `n` variables. -/
inductive PTerm (n : Nat) where
  | var (index : Fin n)
  | zero
  | succ (t : PTerm n)
  | add (t u : PTerm n)
  | mul (t u : PTerm n)
  deriving DecidableEq, Repr

namespace PTerm

variable {n k : Nat}

/-- Simultaneous substitution for the `k` variables of a pattern. -/
def subst (σ : Fin k → PTerm n) : PTerm k → PTerm n
  | .var i => σ i
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .add t u => .add (subst σ t) (subst σ u)
  | .mul t u => .mul (subst σ t) (subst σ u)

/-- The value in the standard model. -/
def value (ρ : Fin n → ℕ) : PTerm n → ℕ
  | .var i => ρ i
  | .zero => 0
  | .succ t => value ρ t + 1
  | .add t u => value ρ t + value ρ u
  | .mul t u => value ρ t * value ρ u

theorem value_subst (ρ : Fin n → ℕ) (σ : Fin k → PTerm n) (t : PTerm k) :
    value ρ (subst σ t) = value (fun i => value ρ (σ i)) t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => simp only [subst, value, ih]
  | add t u iht ihu => simp only [subst, value, iht, ihu]
  | mul t u iht ihu => simp only [subst, value, iht, ihu]

/-- The numeral `suc (... (suc 0))`. -/
def numeral : ℕ → PTerm n
  | 0 => .zero
  | m + 1 => .succ (numeral m)

theorem value_numeral (ρ : Fin n → ℕ) : ∀ m : ℕ, value ρ (numeral m) = m
  | 0 => rfl
  | m + 1 => by simp only [numeral, value, value_numeral ρ m]

end PTerm

/-! ## The sorts and term constructors -/

abbrev wffSort : Nat := 0
abbrev natSort : Nat := 1

/-- `strict provable sort wff;` and `sort nat;`. -/
def sorts : SortSignature
  | 0 => some { strict := true, provable := true }
  | 1 => some {}
  | _ => none

abbrev wffBinder : Binder := .regular wffSort ∅
abbrev natBinder : Binder := .regular natSort ∅

/-- The context of `n` variables of sort `nat`. -/
abbrev natContext (n : Nat) : Context := List.replicate n natBinder

/-- The term constructors `im`, `not`, `eq`, `d0`, `suc`, `add` and `mul`, in this
order. -/
def terms : TermSignature
  | 0 => some ⟨[wffBinder, wffBinder], wffSort, ∅⟩
  | 1 => some ⟨[wffBinder], wffSort, ∅⟩
  | 2 => some ⟨[natBinder, natBinder], wffSort, ∅⟩
  | 3 => some ⟨[], natSort, ∅⟩
  | 4 => some ⟨[natBinder], natSort, ∅⟩
  | 5 => some ⟨[natBinder, natBinder], natSort, ∅⟩
  | 6 => some ⟨[natBinder, natBinder], natSort, ∅⟩
  | _ => none

/-- The native names of the term constructors. -/
def termName : Nat → String
  | 0 => "im"
  | 1 => "not"
  | 2 => "eq"
  | 3 => "d0"
  | 4 => "suc"
  | 5 => "add"
  | 6 => "mul"
  | _ => "unknown"

/-- The fragment declares no definitions. -/
def definitions : Definition.Signature := fun _ => none

/-! ## Expressions -/

/-- `p -> q`. -/
abbrev imp (p q : Preterm) : Preterm := .app (.app (.term 0) p) q
/-- `~ p`. -/
abbrev neg (p : Preterm) : Preterm := .app (.term 1) p
/-- `a = b`. -/
abbrev eqn (a b : Preterm) : Preterm := .app (.app (.term 2) a) b
/-- `0`. -/
abbrev zeroE : Preterm := .term 3
/-- `suc a`. -/
abbrev sucE (a : Preterm) : Preterm := .app (.term 4) a
/-- `a + b`. -/
abbrev addE (a b : Preterm) : Preterm := .app (.app (.term 5) a) b
/-- `a * b`. -/
abbrev mulE (a b : Preterm) : Preterm := .app (.app (.term 6) a) b
/-- The variable in position `i` of a context. -/
abbrev v (i : Nat) : Preterm := .var i

/-- The encoding of guest terms; the variable `i` is the `i`-th binder of the
context. -/
def encode {n : Nat} : PTerm n → Preterm
  | .var i => .var i.val
  | .zero => zeroE
  | .succ t => sucE (encode t)
  | .add t u => addE (encode t) (encode u)
  | .mul t u => mulE (encode t) (encode u)

/-! ## The theorem table -/

/-- One declaration of the table, with its native name. `axiomatic` records
whether it is an axiom or a proved theorem of the native files. -/
structure Entry where
  name : String
  axiomatic : Bool
  declaration : TheoremDecl

def mpDecl : TheoremDecl := ⟨[wffBinder, wffBinder], [imp (v 0) (v 1), v 0], v 1⟩
def ax1Decl : TheoremDecl := ⟨[wffBinder, wffBinder], [], imp (v 0) (imp (v 1) (v 0))⟩
def ax3Decl : TheoremDecl :=
  ⟨[wffBinder, wffBinder], [], imp (imp (neg (v 0)) (neg (v 1))) (imp (v 1) (v 0))⟩
def addeqDecl : TheoremDecl :=
  ⟨natContext 4, [], imp (eqn (v 0) (v 1))
    (imp (eqn (v 2) (v 3)) (eqn (addE (v 0) (v 2)) (addE (v 1) (v 3))))⟩
def muleqDecl : TheoremDecl :=
  ⟨natContext 4, [], imp (eqn (v 0) (v 1))
    (imp (eqn (v 2) (v 3)) (eqn (mulE (v 0) (v 2)) (mulE (v 1) (v 3))))⟩
def add0Decl : TheoremDecl := ⟨natContext 1, [], eqn (addE (v 0) zeroE) (v 0)⟩
def addSDecl : TheoremDecl :=
  ⟨natContext 2, [], eqn (addE (v 0) (sucE (v 1))) (sucE (addE (v 0) (v 1)))⟩
def mul0Decl : TheoremDecl := ⟨natContext 1, [], eqn (mulE (v 0) zeroE) zeroE⟩
def mulSDecl : TheoremDecl :=
  ⟨natContext 2, [], eqn (mulE (v 0) (sucE (v 1))) (addE (mulE (v 0) (v 1)) (v 0))⟩
def eqidDecl : TheoremDecl := ⟨natContext 1, [], eqn (v 0) (v 0)⟩
def eqcomDecl : TheoremDecl := ⟨natContext 2, [], imp (eqn (v 0) (v 1)) (eqn (v 1) (v 0))⟩
def eqtrDecl : TheoremDecl :=
  ⟨natContext 3, [], imp (eqn (v 0) (v 1)) (imp (eqn (v 1) (v 2)) (eqn (v 0) (v 2)))⟩
def suceqDecl : TheoremDecl :=
  ⟨natContext 2, [], imp (eqn (v 0) (v 1)) (eqn (sucE (v 0)) (sucE (v 1)))⟩
def addZeroLeftDecl : TheoremDecl := ⟨natContext 1, [], eqn (addE zeroE (v 0)) (v 0)⟩
def addSuccLeftDecl : TheoremDecl :=
  ⟨natContext 2, [], eqn (addE (sucE (v 0)) (v 1)) (sucE (addE (v 0) (v 1)))⟩
def mulZeroLeftDecl : TheoremDecl := ⟨natContext 1, [], eqn (mulE zeroE (v 0)) zeroE⟩
def mulSuccLeftDecl : TheoremDecl :=
  ⟨natContext 2, [], eqn (mulE (sucE (v 0)) (v 1)) (addE (mulE (v 0) (v 1)) (v 1))⟩
def sucNeZeroDecl : TheoremDecl := ⟨natContext 1, [], neg (eqn (sucE (v 0)) zeroE)⟩

/-- Axioms of `peano.mm0`, then the public theorems of the extending file
`peano_rung.mm0`: the equality structure and the left recursion equations,
proved there by induction. -/
def baseEntries : List Entry :=
  [ ⟨"ax_mp", true, mpDecl⟩,
    ⟨"ax_1", true, ax1Decl⟩,
    ⟨"ax_3", true, ax3Decl⟩,
    ⟨"addeq", true, addeqDecl⟩,
    ⟨"muleq", true, muleqDecl⟩,
    ⟨"add0", true, add0Decl⟩,
    ⟨"addS", true, addSDecl⟩,
    ⟨"mul0", true, mul0Decl⟩,
    ⟨"mulS", true, mulSDecl⟩,
    ⟨"rung_eqid", false, eqidDecl⟩,
    ⟨"rung_eqcom", false, eqcomDecl⟩,
    ⟨"rung_eqtr", false, eqtrDecl⟩,
    ⟨"rung_suceq", false, suceqDecl⟩,
    ⟨"rung_add_zero_left", false, addZeroLeftDecl⟩,
    ⟨"rung_add_succ_left", false, addSuccLeftDecl⟩,
    ⟨"rung_mul_zero_left", false, mulZeroLeftDecl⟩,
    ⟨"rung_mul_succ_left", false, mulSuccLeftDecl⟩,
    ⟨"rung_suc_ne_zero", false, sucNeZeroDecl⟩ ]

/-- The base table followed by further declarations. -/
def table (extra : List Entry) : TheoremSignature :=
  fun index => ((baseEntries ++ extra)[index]?).map Entry.declaration

/-- The native name of a table position. -/
def entryName (extra : List Entry) (index : Nat) : String :=
  match (baseEntries ++ extra)[index]? with
  | some entry => entry.name
  | none => "unknown"

/-- The table of the root: exactly the base entries. -/
abbrev theorems : TheoremSignature := table []

abbrev mpIndex : Nat := 0
abbrev ax1Index : Nat := 1
abbrev ax3Index : Nat := 2
abbrev addeqIndex : Nat := 3
abbrev muleqIndex : Nat := 4
abbrev add0Index : Nat := 5
abbrev addSIndex : Nat := 6
abbrev mul0Index : Nat := 7
abbrev mulSIndex : Nat := 8
abbrev eqidIndex : Nat := 9
abbrev eqcomIndex : Nat := 10
abbrev eqtrIndex : Nat := 11
abbrev suceqIndex : Nat := 12
abbrev addZeroLeftIndex : Nat := 13
abbrev addSuccLeftIndex : Nat := 14
abbrev mulZeroLeftIndex : Nat := 15
abbrev mulSuccLeftIndex : Nat := 16
abbrev sucNeZeroIndex : Nat := 17

section Lookup

variable (extra : List Entry)

theorem lookup_mp : table extra mpIndex = some mpDecl := rfl
theorem lookup_ax1 : table extra ax1Index = some ax1Decl := rfl
theorem lookup_ax3 : table extra ax3Index = some ax3Decl := rfl
theorem lookup_addeq : table extra addeqIndex = some addeqDecl := rfl
theorem lookup_muleq : table extra muleqIndex = some muleqDecl := rfl
theorem lookup_add0 : table extra add0Index = some add0Decl := rfl
theorem lookup_addS : table extra addSIndex = some addSDecl := rfl
theorem lookup_mul0 : table extra mul0Index = some mul0Decl := rfl
theorem lookup_mulS : table extra mulSIndex = some mulSDecl := rfl
theorem lookup_eqid : table extra eqidIndex = some eqidDecl := rfl
theorem lookup_eqcom : table extra eqcomIndex = some eqcomDecl := rfl
theorem lookup_eqtr : table extra eqtrIndex = some eqtrDecl := rfl
theorem lookup_suceq : table extra suceqIndex = some suceqDecl := rfl
theorem lookup_addZeroLeft : table extra addZeroLeftIndex = some addZeroLeftDecl := rfl
theorem lookup_addSuccLeft : table extra addSuccLeftIndex = some addSuccLeftDecl := rfl
theorem lookup_mulZeroLeft : table extra mulZeroLeftIndex = some mulZeroLeftDecl := rfl
theorem lookup_mulSuccLeft : table extra mulSuccLeftIndex = some mulSuccLeftDecl := rfl
theorem lookup_sucNeZero : table extra sucNeZeroIndex = some sucNeZeroDecl := rfl

/-- The position after the base entries holds the first extra entry. -/
theorem lookup_extra (entry : Entry) (rest : List Entry) :
    table (entry :: rest) baseEntries.length = some entry.declaration := rfl

end Lookup

/-- Every declaration of a table is one of its entries. -/
theorem table_mem {extra : List Entry} {index : Nat} {declaration : TheoremDecl}
    (lookup : table extra index = some declaration) :
    ∃ entry ∈ baseEntries ++ extra, entry.declaration = declaration := by
  unfold table at lookup
  cases found : (baseEntries ++ extra)[index]? with
  | none => rw [found] at lookup; cases lookup
  | some entry =>
      rw [found] at lookup
      exact ⟨entry, List.mem_of_getElem? found, Option.some.inj lookup⟩

/-! ## Typing -/

/-- A saturated numeric expression in the context of `n` numeric variables. -/
abbrev NatTyped (n : Nat) (expression : Preterm) : Prop :=
  Preterm.HasType terms (natContext n) expression [] natSort

/-- A saturated formula in the context of `n` numeric variables. -/
abbrev WffTyped (n : Nat) (expression : Preterm) : Prop :=
  Preterm.HasType terms (natContext n) expression [] wffSort

theorem natContext_lookup {n : Nat} (i : Fin n) : (natContext n)[i.val]? = some natBinder := by
  simp [natContext, i.isLt]

theorem term_im : terms 0 = some ⟨[wffBinder, wffBinder], wffSort, ∅⟩ := rfl
theorem term_not : terms 1 = some ⟨[wffBinder], wffSort, ∅⟩ := rfl
theorem term_eq : terms 2 = some ⟨[natBinder, natBinder], wffSort, ∅⟩ := rfl
theorem term_d0 : terms 3 = some ⟨[], natSort, ∅⟩ := rfl
theorem term_suc : terms 4 = some ⟨[natBinder], natSort, ∅⟩ := rfl
theorem term_add : terms 5 = some ⟨[natBinder, natBinder], natSort, ∅⟩ := rfl
theorem term_mul : terms 6 = some ⟨[natBinder, natBinder], natSort, ∅⟩ := rfl

theorem zeroE_typed {n : Nat} : NatTyped n zeroE := Preterm.HasType.term term_d0

theorem sucE_typed {n : Nat} {a : Preterm} (ha : NatTyped n a) : NatTyped n (sucE a) :=
  Preterm.HasType.regular (Preterm.HasType.term term_suc) ha

theorem addE_typed {n : Nat} {a b : Preterm} (ha : NatTyped n a) (hb : NatTyped n b) :
    NatTyped n (addE a b) :=
  Preterm.HasType.regular (Preterm.HasType.regular (Preterm.HasType.term term_add) ha) hb

theorem mulE_typed {n : Nat} {a b : Preterm} (ha : NatTyped n a) (hb : NatTyped n b) :
    NatTyped n (mulE a b) :=
  Preterm.HasType.regular (Preterm.HasType.regular (Preterm.HasType.term term_mul) ha) hb

theorem eqn_typed {n : Nat} {a b : Preterm} (ha : NatTyped n a) (hb : NatTyped n b) :
    WffTyped n (eqn a b) :=
  Preterm.HasType.regular (Preterm.HasType.regular (Preterm.HasType.term term_eq) ha) hb

theorem imp_typed {n : Nat} {p q : Preterm} (hp : WffTyped n p) (hq : WffTyped n q) :
    WffTyped n (imp p q) :=
  Preterm.HasType.regular (Preterm.HasType.regular (Preterm.HasType.term term_im) hp) hq

theorem neg_typed {n : Nat} {p : Preterm} (hp : WffTyped n p) : WffTyped n (neg p) :=
  Preterm.HasType.regular (Preterm.HasType.term term_not) hp

/-- **Every encoded term is a saturated numeric expression.** -/
theorem encode_typed {n : Nat} : ∀ t : PTerm n, NatTyped n (encode t)
  | .var i => Preterm.HasType.var (natContext_lookup i)
  | .zero => zeroE_typed
  | .succ t => sucE_typed (encode_typed t)
  | .add t u => addE_typed (encode_typed t) (encode_typed u)
  | .mul t u => mulE_typed (encode_typed t) (encode_typed u)

/-! ## Instances of table entries -/

/-- Every formal binder is regular: no bound variables, so no disjointness
conditions. -/
def AllRegular (formal : Context) : Prop :=
  ∀ binder ∈ formal, ∃ sort dependencies, binder = .regular sort dependencies

theorem allRegular_natContext (k : Nat) : AllRegular (natContext k) := by
  intro binder member
  exact ⟨natSort, ∅, (List.mem_replicate.mp member).2⟩

theorem allRegular_wff2 : AllRegular [wffBinder, wffBinder] := by
  intro binder member
  rcases List.mem_cons.mp member with same | member
  · exact ⟨wffSort, ∅, same⟩
  · rcases List.mem_cons.mp member with same | member
    · exact ⟨wffSort, ∅, same⟩
    · cases member

/-- With regular formals only, admissibility is the typing of the arguments. -/
theorem admissible_of_allRegular {formal target : Context} {args : List Preterm}
    (regular : AllRegular formal)
    (typed : List.Forall₂ (Preterm.FitsBinder terms target) args formal) :
    Substitution.Admissible terms formal target args where
  typed := typed
  independent := by
    intro entry member sort image same
    have pairMember : entry.1 ∈ formal.zip args := List.fst_mem_of_mem_zipIdx member
    have binderMember : entry.1.1 ∈ formal := (List.of_mem_zip pairMember).1
    obtain ⟨regularSort, dependencies, isRegular⟩ := regular _ binderMember
    have isBound : entry.1.1 = .bound sort := by rw [same]
    rw [isRegular] at isBound
    cases isBound

/-- An instance of a declaration with regular formals, from the computed
substitution of its hypotheses and conclusion. -/
theorem instantiates {ctx : Context} {declaration : TheoremDecl}
    {args hypotheses : List Preterm} {conclusion : Preterm}
    (regular : AllRegular declaration.arguments)
    (typed : List.Forall₂ (Preterm.FitsBinder terms ctx) args declaration.arguments)
    (hypothesesEq : Substitution.substituteList (Substitution.ofList args)
      declaration.hypotheses = some hypotheses)
    (conclusionEq : declaration.conclusion.substitute (Substitution.ofList args) =
      some conclusion) :
    TheoremDecl.Instantiates terms ctx declaration args ⟨hypotheses, conclusion⟩ :=
  ⟨admissible_of_allRegular regular typed,
    (Substitution.substituteList_eq_some_iff _ _ _).mp hypothesesEq,
    Preterm.substitute_sound conclusionEq⟩

/-- Substituting the encodings of a substitution into an encoded pattern
encodes the substituted pattern. -/
theorem substitute_encode {k n : Nat} (σ : Fin k → PTerm n) :
    ∀ t : PTerm k, (encode t).substitute (Substitution.ofList (List.ofFn fun i => encode (σ i))) =
      some (encode (t.subst σ))
  | .var i => by
      simp [encode, PTerm.subst, Preterm.substitute, Substitution.ofList, i.isLt]
  | .zero => rfl
  | .succ t => by
      simp [encode, PTerm.subst, Preterm.substitute, substitute_encode σ t]
  | .add t u => by
      simp [encode, PTerm.subst, Preterm.substitute, substitute_encode σ t,
        substitute_encode σ u]
  | .mul t u => by
      simp [encode, PTerm.subst, Preterm.substitute, substitute_encode σ t,
        substitute_encode σ u]

/-- The encodings of a substitution fit the numeric context of a pattern. -/
theorem ofFn_fits {n : Nat} : ∀ {k : Nat} (σ : Fin k → PTerm n),
    List.Forall₂ (Preterm.FitsBinder terms (natContext n)) (List.ofFn fun i => encode (σ i))
      (natContext k)
  | 0, _ => .nil
  | k + 1, σ => by
      rw [List.ofFn_succ]
      exact .cons (.regular (encode_typed _)) (ofFn_fits (fun i => σ i.succ))

/-! ## Witnesses for the equality structure -/

/-- The kernel model accepts a witness for an expression, in the context of
`n` numeric variables, without hypotheses. -/
abbrev Checks (extra : List Entry) (n : Nat) (witness : ProofWitness) (expression : Preterm) :
    Prop :=
  ProofWitness.Checks terms definitions (table extra) (natContext n) [] witness expression

/-- Modus ponens: from `p -> q` and `p`, infer `q`. -/
def mpW (p q : Preterm) (major minor : ProofWitness) : ProofWitness :=
  .theoremApp mpIndex [p, q] [major, minor]

/-- `a = a`. -/
def reflW (a : Preterm) : ProofWitness := .theoremApp eqidIndex [a] []

/-- From `a = b`, infer `b = a`. -/
def symmW (a b : Preterm) (receipt : ProofWitness) : ProofWitness :=
  mpW (eqn a b) (eqn b a) (.theoremApp eqcomIndex [a, b] []) receipt

/-- From `a = b` and `b = c`, infer `a = c`. -/
def transW (a b c : Preterm) (first second : ProofWitness) : ProofWitness :=
  mpW (eqn b c) (eqn a c)
    (mpW (eqn a b) (imp (eqn b c) (eqn a c)) (.theoremApp eqtrIndex [a, b, c] []) first) second

/-- From `a = b`, infer `suc a = suc b`. -/
def sucW (a b : Preterm) (receipt : ProofWitness) : ProofWitness :=
  mpW (eqn a b) (eqn (sucE a) (sucE b)) (.theoremApp suceqIndex [a, b] []) receipt

/-- From `a = b` and `c = d`, infer `a + c = b + d`. -/
def addW (a b c d : Preterm) (left right : ProofWitness) : ProofWitness :=
  mpW (eqn c d) (eqn (addE a c) (addE b d))
    (mpW (eqn a b) (imp (eqn c d) (eqn (addE a c) (addE b d)))
      (.theoremApp addeqIndex [a, b, c, d] []) left) right

/-- From `a = b` and `c = d`, infer `a * c = b * d`. -/
def mulW (a b c d : Preterm) (left right : ProofWitness) : ProofWitness :=
  mpW (eqn c d) (eqn (mulE a c) (mulE b d))
    (mpW (eqn a b) (imp (eqn c d) (eqn (mulE a c) (mulE b d)))
      (.theoremApp muleqIndex [a, b, c, d] []) left) right

section Checks

variable {extra : List Entry} {n : Nat}

theorem checks_mp {p q : Preterm} {major minor : ProofWitness}
    (hp : WffTyped n p) (hq : WffTyped n q)
    (hmajor : Checks extra n major (imp p q)) (hminor : Checks extra n minor p) :
    Checks extra n (mpW p q major minor) q :=
  .theoremApp (lookup_mp extra)
    (instantiates (hypotheses := [imp p q, p]) allRegular_wff2
      (.cons (.regular hp) (.cons (.regular hq) .nil)) rfl rfl)
    (.cons hmajor (.cons hminor .nil))

theorem checks_refl {a : Preterm} (ha : NatTyped n a) : Checks extra n (reflW a) (eqn a a) :=
  .theoremApp (lookup_eqid extra)
    (instantiates (hypotheses := []) (allRegular_natContext 1) (.cons (.regular ha) .nil) rfl rfl)
    .nil

theorem checks_symm {a b : Preterm} {receipt : ProofWitness}
    (ha : NatTyped n a) (hb : NatTyped n b) (hreceipt : Checks extra n receipt (eqn a b)) :
    Checks extra n (symmW a b receipt) (eqn b a) :=
  checks_mp (eqn_typed ha hb) (eqn_typed hb ha)
    (.theoremApp (lookup_eqcom extra)
      (instantiates (hypotheses := []) (allRegular_natContext 2)
        (.cons (.regular ha) (.cons (.regular hb) .nil)) rfl rfl) .nil)
    hreceipt

theorem checks_trans {a b c : Preterm} {first second : ProofWitness}
    (ha : NatTyped n a) (hb : NatTyped n b) (hc : NatTyped n c)
    (hfirst : Checks extra n first (eqn a b)) (hsecond : Checks extra n second (eqn b c)) :
    Checks extra n (transW a b c first second) (eqn a c) :=
  checks_mp (eqn_typed hb hc) (eqn_typed ha hc)
    (checks_mp (eqn_typed ha hb) (imp_typed (eqn_typed hb hc) (eqn_typed ha hc))
      (.theoremApp (lookup_eqtr extra)
        (instantiates (hypotheses := []) (allRegular_natContext 3)
          (.cons (.regular ha) (.cons (.regular hb) (.cons (.regular hc) .nil))) rfl rfl) .nil)
      hfirst)
    hsecond

theorem checks_suc {a b : Preterm} {receipt : ProofWitness}
    (ha : NatTyped n a) (hb : NatTyped n b) (hreceipt : Checks extra n receipt (eqn a b)) :
    Checks extra n (sucW a b receipt) (eqn (sucE a) (sucE b)) :=
  checks_mp (eqn_typed ha hb) (eqn_typed (sucE_typed ha) (sucE_typed hb))
    (.theoremApp (lookup_suceq extra)
      (instantiates (hypotheses := []) (allRegular_natContext 2)
        (.cons (.regular ha) (.cons (.regular hb) .nil)) rfl rfl) .nil)
    hreceipt

theorem checks_add {a b c d : Preterm} {left right : ProofWitness}
    (ha : NatTyped n a) (hb : NatTyped n b) (hc : NatTyped n c) (hd : NatTyped n d)
    (hleft : Checks extra n left (eqn a b)) (hright : Checks extra n right (eqn c d)) :
    Checks extra n (addW a b c d left right) (eqn (addE a c) (addE b d)) :=
  checks_mp (eqn_typed hc hd) (eqn_typed (addE_typed ha hc) (addE_typed hb hd))
    (checks_mp (eqn_typed ha hb)
      (imp_typed (eqn_typed hc hd) (eqn_typed (addE_typed ha hc) (addE_typed hb hd)))
      (.theoremApp (lookup_addeq extra)
        (instantiates (hypotheses := []) (allRegular_natContext 4)
          (.cons (.regular ha) (.cons (.regular hb) (.cons (.regular hc)
            (.cons (.regular hd) .nil)))) rfl rfl) .nil)
      hleft)
    hright

theorem checks_mul {a b c d : Preterm} {left right : ProofWitness}
    (ha : NatTyped n a) (hb : NatTyped n b) (hc : NatTyped n c) (hd : NatTyped n d)
    (hleft : Checks extra n left (eqn a b)) (hright : Checks extra n right (eqn c d)) :
    Checks extra n (mulW a b c d left right) (eqn (mulE a c) (mulE b d)) :=
  checks_mp (eqn_typed hc hd) (eqn_typed (mulE_typed ha hc) (mulE_typed hb hd))
    (checks_mp (eqn_typed ha hb)
      (imp_typed (eqn_typed hc hd) (eqn_typed (mulE_typed ha hc) (mulE_typed hb hd)))
      (.theoremApp (lookup_muleq extra)
        (instantiates (hypotheses := []) (allRegular_natContext 4)
          (.cons (.regular ha) (.cons (.regular hb) (.cons (.regular hc)
            (.cons (.regular hd) .nil)))) rfl rfl) .nil)
      hleft)
    hright

/-- **An equation of the table, at encoded arguments.** If the table holds
`l = r` over `k` numeric variables at `index`, the one-node witness at the
encodings of `σ` proves the substituted equation. -/
theorem checks_instance {index k : Nat} {left right : PTerm k}
    (lookup : table extra index = some ⟨natContext k, [], eqn (encode left) (encode right)⟩)
    (σ : Fin k → PTerm n) :
    Checks extra n (.theoremApp index (List.ofFn fun i => encode (σ i)) [])
      (eqn (encode (left.subst σ)) (encode (right.subst σ))) :=
  .theoremApp lookup
    (instantiates (hypotheses := []) (allRegular_natContext k) (ofFn_fits σ) rfl
      (by simp [Preterm.substitute, substitute_encode]))
    .nil

end Checks

/-! ## Witness size -/

mutual

/-- The number of nodes of a witness: every theorem application, hypothesis
reference and conversion counts one. -/
def nodeCount : ProofWitness → Nat
  | .hyp _ => 1
  | .theoremApp _ _ children => nodeCountList children + 1
  | .conversion _ child => nodeCount child + 1

def nodeCountList : List ProofWitness → Nat
  | [] => 0
  | child :: children => nodeCount child + nodeCountList children

end

@[simp] theorem nodeCount_theoremApp (index : Nat) (args : List Preterm)
    (children : List ProofWitness) :
    nodeCount (.theoremApp index args children) = nodeCountList children + 1 := by
  simp [nodeCount]

@[simp] theorem nodeCountList_nil : nodeCountList [] = 0 := by simp [nodeCountList]

@[simp] theorem nodeCountList_cons (child : ProofWitness) (children : List ProofWitness) :
    nodeCountList (child :: children) = nodeCount child + nodeCountList children := by
  simp [nodeCountList]

theorem nodeCount_mp (p q : Preterm) (major minor : ProofWitness) :
    nodeCount (mpW p q major minor) = nodeCount major + nodeCount minor + 1 := by
  simp only [mpW, nodeCount_theoremApp, nodeCountList_cons, nodeCountList_nil]
  omega

theorem nodeCount_refl (a : Preterm) : nodeCount (reflW a) = 1 := by
  simp only [reflW, nodeCount_theoremApp, nodeCountList_nil]

theorem nodeCount_symm (a b : Preterm) (receipt : ProofWitness) :
    nodeCount (symmW a b receipt) = nodeCount receipt + 2 := by
  simp only [symmW, nodeCount_mp, nodeCount_theoremApp, nodeCountList_nil]
  omega

theorem nodeCount_trans (a b c : Preterm) (first second : ProofWitness) :
    nodeCount (transW a b c first second) = nodeCount first + nodeCount second + 3 := by
  simp only [transW, nodeCount_mp, nodeCount_theoremApp, nodeCountList_nil]
  omega

theorem nodeCount_suc (a b : Preterm) (receipt : ProofWitness) :
    nodeCount (sucW a b receipt) = nodeCount receipt + 2 := by
  simp only [sucW, nodeCount_mp, nodeCount_theoremApp, nodeCountList_nil]
  omega

theorem nodeCount_add (a b c d : Preterm) (left right : ProofWitness) :
    nodeCount (addW a b c d left right) = nodeCount left + nodeCount right + 3 := by
  simp only [addW, nodeCount_mp, nodeCount_theoremApp, nodeCountList_nil]
  omega

theorem nodeCount_mul (a b c d : Preterm) (left right : ProofWitness) :
    nodeCount (mulW a b c d left right) = nodeCount left + nodeCount right + 3 := by
  simp only [mulW, nodeCount_mp, nodeCount_theoremApp, nodeCountList_nil]
  omega

/-! ## The standard model -/

/-- The numeric reading of an expression; `0` on expressions of other shapes. -/
def num (ρ : Nat → ℕ) : Preterm → ℕ
  | .var i => ρ i
  | .app (.term 4) a => num ρ a + 1
  | .app (.app (.term 5) a) b => num ρ a + num ρ b
  | .app (.app (.term 6) a) b => num ρ a * num ρ b
  | _ => 0

/-- The truth reading of an expression; false on expressions of other shapes. -/
def holds (ρ : Nat → ℕ) (π : Nat → Prop) : Preterm → Prop
  | .var i => π i
  | .app (.app (.term 0) p) q => holds ρ π p → holds ρ π q
  | .app (.term 1) p => ¬ holds ρ π p
  | .app (.app (.term 2) a) b => num ρ a = num ρ b
  | _ => False

section ModelEquations

variable (ρ : Nat → ℕ) (π : Nat → Prop)

@[simp] theorem num_var (i : Nat) : num ρ (.var i) = ρ i := rfl
@[simp] theorem num_zeroE : num ρ zeroE = 0 := rfl
@[simp] theorem num_sucE (a : Preterm) : num ρ (sucE a) = num ρ a + 1 := rfl
@[simp] theorem num_addE (a b : Preterm) : num ρ (addE a b) = num ρ a + num ρ b := rfl
@[simp] theorem num_mulE (a b : Preterm) : num ρ (mulE a b) = num ρ a * num ρ b := rfl
@[simp] theorem holds_var (i : Nat) : holds ρ π (.var i) = π i := rfl
@[simp] theorem holds_imp (p q : Preterm) :
    holds ρ π (imp p q) = (holds ρ π p → holds ρ π q) := rfl
@[simp] theorem holds_neg (p : Preterm) : holds ρ π (neg p) = ¬ holds ρ π p := rfl
@[simp] theorem holds_eqn (a b : Preterm) : holds ρ π (eqn a b) = (num ρ a = num ρ b) := rfl

end ModelEquations

/-- The value of an encoded term is its value in the standard model. -/
theorem num_encode {n : Nat} (ρ : Nat → ℕ) :
    ∀ t : PTerm n, num ρ (encode t) = t.value (fun i => ρ i.val)
  | .var _ => rfl
  | .zero => rfl
  | .succ t => by simp [encode, PTerm.value, num_encode ρ t]
  | .add t u => by simp [encode, PTerm.value, num_encode ρ t, num_encode ρ u]
  | .mul t u => by simp [encode, PTerm.value, num_encode ρ t, num_encode ρ u]

/-- Numeric expressions of the fragment. -/
inductive NumShape : Preterm → Prop where
  | var (i : Nat) : NumShape (.var i)
  | zero : NumShape zeroE
  | suc {a : Preterm} : NumShape a → NumShape (sucE a)
  | add {a b : Preterm} : NumShape a → NumShape b → NumShape (addE a b)
  | mul {a b : Preterm} : NumShape a → NumShape b → NumShape (mulE a b)

/-- Formulas of the fragment. -/
inductive WffShape : Preterm → Prop where
  | var (i : Nat) : WffShape (.var i)
  | imp {p q : Preterm} : WffShape p → WffShape q → WffShape (imp p q)
  | neg {p : Preterm} : WffShape p → WffShape (neg p)
  | eqn {a b : Preterm} : NumShape a → NumShape b → WffShape (eqn a b)

/-- Substitution moves the numeric reading to the valuation of the images. -/
theorem num_substitutes {σ : Substitution} {ρ ρ' : Nat → ℕ}
    (agree : ∀ i image, σ i = some image → num ρ image = ρ' i)
    {e e' : Preterm} (shape : NumShape e) (substituted : Preterm.Substitutes σ e e') :
    num ρ e' = num ρ' e := by
  induction shape generalizing e' with
  | var i =>
      cases substituted with
      | var lookup => exact agree i _ lookup
  | zero =>
      cases substituted
      rfl
  | suc _ ih =>
      cases substituted with
      | app function argument =>
          cases function
          simp only [num_sucE, ih argument]
  | add _ _ ihLeft ihRight =>
      cases substituted with
      | app function argument =>
          cases function with
          | app inner left =>
              cases inner
              simp only [num_addE, ihLeft left, ihRight argument]
  | mul _ _ ihLeft ihRight =>
      cases substituted with
      | app function argument =>
          cases function with
          | app inner left =>
              cases inner
              simp only [num_mulE, ihLeft left, ihRight argument]

/-- Substitution moves the truth reading to the valuation of the images. -/
theorem holds_substitutes {σ : Substitution} {ρ ρ' : Nat → ℕ} {π π' : Nat → Prop}
    (agreeNum : ∀ i image, σ i = some image → num ρ image = ρ' i)
    (agreeWff : ∀ i image, σ i = some image → (holds ρ π image ↔ π' i))
    {e e' : Preterm} (shape : WffShape e) (substituted : Preterm.Substitutes σ e e') :
    holds ρ π e' ↔ holds ρ' π' e := by
  induction shape generalizing e' with
  | var i =>
      cases substituted with
      | var lookup => exact agreeWff i _ lookup
  | imp _ _ ihLeft ihRight =>
      cases substituted with
      | app function argument =>
          cases function with
          | app inner left =>
              cases inner
              simp only [holds_imp, ihLeft left, ihRight argument]
  | neg _ ih =>
      cases substituted with
      | app function argument =>
          cases function
          simp only [holds_neg, ih argument]
  | eqn left right =>
      cases substituted with
      | app function argument =>
          cases function with
          | app inner leftSubstituted =>
              cases inner
              simp only [holds_eqn, num_substitutes agreeNum left leftSubstituted,
                num_substitutes agreeNum right argument]

/-- A declaration is sound when all its statements are formulas of the
fragment and every valuation satisfying its hypotheses satisfies its
conclusion. -/
structure Sound (declaration : TheoremDecl) : Prop where
  hypothesesShaped : ∀ h ∈ declaration.hypotheses, WffShape h
  conclusionShaped : WffShape declaration.conclusion
  valid : ∀ (ρ : Nat → ℕ) (π : Nat → Prop),
    (∀ h ∈ declaration.hypotheses, holds ρ π h) → holds ρ π declaration.conclusion

/-- A declaration without hypotheses is sound when its conclusion is a formula
that holds under every valuation. -/
theorem Sound.of_conclusion {arguments : Context} {conclusion : Preterm}
    (shape : WffShape conclusion) (valid : ∀ (ρ : Nat → ℕ) (π : Nat → Prop), holds ρ π conclusion) :
    Sound ⟨arguments, [], conclusion⟩ :=
  ⟨fun _ member => (List.not_mem_nil member).elim, shape, fun ρ π _ => valid ρ π⟩

theorem mpDecl_sound : Sound mpDecl where
  hypothesesShaped := by
    intro h member
    rcases List.mem_cons.mp member with rfl | member
    · repeat constructor
    · rcases List.mem_cons.mp member with rfl | member
      · constructor
      · cases member
  conclusionShaped := by repeat constructor
  valid := by
    intro ρ π premises
    have major := premises _ (List.mem_cons_self ..)
    have minor := premises _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact major minor

theorem ax1Decl_sound : Sound ax1Decl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp only [holds_imp]; exact fun a _ => a)

theorem ax3Decl_sound : Sound ax3Decl :=
  Sound.of_conclusion (by repeat constructor) (by
    intro ρ π
    simp only [holds_imp, holds_neg]
    intro contrapositive second
    by_contra first
    exact contrapositive first second)

theorem addeqDecl_sound : Sound addeqDecl :=
  Sound.of_conclusion (by repeat constructor) (by
    intro ρ π
    simp only [holds_imp, holds_eqn, num_addE, num_var]
    intro first second
    rw [first, second])

theorem muleqDecl_sound : Sound muleqDecl :=
  Sound.of_conclusion (by repeat constructor) (by
    intro ρ π
    simp only [holds_imp, holds_eqn, num_mulE, num_var]
    intro first second
    rw [first, second])

theorem add0Decl_sound : Sound add0Decl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp)

theorem addSDecl_sound : Sound addSDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp; omega)

theorem mul0Decl_sound : Sound mul0Decl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp)

theorem mulSDecl_sound : Sound mulSDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp [Nat.mul_succ])

theorem eqidDecl_sound : Sound eqidDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp)

theorem eqcomDecl_sound : Sound eqcomDecl :=
  Sound.of_conclusion (by repeat constructor) (by
    intro ρ π
    simp only [holds_imp, holds_eqn, num_var]
    exact Eq.symm)

theorem eqtrDecl_sound : Sound eqtrDecl :=
  Sound.of_conclusion (by repeat constructor) (by
    intro ρ π
    simp only [holds_imp, holds_eqn, num_var]
    exact Eq.trans)

theorem suceqDecl_sound : Sound suceqDecl :=
  Sound.of_conclusion (by repeat constructor) (by
    intro ρ π
    simp only [holds_imp, holds_eqn, num_sucE, num_var]
    intro equal
    rw [equal])

theorem addZeroLeftDecl_sound : Sound addZeroLeftDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp)

theorem addSuccLeftDecl_sound : Sound addSuccLeftDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp; omega)

theorem mulZeroLeftDecl_sound : Sound mulZeroLeftDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp)

theorem mulSuccLeftDecl_sound : Sound mulSuccLeftDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp [Nat.succ_mul])

theorem sucNeZeroDecl_sound : Sound sucNeZeroDecl :=
  Sound.of_conclusion (by repeat constructor) (by intro ρ π; simp)

/-- **Every base entry is sound in the natural numbers.** -/
theorem baseEntries_sound : ∀ entry ∈ baseEntries, Sound entry.declaration := by
  simp only [baseEntries, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨mpDecl_sound, ax1Decl_sound, ax3Decl_sound, addeqDecl_sound, muleqDecl_sound,
    add0Decl_sound, addSDecl_sound, mul0Decl_sound, mulSDecl_sound, eqidDecl_sound,
    eqcomDecl_sound, eqtrDecl_sound, suceqDecl_sound, addZeroLeftDecl_sound,
    addSuccLeftDecl_sound, mulZeroLeftDecl_sound, mulSuccLeftDecl_sound, sucNeZeroDecl_sound⟩

/-- **The fragment's conversion is syntactic identity**: it has no definitions
to unfold. -/
theorem converts_eq {ctx : Context} {left right : Preterm} {sort : Nat}
    (converted : Converts terms definitions ctx left right sort) : left = right := by
  induction converted using Converts.rec
      (motive_2 := fun lefts rights _ _ => lefts = rights) with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | congruence _ _ ih => rw [ih]
  | unfold _ unfolds _ =>
      cases unfolds with
      | intro _ body => simp [definitions] at body
  | nil => rfl
  | cons _ _ _ _ ihHead ihTail => rw [ihHead, ihTail]

/-- Hypotheses transfer along a substitution, pointwise. -/
theorem holds_of_forall₂ {σ : Substitution} {ρ ρ' : Nat → ℕ} {π π' : Nat → Prop}
    (agreeNum : ∀ i image, σ i = some image → num ρ image = ρ' i)
    (agreeWff : ∀ i image, σ i = some image → (holds ρ π image ↔ π' i)) :
    ∀ {sources images : List Preterm}, List.Forall₂ (Preterm.Substitutes σ) sources images →
      (∀ h ∈ sources, WffShape h) → (∀ e ∈ images, holds ρ π e) →
        ∀ h ∈ sources, holds ρ' π' h
  | _, _, .nil, _, _ => fun _ member => by cases member
  | _, _, .cons head tail, shaped, holdsImages => by
      intro h member
      rcases List.mem_cons.mp member with rfl | rest
      · exact (holds_substitutes agreeNum agreeWff (shaped _ (List.mem_cons_self ..)) head).mp
          (holdsImages _ (List.mem_cons_self ..))
      · exact holds_of_forall₂ agreeNum agreeWff tail
          (fun h' member' => shaped h' (List.mem_cons_of_mem _ member'))
          (fun e member' => holdsImages e (List.mem_cons_of_mem _ member')) h rest

/-- **Soundness in the standard model.** Every expression that the base table
derives without hypotheses holds under every valuation. -/
theorem derives_sound {ctx : Context} {expression : Preterm}
    (derived : Derives terms definitions theorems ctx [] expression)
    (ρ : Nat → ℕ) (π : Nat → Prop) : holds ρ π expression := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ => ∀ e ∈ expressions, holds ρ π e) with
  | hypothesis member => cases member
  | @theoremApp index declaration args instantiation lookup instantiated _ ih =>
      obtain ⟨entry, member, same⟩ := table_mem lookup
      rw [List.append_nil] at member
      obtain ⟨hypothesesShaped, conclusionShaped, valid⟩ :=
        same ▸ baseEntries_sound entry member
      let ρ' : Nat → ℕ := fun i => num ρ ((args[i]?).getD zeroE)
      let π' : Nat → Prop := fun i => holds ρ π ((args[i]?).getD zeroE)
      have agreeNum : ∀ i image, Substitution.ofList args i = some image →
          num ρ image = ρ' i := by
        intro i image lookupImage
        simp only [Substitution.ofList] at lookupImage
        simp only [ρ', lookupImage, Option.getD_some]
      have agreeWff : ∀ i image, Substitution.ofList args i = some image →
          (holds ρ π image ↔ π' i) := by
        intro i image lookupImage
        simp only [Substitution.ofList] at lookupImage
        simp only [π', lookupImage, Option.getD_some]
      exact (holds_substitutes agreeNum agreeWff conclusionShaped instantiated.conclusion).mpr
        (valid ρ' π' (holds_of_forall₂ agreeNum agreeWff instantiated.hypotheses
          hypothesesShaped ih))
  | conversion converted _ ih =>
      rw [← converts_eq converted]
      exact ih
  | nil =>
      rename_i member
      cases member
  | cons _ _ ihHead ihTail =>
      rename_i e member
      rcases List.mem_cons.mp member with rfl | rest
      · exact ihHead
      · exact ihTail e rest

/-- **The root derives no false equation at a closed instance**: not
`1 + 0 = 0`. -/
theorem not_derives_one_add_zero_eq_zero {ctx : Context} :
    ¬ Derives terms definitions theorems ctx [] (eqn (addE (sucE zeroE) zeroE) zeroE) := by
  intro derived
  have holdsInModel := derives_sound derived (fun _ => 0) (fun _ => True)
  simp at holdsInModel

/-- The root does not derive `suc 0 = 0`. -/
theorem not_derives_suc_zero_eq_zero {ctx : Context} :
    ¬ Derives terms definitions theorems ctx [] (eqn (sucE zeroE) zeroE) := by
  intro derived
  have holdsInModel := derives_sound derived (fun _ => 0) (fun _ => True)
  simp at holdsInModel

/-- **The root is consistent**: some formula is not derived. -/
theorem root_consistent {ctx : Context} :
    ∃ expression, WffTyped 0 expression ∧ ¬ Derives terms definitions theorems ctx [] expression :=
  ⟨eqn (sucE zeroE) zeroE, eqn_typed (sucE_typed zeroE_typed) zeroE_typed,
    not_derives_suc_zero_eq_zero⟩

/-- An equation between encoded terms that the root derives holds for every
value of the variables. -/
theorem derives_value {n : Nat} {t u : PTerm n}
    (derived : Derives terms definitions theorems (natContext n) [] (eqn (encode t) (encode u)))
    (ρ : Fin n → ℕ) : t.value ρ = u.value ρ := by
  have holdsInModel := derives_sound derived (fun i => if h : i < n then ρ ⟨i, h⟩ else 0)
    (fun _ => True)
  simp only [holds_eqn, num_encode] at holdsInModel
  simpa using holdsInModel

/-! ## Printing -/

/-- The variable names of printed declarations. -/
def varName (i : Nat) : String :=
  match i with
  | 0 => "a"
  | 1 => "b"
  | 2 => "c"
  | 3 => "d"
  | i => "v" ++ toString i

/-- An expression as an s-expression, with the arguments already printed. -/
def printSExprAux (arguments : List String) : Preterm → String
  | .var i =>
      if arguments.isEmpty then varName i else "(" ++ " ".intercalate (varName i :: arguments) ++ ")"
  | .term k => "(" ++ " ".intercalate (termName k :: arguments) ++ ")"
  | .app function argument => printSExprAux (printSExprAux [] argument :: arguments) function

/-- An expression in the s-expression syntax shared by MMU and MM1 proof terms. -/
def printSExpr (expression : Preterm) : String := printSExprAux [] expression

/-- An expression in MM0 math syntax, fully parenthesized. -/
def printMath : Preterm → String
  | .var i => varName i
  | .term 3 => "0"
  | .app (.term 4) a => "(suc " ++ printMath a ++ ")"
  | .app (.term 1) p => "(~ " ++ printMath p ++ ")"
  | .app (.app (.term 0) p) q => "(" ++ printMath p ++ " -> " ++ printMath q ++ ")"
  | .app (.app (.term 2) a) b => "(" ++ printMath a ++ " = " ++ printMath b ++ ")"
  | .app (.app (.term 5) a) b => "(" ++ printMath a ++ " + " ++ printMath b ++ ")"
  | .app (.app (.term 6) a) b => "(" ++ printMath a ++ " * " ++ printMath b ++ ")"
  | _ => "unknown"

mutual

/-- A witness as an MM1 proof term, every argument explicit. -/
def printWitness (extra : List Entry) : ProofWitness → String
  | .hyp i => "h" ++ toString i
  | .theoremApp index args children =>
      "(! " ++ " ".intercalate (entryName extra index :: args.map printSExpr ++
        printWitnessList extra children) ++ ")"
  | .conversion _ child => printWitness extra child

def printWitnessList (extra : List Entry) : List ProofWitness → List String
  | [] => []
  | child :: children => printWitness extra child :: printWitnessList extra children

end

/-- A binder in MMU syntax. -/
def printBinder (i : Nat) : Binder → String
  | .regular 0 _ => "(" ++ varName i ++ " wff ())"
  | .regular 1 _ => "(" ++ varName i ++ " nat ())"
  | _ => "(" ++ varName i ++ " unknown ())"

/-- The MMU header of a table entry: kind, name, binders, hypotheses and
conclusion. -/
def printEntryHeader (entry : Entry) : String :=
  "(" ++ (if entry.axiomatic then "axiom " else "theorem ") ++ entry.name ++ " (" ++
    " ".intercalate ((entry.declaration.arguments.zipIdx).map fun (b, i) => printBinder i b) ++
    ") (" ++ " ".intercalate (entry.declaration.hypotheses.map printSExpr) ++ ") " ++
    printSExpr entry.declaration.conclusion

/-- The MM0 binders of `n` numeric variables. -/
def printNatBinders (n : Nat) : String :=
  if n = 0 then "" else " (" ++ " ".intercalate ((List.range n).map varName) ++ ": nat)"

/-- An MM0 specification line for a theorem over `n` numeric variables. -/
def printMM0Theorem (name : String) (n : Nat) (statement : Preterm) : String :=
  "theorem " ++ name ++ printNatBinders n ++ ": $ " ++ printMath statement ++ " $;"

/-- An MM1 theorem over `n` numeric variables, proved by a witness. -/
def printMM1Theorem (extra : List Entry) (name : String) (n : Nat) (statement : Preterm)
    (witness : ProofWitness) : String :=
  "pub theorem " ++ name ++ printNatBinders n ++ ": $ " ++ printMath statement ++ " $ =\n'" ++
    printWitness extra witness ++ ";"

/-! ## Axiom audit -/

#print axioms encode_typed
#print axioms checks_trans
#print axioms checks_add
#print axioms checks_instance
#print axioms baseEntries_sound
#print axioms converts_eq
#print axioms derives_sound
#print axioms not_derives_one_add_zero_eq_zero
#print axioms root_consistent
#print axioms derives_value

end Mettapedia.Languages.MM0.PeanoEquationalFragment
