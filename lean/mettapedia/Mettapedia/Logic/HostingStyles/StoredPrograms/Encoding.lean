import Mettapedia.GSLT.Dedukti.ConfluenceApplied
import Mettapedia.GSLT.Dedukti.TableEvaluator
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataEquality
import Std.Data.String.ToNat

/-!
# Engine data as terms of the calculus

The equation engine computes on first-order terms: symbols, literals by their
spelling, variables, expressions and list values
(`DeterministicEquations.Term`).  A rule table computes on λΠ terms.  This
module reads the first as the second.

* A datum is read constructor by constructor (`datum`): a symbol, a literal
  or a variable is its kind applied to the writing of its name, an expression
  or a list value is its kind applied to the cells of its items.  The reading
  is the existing reading of engine data as patterns
  (`Authored.termPattern`), in λΠ terms.
* A literal that is the decimal writing of a number is read as that number in
  unary, marked as canonically written (`numeral`); another spelling of a
  number keeps its spelling beside the number, and a literal that is no
  number keeps its spelling alone (`literal`).  So a rule can compute with
  the number, and two literals have one reading only when they are one
  literal.
* How a name is written is a parameter (`Spelling`).  With a name written as
  a constant (`constantSpelling`) the reading of a symbol is its kind applied
  to one constant.
* A call is read apart from every datum: the constant `call` applied to the
  head and to the cells of the arguments (`callTerm`).  The number of
  arguments is in the cells, so a head needs no fixed arity, and a datum that
  has the shape of a call of the program, `(f a)`, is not a call.

The reading of data identifies no two data when the spelling identifies no
two names (`datum_injective`).  A datum is a passive term: it has no variable
and no binder, and no part of it is a call (`passive_datum`).  A passive term
has no step in any theory whose rules rewrite calls (`passive_normal`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (natural boolean)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule RootStep Step Reduces inst binderFree usesOnly)
open Mettapedia.Logic.Relation (IsNormal)

/-- A term of the equation engine: program text and data. -/
abbrev EngineTerm : Type := DeterministicEquations.Term

/-! ## Passive terms -/

/-- The constants that begin a redex of a stored table: `call` for a head of
the program or a primitive, `lib` for a helper of the table. -/
def redexKinds : List String := ["call", "lib"]

/-- Whether a term is a redex kind applied to something: the function part of
a redex of a stored table. -/
def opensRedex : LF.Term → Bool
  | .app (.con kind) _ => redexKinds.contains kind
  | _ => false

/-- **A passive term**: constants and applications, no part of which is a
redex kind applied to two terms. -/
def passive : LF.Term → Bool
  | .con _ => true
  | .app function argument => !opensRedex function && passive function && passive argument
  | _ => false

theorem passive_app {function argument : LF.Term} :
    passive (.app function argument) = true ↔
      opensRedex function = false ∧ passive function = true ∧ passive argument = true := by
  simp [passive, and_assoc]

/-- A passive term has no variable: instantiation leaves it as it is. -/
theorem inst_passive (assignment : Nat → LF.Term) :
    ∀ {term : LF.Term}, passive term = true → inst assignment term = term := by
  intro term
  induction term with
  | con name => intro _; rfl
  | app function argument ihFunction ihArgument =>
      intro quiet
      obtain ⟨-, functionQuiet, argumentQuiet⟩ := passive_app.mp quiet
      rw [Dedukti.inst_app, ihFunction functionQuiet, ihArgument argumentQuiet]
  | var index => intro quiet; simp [passive] at quiet
  | srt sort => intro quiet; simp [passive] at quiet
  | pi domain body _ _ => intro quiet; simp [passive] at quiet
  | lam domain body _ _ => intro quiet; simp [passive] at quiet

/-- A passive term has no binder. -/
theorem binderFree_passive : ∀ {term : LF.Term}, passive term = true → binderFree term = true := by
  intro term
  induction term with
  | con name => intro _; rfl
  | app function argument ihFunction ihArgument =>
      intro quiet
      obtain ⟨-, functionQuiet, argumentQuiet⟩ := passive_app.mp quiet
      simp [binderFree, ihFunction functionQuiet, ihArgument argumentQuiet]
  | var index => intro quiet; simp [passive] at quiet
  | srt sort => intro quiet; simp [passive] at quiet
  | pi domain body _ _ => intro quiet; simp [passive] at quiet
  | lam domain body _ _ => intro quiet; simp [passive] at quiet

/-- A passive term has no pattern variable. -/
theorem patternVars_passive :
    ∀ {term : LF.Term}, passive term = true → Dedukti.patternVars term = [] := by
  intro term
  induction term with
  | con name => intro _; rfl
  | app function argument ihFunction ihArgument =>
      intro quiet
      obtain ⟨-, functionQuiet, argumentQuiet⟩ := passive_app.mp quiet
      simp [Dedukti.patternVars, ihFunction functionQuiet, ihArgument argumentQuiet]
  | var index => intro quiet; simp [passive] at quiet
  | srt sort => intro quiet; simp [passive] at quiet
  | pi domain body _ _ => intro quiet; simp [passive] at quiet
  | lam domain body _ _ => intro quiet; simp [passive] at quiet

/-- A passive term uses no variable at all. -/
theorem usesOnly_passive (allowed : List Nat) (depth : Nat) :
    ∀ {term : LF.Term}, passive term = true → usesOnly allowed depth term = true := by
  intro term
  induction term with
  | con name => intro _; rfl
  | app function argument ihFunction ihArgument =>
      intro quiet
      obtain ⟨-, functionQuiet, argumentQuiet⟩ := passive_app.mp quiet
      simp [usesOnly, ihFunction functionQuiet, ihArgument argumentQuiet]
  | var index => intro quiet; simp [passive] at quiet
  | srt sort => intro quiet; simp [passive] at quiet
  | pi domain body _ _ => intro quiet; simp [passive] at quiet
  | lam domain body _ _ => intro quiet; simp [passive] at quiet

/-- **A rule that rewrites a call**: its left side is a redex kind applied to
a head and to one argument. -/
def rewritesCall (rule : RewriteRule) : Bool :=
  match rule.lhs with
  | .app (.app (.con kind) (.con _)) _ => redexKinds.contains kind
  | _ => false

theorem rewritesCall_shape {rule : RewriteRule} (rooted : rewritesCall rule = true) :
    ∃ kind head argument, rule.lhs = .app (.app (.con kind) (.con head)) argument ∧
      redexKinds.contains kind = true := by
  unfold rewritesCall at rooted
  split at rooted
  · next kind head argument same => exact ⟨kind, head, argument, same, rooted⟩
  · cases rooted

/-- **A passive term has no step** in a theory without definition whose rules
rewrite calls. -/
theorem passive_normal {theory : Theory} (undefined : ∀ name, theory.body name = none)
    (rooted : ∀ rule, theory.rule rule → rewritesCall rule = true) :
    ∀ term : LF.Term, passive term = true → IsNormal (Step theory) term := by
  intro term
  induction term with
  | con name =>
      intro _ target step
      rcases step.con_inv.con_inv with defined | ⟨rule, assignment, member, shape, -⟩
      · rw [undefined name] at defined
        cases defined
      · obtain ⟨kind, head, argument, same, -⟩ := rewritesCall_shape (rooted rule member)
        rw [same] at shape
        simp at shape
  | app function argument ihFunction ihArgument =>
      intro quiet target step
      obtain ⟨closed, functionQuiet, argumentQuiet⟩ := passive_app.mp quiet
      rcases step.app_inv with root | ⟨_, inner, -⟩ | ⟨_, inner, -⟩
      · generalize same : LF.Term.app function argument = source at root
        cases root with
        | beta domain body value =>
            cases same
            simp [passive] at functionQuiet
        | delta defined => cases same
        | @rule rule assignment member =>
            obtain ⟨kind, head, inner, shape, isKind⟩ := rewritesCall_shape (rooted rule member)
            rw [shape] at same
            simp only [Dedukti.inst_app, Dedukti.inst_con, LF.Term.app.injEq] at same
            rw [same.1] at closed
            simp only [opensRedex] at closed
            rw [isKind] at closed
            cases closed
      · exact ihFunction functionQuiet _ inner
      · exact ihArgument argumentQuiet _ inner
  | var index => intro quiet; simp [passive] at quiet
  | srt sort => intro quiet; simp [passive] at quiet
  | pi domain body _ _ => intro quiet; simp [passive] at quiet
  | lam domain body _ _ => intro quiet; simp [passive] at quiet

/-! ## Spellings -/

/-- **How a name is written as a term**: the name of a symbol, of a variable,
or the spelling of a literal.  What is written is passive. -/
structure Spelling where
  /-- The writing of a name. -/
  write : String → LF.Term
  /-- What is written is passive. -/
  quiet : ∀ name, passive (write name) = true

/-- **A name written as a constant.** -/
def constantSpelling : Spelling where
  write := .con
  quiet := fun _ => rfl

theorem constantSpelling_injective : Function.Injective constantSpelling.write :=
  fun _ _ same => LF.Term.con.inj same

/-! ## Cells, numbers, literals -/

/-- A kind applied to its content. -/
def tag (kind : String) (content : LF.Term) : LF.Term := .app (.con kind) content

/-- **The cells of a list of terms**: `nil`, and `cons` of a first term and
the cells of the rest. -/
def cells : List LF.Term → LF.Term
  | [] => .con "nil"
  | first :: rest => .app (.app (.con "cons") first) (cells rest)

/-- **A number in unary**: `zero`, and `succ` of a number. -/
def unary : Nat → LF.Term
  | 0 => .con "zero"
  | count + 1 => .app (.con "succ") (unary count)

/-- A number with the mark of how its literal is written. -/
def numbered (value : LF.Term) (mark : LF.Term) : LF.Term := .app (.app (.con "num") value) mark

/-- **The canonically written literal of a number**: the number in unary,
marked `canon`. -/
def numeral (value : Nat) : LF.Term := numbered (unary value) (.con "canon")

/-! ### Which literals spell a number

The host reads a literal as a number with `String.toNat?`.  That function does
not compute in the kernel, so a table whose rules mention a literal could not
be checked by computation.  `spelledNumber` is the same function
(`spelledNumber_eq_toNat?`), written on the list of characters. -/

/-- Whether two underscores are next to each other. -/
def doubledUnderscore : List Char → Bool
  | [] => false
  | first :: rest =>
      match rest with
      | [] => false
      | second :: _ => (first == '_' && second == '_') || doubledUnderscore rest

theorem doubledUnderscore_iff : ∀ characters : List Char,
    doubledUnderscore characters = true ↔ ['_', '_'] <:+: characters
  | [] => by simp [doubledUnderscore]
  | [first] => by
      simp only [doubledUnderscore, Bool.false_eq_true, false_iff]
      intro inside
      have short := inside.length_le
      simp at short
  | first :: second :: rest => by
      have inner := doubledUnderscore_iff (second :: rest)
      rw [List.infix_cons_iff, ← inner]
      simp only [doubledUnderscore, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        List.cons_prefix_cons, List.nil_prefix, and_true]
      exact or_congr_left ⟨fun both => ⟨both.1.symm, both.2.symm⟩,
        fun both => ⟨both.1.symm, both.2.symm⟩⟩

/-- **Whether the characters of a literal spell a number**, as the host reads
it: digits, with single underscores between them. -/
def spellsNumber (characters : List Char) : Bool :=
  !characters.isEmpty && characters.all (fun character => character.isDigit || character == '_') &&
    !doubledUnderscore characters && characters.head? != some '_' && characters.getLast? != some '_'

theorem spellsNumber_toList (spelling : String) : spellsNumber spelling.toList = spelling.isNat := by
  rw [Bool.eq_iff_iff, String.isNat_iff]
  simp only [spellsNumber, Bool.and_eq_true, Bool.not_eq_true', ne_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ← Bool.not_eq_true, doubledUnderscore_iff,
    List.isEmpty_iff, String.toList_eq_nil_iff, and_assoc]

/-- **The number that a literal spells**, if it spells one. -/
def spelledNumber (spelling : String) : Option Nat :=
  if spellsNumber spelling.toList then
    some (Nat.ofDigitChars 10 (spelling.toList.filter (· != '_')) 0)
  else none

/-- It is the number that the host reads. -/
theorem spelledNumber_eq_toNat? (spelling : String) : spelledNumber spelling = spelling.toNat? := by
  unfold spelledNumber
  rw [spellsNumber_toList]
  cases isNumber : spelling.isNat with
  | true => simp [String.toNat?_eq_some_ofDigitChars isNumber]
  | false => simp [String.toNat?_eq_none isNumber]

/-- **Positive**: `12` spells twelve, and so does `1_2`. -/
theorem spelledNumber_twelve : spelledNumber "12" = some 12 ∧ spelledNumber "1_2" = some 12 := by
  decide +kernel

/-- **Negative**: a name spells no number. -/
theorem spelledNumber_name : spelledNumber "mm0-hypothesis" = none := by decide +kernel

/-- **A literal**, by its spelling: the decimal writing of a number is that
number; another spelling of a number is the number with its spelling; a
spelling of no number is the spelling. -/
def literal (N : Spelling) (spelling : String) : LF.Term :=
  match spelledNumber spelling with
  | some value =>
      if value.repr = spelling then numeral value
      else numbered (unary value) (tag "spelled" (N.write spelling))
  | none => tag "lit" (N.write spelling)

theorem tag_injective {kind other : String} {content payload : LF.Term}
    (same : tag kind content = tag other payload) : kind = other ∧ content = payload := by
  simp only [tag, LF.Term.app.injEq, LF.Term.con.injEq] at same
  exact same

theorem cells_injective : ∀ {first second : List LF.Term}, cells first = cells second → first = second
  | [], [], _ => rfl
  | [], _ :: _, same => by simp [cells] at same
  | _ :: _, [], same => by simp [cells] at same
  | _ :: _, _ :: _, same => by
      simp only [cells, LF.Term.app.injEq, true_and] at same
      rw [same.1, cells_injective same.2]

theorem unary_injective : ∀ {first second : Nat}, unary first = unary second → first = second
  | 0, 0, _ => rfl
  | 0, _ + 1, same => by simp [unary] at same
  | _ + 1, 0, same => by simp [unary] at same
  | _ + 1, _ + 1, same => by
      simp only [unary, LF.Term.app.injEq, true_and] at same
      rw [unary_injective same]

theorem passive_tag {kind : String} {content : LF.Term} (quiet : passive content = true) :
    passive (tag kind content) = true := by
  simp [tag, passive, opensRedex, quiet]

theorem passive_cells : ∀ {items : List LF.Term}, (∀ item ∈ items, passive item = true) →
    passive (cells items) = true
  | [], _ => rfl
  | first :: rest, quiet => by
      have firstQuiet := quiet first (List.mem_cons_self ..)
      have restQuiet := passive_cells fun item member => quiet item (List.mem_cons_of_mem _ member)
      simp [cells, passive, opensRedex, redexKinds, firstQuiet, restQuiet]

theorem passive_unary : ∀ count : Nat, passive (unary count) = true
  | 0 => rfl
  | count + 1 => by simp [unary, passive, opensRedex, passive_unary count]

theorem passive_numbered {value mark : LF.Term} (valueQuiet : passive value = true)
    (markQuiet : passive mark = true) : passive (numbered value mark) = true := by
  simp [numbered, passive, opensRedex, redexKinds, valueQuiet, markQuiet]

theorem passive_numeral (value : Nat) : passive (numeral value) = true :=
  passive_numbered (passive_unary value) rfl

theorem passive_literal (N : Spelling) (spelling : String) : passive (literal N spelling) = true := by
  unfold literal
  split
  · split
    · exact passive_numeral _
    · exact passive_numbered (passive_unary _) (passive_tag (N.quiet spelling))
  · exact passive_tag (N.quiet spelling)

/-- The literal of a number, as the engine writes it, is the number. -/
theorem literal_repr (N : Spelling) (value : Nat) : literal N value.repr = numeral value := by
  simp [literal, spelledNumber_eq_toNat?, Nat.toNat?_repr]

/-- **Two literals with one reading are one literal.** -/
theorem literal_injective {N : Spelling} (injective : Function.Injective N.write)
    {first second : String} (same : literal N first = literal N second) : first = second := by
  unfold literal at same
  cases firstValue : spelledNumber first with
  | none =>
      cases secondValue : spelledNumber second with
      | none =>
          simp only [firstValue, secondValue] at same
          exact injective (tag_injective same).2
      | some other =>
          simp only [firstValue, secondValue] at same
          split at same <;> simp [numeral, numbered, tag] at same
  | some value =>
      cases secondValue : spelledNumber second with
      | none =>
          simp only [firstValue, secondValue] at same
          split at same <;> simp [numeral, numbered, tag] at same
      | some other =>
          simp only [firstValue, secondValue] at same
          split at same <;> split at same
          · next canonical otherCanonical =>
              simp only [numeral, numbered, LF.Term.app.injEq, and_true, true_and] at same
              rw [← canonical, ← otherCanonical, unary_injective same]
          · simp [numeral, numbered, tag] at same
          · simp [numeral, numbered, tag] at same
          · simp only [numbered, tag, LF.Term.app.injEq, true_and] at same
            exact injective same.2

/-! ## Data -/

mutual

/-- **A datum of the engine as a term**, constructor by constructor. -/
def datum (N : Spelling) : EngineTerm → LF.Term
  | .sym name => tag "sym" (N.write name)
  | .lit spelling => literal N spelling
  | .var name => tag "var" (N.write name)
  | .expr items => tag "expr" (cells (data N items))
  | .list items => tag "list" (cells (data N items))

/-- The data of a list, item by item. -/
def data (N : Spelling) : List EngineTerm → List LF.Term
  | [] => []
  | first :: rest => datum N first :: data N rest

end

theorem data_eq_map (N : Spelling) : ∀ items : List EngineTerm, data N items = items.map (datum N)
  | [] => rfl
  | first :: rest => by simp [data, data_eq_map N rest]

theorem data_length (N : Spelling) (items : List EngineTerm) :
    (data N items).length = items.length := by
  simp [data_eq_map]

mutual

/-- **A datum is passive.** -/
theorem passive_datum (N : Spelling) : ∀ term : EngineTerm, passive (datum N term) = true
  | .sym name => by simpa [datum] using passive_tag (N.quiet name)
  | .lit spelling => by simpa [datum] using passive_literal N spelling
  | .var name => by simpa [datum] using passive_tag (N.quiet name)
  | .expr items => by simpa [datum] using passive_tag (passive_cells (passive_data N items))
  | .list items => by simpa [datum] using passive_tag (passive_cells (passive_data N items))

theorem passive_data (N : Spelling) :
    ∀ items : List EngineTerm, ∀ item ∈ data N items, passive item = true
  | [] => by simp [data]
  | first :: rest => by
      intro item member
      simp only [data, List.mem_cons] at member
      rcases member with rfl | later
      · exact passive_datum N first
      · exact passive_data N rest item later

end

/-- A datum has no variable. -/
theorem inst_datum (N : Spelling) (assignment : Nat → LF.Term) (term : EngineTerm) :
    inst assignment (datum N term) = datum N term :=
  inst_passive assignment (passive_datum N term)

/-- A literal has no variable. -/
theorem inst_literal (N : Spelling) (assignment : Nat → LF.Term) (spelling : String) :
    inst assignment (literal N spelling) = literal N spelling :=
  inst_passive assignment (passive_literal N spelling)

/-- What is written has no variable. -/
theorem inst_write (N : Spelling) (assignment : Nat → LF.Term) (name : String) :
    inst assignment (N.write name) = N.write name :=
  inst_passive assignment (N.quiet name)

/-- A literal that is a number is read apart from every kind applied to a
content. -/
theorem literal_ne_tag (N : Spelling) {spelling kind : String} {content : LF.Term}
    (other : kind ≠ "lit") : literal N spelling ≠ tag kind content := by
  unfold literal
  split
  · split <;> simp [numeral, numbered, tag]
  · intro same
    exact other (tag_injective same).1.symm

mutual

/-- **The reading of data identifies no two data**, when the spelling
identifies no two names. -/
theorem datum_injective {N : Spelling} (injective : Function.Injective N.write) :
    ∀ {first second : EngineTerm}, datum N first = datum N second → first = second
  | .sym _, .sym _, same => by
      simp only [datum] at same
      rw [injective (tag_injective same).2]
  | .lit _, .lit _, same => by
      simp only [datum] at same
      rw [literal_injective injective same]
  | .var _, .var _, same => by
      simp only [datum] at same
      rw [injective (tag_injective same).2]
  | .expr _, .expr _, same => by
      simp only [datum] at same
      rw [data_injective injective (cells_injective (tag_injective same).2)]
  | .list _, .list _, same => by
      simp only [datum] at same
      rw [data_injective injective (cells_injective (tag_injective same).2)]
  | .lit _, .sym _, same => absurd (by simpa [datum] using same) (literal_ne_tag N (by decide))
  | .lit _, .var _, same => absurd (by simpa [datum] using same) (literal_ne_tag N (by decide))
  | .lit _, .expr _, same => absurd (by simpa [datum] using same) (literal_ne_tag N (by decide))
  | .lit _, .list _, same => absurd (by simpa [datum] using same) (literal_ne_tag N (by decide))
  | .sym _, .lit _, same =>
      absurd (by simpa [datum] using same.symm) (literal_ne_tag N (by decide))
  | .var _, .lit _, same =>
      absurd (by simpa [datum] using same.symm) (literal_ne_tag N (by decide))
  | .expr _, .lit _, same =>
      absurd (by simpa [datum] using same.symm) (literal_ne_tag N (by decide))
  | .list _, .lit _, same =>
      absurd (by simpa [datum] using same.symm) (literal_ne_tag N (by decide))
  | .sym _, .var _, same | .sym _, .expr _, same | .sym _, .list _, same
  | .var _, .sym _, same | .var _, .expr _, same | .var _, .list _, same
  | .expr _, .sym _, same | .expr _, .var _, same | .expr _, .list _, same
  | .list _, .sym _, same | .list _, .var _, same | .list _, .expr _, same => by
      simp [datum, tag] at same

theorem data_injective {N : Spelling} (injective : Function.Injective N.write) :
    ∀ {first second : List EngineTerm}, data N first = data N second → first = second
  | [], [], _ => rfl
  | [], _ :: _, same => by simp [data] at same
  | _ :: _, [], same => by simp [data] at same
  | _ :: _, _ :: _, same => by
      simp only [data, List.cons.injEq] at same
      rw [datum_injective injective same.1, data_injective injective same.2]

end

/-! ## The readings of the engine's numbers and truth values -/

theorem datum_natural (N : Spelling) (value : Nat) : datum N (natural value) = numeral value := by
  simp [natural, datum, literal_repr]

theorem datum_boolean (N : Spelling) (value : Bool) :
    datum N (boolean value) = tag "sym" (N.write (if value then "True" else "False")) := by
  simp [boolean, datum]

/-! ## Calls -/

/-- **A call of a head on arguments**: the constant `call`, the head, and the
cells of the arguments. -/
def callTerm (head : String) (arguments : List LF.Term) : LF.Term :=
  .app (.app (.con "call") (.con head)) (cells arguments)

/-- **A call of a helper of a table**: the constant `lib`, the helper, and
the cells of the arguments. -/
def libTerm (head : String) (arguments : List LF.Term) : LF.Term :=
  .app (.app (.con "lib") (.con head)) (cells arguments)

/-- **Negative**: a call is not passive. -/
theorem callTerm_not_passive (head : String) (arguments : List LF.Term) :
    passive (callTerm head arguments) = false := by
  simp [callTerm, passive, opensRedex, redexKinds]

/-- **A datum is no call**, whatever its shape: the datum `(f a)` and the call
of `f` on `a` are two terms. -/
theorem datum_ne_callTerm (N : Spelling) (term : EngineTerm) (head : String)
    (arguments : List LF.Term) : datum N term ≠ callTerm head arguments := by
  intro same
  have quiet := passive_datum N term
  rw [same, callTerm_not_passive] at quiet
  cases quiet

/-- **A datum has no step** in a theory without definition whose rules
rewrite calls. -/
theorem datum_normal {theory : Theory} (undefined : ∀ name, theory.body name = none)
    (rooted : ∀ rule, theory.rule rule → rewritesCall rule = true) (N : Spelling)
    (term : EngineTerm) : IsNormal (Step theory) (datum N term) :=
  passive_normal undefined rooted _ (passive_datum N term)

/-! ## Reduction inside cells, kinds and calls -/

theorem reduces_tag {theory : Theory} (kind : String) {source target : LF.Term}
    (reduces : Reduces theory source target) :
    Reduces theory (tag kind source) (tag kind target) :=
  Dedukti.Reduces.app .refl reduces

theorem reduces_cells {theory : Theory} : ∀ {sources targets : List LF.Term},
    List.Forall₂ (Reduces theory) sources targets → Reduces theory (cells sources) (cells targets)
  | _, _, .nil => .refl
  | _, _, .cons first rest =>
      Dedukti.Reduces.app (Dedukti.Reduces.app .refl first) (reduces_cells rest)

theorem reduces_callTerm {theory : Theory} (head : String) {sources targets : List LF.Term}
    (reduces : List.Forall₂ (Reduces theory) sources targets) :
    Reduces theory (callTerm head sources) (callTerm head targets) :=
  Dedukti.Reduces.app .refl (reduces_cells reduces)

theorem reduces_libTerm {theory : Theory} (head : String) {sources targets : List LF.Term}
    (reduces : List.Forall₂ (Reduces theory) sources targets) :
    Reduces theory (libTerm head sources) (libTerm head targets) :=
  Dedukti.Reduces.app .refl (reduces_cells reduces)

theorem inst_tag (assignment : Nat → LF.Term) (kind : String) (content : LF.Term) :
    inst assignment (tag kind content) = tag kind (inst assignment content) := rfl

theorem inst_cells (assignment : Nat → LF.Term) : ∀ items : List LF.Term,
    inst assignment (cells items) = cells (items.map (inst assignment))
  | [] => rfl
  | first :: rest => by
      rw [cells, Dedukti.inst_app, Dedukti.inst_app, Dedukti.inst_con, inst_cells assignment rest]
      rfl

theorem inst_callTerm (assignment : Nat → LF.Term) (head : String) (arguments : List LF.Term) :
    inst assignment (callTerm head arguments) =
      callTerm head (arguments.map (inst assignment)) := by
  rw [callTerm, Dedukti.inst_app, inst_cells]
  rfl

theorem inst_libTerm (assignment : Nat → LF.Term) (head : String) (arguments : List LF.Term) :
    inst assignment (libTerm head arguments) = libTerm head (arguments.map (inst assignment)) := by
  rw [libTerm, Dedukti.inst_app, inst_cells]
  rfl

#print axioms inst_passive
#print axioms passive_normal
#print axioms literal_injective
#print axioms passive_datum
#print axioms datum_injective
#print axioms datum_natural
#print axioms datum_ne_callTerm
#print axioms datum_normal
#print axioms reduces_cells

end Mettapedia.Logic.HostingStyles.StoredPrograms
