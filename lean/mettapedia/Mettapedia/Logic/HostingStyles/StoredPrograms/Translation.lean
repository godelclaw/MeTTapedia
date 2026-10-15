import Mettapedia.Logic.HostingStyles.StoredPrograms.Encoding
import Mettapedia.Logic.HostingStyles.AtomsReduce.Programs
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Typing
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListAppendProgram

/-!
# An equation program as a rule table

An equation of the engine is read as one rewrite rule, and a program as the
list of the rules of its equations (`programRules`).

* The left side of the rule of `f p₁ … pₙ = r` is the call of `f` on the
  patterns (`ruleOf`).  A pattern is read as a datum, with a variable read
  as a pattern variable: the position of its first occurrence in the left
  side (`pattern`, `slots`).
* The right side is read as the engine evaluates it (`body`): a variable is
  the pattern variable of its name, a list value is its kind on the cells of
  its items, and an expression whose head is a symbol is a **call** when the
  program defines the symbol or the symbol is one of the primitives that the
  table computes by rules, and a **datum** otherwise (`expression`,
  `isCalled`).  The evaluator decides this when it runs; the table decides
  it when it is written.

## The class

`Storable program host primitives` states when the table reads the program as
the engine does.

* No variable occurs twice in a left side.  The engine binds a repeated
  variable at its first occurrence and does not compare the two values; a
  rule compares them.
* No right side has a special form: `let` on three arguments or
  `metta-nullary` on one.  A `let` binds, and a rule whose right side binds is
  not applied by the candidate (`AtomsReduce.bindingRule_not_preserved`), so a
  program with a `let` is outside the class (`withLet_not_storable`).
* The variables of a right side are among those of its left side.
* The host handles a head that a right side calls exactly when the head is
  one of the `primitives`.  With no primitive, this is: **the program calls no
  primitive of the host** (`Storable program host []`).

**One arity for a head is not asked.**  A call carries its arguments in cells,
so the equations of one head at two arities are rules that no call matches
both.

The table of a program whose right sides are bound is a table of first-order
rules with bound right sides (`programRules_runnable`).

Positive: unary addition (`additionProgram_storable`), whose table is two
rules.  Negative: list append under the shared host, which calls the list
view (`listAppend_not_hostFree`); a `let` (`withLet_not_storable`); a repeated
variable (`repeated_not_storable`); an unbound right side
(`unbound_not_storable`, `unbound_not_runnable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env Special LeftLinear patternVarsList computationalHost listAppendProgram)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.TypingExamples (noPrimitives)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule RootStep Step Reduces inst binderFree usesOnly)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-! ## Patterns -/

/-- **The slots of an equation**: the variables of its left side, in order.
The pattern variable of a name is the position of its first occurrence. -/
def slots (equation : Equation) : List String := patternVarsList equation.params

mutual

/-- **A pattern of an equation as a term**: a datum, with each variable read
as the pattern variable of its name. -/
def pattern (N : Spelling) (names : List String) : EngineTerm → LF.Term
  | .var name => .var (names.idxOf name)
  | .sym name => tag "sym" (N.write name)
  | .lit spelling => literal N spelling
  | .expr items => tag "expr" (cells (patterns N names items))
  | .list items => tag "list" (cells (patterns N names items))

/-- The patterns of a list, item by item. -/
def patterns (N : Spelling) (names : List String) : List EngineTerm → List LF.Term
  | [] => []
  | first :: rest => pattern N names first :: patterns N names rest

end

/-! ## Right sides -/

/-- **Whether a head is called**: the program defines it, or it is one of the
primitives that the table computes by rules.  Any other symbol at the head of
an expression builds a datum. -/
def isCalled (program : Program) (primitives : List String) (head : String) : Bool :=
  program.defines head || primitives.contains head

/-- **An expression of a right side**, from its items and their readings: a
call of its head symbol when that symbol is called, and the datum of its
items otherwise. -/
def expression (called : String → Bool) (items : List EngineTerm) (readings : List LF.Term) :
    LF.Term :=
  match items with
  | .sym head :: _ => if called head then callTerm head readings.tail else tag "expr" (cells readings)
  | _ => tag "expr" (cells readings)

mutual

/-- **A right side as a term**, read as the engine evaluates it. -/
def body (N : Spelling) (called : String → Bool) (names : List String) : EngineTerm → LF.Term
  | .var name => .var (names.idxOf name)
  | .sym name => tag "sym" (N.write name)
  | .lit spelling => literal N spelling
  | .list items => tag "list" (cells (bodies N called names items))
  | .expr items => expression called items (bodies N called names items)

/-- The right sides of a list, item by item. -/
def bodies (N : Spelling) (called : String → Bool) (names : List String) :
    List EngineTerm → List LF.Term
  | [] => []
  | first :: rest => body N called names first :: bodies N called names rest

end

theorem bodies_length (N : Spelling) (called : String → Bool) (names : List String) :
    ∀ items : List EngineTerm, (bodies N called names items).length = items.length
  | [] => rfl
  | _ :: rest => by simp [bodies, bodies_length N called names rest]

/-! ## Rules and tables -/

/-- **The rule of an equation**: the call of its head on its patterns
rewrites to its right side. -/
def ruleOf (N : Spelling) (called : String → Bool) (equation : Equation) : RewriteRule :=
  ⟨callTerm equation.head (patterns N (slots equation) equation.params),
    body N called (slots equation) equation.body⟩

/-- **The table of a program**: the rules of its equations, in the order of
the equations.  `primitives` are the heads that further rules compute. -/
def programRules (N : Spelling) (program : Program) (primitives : List String) :
    List RewriteRule :=
  program.map (ruleOf N (isCalled program primitives))

theorem ruleOf_mem {N : Spelling} {program : Program} {primitives : List String}
    {equation : Equation} (member : equation ∈ program) :
    ruleOf N (isCalled program primitives) equation ∈ programRules N program primitives :=
  List.mem_map_of_mem member

/-- The rule of an equation rewrites a call. -/
theorem ruleOf_rewritesCall (N : Spelling) (called : String → Bool) (equation : Equation) :
    rewritesCall (ruleOf N called equation) = true := rfl

theorem programRules_rewriteCalls (N : Spelling) (program : Program) (primitives : List String) :
    ∀ rule ∈ programRules N program primitives, rewritesCall rule = true := by
  intro rule member
  obtain ⟨equation, -, rfl⟩ := List.mem_map.mp member
  exact ruleOf_rewritesCall N _ equation

/-! ## The class -/

/-- Whether the head of an expression is no special form of the evaluator. -/
def ordinaryHead : List EngineTerm → Bool
  | .sym head :: arguments => !decide (Special head arguments)
  | _ => true

mutual

/-- **A term without special form**: no `let` on three arguments and no
`metta-nullary` on one, at any depth. -/
def ordinary : EngineTerm → Bool
  | .expr items => ordinaryHead items && ordinaryList items
  | .list items => ordinaryList items
  | _ => true

def ordinaryList : List EngineTerm → Bool
  | [] => true
  | first :: rest => ordinary first && ordinaryList rest

end

theorem ordinaryList_mem : ∀ {items : List EngineTerm}, ordinaryList items = true →
    ∀ item ∈ items, ordinary item = true
  | [], _, _, member => by cases member
  | first :: rest, plain, item, member => by
      simp only [ordinaryList, Bool.and_eq_true] at plain
      rcases List.mem_cons.mp member with rfl | later
      · exact plain.1
      · exact ordinaryList_mem plain.2 item later

theorem ordinary_expr {items : List EngineTerm} (plain : ordinary (.expr items) = true) :
    ordinaryHead items = true ∧ ∀ item ∈ items, ordinary item = true := by
  simp only [ordinary, Bool.and_eq_true] at plain
  exact ⟨plain.1, ordinaryList_mem plain.2⟩

theorem ordinary_list {items : List EngineTerm} (plain : ordinary (.list items) = true) :
    ∀ item ∈ items, ordinary item = true := by
  simp only [ordinary] at plain
  exact ordinaryList_mem plain

/-- **A bound right side**: every variable of the right side of the equation
is a variable of its left side. -/
def boundRight (equation : Equation) : Bool :=
  (DeterministicEquations.patternVars equation.body).all fun name => (slots equation).contains name

/-- **The class of programs that a table reads as the engine does**, for a
host and the primitives of it that the table computes by rules. -/
structure Storable (program : Program) (host : Host) (primitives : List String) : Prop where
  /-- No variable occurs twice in a left side. -/
  leftLinear : LeftLinear program
  /-- No right side has a special form. -/
  ordinary : ∀ equation ∈ program, ordinary equation.body = true
  /-- The variables of a right side are among those of its left side. -/
  bound : ∀ equation ∈ program, boundRight equation = true
  /-- The host handles every primitive that the table computes. -/
  handled : ∀ head ∈ primitives, ∀ arguments, host.primitive head arguments ≠ .unhandled
  /-- The host handles no other head that a right side calls and the program
  does not define. -/
  constructs : ∀ head ∈ program.calledHeads, program.defines head = false → head ∉ primitives →
    ∀ arguments, host.primitive head arguments = .unhandled

/-- **The part of the class that is read off the program text.** -/
def storableText (program : Program) : Bool :=
  program.all fun equation =>
    decide (patternVarsList equation.params).Nodup && ordinary equation.body &&
      boundRight equation

theorem storableText_iff (program : Program) :
    storableText program = true ↔
      LeftLinear program ∧ (∀ equation ∈ program, ordinary equation.body = true) ∧
        ∀ equation ∈ program, boundRight equation = true := by
  simp only [storableText, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, LeftLinear]
  exact ⟨fun each => ⟨fun equation member => (each equation member).1.1,
      fun equation member => (each equation member).1.2,
      fun equation member => (each equation member).2⟩,
    fun parts equation member =>
      ⟨⟨parts.1 equation member, parts.2.1 equation member⟩, parts.2.2 equation member⟩⟩

/-- **A program that calls no primitive of its host**: the host handles no
head that a right side calls and the program does not define. -/
def HostFree (program : Program) (host : Host) : Prop :=
  ∀ head ∈ program.calledHeads, program.defines head = false →
    ∀ arguments, host.primitive head arguments = .unhandled

/-- The class without primitives, from the program text and a host that the
program does not call. -/
theorem Storable.of_text {program : Program} {host : Host} (text : storableText program = true)
    (hostFree : HostFree program host) : Storable program host [] where
  leftLinear := ((storableText_iff program).mp text).1
  ordinary := ((storableText_iff program).mp text).2.1
  bound := ((storableText_iff program).mp text).2.2
  handled := fun _ member => absurd member List.not_mem_nil
  constructs := fun head called undefined _ => hostFree head called undefined

theorem Storable.hostFree {program : Program} {host : Host}
    (storable : Storable program host []) : HostFree program host :=
  fun head called undefined => storable.constructs head called undefined List.not_mem_nil

/-- Every program is host-free under the host without primitives. -/
theorem hostFree_noPrimitives (program : Program) : HostFree program noPrimitives :=
  fun _ _ _ _ => rfl

/-! ## The table of a program has first-order rules with bound right sides -/

theorem binderFree_tag {kind : String} {content : LF.Term} (free : binderFree content = true) :
    binderFree (tag kind content) = true := by
  simp [tag, binderFree, free]

theorem binderFree_cells : ∀ {items : List LF.Term}, (∀ item ∈ items, binderFree item = true) →
    binderFree (cells items) = true
  | [], _ => rfl
  | first :: rest, free => by
      have firstFree := free first (List.mem_cons_self ..)
      have restFree := binderFree_cells fun item member => free item (List.mem_cons_of_mem _ member)
      simp [cells, binderFree, firstFree, restFree]

theorem binderFree_callTerm {head : String} {arguments : List LF.Term}
    (free : ∀ argument ∈ arguments, binderFree argument = true) :
    binderFree (callTerm head arguments) = true := by
  simp [callTerm, binderFree, binderFree_cells free]

mutual

theorem binderFree_pattern (N : Spelling) (names : List String) :
    ∀ term : EngineTerm, binderFree (pattern N names term) = true
  | .var _ => rfl
  | .sym name => by simpa [pattern] using binderFree_tag (binderFree_passive (N.quiet name))
  | .lit spelling => by simpa [pattern] using binderFree_passive (passive_literal N spelling)
  | .expr items => by
      simpa [pattern] using binderFree_tag (binderFree_cells (binderFree_patterns N names items))
  | .list items => by
      simpa [pattern] using binderFree_tag (binderFree_cells (binderFree_patterns N names items))

theorem binderFree_patterns (N : Spelling) (names : List String) :
    ∀ items : List EngineTerm, ∀ item ∈ patterns N names items, binderFree item = true
  | [] => by simp [patterns]
  | first :: rest => by
      intro item member
      simp only [patterns, List.mem_cons] at member
      rcases member with rfl | later
      · exact binderFree_pattern N names first
      · exact binderFree_patterns N names rest item later

end

theorem binderFree_expression (called : String → Bool) (items : List EngineTerm)
    {readings : List LF.Term} (free : ∀ reading ∈ readings, binderFree reading = true) :
    binderFree (expression called items readings) = true := by
  unfold expression
  split
  · split
    · exact binderFree_callTerm fun argument member => free argument (List.mem_of_mem_tail member)
    · exact binderFree_tag (binderFree_cells free)
  · exact binderFree_tag (binderFree_cells free)

mutual

theorem binderFree_body (N : Spelling) (called : String → Bool) (names : List String) :
    ∀ term : EngineTerm, binderFree (body N called names term) = true
  | .var _ => rfl
  | .sym name => by simpa [body] using binderFree_tag (binderFree_passive (N.quiet name))
  | .lit spelling => by simpa [body] using binderFree_passive (passive_literal N spelling)
  | .list items => by
      simpa [body] using binderFree_tag (binderFree_cells (binderFree_bodies N called names items))
  | .expr items => by
      simpa [body] using binderFree_expression called items (binderFree_bodies N called names items)

theorem binderFree_bodies (N : Spelling) (called : String → Bool) (names : List String) :
    ∀ items : List EngineTerm, ∀ item ∈ bodies N called names items, binderFree item = true
  | [] => by simp [bodies]
  | first :: rest => by
      intro item member
      simp only [bodies, List.mem_cons] at member
      rcases member with rfl | later
      · exact binderFree_body N called names first
      · exact binderFree_bodies N called names rest item later

end

theorem patternVars_tag (kind : String) (content : LF.Term) :
    Dedukti.patternVars (tag kind content) = Dedukti.patternVars content := by
  simp [tag, Dedukti.patternVars]

theorem patternVars_cells : ∀ items : List LF.Term,
    Dedukti.patternVars (cells items) = items.flatMap Dedukti.patternVars
  | [] => rfl
  | first :: rest => by
      simp [cells, Dedukti.patternVars, patternVars_cells rest]

mutual

/-- **The pattern variables of a pattern** are the positions of its
variables. -/
theorem patternVars_pattern (N : Spelling) (names : List String) :
    ∀ term : EngineTerm, Dedukti.patternVars (pattern N names term) =
      (DeterministicEquations.patternVars term).map names.idxOf
  | .var name => by simp [pattern, Dedukti.patternVars, DeterministicEquations.patternVars]
  | .sym name => by
      simp [pattern, patternVars_tag, patternVars_passive (N.quiet name),
        DeterministicEquations.patternVars]
  | .lit spelling => by
      simp [pattern, patternVars_passive (passive_literal N spelling),
        DeterministicEquations.patternVars]
  | .expr items => by
      simp [pattern, patternVars_tag, patternVars_cells, patternVars_patterns N names items,
        DeterministicEquations.patternVars]
  | .list items => by
      simp [pattern, patternVars_tag, patternVars_cells, patternVars_patterns N names items,
        DeterministicEquations.patternVars]

theorem patternVars_patterns (N : Spelling) (names : List String) :
    ∀ items : List EngineTerm, (patterns N names items).flatMap Dedukti.patternVars =
      (patternVarsList items).map names.idxOf
  | [] => by simp [patterns, patternVarsList]
  | first :: rest => by
      simp [patterns, patternVarsList, patternVars_pattern N names first,
        patternVars_patterns N names rest]

end

/-- The pattern variables of the left side of the rule of an equation are the
positions of its slots. -/
theorem patternVars_ruleOf (N : Spelling) (called : String → Bool) (equation : Equation) :
    Dedukti.patternVars (ruleOf N called equation).lhs =
      (slots equation).map (slots equation).idxOf := by
  simp [ruleOf, callTerm, Dedukti.patternVars, patternVars_cells, patternVars_patterns, slots]

theorem usesOnly_tag {allowed : List Nat} {depth : Nat} {kind : String} {content : LF.Term}
    (uses : usesOnly allowed depth content = true) :
    usesOnly allowed depth (tag kind content) = true := by
  simp [tag, usesOnly, uses]

theorem usesOnly_cells {allowed : List Nat} {depth : Nat} : ∀ {items : List LF.Term},
    (∀ item ∈ items, usesOnly allowed depth item = true) →
      usesOnly allowed depth (cells items) = true
  | [], _ => rfl
  | first :: rest, uses => by
      have firstUses := uses first (List.mem_cons_self ..)
      have restUses := usesOnly_cells fun item member => uses item (List.mem_cons_of_mem _ member)
      simp [cells, usesOnly, firstUses, restUses]

theorem usesOnly_callTerm {allowed : List Nat} {depth : Nat} {head : String}
    {arguments : List LF.Term} (uses : ∀ argument ∈ arguments, usesOnly allowed depth argument = true) :
    usesOnly allowed depth (callTerm head arguments) = true := by
  simp [callTerm, usesOnly, usesOnly_cells uses]

theorem usesOnly_expression {allowed : List Nat} {depth : Nat} (called : String → Bool)
    (items : List EngineTerm) {readings : List LF.Term}
    (uses : ∀ reading ∈ readings, usesOnly allowed depth reading = true) :
    usesOnly allowed depth (expression called items readings) = true := by
  unfold expression
  split
  · split
    · exact usesOnly_callTerm fun argument member => uses argument (List.mem_of_mem_tail member)
    · exact usesOnly_tag (usesOnly_cells uses)
  · exact usesOnly_tag (usesOnly_cells uses)

mutual

/-- A right side uses only the pattern variables of its names. -/
theorem usesOnly_body (N : Spelling) (called : String → Bool) (names : List String)
    (allowed : List Nat) :
    ∀ term : EngineTerm,
      (∀ name ∈ DeterministicEquations.patternVars term, names.idxOf name ∈ allowed) →
        usesOnly allowed 0 (body N called names term) = true
  | .var name, within => by
      simpa [body, usesOnly] using within name (by simp [DeterministicEquations.patternVars])
  | .sym name, _ => by
      simpa [body] using usesOnly_tag (usesOnly_passive allowed 0 (N.quiet name))
  | .lit spelling, _ => by
      simpa [body] using usesOnly_passive allowed 0 (passive_literal N spelling)
  | .list items, within => by
      have inner := usesOnly_bodies N called names allowed items
        (by simpa [DeterministicEquations.patternVars] using within)
      simpa [body] using usesOnly_tag (usesOnly_cells inner)
  | .expr items, within => by
      have inner := usesOnly_bodies N called names allowed items
        (by simpa [DeterministicEquations.patternVars] using within)
      simpa [body] using usesOnly_expression called items inner

theorem usesOnly_bodies (N : Spelling) (called : String → Bool) (names : List String)
    (allowed : List Nat) :
    ∀ items : List EngineTerm, (∀ name ∈ patternVarsList items, names.idxOf name ∈ allowed) →
      ∀ item ∈ bodies N called names items, usesOnly allowed 0 item = true
  | [], _ => by simp [bodies]
  | first :: rest, within => by
      intro item member
      simp only [bodies, List.mem_cons] at member
      simp only [patternVarsList, List.mem_append] at within
      rcases member with rfl | later
      · exact usesOnly_body N called names allowed first fun name found => within name (.inl found)
      · exact usesOnly_bodies N called names allowed rest
          (fun name found => within name (.inr found)) item later

end

/-- **The rule of an equation with a bound right side is first-order with a
bound right side.** -/
theorem ruleOf_runnable (N : Spelling) (called : String → Bool) {equation : Equation}
    (bound : boundRight equation = true) :
    (binderFree (ruleOf N called equation).lhs = true ∧
        binderFree (ruleOf N called equation).rhs = true) ∧
      usesOnly (Dedukti.patternVars (ruleOf N called equation).lhs) 0
        (ruleOf N called equation).rhs = true := by
  refine ⟨⟨binderFree_callTerm (binderFree_patterns N _ _), binderFree_body N called _ _⟩, ?_⟩
  rw [patternVars_ruleOf]
  refine usesOnly_body N called _ _ _ fun name found => ?_
  simp only [boundRight, List.all_eq_true, List.contains_iff_mem] at bound
  exact List.mem_map_of_mem (bound name found)

/-- **The table of a program whose right sides are bound is a table of
first-order rules with bound right sides**: the equations that a space of the
candidate runs. -/
theorem programRules_runnable (N : Spelling) {program : Program} (primitives : List String)
    (bound : ∀ equation ∈ program, boundRight equation = true) :
    RunnableEquations (programRules N program primitives) := by
  constructor
  · intro rule member
    obtain ⟨equation, inProgram, rfl⟩ := List.mem_map.mp member
    exact (ruleOf_runnable N _ (bound equation inProgram)).1
  · intro rule member
    obtain ⟨equation, inProgram, rfl⟩ := List.mem_map.mp member
    exact (ruleOf_runnable N _ (bound equation inProgram)).2

theorem Storable.runnable (N : Spelling) {program : Program} {host : Host}
    {primitives : List String} (storable : Storable program host primitives) :
    RunnableEquations (programRules N program primitives) :=
  programRules_runnable N primitives storable.bound

/-! ## A positive program: unary addition -/

/-- **Unary addition as an equation program**:
`(add Z y) = y` and `(add (S x) y) = (S (add x y))`. -/
def additionProgram : Program := [
  ⟨"add-zero", "add", [.sym "Z", .var "y"], .var "y"⟩,
  ⟨"add-succ", "add", [.expr [.sym "S", .var "x"], .var "y"],
    .expr [.sym "S", .expr [.sym "add", .var "x", .var "y"]]⟩]

/-- **Positive**: unary addition is in the class, under the host without
primitives. -/
theorem additionProgram_storable : Storable additionProgram noPrimitives [] :=
  .of_text (by decide) (hostFree_noPrimitives _)

/-- **Its table**, with names written as constants: the call of `add` on
`Z` and a term rewrites to the term, and the call of `add` on `(S x)` and `y`
rewrites to the datum `(S …)` of the call of `add` on `x` and `y`. -/
theorem additionProgram_rules :
    programRules constantSpelling additionProgram [] =
      [⟨callTerm "add" [tag "sym" (.con "Z"), .var 0], .var 0⟩,
        ⟨callTerm "add" [tag "expr" (cells [tag "sym" (.con "S"), .var 0]), .var 1],
          tag "expr" (cells [tag "sym" (.con "S"), callTerm "add" [.var 0, .var 1]])⟩] := by
  decide

/-- The table of unary addition is orthogonal. -/
theorem additionProgram_orthogonal :
    Dedukti.orthogonalCheck (programRules constantSpelling additionProgram []) = true := by
  decide

/-! ## Negative programs -/

/-- **Negative**: list append calls the list view, a primitive of the shared
host. -/
theorem listAppend_not_hostFree : ¬ HostFree listAppendProgram computationalHost := by
  intro hostFree
  have unhandled := hostFree "nik:list-view" (by decide) (by decide) [.list []]
  cases unhandled

/-- So list append is outside the class without primitives. -/
theorem listAppend_not_storable : ¬ Storable listAppendProgram computationalHost [] :=
  fun storable => listAppend_not_hostFree storable.hostFree

/-- A program with a `let`: `(twice x) = (let y x (pair y y))`. -/
def withLet : Program := [
  ⟨"twice", "twice", [.var "x"],
    .expr [.sym "let", .var "y", .var "x", .expr [.sym "pair", .var "y", .var "y"]]⟩]

/-- **Negative**: a program with a `let` is outside the class, under every
host and for every list of primitives. -/
theorem withLet_not_storable (host : Host) (primitives : List String) :
    ¬ Storable withLet host primitives := by
  intro storable
  have plain := storable.ordinary _ (List.mem_singleton.mpr rfl)
  revert plain
  decide

/-- A program with a repeated variable: `(same x x) = x`. -/
def repeated : Program := [⟨"same", "same", [.var "x", .var "x"], .var "x"⟩]

/-- **Negative**: a program with a repeated variable is outside the class. -/
theorem repeated_not_storable (host : Host) (primitives : List String) :
    ¬ Storable repeated host primitives := by
  intro storable
  have linear := storable.leftLinear _ (List.mem_singleton.mpr rfl)
  revert linear
  decide

/-- A program with an unbound right side: `(any) = x`. -/
def unbound : Program := [⟨"any", "any", [], .var "x"⟩]

/-- **Negative**: a program with an unbound right side is outside the
class. -/
theorem unbound_not_storable (host : Host) (primitives : List String) :
    ¬ Storable unbound host primitives := by
  intro storable
  have bound := storable.bound _ (List.mem_singleton.mpr rfl)
  revert bound
  decide

/-- And its table is no table that a space of the candidate runs. -/
theorem unbound_not_runnable : ¬ RunnableEquations (programRules constantSpelling unbound []) := by
  intro runnable
  have bound := runnable.2 _ (List.mem_singleton.mpr rfl)
  revert bound
  decide

#print axioms patternVars_ruleOf
#print axioms ruleOf_runnable
#print axioms programRules_runnable
#print axioms Storable.runnable
#print axioms additionProgram_storable
#print axioms additionProgram_rules
#print axioms additionProgram_orthogonal
#print axioms listAppend_not_hostFree
#print axioms withLet_not_storable
#print axioms repeated_not_storable
#print axioms unbound_not_storable
#print axioms unbound_not_runnable

end Mettapedia.Logic.HostingStyles.StoredPrograms
