import Mettapedia.Languages.MM0.Kernel.FirstOrderTheories
import Mettapedia.Computability.ElementaryFormalSystems

/-!
# The theorems of a first-order MM0 theory are recursively enumerable

Every first-order MM0 theory, in any fixed context and under any fixed list
of hypotheses, is compiled to an elementary formal system. Expressions are
written in a prefix code: a variable is an odd number, a term constant an
even positive number, and an application is zero followed by its two parts.
The code has unique readability.

The system has three kinds of strings, one for each judgment of the kernel:
`wfLine s e` states that `e` has sort `s`, `convLine s a b` states that `a`
converts to `b` at sort `s`, and `provLine e` states that `e` is derivable.
Its rules are the kernel's rules, one for one: formation for each term
constructor and each variable of the context, reflexivity, symmetry,
transitivity and transport for each sort, congruence for each constructor,
unfolding for each definition, one axiom for each local hypothesis, and one
rule for each theorem of the theory. Every substituted argument is required
to be well formed, so a rule instance determines the expressions it is an
instance at.

`derives_iff_derivable` proves that the kernel derives an expression
exactly when the system derives its line. Soundness holds for every theory;
completeness uses that the theory is first-order. With the recursive
enumerability of elementary formal systems this gives `derives_re`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.FirstOrderEnumeration

open Mettapedia.Computability.ElementaryFormalSystems (Word Rule Derivable substitute
  substitute_cons substitute_nil substitute_append substitute_constants derivable_re)

/-! ## Codes of expressions -/

/-- The prefix code of an expression. -/
def code : Preterm → List ℕ
  | .var index => [2 * index + 1]
  | .term index => [2 * index + 2]
  | .app function argument => 0 :: (code function ++ code argument)

/-- **Unique readability.** A code is never a proper prefix of another. -/
theorem code_append_inj : ∀ (first second : Preterm) (rest rest' : List ℕ),
    code first ++ rest = code second ++ rest' → first = second ∧ rest = rest'
  | .var i, .var j, rest, rest', same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      exact ⟨by rw [show i = j by omega], same.2⟩
  | .var i, .term j, _, _, same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      omega
  | .var i, .app _ _, _, _, same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      omega
  | .term i, .var j, _, _, same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      omega
  | .term i, .term j, rest, rest', same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      exact ⟨by rw [show i = j by omega], same.2⟩
  | .term i, .app _ _, _, _, same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      omega
  | .app _ _, .var j, _, _, same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      omega
  | .app _ _, .term j, _, _, same => by
      simp only [code, List.cons_append, List.nil_append, List.cons.injEq] at same
      omega
  | .app f a, .app g b, rest, rest', same => by
      simp only [code, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at same
      obtain ⟨rfl, tail⟩ := code_append_inj f g _ _ same
      obtain ⟨rfl, rest⟩ := code_append_inj a b _ _ tail
      exact ⟨rfl, rest⟩

theorem code_injective {first second : Preterm} (same : code first = code second) :
    first = second :=
  (code_append_inj first second [] [] (by simpa using same)).1

theorem code_pair_inj {a b c d : Preterm} (same : code a ++ code b = code c ++ code d) :
    a = c ∧ b = d := by
  obtain ⟨rfl, rest⟩ := code_append_inj a c _ _ same
  exact ⟨rfl, code_injective rest⟩

/-! ## Rule words -/

/-- The word of an expression whose variables are the variables of a rule. -/
def word : Preterm → Word
  | .var index => [.inl index]
  | .term index => [.inr (2 * index + 2)]
  | .app function argument => .inr 0 :: (word function ++ word argument)

/-- A variable of a rule. -/
def slot (index : ℕ) : Word := [.inl index]

@[simp] theorem substitute_slot (strings : List (List ℕ)) (index : ℕ) :
    substitute strings (slot index) = strings.getD index [] := by
  simp [slot]

theorem substitute_word {strings : List (List ℕ)} {values : List Preterm}
    (agree : ∀ index value, values[index]? = some value → strings.getD index [] = code value) :
    ∀ {expression result : Preterm},
      Preterm.Substitutes (Substitution.ofList values) expression result →
        substitute strings (word expression) = code result
  | _, _, .var lookup => by
      simpa [word, code] using agree _ _ lookup
  | _, _, .term index => by simp [word, code]
  | _, _, .app function argument => by
      simp [word, code, substitute_word agree function, substitute_word agree argument]

/-- Every variable of the expression is below the bound. -/
def varsBelow (bound : ℕ) : Preterm → Bool
  | .var index => decide (index < bound)
  | .term _ => true
  | .app function argument => varsBelow bound function && varsBelow bound argument

theorem varsBelow_iff (bound : ℕ) :
    ∀ expression : Preterm, varsBelow bound expression = true ↔
      ∀ index, Preterm.Occurs index expression → index < bound
  | .var index => by
      simp only [varsBelow, decide_eq_true_eq]
      constructor
      · intro below other occurrence
        cases occurrence
        exact below
      · intro below
        exact below index .var
  | .term _ => by
      simp only [varsBelow, true_iff]
      intro index occurrence
      cases occurrence
  | .app function argument => by
      simp only [varsBelow, Bool.and_eq_true, varsBelow_iff bound function,
        varsBelow_iff bound argument]
      constructor
      · rintro ⟨inFunction, inArgument⟩ index occurrence
        cases occurrence with
        | function occurs => exact inFunction index occurs
        | argument occurs => exact inArgument index occurs
      · intro below
        exact ⟨fun index occurs => below index (.function occurs),
          fun index occurs => below index (.argument occurs)⟩

theorem substitutes_of_varsBelow {values : List Preterm} {expression : Preterm}
    (below : varsBelow values.length expression = true) :
    ∃ result, Preterm.Substitutes (Substitution.ofList values) expression result := by
  obtain ⟨result, accepted⟩ := (Preterm.substitute_ofList_defined_iff values expression).mpr
    ((varsBelow_iff _ _).mp below)
  exact ⟨result, Preterm.substitute_sound accepted⟩

theorem varsBelow_of_substitutes {values : List Preterm} {expression result : Preterm}
    (substitutes : Preterm.Substitutes (Substitution.ofList values) expression result) :
    varsBelow values.length expression = true :=
  (varsBelow_iff _ _).mpr ((Preterm.substitute_ofList_defined_iff values expression).mp
    ⟨result, substitutes.eval⟩)

/-- A constant applied to the variables `offset`, …, `offset + count - 1`. -/
def spine (symbol offset count : ℕ) : Preterm :=
  Preterm.applyArgs (.term symbol) ((List.range count).map fun index => .var (offset + index))

theorem substitute_spine {strings : List (List ℕ)} (symbol offset : ℕ) :
    ∀ (arguments : List Preterm),
      (∀ index value, arguments[index]? = some value →
        strings.getD (offset + index) [] = code value) →
      substitute strings (word (spine symbol offset arguments.length)) =
        code (Preterm.applyArgs (.term symbol) arguments) := by
  intro arguments
  induction arguments using List.reverseRecOn with
  | nil => intro _; simp [spine, word, code]
  | append_singleton arguments last ih =>
      intro agree
      have earlier : ∀ index value, arguments[index]? = some value →
          strings.getD (offset + index) [] = code value := by
        intro index value lookup
        apply agree index value
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).1]
        exact lookup
      have final := agree arguments.length last (by simp)
      have previous := ih earlier
      simp only [spine, List.length_append, List.length_singleton, List.range_succ,
        List.map_append, List.map_singleton, Preterm.applyArgs_append, Preterm.applyArgs,
        word, code] at previous ⊢
      rw [List.getD_eq_getElem?_getD] at final
      simp [previous, final]

/-! ## Lines and the rules -/

def wfLine (sort : ℕ) (expression : Preterm) : List ℕ := 0 :: sort :: code expression
def convLine (sort : ℕ) (left right : Preterm) : List ℕ :=
  1 :: sort :: (code left ++ code right)
def provLine (expression : Preterm) : List ℕ := 2 :: code expression

def wfWord (sort : ℕ) (body : Word) : Word := .inr 0 :: .inr sort :: body
def convWord (sort : ℕ) (left right : Word) : Word := .inr 1 :: .inr sort :: (left ++ right)
def provWord (body : Word) : Word := .inr 2 :: body

@[simp] theorem substitute_wfWord (strings : List (List ℕ)) (sort : ℕ) (body : Word) :
    substitute strings (wfWord sort body) = 0 :: sort :: substitute strings body := by
  simp [wfWord]

@[simp] theorem substitute_convWord (strings : List (List ℕ)) (sort : ℕ) (left right : Word) :
    substitute strings (convWord sort left right) =
      1 :: sort :: (substitute strings left ++ substitute strings right) := by
  simp [convWord]

@[simp] theorem substitute_provWord (strings : List (List ℕ)) (body : Word) :
    substitute strings (provWord body) = 2 :: substitute strings body := by
  simp [provWord]

/-- Every formal is a regular variable. -/
def allRegular (formals : Context) : Bool :=
  formals.all fun binder => match binder with
    | .regular _ _ => true
    | .bound _ => false

theorem regular_of_allRegular {formals : Context} (regular : allRegular formals = true)
    {binder : Binder} (member : binder ∈ formals) :
    ∃ sort dependencies, binder = .regular sort dependencies := by
  have holds := List.all_eq_true.mp regular binder member
  cases binder with
  | bound sort => simp at holds
  | regular sort dependencies => exact ⟨sort, dependencies, rfl⟩

/-- One well-formedness premise for each formal, at the variable of its position. -/
def formalPremises (formals : Context) : List Word :=
  formals.zipIdx.map fun entry => wfWord entry.1.sort (slot entry.2)

def formationRule (symbol : ℕ) (declaration : TermDecl) : Rule :=
  (formalPremises declaration.arguments,
    wfWord declaration.resultSort (word (spine symbol 0 declaration.arguments.length)))

def congruenceRule (symbol : ℕ) (declaration : TermDecl) : Rule :=
  let count := declaration.arguments.length
  (declaration.arguments.zipIdx.flatMap fun entry =>
      [wfWord entry.1.sort (slot entry.2), wfWord entry.1.sort (slot (count + entry.2)),
        convWord entry.1.sort (slot entry.2) (slot (count + entry.2))],
    convWord declaration.resultSort (word (spine symbol 0 count))
      (word (spine symbol count count)))

def unfoldRule (symbol : ℕ) (declaration : TermDecl) (body : Definition.Body) : Rule :=
  (formalPremises declaration.arguments ++ [wfWord declaration.resultSort (word body.expression)],
    convWord declaration.resultSort (word (spine symbol 0 declaration.arguments.length))
      (word body.expression))

def theoremRule (declaration : TheoremDecl) : Rule :=
  (formalPremises declaration.arguments ++ declaration.hypotheses.map (provWord ∘ word),
    provWord (word declaration.conclusion))

def sortRules (sort : ℕ) : List Rule :=
  [([wfWord sort (slot 0)], convWord sort (slot 0) (slot 0)),
    ([wfWord sort (slot 0), wfWord sort (slot 1), convWord sort (slot 0) (slot 1)],
      convWord sort (slot 1) (slot 0)),
    ([wfWord sort (slot 0), wfWord sort (slot 1), wfWord sort (slot 2),
        convWord sort (slot 0) (slot 1), convWord sort (slot 1) (slot 2)],
      convWord sort (slot 0) (slot 2)),
    ([wfWord sort (slot 0), wfWord sort (slot 1), convWord sort (slot 0) (slot 1),
        provWord (slot 0)], provWord (slot 1))]

def termRules (signature : TermSignature) (symbol : ℕ) : List Rule :=
  match signature symbol with
  | none => []
  | some declaration =>
      if allRegular declaration.arguments then
        [formationRule symbol declaration, congruenceRule symbol declaration]
      else []

def definitionRules (signature : TermSignature) (definitions : Definition.Signature)
    (symbol : ℕ) : List Rule :=
  match signature symbol, definitions symbol with
  | some declaration, some body =>
      if allRegular declaration.arguments && body.dummies.isEmpty &&
          varsBelow declaration.arguments.length body.expression then
        [unfoldRule symbol declaration body]
      else []
  | _, _ => []

def theoremRules (theorems : TheoremSignature) (index : ℕ) : List Rule :=
  match theorems index with
  | none => []
  | some declaration =>
      if allRegular declaration.arguments &&
          declaration.hypotheses.all (varsBelow declaration.arguments.length) &&
          varsBelow declaration.arguments.length declaration.conclusion then
        [theoremRule declaration]
      else []

/-- The sorts at which a typing judgment can hold. -/
def sortsOf (signature : TermSignature) (termKeys : List ℕ) (context : Context) : List ℕ :=
  context.map Binder.sort ++ termKeys.filterMap fun symbol =>
    (signature symbol).map TermDecl.resultSort

/-- The elementary formal system of a theory, given by its signatures and
their keys, in a context, under hypotheses. -/
def systemOf (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (termKeys definitionKeys theoremKeys : List ℕ)
    (context : Context) (hypotheses : List Preterm) : List Rule :=
  termKeys.flatMap (termRules signature) ++
  definitionKeys.flatMap (definitionRules signature definitions) ++
  theoremKeys.flatMap (theoremRules theorems) ++
  (sortsOf signature termKeys context).flatMap sortRules ++
  context.zipIdx.map (fun entry => (([] : List Word),
    (wfLine entry.1.sort (.var entry.2)).map Sum.inr)) ++
  hypotheses.map fun hypothesis => (([] : List Word), (provLine hypothesis).map Sum.inr)

/-- The elementary formal system of a theory in a context, under hypotheses. -/
def system (theory : Theory) (context : Context) (hypotheses : List Preterm) : List Rule :=
  systemOf theory.termSignature theory.definitionSignature theory.theoremSignature
    (theory.terms.map Prod.fst) (theory.definitions.map Prod.fst)
    (theory.theorems.map Prod.fst) context hypotheses

/-! ## Soundness -/

section Soundness

variable {signature : TermSignature} {definitions : Definition.Signature}
  {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

/-- What a string of the system states. -/
def Holds (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (string : List ℕ) : Prop :=
  (∃ sort expression, string = wfLine sort expression ∧
      Preterm.HasType signature context expression [] sort) ∨
  (∃ sort left right, string = convLine sort left right ∧
      Converts signature definitions context left right sort) ∨
  (∃ expression, string = provLine expression ∧
      Derives signature definitions theorems context hypotheses expression)

theorem holds_wf {sort : ℕ} {rest : List ℕ}
    (holds : Holds signature definitions theorems context hypotheses (0 :: sort :: rest)) :
    ∃ expression, rest = code expression ∧
      Preterm.HasType signature context expression [] sort := by
  rcases holds with ⟨sort', expression, same, typed⟩ | ⟨_, _, _, same, _⟩ | ⟨_, same, _⟩
  · simp only [wfLine, List.cons.injEq, true_and] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨expression, rfl, typed⟩
  · simp [convLine] at same
  · simp [provLine] at same

theorem holds_conv {sort : ℕ} {rest : List ℕ}
    (holds : Holds signature definitions theorems context hypotheses (1 :: sort :: rest)) :
    ∃ left right, rest = code left ++ code right ∧
      Converts signature definitions context left right sort := by
  rcases holds with ⟨_, _, same, _⟩ | ⟨sort', left, right, same, converts⟩ |
    ⟨_, same, _⟩
  · simp [wfLine] at same
  · simp only [convLine, List.cons.injEq, true_and] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨left, right, rfl, converts⟩
  · simp [provLine] at same

theorem holds_prov {rest : List ℕ}
    (holds : Holds signature definitions theorems context hypotheses (2 :: rest)) :
    ∃ expression, rest = code expression ∧
      Derives signature definitions theorems context hypotheses expression := by
  rcases holds with ⟨_, _, same, _⟩ | ⟨_, _, _, same, _⟩ | ⟨expression, same, derived⟩
  · simp [wfLine] at same
  · simp [convLine] at same
  · simp only [provLine, List.cons.injEq, true_and] at same
    exact ⟨expression, same, derived⟩

/-- Values for consecutive variables of a rule instance. -/
theorem values_exist {strings : List (List ℕ)} (offset : ℕ) {P : ℕ → Preterm → Prop} :
    ∀ count : ℕ, (∀ index < count,
        ∃ value, strings.getD (offset + index) [] = code value ∧
        P index value) →
      ∃ values : List Preterm, values.length = count ∧ ∀ index value,
        values[index]? = some value → strings.getD (offset + index) [] = code value ∧
          P index value
  | 0, _ => ⟨[], rfl, by simp⟩
  | count + 1, each => by
      obtain ⟨values, length, agree⟩ := values_exist offset count
        fun index below => each index (Nat.lt_succ_of_lt below)
      obtain ⟨last, lastCode, lastHolds⟩ := each count (Nat.lt_succ_self count)
      refine ⟨values ++ [last], by simp [length], ?_⟩
      intro index value lookup
      rcases Nat.lt_or_ge index values.length with below | beyond
      · rw [List.getElem?_append_left below] at lookup
        exact agree index value lookup
      · rw [List.getElem?_append_right beyond] at lookup
        have zero : index - values.length = 0 := by
          by_contra nonzero
          simp [nonzero] at lookup
        have same : index = count := by omega
        subst same
        simp only [zero, List.getElem?_cons_zero, Option.some.injEq] at lookup
        subst lookup
        exact ⟨lastCode, lastHolds⟩

theorem mem_formalPremises {formals : Context} {index : ℕ} {binder : Binder}
    (lookup : formals[index]? = some binder) :
    wfWord binder.sort (slot index) ∈ formalPremises formals := by
  unfold formalPremises
  exact List.mem_map.mpr ⟨(binder, index), List.mem_zipIdx_iff_getElem?.mpr lookup, rfl⟩

/-- The well-formed values of the formals of a rule instance. -/
theorem formal_values {formals : Context} {strings : List (List ℕ)} (offset : ℕ)
    (premises : ∀ (index : ℕ) (binder : Binder), formals[index]? = some binder →
      Holds signature definitions theorems context hypotheses
        (0 :: binder.sort :: strings.getD (offset + index) [])) :
    ∃ values : List Preterm, values.length = formals.length ∧
      (∀ (index : ℕ) (value : Preterm), values[index]? = some value →
        strings.getD (offset + index) [] = code value) ∧
      (∀ (index : ℕ) (value : Preterm) (binder : Binder),
        values[index]? = some value → formals[index]? = some binder →
          Preterm.HasType signature context value [] binder.sort) := by
  obtain ⟨values, length, agree⟩ := values_exist (strings := strings) offset
    (P := fun index value => ∀ binder, formals[index]? = some binder →
      Preterm.HasType signature context value [] binder.sort) formals.length
    (by
      intro index below
      obtain ⟨value, same, typed⟩ := holds_wf (premises index formals[index]
        (List.getElem?_eq_some_iff.mpr ⟨below, rfl⟩))
      refine ⟨value, same, fun binder lookup => ?_⟩
      rw [List.getElem?_eq_some_iff.mpr ⟨below, rfl⟩] at lookup
      cases lookup
      exact typed)
  exact ⟨values, length, fun index value lookup => (agree index value lookup).1,
    fun index value binder lookup formal => (agree index value lookup).2 binder formal⟩

theorem fits_of_values {formals : Context} (regular : allRegular formals = true)
    {values : List Preterm} (length : values.length = formals.length)
    (typed : ∀ (index : ℕ) (value : Preterm) (binder : Binder), values[index]? = some value →
      formals[index]? = some binder →
      Preterm.HasType signature context value [] binder.sort) :
    List.Forall₂ (Preterm.FitsBinder signature context) values formals := by
  rw [List.forall₂_iff_get]
  refine ⟨length, fun index below other => ?_⟩
  simp only [List.get_eq_getElem]
  have binderMember : formals[index] ∈ formals := List.getElem_mem other
  obtain ⟨sort, dependencies, shape⟩ := regular_of_allRegular regular binderMember
  have value := typed index values[index] formals[index] (List.getElem?_eq_getElem below)
    (List.getElem?_eq_getElem other)
  rw [shape] at value ⊢
  exact .regular value

theorem admissible_of_regular {formals : Context} (regular : allRegular formals = true)
    {values : List Preterm}
    (fits : List.Forall₂ (Preterm.FitsBinder signature context) values formals) :
    Substitution.Admissible signature formals context values := by
  refine ⟨fits, ?_⟩
  intro entry member sort image shape
  have inZip : entry.1 ∈ formals.zip values :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member)
  have formal := (List.of_mem_zip inZip).1
  rw [congrArg Prod.fst shape] at formal
  obtain ⟨_, _, impossible⟩ := regular_of_allRegular regular formal
  cases impossible

theorem convertsArgs_of_values :
    ∀ {formals : Context}, allRegular formals = true →
    ∀ {lefts rights : List Preterm}, lefts.length = formals.length →
      rights.length = formals.length →
      (∀ (index : ℕ) (left right : Preterm) (binder : Binder), lefts[index]? = some left →
        rights[index]? = some right → formals[index]? = some binder →
          Preterm.HasType signature context left [] binder.sort ∧
            Preterm.HasType signature context right [] binder.sort ∧
            Converts signature definitions context left right binder.sort) →
      ConvertsArgs signature definitions context lefts rights formals
  | [], _, [], [], _, _, _ => .nil
  | binder :: formals, regular, left :: lefts, right :: rights, leftLength, rightLength, each => by
      simp only [allRegular, List.all_cons, Bool.and_eq_true] at regular
      have head := each 0 left right binder rfl rfl rfl
      have restRegular : allRegular formals = true := regular.2
      obtain ⟨sort, dependencies, rfl⟩ : ∃ sort dependencies,
          binder = .regular sort dependencies := by
        cases binder with
        | bound sort => simp at regular
        | regular sort dependencies => exact ⟨sort, dependencies, rfl⟩
      exact .cons (.regular head.1) (.regular head.2.1) head.2.2
        (convertsArgs_of_values restRegular (by simpa using leftLength)
          (by simpa using rightLength)
          fun index left right binder leftLookup rightLookup formal =>
            each (index + 1) left right binder leftLookup rightLookup formal)
  | [], _, _ :: _, _, leftLength, _, _ => by simp at leftLength
  | [], _, [], _ :: _, _, rightLength, _ => by simp at rightLength
  | _ :: _, _, [], _, leftLength, _, _ => by simp at leftLength
  | _ :: _, _, _ :: _, [], _, rightLength, _ => by simp at rightLength

/-- Results of substitution for every hypothesis of a theorem. -/
theorem substituted_list {values : List Preterm} {P : Preterm → Prop} :
    ∀ sources : List Preterm, (∀ source ∈ sources,
        ∃ result, Preterm.Substitutes (Substitution.ofList values) source result ∧ P result) →
      ∃ results,
        List.Forall₂ (Preterm.Substitutes (Substitution.ofList values)) sources results ∧
        ∀ result ∈ results, P result
  | [], _ => ⟨[], .nil, by simp⟩
  | source :: sources, each => by
      obtain ⟨result, substitutes, holds⟩ := each source (by simp)
      obtain ⟨results, rest, others⟩ := substituted_list sources
        fun other member => each other (by simp [member])
      exact ⟨result :: results, .cons substitutes rest, by
        intro value member
        rcases List.mem_cons.mp member with rfl | later
        · exact holds
        · exact others value later⟩

/-- **Soundness.** Every string the system derives states a judgment the
kernel derives. -/
theorem holds_of_derivable {termKeys definitionKeys theoremKeys : List ℕ} {string : List ℕ}
    (derivable : Derivable (systemOf signature definitions theorems termKeys definitionKeys
      theoremKeys context hypotheses) string) :
    Holds signature definitions theorems context hypotheses string := by
  induction derivable with
  | @rule rule member strings _ ih =>
    simp only [systemOf, List.mem_append, List.mem_flatMap, List.mem_map] at member
    rcases member with ((((⟨symbol, -, inTerm⟩ | ⟨symbol, -, inDefinition⟩) |
      ⟨index, -, inTheorem⟩) | ⟨sort, -, inSort⟩) | ⟨entry, inContext, rfl⟩) |
      ⟨hypothesis, inHypotheses, rfl⟩
    · unfold termRules at inTerm
      split at inTerm
      · simp at inTerm
      · rename_i declaration lookup
        by_cases regular : allRegular declaration.arguments = true
        · rw [if_pos regular] at inTerm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inTerm
          rcases inTerm with rfl | rfl
          · obtain ⟨values, length, codes, typed⟩ := formal_values (strings := strings) 0
              (fun index binder formal => by
                simpa using ih _ (mem_formalPremises formal))
            have spineCode := substitute_spine (strings := strings) symbol 0 values codes
            rw [length] at spineCode
            refine Or.inl ⟨declaration.resultSort, Preterm.applyArgs (.term symbol) values,
              ?_, ?_⟩
            · simp only [formationRule, substitute_wfWord, spineCode, wfLine]
            · exact (Preterm.HasType.term lookup).applyArgs (fits_of_values regular length typed)
          · let count := declaration.arguments.length
            have premise : ∀ (index : ℕ) (binder : Binder),
                declaration.arguments[index]? = some binder →
                  Holds signature definitions theorems context hypotheses
                      (0 :: binder.sort :: strings.getD index []) ∧
                    Holds signature definitions theorems context hypotheses
                      (0 :: binder.sort :: strings.getD (count + index) []) ∧
                    Holds signature definitions theorems context hypotheses
                      (1 :: binder.sort :: (strings.getD index [] ++
                        strings.getD (count + index) [])) := by
              intro index binder formal
              have inZip : (binder, index) ∈ declaration.arguments.zipIdx :=
                List.mem_zipIdx_iff_getElem?.mpr formal
              have inPremises : ∀ premise ∈ [wfWord binder.sort (slot index),
                  wfWord binder.sort (slot (count + index)),
                  convWord binder.sort (slot index) (slot (count + index))],
                  premise ∈ (congruenceRule symbol declaration).1 := fun premise inList =>
                List.mem_flatMap.mpr ⟨(binder, index), inZip, inList⟩
              refine ⟨?_, ?_, ?_⟩
              · simpa using ih (wfWord binder.sort (slot index)) (inPremises _ (by simp))
              · simpa using ih (wfWord binder.sort (slot (count + index))) (inPremises _ (by simp))
              · simpa using ih (convWord binder.sort (slot index) (slot (count + index)))
                  (inPremises _ (by simp))
            obtain ⟨lefts, leftLength, leftCodes, leftTyped⟩ :=
              formal_values (strings := strings) 0
              (fun index binder formal => by simpa using (premise index binder formal).1)
            obtain ⟨rights, rightLength, rightCodes, rightTyped⟩ :=
              formal_values (strings := strings) count
                (fun index binder formal => (premise index binder formal).2.1)
            have leftSpine := substitute_spine (strings := strings) symbol 0 lefts leftCodes
            have rightSpine := substitute_spine (strings := strings) symbol count rights rightCodes
            rw [leftLength] at leftSpine
            rw [rightLength] at rightSpine
            refine Or.inr (Or.inl ⟨declaration.resultSort, Preterm.applyArgs (.term symbol) lefts,
              Preterm.applyArgs (.term symbol) rights, ?_, ?_⟩)
            · simp only [congruenceRule, substitute_convWord, convLine]
              rw [leftSpine, rightSpine]
            · refine Converts.congruence lookup (convertsArgs_of_values regular leftLength
                rightLength fun index left right binder leftLookup rightLookup formal => ?_)
              obtain ⟨left', right', same, converts⟩ :=
                holds_conv (premise index binder formal).2.2
              have leftCode := leftCodes index left leftLookup
              have rightCode := rightCodes index right rightLookup
              simp only [Nat.zero_add] at leftCode
              rw [leftCode, rightCode] at same
              obtain ⟨sameLeft, sameRight⟩ := code_pair_inj same
              rw [← sameLeft, ← sameRight] at converts
              exact ⟨leftTyped index left binder leftLookup formal,
                rightTyped index right binder rightLookup formal, converts⟩
        · rw [if_neg regular] at inTerm
          simp at inTerm
    · unfold definitionRules at inDefinition
      split at inDefinition
      · rename_i declaration body lookup known
        by_cases admitted : (allRegular declaration.arguments && body.dummies.isEmpty &&
            varsBelow declaration.arguments.length body.expression) = true
        · rw [if_pos admitted, List.mem_singleton] at inDefinition
          subst inDefinition
          simp only [Bool.and_eq_true, List.isEmpty_iff] at admitted
          obtain ⟨⟨regular, noDummies⟩, below⟩ := admitted
          obtain ⟨values, length, codes, typed⟩ := formal_values (strings := strings) 0
            (fun index binder formal => by
              simpa using ih _ (List.mem_append_left _ (mem_formalPremises formal)))
          have agree : ∀ index value, values[index]? = some value →
              strings.getD index [] = code value := by simpa using codes
          obtain ⟨result, substitutes⟩ := substitutes_of_varsBelow (values := values)
            (by rw [length]; exact below)
          have resultPremise := ih (wfWord declaration.resultSort (word body.expression))
            (List.mem_append_right _ (List.mem_singleton_self _))
          rw [substitute_wfWord, substitute_word agree substitutes] at resultPremise
          obtain ⟨result', same, resultTyped⟩ := holds_wf resultPremise
          obtain rfl := code_injective same
          have spineCode := substitute_spine (strings := strings) symbol 0 values codes
          rw [length] at spineCode
          refine Or.inr (Or.inl ⟨declaration.resultSort, Preterm.applyArgs (.term symbol) values,
            result, ?_, ?_⟩)
          · simp only [unfoldRule, substitute_convWord, convLine]
            rw [spineCode, substitute_word agree substitutes]
          · refine Converts.unfold (images := []) lookup ?_ resultTyped
            refine Definition.Unfolds.intro lookup known (fits_of_values regular length typed)
              ?_ ?_
            · rw [noDummies]; exact .nil values
            · simpa [Definition.substitutionValues] using substitutes
        · rw [if_neg admitted] at inDefinition
          simp at inDefinition
      · simp at inDefinition
    · unfold theoremRules at inTheorem
      split at inTheorem
      · simp at inTheorem
      · rename_i declaration lookup
        by_cases admitted : (allRegular declaration.arguments &&
            declaration.hypotheses.all (varsBelow declaration.arguments.length) &&
            varsBelow declaration.arguments.length declaration.conclusion) = true
        · rw [if_pos admitted, List.mem_singleton] at inTheorem
          subst inTheorem
          simp only [Bool.and_eq_true, List.all_eq_true] at admitted
          obtain ⟨⟨regular, hypothesesBelow⟩, conclusionBelow⟩ := admitted
          obtain ⟨values, length, codes, typed⟩ := formal_values (strings := strings) 0
            (fun index binder formal => by
              simpa using ih _ (List.mem_append_left _ (mem_formalPremises formal)))
          have agree : ∀ index value, values[index]? = some value →
              strings.getD index [] = code value := by simpa using codes
          obtain ⟨results, hypothesesSubstitute, derivedHypotheses⟩ := substituted_list
            (values := values)
            (P := Derives signature definitions theorems context hypotheses)
            declaration.hypotheses (by
              intro source member
              obtain ⟨result, substitutes⟩ := substitutes_of_varsBelow (values := values)
                (by rw [length]; exact hypothesesBelow source member)
              have premise := ih (provWord (word source))
                (List.mem_append_right _ (List.mem_map.mpr ⟨source, member, rfl⟩))
              rw [substitute_provWord, substitute_word agree substitutes] at premise
              obtain ⟨result', same, derived⟩ := holds_prov premise
              obtain rfl := code_injective same
              exact ⟨result, substitutes, derived⟩)
          obtain ⟨conclusion, concludes⟩ := substitutes_of_varsBelow (values := values)
            (by rw [length]; exact conclusionBelow)
          refine Or.inr (Or.inr ⟨conclusion, ?_, ?_⟩)
          · simp only [theoremRule, substitute_provWord, provLine]
            rw [substitute_word agree concludes]
          · exact Derives.theoremApp (instantiation := ⟨results, conclusion⟩) lookup
              ⟨admissible_of_regular regular (fits_of_values regular length typed),
                hypothesesSubstitute, concludes⟩
              ((derivesList_iff _ _ _ _ _ _).mpr derivedHypotheses)
        · rw [if_neg admitted] at inTheorem
          simp at inTheorem
    · simp only [sortRules, List.mem_cons, List.not_mem_nil, or_false] at inSort
      rcases inSort with rfl | rfl | rfl | rfl
      · have first := ih (wfWord sort (slot 0)) (by simp)
        simp only [substitute_wfWord, substitute_slot] at first
        obtain ⟨a, codeA, typedA⟩ := holds_wf first
        refine Or.inr (Or.inl ⟨sort, a, a, ?_, .refl typedA⟩)
        simp only [substitute_convWord, substitute_slot, convLine, codeA]
      · have first := ih (wfWord sort (slot 0)) (by simp)
        have second := ih (wfWord sort (slot 1)) (by simp)
        have converted := ih (convWord sort (slot 0) (slot 1)) (by simp)
        simp only [substitute_wfWord, substitute_convWord,
          substitute_slot] at first second converted
        obtain ⟨a, codeA, -⟩ := holds_wf first
        obtain ⟨b, codeB, -⟩ := holds_wf second
        obtain ⟨a', b', same, converts⟩ := holds_conv converted
        rw [codeA, codeB] at same
        obtain ⟨rfl, rfl⟩ := code_pair_inj same
        refine Or.inr (Or.inl ⟨sort, b, a, ?_, .symm converts⟩)
        simp only [substitute_convWord, substitute_slot, convLine, codeA, codeB]
      · have first := ih (wfWord sort (slot 0)) (by simp)
        have second := ih (wfWord sort (slot 1)) (by simp)
        have third := ih (wfWord sort (slot 2)) (by simp)
        have firstConversion := ih (convWord sort (slot 0) (slot 1)) (by simp)
        have secondConversion := ih (convWord sort (slot 1) (slot 2)) (by simp)
        simp only [substitute_wfWord, substitute_convWord,
          substitute_slot] at first second third firstConversion secondConversion
        obtain ⟨a, codeA, -⟩ := holds_wf first
        obtain ⟨b, codeB, -⟩ := holds_wf second
        obtain ⟨c, codeC, -⟩ := holds_wf third
        obtain ⟨a', b', same, convertsFirst⟩ := holds_conv firstConversion
        obtain ⟨b'', c', same', convertsSecond⟩ := holds_conv secondConversion
        rw [codeA, codeB] at same
        rw [codeB, codeC] at same'
        obtain ⟨rfl, rfl⟩ := code_pair_inj same
        obtain ⟨rfl, rfl⟩ := code_pair_inj same'
        refine Or.inr (Or.inl ⟨sort, a, c, ?_, .trans convertsFirst convertsSecond⟩)
        simp only [substitute_convWord, substitute_slot, convLine, codeA, codeC]
      · have first := ih (wfWord sort (slot 0)) (by simp)
        have second := ih (wfWord sort (slot 1)) (by simp)
        have converted := ih (convWord sort (slot 0) (slot 1)) (by simp)
        have derivedFirst := ih (provWord (slot 0)) (by simp)
        simp only [substitute_wfWord, substitute_convWord, substitute_provWord,
          substitute_slot] at first second converted derivedFirst
        obtain ⟨a, codeA, -⟩ := holds_wf first
        obtain ⟨b, codeB, -⟩ := holds_wf second
        obtain ⟨a', b', same, converts⟩ := holds_conv converted
        obtain ⟨a'', same'', derived⟩ := holds_prov derivedFirst
        rw [codeA, codeB] at same
        obtain ⟨rfl, rfl⟩ := code_pair_inj same
        rw [codeA] at same''
        obtain rfl := code_injective same''
        refine Or.inr (Or.inr ⟨b, ?_, .conversion converts derived⟩)
        simp only [substitute_provWord, substitute_slot, provLine, codeB]
    · refine Or.inl ⟨entry.1.sort, .var entry.2, by simp [wfLine], ?_⟩
      exact .var (List.mem_zipIdx_iff_getElem?.mp inContext)
    · exact Or.inr (Or.inr ⟨hypothesis, by simp [provLine], .hypothesis inHypotheses⟩)

end Soundness

/-! ## Completeness -/

section Completeness

variable {signature : TermSignature} {definitions : Definition.Signature}
  {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
  {termKeys definitionKeys theoremKeys : List ℕ}

/-- What completeness uses: every declaration is listed, every formal is a
regular variable, and no definition has a dummy variable. -/
structure Covers (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (termKeys definitionKeys theoremKeys : List ℕ) : Prop where
  terms : ∀ symbol declaration, signature symbol = some declaration → symbol ∈ termKeys
  termsRegular : ∀ symbol declaration, signature symbol = some declaration →
    allRegular declaration.arguments = true
  definitionsListed : ∀ symbol body, definitions symbol = some body → symbol ∈ definitionKeys
  noDummies : ∀ symbol body, definitions symbol = some body → body.dummies = []
  theoremsListed : ∀ index declaration, theorems index = some declaration →
    index ∈ theoremKeys
  theoremsRegular : ∀ index declaration, theorems index = some declaration →
    allRegular declaration.arguments = true

theorem derivable_of_rule {rules : List Rule} {rule : Rule} (member : rule ∈ rules)
    (strings : List (List ℕ))
    (premises : ∀ premise ∈ rule.1, Derivable rules (substitute strings premise))
    {string : List ℕ} (conclusion : substitute strings rule.2 = string) :
    Derivable rules string :=
  conclusion ▸ Derivable.rule member strings premises

theorem mem_system_term {rule : Rule} {symbol : ℕ} (known : symbol ∈ termKeys)
    (member : rule ∈ termRules signature symbol) :
    rule ∈ systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses := by
  simp only [systemOf, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨symbol, known, member⟩))))

theorem mem_system_definition {rule : Rule} {symbol : ℕ} (known : symbol ∈ definitionKeys)
    (member : rule ∈ definitionRules signature definitions symbol) :
    rule ∈ systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses := by
  simp only [systemOf, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨symbol, known, member⟩))))

theorem mem_system_theorem {rule : Rule} {index : ℕ} (known : index ∈ theoremKeys)
    (member : rule ∈ theoremRules theorems index) :
    rule ∈ systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses := by
  simp only [systemOf, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨index, known, member⟩)))

theorem mem_system_sort {rule : Rule} {sort : ℕ}
    (known : sort ∈ sortsOf signature termKeys context) (member : rule ∈ sortRules sort) :
    rule ∈ systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses := by
  simp only [systemOf, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨sort, known, member⟩))

theorem mem_system_context {index : ℕ} {binder : Binder}
    (lookup : context[index]? = some binder) :
    (([] : List Word), (wfLine binder.sort (.var index)).map Sum.inr) ∈
      systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
        hypotheses := by
  simp only [systemOf, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inr ⟨(binder, index), List.mem_zipIdx_iff_getElem?.mpr lookup, rfl⟩)

theorem mem_system_hypothesis {hypothesis : Preterm} (member : hypothesis ∈ hypotheses) :
    (([] : List Word), (provLine hypothesis).map Sum.inr) ∈
      systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
        hypotheses := by
  simp only [systemOf, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨hypothesis, member, rfl⟩

theorem getD_codes {values : List Preterm} {index : ℕ} {value : Preterm}
    (lookup : values[index]? = some value) : (values.map code).getD index [] = code value := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, lookup]

theorem sort_mem
    (covers : Covers signature definitions theorems termKeys definitionKeys theoremKeys)
    {expression : Preterm} {remaining : Context} {sort : ℕ}
    (typed : Preterm.HasType signature context expression remaining sort) :
    sort ∈ sortsOf signature termKeys context := by
  induction typed with
  | var lookup =>
      exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_of_getElem? lookup))
  | @term symbol declaration lookup =>
      exact List.mem_append_right _ (List.mem_filterMap.mpr
        ⟨symbol, covers.terms symbol declaration lookup, by simp [lookup]⟩)
  | bound _ _ ih => exact ih
  | regular _ _ ih _ => exact ih

theorem wf_of_application
    (covers : Covers signature definitions theorems termKeys definitionKeys theoremKeys)
    {symbol : ℕ} {declaration : TermDecl} (lookup : signature symbol = some declaration)
    {arguments : List Preterm} (length : arguments.length = declaration.arguments.length)
    (each : ∀ (index : ℕ) (value : Preterm) (binder : Binder),
      arguments[index]? = some value →
      declaration.arguments[index]? = some binder →
        Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys
          context hypotheses) (wfLine binder.sort value)) :
    Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses) (wfLine declaration.resultSort (Preterm.applyArgs (.term symbol) arguments)) := by
  have member : formationRule symbol declaration ∈ termRules signature symbol := by
    simp [termRules, lookup, covers.termsRegular symbol declaration lookup]
  refine derivable_of_rule (mem_system_term (covers.terms symbol declaration lookup) member)
    (arguments.map code) ?_ ?_
  · intro premise inPremises
    simp only [formationRule, formalPremises, List.mem_map] at inPremises
    obtain ⟨⟨binder, index⟩, inZip, rfl⟩ := inPremises
    have formal := List.mem_zipIdx_iff_getElem?.mp inZip
    have below : index < arguments.length := length ▸ (List.getElem?_eq_some_iff.mp formal).1
    simp only [substitute_wfWord, substitute_slot, getD_codes (List.getElem?_eq_getElem below)]
    exact each index arguments[index] binder (List.getElem?_eq_getElem below) formal
  · have spineCode := substitute_spine (strings := arguments.map code) symbol 0 arguments
      (fun index value lookup => by simpa using getD_codes lookup)
    rw [length] at spineCode
    simp only [formationRule, substitute_wfWord, spineCode, wfLine]

/-- The typed expressions: variables, and constants applied to a prefix of
their formals, each argument with a derivable line. -/
theorem typed_shape (covers : Covers signature definitions theorems termKeys definitionKeys
    theoremKeys) {expression : Preterm} {remaining : Context} {sort : ℕ}
    (typed : Preterm.HasType signature context expression remaining sort) :
    (remaining = [] ∧ Derivable (systemOf signature definitions theorems termKeys definitionKeys
        theoremKeys context hypotheses) (wfLine sort expression)) ∨
    (∃ symbol declaration arguments, signature symbol = some declaration ∧
      declaration.resultSort = sort ∧ expression = Preterm.applyArgs (.term symbol) arguments ∧
      remaining = declaration.arguments.drop arguments.length ∧
      arguments.length ≤ declaration.arguments.length ∧
      ∀ (index : ℕ) (value : Preterm) (binder : Binder), arguments[index]? = some value →
        declaration.arguments[index]? = some binder →
          Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys
            context hypotheses) (wfLine binder.sort value)) := by
  induction typed with
  | @var index binder lookup =>
      refine Or.inl ⟨rfl, ?_⟩
      exact derivable_of_rule (mem_system_context lookup) [] (by simp) (by simp)
  | @term symbol declaration lookup =>
      exact Or.inr ⟨symbol, declaration, [], lookup, rfl, rfl, by simp, by simp, by simp⟩
  | @bound function index sort result rest _ _ ih =>
      rcases ih with ⟨impossible, _⟩ |
        ⟨symbol, declaration, arguments, lookup, _, _, shape, _, _⟩
      · cases impossible
      · have member : Binder.bound sort ∈ declaration.arguments :=
          List.mem_of_mem_drop (shape ▸ List.mem_cons_self)
        obtain ⟨_, _, impossible⟩ :=
          regular_of_allRegular (covers.termsRegular symbol declaration lookup) member
        cases impossible
  | @regular function argument sort result dependencies rest _ argumentTyped ihFunction
      ihArgument =>
      have argumentLine : Derivable (systemOf signature definitions theorems termKeys
          definitionKeys theoremKeys context hypotheses) (wfLine sort argument) := by
        rcases ihArgument with ⟨_, line⟩ |
          ⟨symbol, declaration, arguments, lookup, rfl, rfl, shape, below, each⟩
        · exact line
        · have length : arguments.length = declaration.arguments.length := by
            have empty := shape.symm
            rw [List.drop_eq_nil_iff] at empty
            omega
          exact wf_of_application covers lookup length each
      rcases ihFunction with ⟨impossible, _⟩ |
        ⟨symbol, declaration, arguments, lookup, rfl, rfl, shape, below, each⟩
      · cases impossible
      · have position : declaration.arguments[arguments.length]? =
            some (.regular sort dependencies) := by
          have head := congrArg (·[0]?) shape
          simpa [List.getElem?_drop] using head.symm
        have longer : arguments.length < declaration.arguments.length :=
          (List.getElem?_eq_some_iff.mp position).1
        refine Or.inr ⟨symbol, declaration, arguments ++ [argument], lookup, rfl,
          ?_, ?_, ?_, ?_⟩
        · simp [Preterm.applyArgs_append, Preterm.applyArgs]
        · have tail := congrArg List.tail shape
          simpa [List.tail_drop] using tail
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro index value binder lookupValue formal
          rcases Nat.lt_or_ge index arguments.length with earlier | later
          · rw [List.getElem?_append_left earlier] at lookupValue
            exact each index value binder lookupValue formal
          · rw [List.getElem?_append_right later] at lookupValue
            have zero : index - arguments.length = 0 := by
              by_contra nonzero
              simp [nonzero] at lookupValue
            have same : index = arguments.length := by omega
            subst same
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at lookupValue
            subst lookupValue
            rw [position, Option.some.injEq] at formal
            subst formal
            exact argumentLine

/-- **Completeness of formation.** -/
theorem wf_complete (covers : Covers signature definitions theorems termKeys definitionKeys
    theoremKeys) {expression : Preterm} {sort : ℕ}
    (typed : Preterm.HasType signature context expression [] sort) :
    Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses) (wfLine sort expression) := by
  rcases typed_shape (hypotheses := hypotheses) (definitionKeys := definitionKeys)
      (theoremKeys := theoremKeys) covers typed with
    ⟨_, line⟩ | ⟨symbol, declaration, arguments, lookup, rfl, rfl, shape, below, each⟩
  · exact line
  · have length : arguments.length = declaration.arguments.length := by
      have empty := shape.symm
      rw [List.drop_eq_nil_iff] at empty
      omega
    exact wf_of_application covers lookup length each

theorem fits_typed {expression : Preterm} {binder : Binder}
    (fits : Preterm.FitsBinder signature context expression binder) :
    Preterm.HasType signature context expression [] binder.sort := by
  cases fits with
  | bound lookup => exact .var lookup
  | regular typed => exact typed

/-- Every source with a substitution result is below the length of the values. -/
theorem forall₂_exists {values : List Preterm} :
    ∀ {sources results : List Preterm},
      List.Forall₂ (Preterm.Substitutes (Substitution.ofList values)) sources results →
      ∀ source ∈ sources, ∃ result ∈ results,
        Preterm.Substitutes (Substitution.ofList values) source result
  | _, _, .nil => by simp
  | _, _, .cons first rest => by
      intro source member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, first⟩
      · obtain ⟨result, inResults, substitutes⟩ := forall₂_exists rest source later
        exact ⟨result, List.mem_cons_of_mem _ inResults, substitutes⟩

/-- **Completeness of conversion.** -/
theorem conv_complete (covers : Covers signature definitions theorems termKeys definitionKeys
    theoremKeys) {left right : Preterm} {sort : ℕ}
    (conversion : Converts signature definitions context left right sort) :
    Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses) (convLine sort left right) := by
  induction conversion using Converts.rec
      (motive_2 := fun lefts rights binders _ =>
        lefts.length = binders.length ∧ rights.length = binders.length ∧
        ∀ (index : ℕ) (left right : Preterm) (binder : Binder), lefts[index]? = some left →
          rights[index]? = some right → binders[index]? = some binder →
            Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys
                context hypotheses) (convLine binder.sort left right) ∧
              Derivable (systemOf signature definitions theorems termKeys definitionKeys
                theoremKeys context hypotheses) (wfLine binder.sort left) ∧
              Derivable (systemOf signature definitions theorems termKeys definitionKeys
                theoremKeys context hypotheses) (wfLine binder.sort right)) with
  | @refl expression sort typed =>
      refine derivable_of_rule (rule := ([wfWord sort (slot 0)], convWord sort (slot 0) (slot 0)))
        (mem_system_sort (sort_mem covers typed) (by simp [sortRules]))
        [code expression] ?_ (by simp [convLine])
      intro premise member
      simp only [List.mem_singleton] at member
      subst member
      simpa [wfLine] using wf_complete (hypotheses := hypotheses)
        (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers typed
  | @symm left right sort converted ih =>
      obtain ⟨leftTyped, rightTyped⟩ := Converts.typed converted
      refine derivable_of_rule (rule := ([wfWord sort (slot 0), wfWord sort (slot 1),
          convWord sort (slot 0) (slot 1)], convWord sort (slot 1) (slot 0)))
        (mem_system_sort (sort_mem covers leftTyped) (by simp [sortRules]))
        [code left, code right] ?_ (by simp [convLine])
      intro premise member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [wfLine] using wf_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers leftTyped
      · simpa [wfLine] using wf_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers rightTyped
      · simpa [convLine] using ih
  | @trans left middle right sort first second ihFirst ihSecond =>
      obtain ⟨leftTyped, middleTyped⟩ := Converts.typed first
      obtain ⟨_, rightTyped⟩ := Converts.typed second
      refine derivable_of_rule (rule := ([wfWord sort (slot 0), wfWord sort (slot 1),
          wfWord sort (slot 2), convWord sort (slot 0) (slot 1), convWord sort (slot 1) (slot 2)],
          convWord sort (slot 0) (slot 2)))
        (mem_system_sort (sort_mem covers leftTyped) (by simp [sortRules]))
        [code left, code middle, code right] ?_ (by simp [convLine])
      intro premise member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · simpa [wfLine] using wf_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers leftTyped
      · simpa [wfLine] using wf_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers middleTyped
      · simpa [wfLine] using wf_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers rightTyped
      · simpa [convLine] using ihFirst
      · simpa [convLine] using ihSecond
  | @congruence symbol declaration lefts rights lookup _ ih =>
      obtain ⟨leftLength, rightLength, each⟩ := ih
      have member : congruenceRule symbol declaration ∈ termRules signature symbol := by
        simp [termRules, lookup, covers.termsRegular symbol declaration lookup]
      let strings := lefts.map code ++ rights.map code
      have leftStrings : ∀ index value, lefts[index]? = some value →
          strings.getD index [] = code value := by
        intro index value lookupValue
        have below := (List.getElem?_eq_some_iff.mp lookupValue).1
        simp [strings, List.getD_eq_getElem?_getD, List.getElem?_append_left
          (show index < (lefts.map code).length by simpa using below), lookupValue]
      have rightStrings : ∀ index value, rights[index]? = some value →
          strings.getD (declaration.arguments.length + index) [] = code value := by
        intro index value lookupValue
        rw [← leftLength]
        have shifted : strings[lefts.length + index]? = (rights.map code)[index]? := by
          rw [List.getElem?_append_right (by simp)]
          simp
        rw [List.getD_eq_getElem?_getD, shifted, List.getElem?_map, lookupValue]
        rfl
      refine derivable_of_rule (mem_system_term (covers.terms symbol declaration lookup) member)
        strings ?_ ?_
      · intro premise inPremises
        simp only [congruenceRule, List.mem_flatMap] at inPremises
        obtain ⟨⟨binder, index⟩, inZip, inList⟩ := inPremises
        have formal := List.mem_zipIdx_iff_getElem?.mp inZip
        have below : index < declaration.arguments.length :=
          (List.getElem?_eq_some_iff.mp formal).1
        have leftLookup : lefts[index]? = some lefts[index] :=
          List.getElem?_eq_getElem (by omega)
        have rightLookup : rights[index]? = some rights[index] :=
          List.getElem?_eq_getElem (by omega)
        obtain ⟨converted, leftLine, rightLine⟩ :=
          each index _ _ binder leftLookup rightLookup formal
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inList
        rcases inList with rfl | rfl | rfl
        · simp only [substitute_wfWord, substitute_slot, leftStrings index _ leftLookup]
          exact leftLine
        · simp only [substitute_wfWord, substitute_slot, rightStrings index _ rightLookup]
          exact rightLine
        · simp only [substitute_convWord, substitute_slot, leftStrings index _ leftLookup,
            rightStrings index _ rightLookup]
          exact converted
      · have leftSpine := substitute_spine (strings := strings) symbol 0 lefts
          (fun index value lookupValue => by simpa using leftStrings index value lookupValue)
        have rightSpine := substitute_spine (strings := strings) symbol
          declaration.arguments.length rights rightStrings
        rw [leftLength] at leftSpine
        rw [rightLength] at rightSpine
        simp only [congruenceRule, substitute_convWord, convLine]
        rw [leftSpine, rightSpine]
  | @unfold symbol declaration arguments images result lookup unfolded typed =>
      cases unfolded with
      | @intro declaration' body result knownTerm knownBody fits fresh substitutes =>
        obtain rfl : declaration = declaration' := Option.some.inj (lookup.symm.trans knownTerm)
        have noDummies := covers.noDummies symbol body knownBody
        rw [noDummies] at fresh
        cases fresh
        simp only [Definition.substitutionValues, List.map_nil, List.append_nil] at substitutes
        have length := fits.length_eq
        have member : unfoldRule symbol declaration body ∈
            definitionRules signature definitions symbol := by
          have below := varsBelow_of_substitutes substitutes
          rw [length] at below
          simp [definitionRules, lookup, knownBody, covers.termsRegular symbol declaration lookup,
            noDummies, below]
        have agree : ∀ index value, arguments[index]? = some value →
            (arguments.map code).getD index [] = code value := fun _ _ => getD_codes
        refine derivable_of_rule (mem_system_definition
          (covers.definitionsListed symbol body knownBody) member) (arguments.map code) ?_ ?_
        · intro premise inPremises
          simp only [unfoldRule, List.mem_append, List.mem_singleton] at inPremises
          rcases inPremises with inFormals | rfl
          · simp only [formalPremises, List.mem_map] at inFormals
            obtain ⟨⟨binder, index⟩, inZip, rfl⟩ := inFormals
            have formal := List.mem_zipIdx_iff_getElem?.mp inZip
            have below : index < arguments.length :=
              length ▸ (List.getElem?_eq_some_iff.mp formal).1
            have argumentFits := (List.forall₂_iff_get.mp fits).2 index below (length ▸ below)
            simp only [List.get_eq_getElem] at argumentFits
            rw [List.getElem?_eq_getElem (length ▸ below), Option.some.injEq] at formal
            rw [← formal]
            simp only [substitute_wfWord, substitute_slot,
              getD_codes (List.getElem?_eq_getElem below)]
            exact wf_complete (hypotheses := hypotheses) (definitionKeys := definitionKeys)
              (theoremKeys := theoremKeys) covers (fits_typed argumentFits)
          · simp only [substitute_wfWord, substitute_word agree substitutes]
            exact wf_complete (hypotheses := hypotheses)
              (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers typed
        · have spineCode := substitute_spine (strings := arguments.map code) symbol 0 arguments
            (fun index value lookupValue => by simpa using getD_codes lookupValue)
          rw [length] at spineCode
          simp only [unfoldRule, substitute_convWord, convLine]
          rw [spineCode, substitute_word agree substitutes]
  | nil => exact ⟨rfl, rfl, by simp⟩
  | @cons left right lefts rights binder binders leftFits rightFits converted _ ihConverted
      ihArguments =>
      obtain ⟨leftLength, rightLength, each⟩ := ihArguments
      refine ⟨by simp [leftLength], by simp [rightLength], ?_⟩
      intro index value value' binder' leftLookup rightLookup formal
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at leftLookup rightLookup formal
          subst leftLookup rightLookup formal
          exact ⟨ihConverted, wf_complete covers (fits_typed leftFits),
            wf_complete covers (fits_typed rightFits)⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at leftLookup rightLookup formal
          exact each index value value' binder' leftLookup rightLookup formal

/-- **Completeness of derivation.** -/
theorem prov_complete (covers : Covers signature definitions theorems termKeys definitionKeys
    theoremKeys) {expression : Preterm}
    (derived : Derives signature definitions theorems context hypotheses expression) :
    Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys context
      hypotheses) (provLine expression) := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ => ∀ expression ∈ expressions,
        Derivable (systemOf signature definitions theorems termKeys definitionKeys theoremKeys
          context hypotheses) (provLine expression)) with
  | hypothesis member =>
      exact derivable_of_rule (mem_system_hypothesis member) [] (by simp) (by simp)
  | @theoremApp index declaration arguments instantiation lookup instantiated _ ih =>
      have fits := instantiated.admissible.typed
      have length := fits.length_eq
      have agree : ∀ index value, arguments[index]? = some value →
          (arguments.map code).getD index [] = code value := fun _ _ => getD_codes
      have member : theoremRule declaration ∈ theoremRules theorems index := by
        have hypothesesBelow : declaration.hypotheses.all
            (varsBelow declaration.arguments.length) = true := by
          rw [List.all_eq_true]
          intro source inSources
          obtain ⟨_, _, substitutes⟩ :=
            forall₂_exists instantiated.hypotheses source inSources
          rw [← length]
          exact varsBelow_of_substitutes substitutes
        have conclusionBelow := varsBelow_of_substitutes instantiated.conclusion
        rw [length] at conclusionBelow
        simp [theoremRules, lookup, covers.theoremsRegular index declaration lookup,
          hypothesesBelow, conclusionBelow]
      refine derivable_of_rule (mem_system_theorem (covers.theoremsListed index declaration lookup)
        member) (arguments.map code) ?_ ?_
      · intro premise inPremises
        simp only [theoremRule, List.mem_append, List.mem_map, Function.comp_apply] at inPremises
        rcases inPremises with inFormals | ⟨source, inSources, rfl⟩
        · simp only [formalPremises, List.mem_map] at inFormals
          obtain ⟨⟨binder, position⟩, inZip, rfl⟩ := inFormals
          have formal := List.mem_zipIdx_iff_getElem?.mp inZip
          have below : position < arguments.length :=
            length ▸ (List.getElem?_eq_some_iff.mp formal).1
          have argumentFits := (List.forall₂_iff_get.mp fits).2 position below (length ▸ below)
          simp only [List.get_eq_getElem] at argumentFits
          rw [List.getElem?_eq_getElem (length ▸ below), Option.some.injEq] at formal
          rw [← formal]
          simp only [substitute_wfWord, substitute_slot,
            getD_codes (List.getElem?_eq_getElem below)]
          exact wf_complete (hypotheses := hypotheses) (definitionKeys := definitionKeys)
            (theoremKeys := theoremKeys) covers (fits_typed argumentFits)
        · obtain ⟨result, inResults, substitutes⟩ :=
            forall₂_exists instantiated.hypotheses source inSources
          simp only [substitute_provWord, substitute_word agree substitutes]
          exact ih result inResults
      · simp only [theoremRule, substitute_provWord, provLine]
        rw [substitute_word agree instantiated.conclusion]
  | @conversion left right sort converted _ ih =>
      obtain ⟨leftTyped, rightTyped⟩ := Converts.typed converted
      refine derivable_of_rule (rule := ([wfWord sort (slot 0), wfWord sort (slot 1),
          convWord sort (slot 0) (slot 1), provWord (slot 0)], provWord (slot 1)))
        (mem_system_sort (sort_mem covers leftTyped) (by simp [sortRules]))
        [code left, code right] ?_ (by simp [provLine])
      intro premise member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa [wfLine] using wf_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers leftTyped
      · simpa [wfLine] using wf_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers rightTyped
      · simpa [convLine] using conv_complete (hypotheses := hypotheses)
          (definitionKeys := definitionKeys) (theoremKeys := theoremKeys) covers converted
      · simpa [provLine] using ih
  | nil => rename_i value member; cases member
  | cons _ _ ihHead ihTail =>
      rename_i value member
      rcases List.mem_cons.mp member with rfl | later
      · exact ihHead
      · exact ihTail value later

end Completeness

/-! ## Theories -/

theorem mem_of_lookup {Value : Type} {entries : List (ℕ × Value)} {key : ℕ} {value : Value}
    (found : entries.lookup key = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp at found
  | cons entry rest ih =>
      rcases entry with ⟨otherKey, otherValue⟩
      by_cases same : key = otherKey
      · subst same
        simp only [List.lookup_cons_self, Option.some.injEq] at found
        subst found
        exact List.mem_cons_self
      · have skip : (key == otherKey) = false := by simpa using same
        simp only [List.lookup, skip] at found
        exact List.mem_cons_of_mem _ (ih found)

theorem key_of_lookup {Value : Type} {entries : List (ℕ × Value)} {key : ℕ} {value : Value}
    (found : entries.lookup key = some value) : key ∈ entries.map Prod.fst :=
  List.mem_map.mpr ⟨(key, value), mem_of_lookup found, rfl⟩

theorem allRegular_of_dependencyFree {formals : Context} (free : Context.DependencyFree formals) :
    allRegular formals = true := by
  rw [allRegular, List.all_eq_true]
  intro binder member
  obtain ⟨sort, rfl⟩ := free binder member
  rfl

theorem covers_of_firstOrder {theory : Theory} (firstOrder : theory.FirstOrder) :
    Covers theory.termSignature theory.definitionSignature theory.theoremSignature
      (theory.terms.map Prod.fst) (theory.definitions.map Prod.fst)
      (theory.theorems.map Prod.fst) where
  terms _ _ found := key_of_lookup found
  termsRegular _ _ found :=
    allRegular_of_dependencyFree (firstOrder.terms _ (mem_of_lookup found)).arguments
  definitionsListed _ _ found := key_of_lookup found
  noDummies _ _ found := (firstOrder.bodies _ (mem_of_lookup found)).1
  theoremsListed _ _ found := key_of_lookup found
  theoremsRegular _ _ found :=
    allRegular_of_dependencyFree (firstOrder.theorems _ (mem_of_lookup found))

/-- **The kernel derives an expression exactly when the elementary formal
system of the theory derives its line.** -/
theorem derives_iff_derivable (theory : Theory) (firstOrder : theory.FirstOrder)
    (context : Context) (hypotheses : List Preterm) (expression : Preterm) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature context
        hypotheses expression ↔
      Derivable (system theory context hypotheses) (provLine expression) := by
  constructor
  · exact prov_complete (covers_of_firstOrder firstOrder)
  · intro derivable
    obtain ⟨other, same, derived⟩ := holds_prov (holds_of_derivable derivable)
    rwa [code_injective same]

/-- **The derivable expressions of a first-order MM0 theory form a
recursively enumerable set**, in every context and under every list of
hypotheses, read through their codes. -/
theorem derives_re (theory : Theory) (firstOrder : theory.FirstOrder) (context : Context)
    (hypotheses : List Preterm) :
    REPred fun string : List ℕ => ∃ expression, code expression = string ∧
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature context
        hypotheses expression := by
  have shifted : REPred fun string : List ℕ =>
      Derivable (system theory context hypotheses) (2 :: string) :=
    Partrec.comp (derivable_re (system theory context hypotheses))
      (Primrec.list_cons.comp (Primrec.const 2) Primrec.id).to_comp
  refine shifted.of_eq fun string => ⟨fun derivable => ?_, ?_⟩
  · obtain ⟨expression, same, derived⟩ := holds_prov (holds_of_derivable derivable)
    exact ⟨expression, same.symm, derived⟩
  · rintro ⟨expression, rfl, derived⟩
    exact (derives_iff_derivable theory firstOrder context hypotheses expression).mp derived

end Mettapedia.Languages.MM0.Kernel.FirstOrderEnumeration
