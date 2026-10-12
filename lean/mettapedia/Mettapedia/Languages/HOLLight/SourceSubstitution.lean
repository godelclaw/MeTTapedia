import Mettapedia.Languages.OpenTheory.TheoremSubstitutionRule
import Mettapedia.Languages.OpenTheory.Definitions
import Mathlib.Data.String.Basic

/-!
# HOL Light substitution through the shared simple-type syntax

HOL Light revision `924faf0c3471a04174ffdeb8576ce7cabcb92d64`
stores substitution pairs as `(replacement, key)`. Its `type_subst` takes
the first matching key and ignores non-name keys. OpenTheory's normalized
table takes the last maplet. Reversing the source list, after discarding keys
which cannot match a type name, connects these conventions.

These laws concern the source calculus and the existing substitution algebra.
They do not validate an external artifact reader or a native implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight

open Mettapedia.Languages.OpenTheory

namespace SourceSubstitution

/-! OCaml names are byte strings. The structured exporter maps each byte to
the Unicode scalar value with that code, escaping it in JSON as needed.
This includes NUL and bytes that are not valid standalone UTF-8. -/

namespace SourceOctets

def encode (bytes : List UInt8) : String := String.ofList (bytes.map Char.ofUInt8)

def decode (text : String) : List UInt8 := text.toList.map Char.toUInt8

@[simp] theorem char_roundtrip (byte : UInt8) : (Char.ofUInt8 byte).toUInt8 = byte := by
  simp [Char.ofUInt8, Char.toUInt8]

theorem char_injective : Function.Injective Char.ofUInt8 := by
  intro left right equal
  have decoded := congrArg Char.toUInt8 equal
  simpa using decoded

@[simp] theorem char_eq_iff (left right : UInt8) :
    Char.ofUInt8 left = Char.ofUInt8 right ↔ left = right := char_injective.eq_iff

@[simp] theorem char_lt_iff (left right : UInt8) :
    Char.ofUInt8 left < Char.ofUInt8 right ↔ left < right := by
  change left.toNat < right.toNat ↔ left.toNat < right.toNat
  rfl

@[simp] theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = bytes := by
  simp [decode, encode, String.toList_ofList, List.map_map, Function.comp_def]

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

theorem characters_lt_iff (left right : List UInt8) :
    left.map Char.ofUInt8 < right.map Char.ofUInt8 ↔ left < right := by
  induction left generalizing right with
  | nil => cases right <;> simp
  | cons byte bytes ih =>
      cases right with
      | nil => simp
      | cons other others => simp [List.cons_lt_cons_iff, ih]

theorem encode_lt_iff (left right : List UInt8) : encode left < encode right ↔ left < right := by
  simpa only [encode, String.lt_iff_toList_lt, String.toList_ofList]
    using characters_lt_iff left right

theorem encode_le_iff (left right : List UInt8) : encode left ≤ encode right ↔ left ≤ right := by
  change (¬ encode right < encode left) ↔ (¬ right < left)
  exact not_congr (encode_lt_iff right left)

/-- Identity and ordering of a source name survive the representation change. -/
def globalName (bytes : List UInt8) : Name := .global (encode bytes)

theorem globalName_injective : Function.Injective globalName := by
  intro left right equal
  exact encode_injective (congrArg Name.component equal)

end SourceOctets

/-- The exact first-match action on a name; non-name keys are ignored. -/
def variableType (entries : List (Ty × Ty)) (name : Name) : Ty :=
  match entries with
  | [] => .var name
  | (replacement, .var key) :: rest =>
      if name = key then replacement else variableType rest name
  | (_, .op _ _) :: rest => variableType rest name

/-- The independent structural source action is simultaneous, rather than
recursing into the replacement selected for a name. -/
def typeAction (entries : List (Ty × Ty)) : Ty → Ty
  | .var name => variableType entries name
  | .op operator arguments => .op operator (arguments.map (typeAction entries))
termination_by type => sizeOf type

/-- Retain all applicable source maplets in their original order. -/
def variableEntries (entries : List (Ty × Ty)) : List (Name × Ty) :=
  entries.filterMap fun (replacement, key) =>
    match key with
    | .var name => some (name, replacement)
    | .op _ _ => none

/-- Reuse the existing normalized table with HOL Light's first-match order. -/
def typeSubstitution (entries : List (Ty × Ty)) : TypeSubst :=
  TypeSubst.ofList (variableEntries entries).reverse

theorem typeSubstitution_cons_variable (replacement : Ty) (key : Name)
    (rest : List (Ty × Ty)) :
    typeSubstitution ((replacement, .var key) :: rest) =
      (typeSubstitution rest).insert key replacement := by
  simp only [typeSubstitution, variableEntries, List.filterMap_cons, List.reverse_cons]
  exact TypeSubst.ofList_append_singleton _ key replacement

theorem typeSubstitution_cons_operator (replacement : Ty) (operator : TypeOp)
    (arguments : List Ty) (rest : List (Ty × Ty)) :
    typeSubstitution ((replacement, .op operator arguments) :: rest) =
      typeSubstitution rest := by
  rfl

/-- First-match action survives normalization, including an identity maplet
which shadows a later non-identity replacement. -/
theorem apply_variable (entries : List (Ty × Ty)) (name : Name) :
    (typeSubstitution entries).apply (.var name) = variableType entries name := by
  induction entries with
  | nil => simp [typeSubstitution, variableEntries, TypeSubst.ofList, variableType]
  | cons entry rest ih =>
      rcases entry with ⟨replacement, key⟩
      cases key with
      | var key =>
          rw [typeSubstitution_cons_variable]
          by_cases same : name = key
          · subst name
            rw [TypeSubst.apply_insert_same]
            simp [variableType]
          · rw [TypeSubst.apply_insert_ne _ _ same, ih]
            simp only [variableType, if_neg same]
      | op operator arguments =>
          rw [typeSubstitution_cons_operator, ih]
          rfl

/-- General correspondence for every source simple type, without bounds on
type depth, map length, duplicate keys or unused non-name keys. -/
theorem apply_type (entries : List (Ty × Ty)) : ∀ type : Ty,
    (typeSubstitution entries).apply type = typeAction entries type
  | .var name => by simpa only [typeAction] using apply_variable entries name
  | .op operator arguments => by
      simp only [TypeSubst.apply_op, typeAction]
      congr 1
      exact List.map_congr_left (fun type _ => apply_type entries type)
termination_by type => sizeOf type

/-- Source instantiation inherits the proved identity law of shared STT. -/
theorem typeAction_nil (type : Ty) : typeAction [] type = type := by
  rw [← apply_type, typeSubstitution]
  exact TypeSubst.apply_empty type

/-- Successive source instantiations are represented by the existing
composition operation, in the same application order. -/
theorem apply_composition (first second : List (Ty × Ty)) (type : Ty) :
    ((typeSubstitution first).compose (typeSubstitution second)).apply type =
      typeAction second (typeAction first type) := by
  rw [TypeSubst.apply_compose, apply_type, apply_type]

/-! ## Term maplets: admission precedes lookup

HOL Light checks every maplet, including shadowed and unused maplets.
The raw shared term table already has first-match lookup, so it is used
without the last-wins `ofList` normalization.
-/

abbrev TermMaplet := CheckedSourceTerm × SourceTerm

def TermMapletAdmissible (entry : TermMaplet) : Prop :=
  match entry.2 with
  | .var _ type => entry.1.ty = type
  | _ => False

def termMapletB (entry : TermMaplet) : Bool :=
  match entry.2 with
  | .var _ type => Ty.same entry.1.ty type
  | _ => false

theorem termMapletB_eq_true_iff (entry : TermMaplet) :
    termMapletB entry = true ↔ TermMapletAdmissible entry := by
  rcases entry with ⟨replacement, key⟩
  cases key <;> simp only [termMapletB, TermMapletAdmissible,
    Bool.false_eq_true, Ty.same_eq_true_iff]

def TermMapletsAdmissible (entries : List TermMaplet) : Prop :=
  ∀ entry ∈ entries, TermMapletAdmissible entry

theorem all_termMapletB_eq_true_iff (entries : List TermMaplet) :
    entries.all termMapletB = true ↔ TermMapletsAdmissible entries := by
  simp only [List.all_eq_true, termMapletB_eq_true_iff, TermMapletsAdmissible]

def termEntries (entries : List TermMaplet) : List (SourceVar × CheckedSourceTerm) :=
  entries.filterMap fun (replacement, key) =>
    match key with
    | .var name type => some (⟨name, type⟩, replacement)
    | _ => none

def termSubstitution (entries : List TermMaplet) : TermSubst :=
  ⟨TypeSubst.empty, termEntries entries⟩

/-- The validity proof observes the entire source list before any lookup.
No shadowed ill-typed entry is silently normalized away. -/
theorem termSubstitution_typeCorrect (entries : List TermMaplet)
    (admitted : TermMapletsAdmissible entries) :
    (termSubstitution entries).TypeCorrect := by
  intro entry member
  obtain ⟨⟨replacement, key⟩, sourceMember, mapped⟩ :=
    List.mem_filterMap.mp member
  have valid := admitted (replacement, key) sourceMember
  cases key with
  | const constant type => exact False.elim valid
  | app function argument => exact False.elim valid
  | abs name type body => exact False.elim valid
  | var name type =>
    simp only [Option.some.injEq] at mapped
    subst entry
    exact valid

def admitTermSubstitution (entries : List TermMaplet) :
    Option TypeCorrectTermSubstitution :=
  if valid : entries.all termMapletB then
    some ⟨termSubstitution entries, termSubstitution_typeCorrect entries
      ((all_termMapletB_eq_true_iff entries).mp valid)⟩
  else none

theorem admitTermSubstitution_isSome_iff (entries : List TermMaplet) :
    (admitTermSubstitution entries).isSome = true ↔
      TermMapletsAdmissible entries := by
  by_cases valid : entries.all termMapletB = true
  · have admitted := (all_termMapletB_eq_true_iff entries).mp valid
    simp [admitTermSubstitution, valid, admitted]
  · have refused : ¬ TermMapletsAdmissible entries :=
      fun admitted => valid ((all_termMapletB_eq_true_iff entries).mpr admitted)
    simp [admitTermSubstitution, valid, refused]

theorem admittedTermSubstitution_raw {entries : List TermMaplet}
    {substitution : TypeCorrectTermSubstitution}
    (accepted : admitTermSubstitution entries = some substitution) :
    substitution.raw = termSubstitution entries := by
  unfold admitTermSubstitution at accepted
  split at accepted
  · cases Option.some.inj accepted
    rfl
  · contradiction

/-- Type instantiation has no term maplets; the shared substitution rule
supplies capture-free action and its general typing theorem. -/
def typeOnlySubstitution (entries : List (Ty × Ty)) :
    TypeCorrectTermSubstitution :=
  TypeCorrectTermSubstitution.ofTypes (typeSubstitution entries)

/-- Source lookup is first-match on the full typed variable identity. -/
def termReplacement (entries : List TermMaplet) (key : SourceVar) :
    Option CheckedSourceTerm :=
  match entries with
  | [] => none
  | (replacement, .var name type) :: rest =>
      if sourceVarSame ⟨name, type⟩ key then some replacement else termReplacement rest key
  | (_, _) :: rest => termReplacement rest key

theorem lookup_termSubstitution (entries : List TermMaplet) (key : SourceVar) :
    (termSubstitution entries).lookup key = termReplacement entries key := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨replacement, sourceKey⟩
      cases sourceKey <;>
        simp only [termSubstitution, termEntries, List.filterMap_cons,
          TermSubst.lookup, List.find?_cons, Option.map, TermSubst.keySame,
          termReplacement] at *
      case var name type =>
        cases matched : sourceVarSame ⟨name, type⟩ key <;>
          simp_all only [Bool.false_eq_true, ↓reduceIte]
      all_goals exact ih

/-! ## Independent nominal type instantiation

HOL Light's `inst` renames a binder when instantiating its type would capture
a free variable or confuse two scoped variables. This structural relation
states the required named result independently of canonical substitution.
Bound occurrences keep their position; free occurrences must remain free.
It permits different fresh spellings and proves that all such results have
the same canonical image. Correspondence with the source's particular
clash-handling procedure is a further implementation-independent source lemma.
-/

inductive NominalTypeInstantiation (entries : List (Ty × Ty)) :
    List SourceVar → List SourceVar → SourceTerm → SourceTerm → Prop where
  | constant {before after : List SourceVar} (constant : Const) (type : Ty) :
      NominalTypeInstantiation entries before after (.const constant type)
        (.const constant (typeAction entries type))
  | free {before after : List SourceVar} (name : Name) (type : Ty)
      (sourceFree : boundIndex ⟨name, type⟩ before = none)
      (targetFree : boundIndex ⟨name, typeAction entries type⟩ after = none) :
      NominalTypeInstantiation entries before after (.var name type)
        (.var name (typeAction entries type))
  | bound {before after : List SourceVar} (sourceName targetName : Name) (type : Ty) (index : Nat)
      (sourceBound : boundIndex ⟨sourceName, type⟩ before = some index)
      (targetBound : boundIndex ⟨targetName, typeAction entries type⟩ after = some index) :
      NominalTypeInstantiation entries before after (.var sourceName type)
        (.var targetName (typeAction entries type))
  | app {before after : List SourceVar} {function argument function' argument' : SourceTerm}
      (functionInstantiated : NominalTypeInstantiation entries before after function function')
      (argumentInstantiated : NominalTypeInstantiation entries before after argument argument') :
      NominalTypeInstantiation entries before after (.app function argument) (.app function' argument')
  | abs {before after : List SourceVar} (sourceName targetName : Name) (domain : Ty)
      {body body' : SourceTerm}
      (bodyInstantiated : NominalTypeInstantiation entries
        (⟨sourceName, domain⟩ :: before) (⟨targetName, typeAction entries domain⟩ :: after) body body') :
      NominalTypeInstantiation entries before after (.abs sourceName domain body)
        (.abs targetName (typeAction entries domain) body')

/-- The independent named binding rules commute with the existing shared
substitution, including substitutions that identify distinct source types. -/
theorem NominalTypeInstantiation.toDB {entries : List (Ty × Ty)}
    {before after : List SourceVar} {source target : SourceTerm}
    (instantiated : NominalTypeInstantiation entries before after source target) :
    target.toDB after = (typeOnlySubstitution entries).raw.applyDB (source.toDB before) := by
  induction instantiated with
  | constant constant type =>
      simp [SourceTerm.toDB, typeOnlySubstitution, apply_type]
  | free name type sourceFree targetFree =>
      simp [SourceTerm.toDB, sourceFree, targetFree, typeOnlySubstitution,
        TermSubst.applyDB, TermSubst.lookup, TypeSubst.applyVar, apply_type]
  | bound sourceName targetName type index sourceBound targetBound =>
      simp [SourceTerm.toDB, sourceBound, targetBound]
  | app _ _ functionIH argumentIH =>
      simp only [SourceTerm.toDB, TermSubst.applyDB_app, functionIH, argumentIH]
  | abs sourceName targetName domain _ bodyIH =>
      simp only [SourceTerm.toDB, TermSubst.applyDB_abs, bodyIH,
        typeOnlySubstitution, apply_type]

/-- Any independently scoped named result checks to exactly the substituted
canonical term. The existing general substitution typing theorem supplies
the type, rather than a second named checker. -/
theorem NominalTypeInstantiation.checked {entries : List (Ty × Ty)}
    (source : CanonicalTerm) {sourceTerm target : SourceTerm}
    (sourceChecked : sourceTerm.check = some source)
    (instantiated : NominalTypeInstantiation entries [] [] sourceTerm target) :
    target.check = some ((typeOnlySubstitution entries).apply source) := by
  rw [SourceTerm.check_eq_some_iff]
  have original := (SourceTerm.check_eq_some_iff _ _).mp sourceChecked
  simpa only [original, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked]
    using instantiated.toDB

/-- Fresh binder choices affect spelling but not the resulting HOL term. -/
theorem NominalTypeInstantiation.alpha_unique {entries : List (Ty × Ty)}
    {source first second : SourceTerm}
    (left : NominalTypeInstantiation entries [] [] source first)
    (right : NominalTypeInstantiation entries [] [] source second) : first.AlphaEq second := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  exact left.toDB.trans right.toDB.symm

/-- The source's typed free variables. Binder occurrences are removed by
exact name-and-type identity; duplicate free occurrences remain inspectable. -/
def nominalFreeVariables : SourceTerm → List SourceVar
  | .const _ _ => []
  | .var name type => [⟨name, type⟩]
  | .app function argument => nominalFreeVariables function ++ nominalFreeVariables argument
  | .abs name domain body =>
      (nominalFreeVariables body).filter fun sourceVar => !sourceVarSame sourceVar ⟨name, domain⟩

/-- Ambient binder lookup matters only on the named term's free variables.
This is proved from the source grammar, independently of substitution. -/
theorem toDB_of_free_lookup_agreement (source : SourceTerm) (before after : List SourceVar)
    (agreement : ∀ sourceVar ∈ nominalFreeVariables source,
      boundIndex sourceVar before = boundIndex sourceVar after) :
    source.toDB before = source.toDB after := by
  cases source with
  | const constant type => simp only [SourceTerm.toDB]
  | var name type =>
      have found := agreement ⟨name, type⟩ (by simp [nominalFreeVariables])
      simp only [SourceTerm.toDB, found]
  | app function argument =>
      simp only [SourceTerm.toDB]
      rw [toDB_of_free_lookup_agreement function before after (fun sourceVar member =>
        agreement sourceVar (List.mem_append_left _ member)),
        toDB_of_free_lookup_agreement argument before after (fun sourceVar member =>
          agreement sourceVar (List.mem_append_right _ member))]
  | abs name domain body =>
      simp only [SourceTerm.toDB]
      congr 1
      apply toDB_of_free_lookup_agreement body
      intro sourceVar member
      by_cases same : sourceVarSame sourceVar ⟨name, domain⟩ = true
      · simp [boundIndex, same]
      · have free : sourceVar ∈ nominalFreeVariables (.abs name domain body) := by
          simp only [nominalFreeVariables, List.mem_filter]
          exact ⟨member, by simp [same]⟩
        simp [boundIndex, same, agreement sourceVar free]
termination_by sizeOf source

theorem toDB_no_capture (source : SourceTerm) (binders : List SourceVar)
    (avoids : ∀ sourceVar ∈ nominalFreeVariables source, boundIndex sourceVar binders = none) :
    source.toDB binders = source.toDB [] :=
  toDB_of_free_lookup_agreement source binders []
    (fun sourceVar member => by simpa [boundIndex] using avoids sourceVar member)

/-- Named variable substitution with independently stated binding guards.
A selected replacement is inserted unchanged after enclosing binders have
been chosen to avoid its free variables. Scoped occurrences are never looked
up in the term map. All-maplet type admission remains a separate source gate. -/
inductive NominalTermInstantiation (entries : List TermMaplet) :
    List SourceVar → List SourceVar → SourceTerm → SourceTerm → Prop where
  | constant {before after : List SourceVar} (constant : Const) (type : Ty) :
      NominalTermInstantiation entries before after (.const constant type) (.const constant type)
  | free {before after : List SourceVar} (name : Name) (type : Ty)
      (sourceFree : boundIndex ⟨name, type⟩ before = none)
      (targetFree : boundIndex ⟨name, type⟩ after = none)
      (notReplaced : termReplacement entries ⟨name, type⟩ = none) :
      NominalTermInstantiation entries before after (.var name type) (.var name type)
  | replacement {before after : List SourceVar} (name : Name) (type : Ty)
      (replacement : CheckedSourceTerm)
      (sourceFree : boundIndex ⟨name, type⟩ before = none)
      (selected : termReplacement entries ⟨name, type⟩ = some replacement)
      (avoids : ∀ sourceVar ∈ nominalFreeVariables replacement.source,
        boundIndex sourceVar after = none) :
      NominalTermInstantiation entries before after (.var name type) replacement.source
  | bound {before after : List SourceVar} (sourceName targetName : Name) (type : Ty) (index : Nat)
      (sourceBound : boundIndex ⟨sourceName, type⟩ before = some index)
      (targetBound : boundIndex ⟨targetName, type⟩ after = some index) :
      NominalTermInstantiation entries before after (.var sourceName type) (.var targetName type)
  | app {before after : List SourceVar} {function argument function' argument' : SourceTerm}
      (functionInstantiated : NominalTermInstantiation entries before after function function')
      (argumentInstantiated : NominalTermInstantiation entries before after argument argument') :
      NominalTermInstantiation entries before after (.app function argument) (.app function' argument')
  | abs {before after : List SourceVar} (sourceName targetName : Name) (domain : Ty)
      {body body' : SourceTerm}
      (bodyInstantiated : NominalTermInstantiation entries
        (⟨sourceName, domain⟩ :: before) (⟨targetName, domain⟩ :: after) body body') :
      NominalTermInstantiation entries before after (.abs sourceName domain body)
        (.abs targetName domain body')

theorem NominalTermInstantiation.toDB {entries : List TermMaplet}
    {before after : List SourceVar} {source target : SourceTerm}
    (instantiated : NominalTermInstantiation entries before after source target) :
    target.toDB after = (termSubstitution entries).applyDB (source.toDB before) := by
  induction instantiated with
  | constant constant type => simp [SourceTerm.toDB, termSubstitution]
  | free name type sourceFree targetFree notReplaced =>
      have found : (termSubstitution entries).lookup
          ((termSubstitution entries).types.applyVar ⟨name, type⟩) = none := by
        simpa only [termSubstitution, TypeSubst.applyVar, TypeSubst.apply_empty] using
          (lookup_termSubstitution entries ⟨name, type⟩).trans notReplaced
      simp only [SourceTerm.toDB, sourceFree, targetFree]
      rw [TermSubst.applyDB_free_of_lookup_none _ _ found]
      simp only [termSubstitution, TypeSubst.applyVar, TypeSubst.apply_empty]
  | replacement name type replacement sourceFree selected avoids =>
      rw [toDB_no_capture replacement.source _ avoids]
      simp only [SourceTerm.toDB, sourceFree, TermSubst.applyDB]
      have found : (termSubstitution entries).lookup
          ((termSubstitution entries).types.applyVar ⟨name, type⟩) = some replacement := by
        simpa only [termSubstitution, TypeSubst.applyVar, TypeSubst.apply_empty] using
          (lookup_termSubstitution entries ⟨name, type⟩).trans selected
      rw [found]
      rfl
  | bound sourceName targetName type index sourceBound targetBound =>
      simp [SourceTerm.toDB, sourceBound, targetBound]
  | app _ _ functionIH argumentIH =>
      simp only [SourceTerm.toDB, TermSubst.applyDB_app, functionIH, argumentIH]
  | abs sourceName targetName domain _ bodyIH =>
      simp only [SourceTerm.toDB, TermSubst.applyDB_abs, bodyIH,
        termSubstitution, TypeSubst.apply_empty]

theorem NominalTermInstantiation.checked {entries : List TermMaplet}
    (source : CanonicalTerm) {sourceTerm target : SourceTerm}
    (admitted : TermMapletsAdmissible entries) (sourceChecked : sourceTerm.check = some source)
    (instantiated : NominalTermInstantiation entries [] [] sourceTerm target) :
    target.check = some ((termSubstitution entries).applyChecked
      (termSubstitution_typeCorrect entries admitted) source) := by
  rw [SourceTerm.check_eq_some_iff]
  have original := (SourceTerm.check_eq_some_iff _ _).mp sourceChecked
  simpa only [original, TermSubst.applyChecked] using instantiated.toDB

theorem NominalTermInstantiation.alpha_unique {entries : List TermMaplet}
    {source first second : SourceTerm}
    (left : NominalTermInstantiation entries [] [] source first)
    (right : NominalTermInstantiation entries [] [] source second) : first.AlphaEq second := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  exact left.toDB.trans right.toDB.symm

namespace Controls

def alpha : Name := .global "A"
def beta : Name := .global "B"

/-- The first replacement wins, unlike an unreversed OpenTheory table. -/
theorem first_duplicate_wins :
    typeAction [(Ty.bool, .var alpha), (.var beta, .var alpha)] (.var alpha) = Ty.bool := by
  simp [typeAction, variableType]

/-- Removing a leading identity must also remove the later shadowed entry. -/
theorem leading_identity_shadows :
    (typeSubstitution [(.var alpha, .var alpha), (Ty.bool, .var alpha)]).apply
      (.var alpha) = .var alpha := by
  rw [apply_variable]
  simp [variableType]

/-- A non-name key cannot substitute an entire function type. -/
theorem nonvariable_key_ignored :
    typeAction [(Ty.bool, .function (.var alpha) (.var beta))]
      (.function (.var alpha) (.var beta)) = .function (.var alpha) (.var beta) := by
  simp [typeAction, Ty.function, variableType]

/-- Replacements are simultaneous: the second maplet does not rewrite the
type supplied by the first one. -/
theorem replacement_not_rewritten :
    typeAction [(.var beta, .var alpha), (Ty.bool, .var beta)] (.var alpha) = .var beta := by
  simp [typeAction, variableType]

def checkedBool (name : String) : CheckedSourceTerm :=
  CheckedSourceTerm.ofVariable ⟨.global name, Ty.bool⟩

def boolKey : SourceTerm := .var (.global "p") Ty.bool

theorem first_term_duplicate_wins :
    (termSubstitution [(checkedBool "q", boolKey), (checkedBool "r", boolKey)]).lookup
      ⟨.global "p", Ty.bool⟩ = some (checkedBool "q") := by
  rw [lookup_termSubstitution]
  simp [termReplacement, boolKey, sourceVarSame]

/-- A shadowed wrong-typed maplet still violates the source admission rule. -/
theorem shadowed_wrong_type_refused :
    ¬ TermMapletsAdmissible
      [(checkedBool "q", boolKey),
        (CheckedSourceTerm.ofVariable ⟨.global "x", .var alpha⟩, boolKey)] := by
  intro valid
  have wrong := valid
    (CheckedSourceTerm.ofVariable ⟨.global "x", .var alpha⟩, boolKey)
    (by simp)
  cases wrong

theorem nonvariable_term_key_refused :
    ¬ TermMapletsAdmissible [(checkedBool "q", .abs (.global "p") Ty.bool boolKey)] := by
  intro valid
  exact valid (checkedBool "q", .abs (.global "p") Ty.bool boolKey) (by simp)

def collisionSource : SourceTerm :=
  .abs (.global "x") (.var alpha) (.var (.global "x") (.var beta))

def collisionSafe : SourceTerm :=
  .abs (.global "y") (.var beta) (.var (.global "x") (.var beta))

def collisionCaptured : SourceTerm :=
  .abs (.global "x") (.var beta) (.var (.global "x") (.var beta))

def identifyTypes : List (Ty × Ty) := [(.var beta, .var alpha)]

/-- The free occurrence of x has another type before instantiation. Renaming
the binder keeps it free after the two source types become equal. -/
theorem collision_safe_instantiation :
    NominalTypeInstantiation identifyTypes [] [] collisionSource collisionSafe := by
  have domain : typeAction identifyTypes (.var alpha) = .var beta := by
    simp [typeAction, identifyTypes, variableType]
  have codomain : typeAction identifyTypes (.var beta) = .var beta := by
    simp [typeAction, identifyTypes, variableType, alpha, beta, Name.global]
  have body : NominalTypeInstantiation identifyTypes
      [⟨.global "x", .var alpha⟩] [⟨.global "y", typeAction identifyTypes (.var alpha)⟩]
      (.var (.global "x") (.var beta))
      (.var (.global "x") (typeAction identifyTypes (.var beta))) := by
    apply NominalTypeInstantiation.free
    · simp [boundIndex, sourceVarSame, alpha, beta, Name.global]
    · simp [boundIndex, sourceVarSame, Name.global]
  simpa only [collisionSource, collisionSafe, domain, codomain] using
    NominalTypeInstantiation.abs (.global "x") (.global "y") (.var alpha) body

/-- Merely replacing type annotations changes a free occurrence into a bound
one, so it is not an admissible instantiation of this source term. -/
theorem collision_capture_refused :
    ¬ NominalTypeInstantiation identifyTypes [] [] collisionSource collisionCaptured := by
  intro instantiated
  have agreement := instantiated.toDB
  simp [collisionSource, collisionCaptured, identifyTypes, SourceTerm.toDB, boundIndex,
    sourceVarSame, alpha, beta, Name.global, typeOnlySubstitution, TermSubst.applyDB,
    TermSubst.lookup, TypeSubst.applyVar] at agreement

def captureEntries : List TermMaplet :=
  [(checkedBool "y", .var (.global "x") Ty.bool)]

def captureSource : SourceTerm :=
  .abs (.global "y") Ty.bool (.var (.global "x") Ty.bool)

def captureSafe : SourceTerm :=
  .abs (.global "z") Ty.bool (.var (.global "y") Ty.bool)

def captureWrong : SourceTerm :=
  .abs (.global "y") Ty.bool (.var (.global "y") Ty.bool)

theorem captureEntries_admitted : TermMapletsAdmissible captureEntries := by
  intro entry member
  have equal : entry = (checkedBool "y", .var (.global "x") Ty.bool) := by
    simpa [captureEntries] using member
  subst entry
  rfl

/-- Renaming the enclosing binder lets the selected replacement keep its
free variable, while all source maplets retain their checked types. -/
theorem capture_safe_substitution :
    NominalTermInstantiation captureEntries [] [] captureSource captureSafe := by
  change NominalTermInstantiation captureEntries [] []
    (.abs (.global "y") Ty.bool (.var (.global "x") Ty.bool))
    (.abs (.global "z") Ty.bool (.var (.global "y") Ty.bool))
  apply NominalTermInstantiation.abs
  apply NominalTermInstantiation.replacement (.global "x") Ty.bool (checkedBool "y")
  · simp [boundIndex, sourceVarSame, Name.global]
  · simp [captureEntries, termReplacement, sourceVarSame]
  · intro sourceVar member
    have equal : sourceVar = ⟨.global "y", Ty.bool⟩ := by
      simpa [nominalFreeVariables, checkedBool, CheckedSourceTerm.ofVariable] using member
    subst sourceVar
    simp [boundIndex, sourceVarSame, Name.global]

theorem capture_wrong_substitution_refused :
    ¬ NominalTermInstantiation captureEntries [] [] captureSource captureWrong := by
  intro instantiated
  have agreement := instantiated.toDB
  simp [captureSource, captureWrong, SourceTerm.toDB, boundIndex, sourceVarSame, Name.global,
    termSubstitution, captureEntries, TermSubst.applyDB, TermSubst.lookup, TermSubst.keySame,
    termEntries, TypeSubst.applyVar, checkedBool, CheckedSourceTerm.ofVariable,
    CheckedSourceTerm.canonical] at agreement

end Controls
end SourceSubstitution
end Mettapedia.Languages.HOLLight
