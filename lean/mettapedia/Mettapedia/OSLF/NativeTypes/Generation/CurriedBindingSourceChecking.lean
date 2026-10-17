import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingSourceCoverage

/-!
# Executable decoding of authored binding inhabitants

The decoder reads original constructor indices, base sorts and declared binder
spines. Successful values carry their exact original pattern readback. Coverage
is proved from the independent scoped typing and canonical object judgments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage.SourceChecking

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open BindingSemanticAdmission

variable {language : LanguageDef}

abbrev Parsed (language : LanguageDef) (context : List String) (sort : String)
    (pattern : Pattern) :=
  {term : Term (signature language) context sort // toPattern term = pattern}

abbrev ParsedArgs (language : LanguageDef) (context : List String)
    (parameters : List TermParam) (patterns : List Pattern) :=
  {arguments : Args (signature language) (slots parameters) context //
    toPatterns parameters arguments = patterns}

def boundVariable? : (context : List String) → (sort : String) → (index : Nat) →
    Option {position : Var context sort // variableIndex position = index}
  | [], _, _ => none
  | head :: _, sort, 0 =>
      if same : head = sort then some ⟨same ▸ Var.zero, by subst sort; rfl⟩ else none
  | _ :: tail, sort, index + 1 => do
      let previous ← boundVariable? tail sort index
      pure ⟨Var.succ previous.val, congrArg (· + 1) previous.property⟩

def unwrap? : Nat → Pattern → Option Pattern
  | 0, body => some body
  | count + 1, .lambda none body => unwrap? count body
  | _ + 1, _ => none

theorem unwrap?_wrap (domains : List String) (body : Pattern) :
    unwrap? domains.length (wrap domains body) = some body := by
  induction domains <;> simp_all [wrap, unwrap?]

def argumentBody? (parameter : TermParam) (pattern : Pattern) : Option Pattern :=
  match parameter with
  | .simple _ _ => some pattern
  | .abstractionNamed _ _ (.base _) => unwrap? 1 pattern
  | .abstractionNamed _ _ type => do
      let spine ← binderSpine? type
      unwrap? spine.1.length pattern
  | .multiAbstractionNamed _ _ _ => none

def argument? (parameter : TermParam) (pattern : Pattern) :
    Option {body : Pattern // printArgument parameter body = pattern} :=
  (argumentBody? parameter pattern).bind fun body =>
    if same : printArgument parameter body = pattern then some ⟨body, same⟩ else none

theorem argumentBody?_printed {parameter : TermParam} {scope : List String} {result : String}
    (meaning : ParameterMeaning parameter scope result) (body : Pattern) :
    argumentBody? parameter (printArgument parameter body) = some body := by
  cases meaning with
  | data => rfl
  | shorthand => rfl
  | @binding binder bodyName domain bodyType domains result spine =>
      have decoded := (binderSpine?_exact _ _ _).mpr (BinderSpine.binder domain spine)
      simp only [argumentBody?, printArgument, decoded]
      change unwrap? (domain :: domains).length (wrap (domain :: domains) body) = some body
      exact unwrap?_wrap (domain :: domains) body

theorem argument?_printed {parameter : TermParam} {scope : List String} {result : String}
    (meaning : ParameterMeaning parameter scope result) (body : Pattern) :
    argument? parameter (printArgument parameter body) = some ⟨body, rfl⟩ := by
  simp only [argument?, argumentBody?_printed meaning body, Option.bind_some, dite_true]

def arguments?
    (recurse : (context : List String) → (sort : String) → (pattern : Pattern) →
      Option (Parsed language context sort pattern))
    (context : List String) : (parameters : List TermParam) → (patterns : List Pattern) →
      Option (ParsedArgs language context parameters patterns)
  | [], [] => some ⟨.nil, rfl⟩
  | parameter :: parameters, pattern :: patterns => do
      let body ← argument? parameter pattern
      let term ← recurse ((slot parameter).1 ++ context) (slot parameter).2 body.val
      let rest ← arguments? recurse context parameters patterns
      pure ⟨.cons term.val rest.val, by
        change printArgument parameter (toPattern term.val) :: toPatterns parameters rest.val =
          pattern :: patterns
        rw [term.property, body.property, rest.property]⟩
  | _, _ => none

def constructor?
    (recurse : (context : List String) → (sort : String) → (pattern : Pattern) →
      Option (Parsed language context sort pattern))
    (admitted : Admitted language) (context : List String) (sort label : String)
    (patterns : List Pattern) (index : Fin language.terms.length) :
    Option (Parsed language context sort (.apply label patterns)) :=
  if category : language.terms[index.val].category = sort then
    if named : language.terms[index.val].label = label then do
      let arguments ← arguments? recurse context language.terms[index.val].params patterns
      let origin : Origin language sort :=
        ⟨index, category, admitted _ (List.getElem_mem index.isLt)⟩
      pure ⟨.op origin arguments.val, by
        change Pattern.apply language.terms[index.val].label
          (toPatterns language.terms[index.val].params arguments.val) = .apply label patterns
        rw [named, arguments.property]⟩
    else none
  else none

def parseFuel? (admitted : Admitted language) : Nat →
    (context : List String) → (sort : String) → (pattern : Pattern) →
    Option (Parsed language context sort pattern)
  | 0, _, _, _ => none
  | _fuel + 1, context, sort, .bvar index => do
      let position ← boundVariable? context sort index
      pure ⟨.var position.val, congrArg Pattern.bvar position.property⟩
  | fuel + 1, context, sort, .apply label patterns =>
      (List.finRange language.terms.length).findSome?
        (constructor? (parseFuel? admitted fuel) admitted context sort label patterns)
  | _ + 1, _, _, _ => none

mutual
  def nodeCount : Pattern → Nat
    | .bvar _ | .fvar _ => 1
    | .apply _ arguments => argumentsCount arguments + 1
    | .lambda _ body | .multiLambda _ _ body => nodeCount body + 1
    | .subst body value => nodeCount body + nodeCount value + 1
    | .collection _ elements _ => argumentsCount elements + 1

  def argumentsCount : List Pattern → Nat
    | [] => 0
    | head :: tail => nodeCount head + argumentsCount tail
end

theorem nodeCount_mem {pattern : Pattern} {patterns : List Pattern}
    (member : pattern ∈ patterns) : nodeCount pattern ≤ argumentsCount patterns := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [argumentsCount]; omega
      · have smaller := ih member
        simp only [argumentsCount]; omega

theorem nodeCount_wrap (domains : List String) (body : Pattern) :
    nodeCount (wrap domains body) = nodeCount body + domains.length := by
  induction domains <;> simp_all [wrap, nodeCount, Nat.add_assoc]

theorem nodeCount_argument (parameter : TermParam) (body : Pattern) :
    nodeCount body ≤ nodeCount (printArgument parameter body) := by
  cases parameter with
  | simple => exact Nat.le_refl _
  | abstractionNamed binder name type =>
      cases type <;> simp only [printArgument, nodeCount]
      all_goals first | omega | cases binderSpine? _ <;> simp only [nodeCount_wrap] <;> omega
  | multiAbstractionNamed => exact Nat.le_refl _

/-- The work bound is derived from the original pattern, rather than supplied
as an unbounded enumeration of possible terms. -/
def parse? (admitted : Admitted language) (context : List String) (sort : String)
    (pattern : Pattern) : Option (Parsed language context sort pattern) :=
  parseFuel? admitted (nodeCount pattern + 1) context sort pattern

theorem readback {admitted : Admitted language} {context : List String} {sort : String}
    {pattern : Pattern} {parsed : Parsed language context sort pattern}
    (_accepted : parse? admitted context sort pattern = some parsed) :
    toPattern parsed.val = pattern := parsed.property


theorem boundVariable?_printed {context : List String} {sort : String}
    (position : Var (Srt := String) context sort) :
    (boundVariable? context sort (variableIndex position)).isSome = true := by
  induction position with
  | zero => simp [boundVariable?, variableIndex]
  | succ previous ih =>
      simp only [boundVariable?, variableIndex]
      cases decoded : boundVariable? _ _ (variableIndex previous) with
      | none => simp [decoded] at ih
      | some value => rfl

theorem boundVariable?_present {context : List String} {sort : String} {index : Nat}
    (typed : context[index]? = some sort) :
    (boundVariable? context sort index).isSome = true := by
  obtain ⟨position, printed⟩ := Mettapedia.GSLT.Poly.BindingLanguage.exists_var_of_get typed
  have same := (variableIndex_eq_varIndex position).trans printed
  rw [← same]
  exact boundVariable?_printed position

theorem arguments?_present {bound : Nat}
    (recurse : (context : List String) → (sort : String) → (pattern : Pattern) →
      Option (Parsed language context sort pattern))
    (complete : ∀ (context : List String) (sort : String) (pattern : Pattern),
      nodeCount pattern < bound →
      HasType language FreeTypeContext.empty
        (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) →
      isObjectPattern pattern = true → pattern.hasCanonicalBinderMetadata = true →
      (recurse context sort pattern).isSome = true) :
    (parameters : List TermParam) →
    (supported : ∀ parameter ∈ parameters, ∃ scope result, ParameterMeaning parameter scope result) →
    (context : List String) → (patterns : List Pattern) →
    ArgumentsHaveTypes language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) patterns parameters →
    (∀ pattern ∈ patterns, nodeCount pattern < bound) →
    (∀ pattern ∈ patterns, isObjectPattern pattern = true) →
    (∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true) →
    (arguments? recurse context parameters patterns).isSome = true
  | [], _, _, _, typed, _, _, _ => by cases typed; rfl
  | parameter :: parameters, supported, context, patterns, typed, small, objects, canonicals => by
      cases patterns with
      | nil => cases typed
      | cons pattern patterns =>
          cases typed with
          | cons representation expectedType headTyped tailTyped =>
              obtain ⟨scope, result, meaning⟩ := supported parameter List.mem_cons_self
              obtain ⟨body, printed, bodyTyped, bodyObject, bodyCanonical, _⟩ :=
                unprintArgument meaning context pattern expectedType headTyped
                  (objects pattern List.mem_cons_self) (canonicals pattern List.mem_cons_self)
              have bodySmall : nodeCount body < bound := by
                have le := nodeCount_argument parameter body
                rw [printed] at le
                exact lt_of_le_of_lt le (small pattern List.mem_cons_self)
              have bodyPresent := complete (scope ++ context) result body bodySmall
                bodyTyped bodyObject bodyCanonical
              have restPresent := arguments?_present recurse complete parameters
                (fun next member => supported next (List.mem_cons_of_mem _ member))
                context patterns tailTyped
                (fun next member => small next (List.mem_cons_of_mem _ member))
                (fun next member => objects next (List.mem_cons_of_mem _ member))
                (fun next member => canonicals next (List.mem_cons_of_mem _ member))
              have bodyPresentSlot :
                  (recurse ((slot parameter).1 ++ context) (slot parameter).2 body).isSome = true := by
                rw [slot_meaning meaning]
                exact bodyPresent
              rw [← printed]
              simp only [arguments?, argument?_printed meaning body, Option.bind_eq_bind, Option.bind_some]
              cases decodedBody : recurse ((slot parameter).1 ++ context) (slot parameter).2 body with
              | none => simp [decodedBody] at bodyPresentSlot
              | some value =>
                  cases decodedRest : arguments? recurse context parameters patterns with
                  | none => simp [decodedRest] at restPresent
                  | some rest => rfl


theorem parseFuel?_present (admitted : Admitted language) :
    (bound : Nat) → (context : List String) → (sort : String) → (pattern : Pattern) →
    nodeCount pattern < bound →
    HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) →
    isObjectPattern pattern = true → pattern.hasCanonicalBinderMetadata = true →
    (parseFuel? admitted bound context sort pattern).isSome = true
  | 0, _, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, context, sort, pattern, small, typed, object, canonical => by
      cases pattern with
      | bvar index =>
          cases typed with
          | bvar lookup =>
              have present := boundVariable?_present
                (Mettapedia.GSLT.Poly.BindingLanguage.lookup_base lookup)
              simp only [parseFuel?]
              cases decoded : boundVariable? context sort index with
              | none => simp [decoded] at present
              | some position => rfl
      | fvar name => cases typed with | fvar lookup => simp [FreeTypeContext.empty] at lookup
      | apply label patterns =>
          cases typed with
          | constructor member ordinary argumentsTyped =>
              rename_i declaration
              have smaller : ∀ pattern ∈ patterns, nodeCount pattern < bound := by
                intro pattern memberPattern
                have le := nodeCount_mem memberPattern
                simp only [nodeCount] at small
                omega
              have objects : ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
                simpa [isObjectPattern, Mettapedia.GSLT.Poly.BindingLanguage.isObjectPatternList_eq_true_iff] using object
              have canonicals : ∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true :=
                (Pattern.hasCanonicalBinderMetadataList_eq_true_iff patterns).mp canonical
              have argumentsPresent := arguments?_present (parseFuel? admitted bound)
                (fun context sort pattern small typed object canonical =>
                  parseFuel?_present admitted bound context sort pattern small typed object canonical)
                declaration.params (admitted declaration member) context patterns argumentsTyped
                smaller objects canonicals
              obtain ⟨index, valid, original⟩ := List.mem_iff_getElem.mp member
              subst declaration
              simp only [parseFuel?]
              apply List.findSome?_isSome_iff.mpr
              refine ⟨⟨index, valid⟩, by simp, ?_⟩
              simp only [constructor?]
              cases decoded : arguments? (parseFuel? admitted bound) context
                  language.terms[index].params patterns with
              | none => simp [decoded] at argumentsPresent
              | some arguments => rfl
      | lambda => cases typed
      | multiLambda => cases typed
      | subst => simp [isObjectPattern] at object
      | collection kind elements rest =>
          obtain ⟨declaration, member, _, name, element, shape⟩ :=
            declared_collection_constructor_of_hasSort typed
          obtain ⟨scope, result, impossible⟩ := admitted declaration member
            (.simple name (.collection kind element))
            (by rw [shape]; exact List.mem_singleton_self _)
          cases impossible

theorem complete (admitted : Admitted language) {context : List String} {sort : String}
    (source : Source language context sort) :
    ∃ parsed, parse? admitted context sort source.val = some parsed := by
  exact Option.isSome_iff_exists.mp (parseFuel?_present admitted (nodeCount source.val + 1)
    context sort source.val (Nat.lt_succ_self _) source.property.1
    source.property.2.1 source.property.2.2)

theorem parse?_exact (admitted : Admitted language) (context : List String) (sort : String)
    (pattern : Pattern) :
    (parse? admitted context sort pattern).isSome = true ↔
      HasType language FreeTypeContext.empty
        (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) ∧
      isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true := by
  constructor
  · intro accepted
    obtain ⟨parsed, _⟩ := Option.isSome_iff_exists.mp accepted
    rw [← parsed.property]
    exact ⟨toPattern_typed parsed.val, toPattern_object parsed.val, toPattern_canonical parsed.val⟩
  · intro source
    obtain ⟨parsed, accepted⟩ := complete admitted ⟨pattern, source⟩
    simp only [accepted, Option.isSome_some]

theorem parse?_printed (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    {context : List String} {sort : String} (term : Term (signature language) context sort) :
    parse? admitted context sort (toPattern term) = some ⟨term, rfl⟩ := by
  obtain ⟨parsed, accepted⟩ := complete admitted
    ⟨toPattern term, toPattern_typed term, toPattern_object term, toPattern_canonical term⟩
  have same : parsed = ⟨term, rfl⟩ :=
    Subtype.ext (toPattern_injective labels parsed.property)
  simpa only [same] using accepted

/-- A computational inverse of the independent source presentation. The only
proof argument discharges the parser's proved coverage test. -/
def decode (admitted : Admitted language) {context : List String} {sort : String}
    (source : Source language context sort) : Term (signature language) context sort :=
  ((parse? admitted context sort source.val).get
    ((parse?_exact admitted context sort source.val).mpr source.property)).val

theorem decode_readback (admitted : Admitted language) {context : List String} {sort : String}
    (source : Source language context sort) : toPattern (decode admitted source) = source.val :=
  ((parse? admitted context sort source.val).get
    ((parse?_exact admitted context sort source.val).mpr source.property)).property

theorem decode_equiv (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) {context : List String} {sort : String}
    (source : Source language context sort) :
    decode admitted source = (sourceEquiv admitted labels context sort).symm source := by
  apply toPattern_injective labels
  exact (decode_readback admitted source).trans
    (congrArg Subtype.val ((sourceEquiv admitted labels context sort).apply_symm_apply source)).symm

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage.SourceChecking
