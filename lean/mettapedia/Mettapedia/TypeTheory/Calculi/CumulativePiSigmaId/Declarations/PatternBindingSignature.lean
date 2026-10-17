import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage
import Mettapedia.OSLF.Syntax.PatternAsBindingSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Finite declaration packages for the authored pattern binding signature

The existing pattern binding signature supplies all source operators and binder
arities. Constructor metadata is retained in reversible declaration names;
variables and binders remain native variables and lambda spines. A package is
an actual finite declaration list for its used operators, with literal lookup
and formation proofs. No operational equations are installed by this module.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature

open Presentation Presentation.Declaration Presentation.FormationSensitive
open Mettapedia.OSLF Mettapedia.OSLF.Binding.PatternPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax


/-- The single source data sort has a dedicated opaque native declaration. -/
def dataName : DeclName := `GSLT.Pattern

private def stringsName : List String → Lean.Name
  | [] => .anonymous
  | name :: rest => .str (stringsName rest) name

private def stringsFromName : Lean.Name → Option (List String)
  | .anonymous => some []
  | .str rest name => (stringsFromName rest).map (name :: ·)
  | .num _ _ => none

private theorem stringsName_roundtrip (names : List String) :
    stringsFromName (stringsName names) = some names := by
  induction names with
  | nil => rfl
  | cons name rest inductionHypothesis =>
      simp only [stringsName, stringsFromName, inductionHypothesis, Option.map_some]

private def optionalName : Option String → Lean.Name
  | none => .anonymous
  | some name => .str .anonymous name

private def optionalFromName : Lean.Name → Option (Option String)
  | .anonymous => some none
  | .str .anonymous name => some (some name)
  | _ => none

private theorem optionalName_roundtrip (name : Option String) :
    optionalFromName (optionalName name) = some name := by cases name <;> rfl

/-- Constructor metadata occupies structural name fields, without numeric
pairing expansion. Source bodies and binders remain in the native term. -/
def operatorName : PatOp .pat → DeclName
  | .fvarOp name => .str (.str .anonymous name) "GSLT.Pattern.free"
  | .applyOp label arity => .str (.num (.str .anonymous label) arity) "GSLT.Pattern.apply"
  | .lamOp none => .str .anonymous "GSLT.Pattern.lambda"
  | .lamOp (some name) => .str (.str .anonymous name) "GSLT.Pattern.lambda.some"
  | .multiLamOp arity names => .str (.num (stringsName names) arity) "GSLT.Pattern.multiLambda"
  | .substOp => .str .anonymous "GSLT.Pattern.substitution"
  | .collOp .vec arity rest => .str (.num (optionalName rest) arity) "GSLT.Pattern.vector"
  | .collOp .hashBag arity rest => .str (.num (optionalName rest) arity) "GSLT.Pattern.bag"
  | .collOp .hashSet arity rest => .str (.num (optionalName rest) arity) "GSLT.Pattern.set"

def decodeName : DeclName → Option (PatOp .pat)
  | .str metadata tag =>
      if tag = "GSLT.Pattern.free" then
        match metadata with | .str .anonymous name => some (.fvarOp name) | _ => none
      else if tag = "GSLT.Pattern.apply" then
        match metadata with
        | .num (.str .anonymous label) arity => some (.applyOp label arity)
        | _ => none
      else if tag = "GSLT.Pattern.lambda" then
        match metadata with | .anonymous => some (.lamOp none) | _ => none
      else if tag = "GSLT.Pattern.lambda.some" then
        match metadata with | .str .anonymous name => some (.lamOp (some name)) | _ => none
      else if tag = "GSLT.Pattern.multiLambda" then
        match metadata with
        | .num labels arity => (stringsFromName labels).map (.multiLamOp arity)
        | _ => none
      else if tag = "GSLT.Pattern.substitution" then
        match metadata with | .anonymous => some .substOp | _ => none
      else if tag = "GSLT.Pattern.vector" then
        match metadata with
        | .num rest arity => (optionalFromName rest).map (.collOp .vec arity)
        | _ => none
      else if tag = "GSLT.Pattern.bag" then
        match metadata with
        | .num rest arity => (optionalFromName rest).map (.collOp .hashBag arity)
        | _ => none
      else if tag = "GSLT.Pattern.set" then
        match metadata with
        | .num rest arity => (optionalFromName rest).map (.collOp .hashSet arity)
        | _ => none
      else none
  | _ => none

@[simp] theorem decodeName_operator (operator : PatOp .pat) :
    decodeName (operatorName operator) = some operator := by
  cases operator with
  | fvarOp name => rfl
  | applyOp label arity => rfl
  | lamOp name => cases name <;> rfl
  | multiLamOp arity names =>
      simp [operatorName, decodeName, stringsName_roundtrip]
  | substOp => rfl
  | collOp kind arity rest =>
      cases kind <;> simp [operatorName, decodeName, optionalName_roundtrip]

theorem operatorName_injective : Function.Injective operatorName := by
  intro first second equality
  have decoded := congrArg decodeName equality
  simpa only [decodeName_operator, Option.some.injEq] using decoded

@[simp] theorem operatorName_ne_dataName (operator : PatOp .pat) :
    operatorName operator ≠ dataName := by
  cases operator with
  | fvarOp name => simp [operatorName, dataName]
  | applyOp label arity => simp [operatorName, dataName]
  | lamOp name => cases name <;> simp [operatorName, dataName]
  | multiLamOp arity names => simp [operatorName, dataName]
  | substOp => simp [operatorName, dataName]
  | collOp kind arity rest => cases kind <;> simp [operatorName, dataName]

def names : BindingSignatureEmbedding.Names patSig where
  sort := fun _ => dataName
  operator := fun {sort} operator => by cases sort; exact operatorName operator

def dataEntry : Entry Tower.Head := ⟨.head (.sort Tower.zero), none⟩

def operatorEntry (operator : PatOp .pat) : Entry Tower.Head :=
  ⟨BindingSignatureEmbedding.operatorType names operator, none⟩

/-- The used-head inventory is preserved as a concrete finite declaration
list. Repeated heads declare the identical opaque entry. -/
def declarationList (operators : List (PatOp .pat)) : List (DeclName × Entry Tower.Head) :=
  (dataName, dataEntry) :: operators.map (fun operator => (operatorName operator, operatorEntry operator))

def signature (operators : List (PatOp .pat)) : Signature Tower.Head :=
  .ofList (declarationList operators)

def rules (operators : List (PatOp .pat)) : Rules Tower.Head :=
  extendRules Tower.rules (signature operators)

@[simp] theorem data_lookup (operators : List (PatOp .pat)) :
    (signature operators).entries dataName = some dataEntry := by
  simp [signature, declarationList, Signature.ofList, Signature.insert]

private theorem constructor_lookup (operators : List (PatOp .pat))
    {operator : PatOp .pat} (present : operator ∈ operators) :
    (Signature.ofList (operators.map (fun op => (operatorName op, operatorEntry op)))).entries
      (operatorName operator) = some (operatorEntry operator) := by
  induction operators with
  | nil => cases present
  | cons first rest inductionHypothesis =>
      by_cases same : operator = first
      · subst first
        simp [Signature.ofList, Signature.insert]
      · have different : operatorName operator ≠ operatorName first :=
          fun equal => same (operatorName_injective equal)
        have inRest : operator ∈ rest := (List.mem_cons.mp present).resolve_left same
        simpa [Signature.ofList, Signature.insert, different] using inductionHypothesis inRest

@[simp] theorem operator_lookup (operators : List (PatOp .pat))
    {operator : PatOp .pat} (present : operator ∈ operators) :
    (signature operators).entries (operatorName operator) = some (operatorEntry operator) := by
  simpa [signature, declarationList, Signature.ofList, Signature.insert,
    operatorName_ne_dataName] using constructor_lookup operators present

def sortRealization (operators : List (PatOp .pat)) :
    BindingSignatureEmbedding.SortRealization names (rules operators) where
  typeUniverse := .sort Tower.zero
  above := .sort (.succ Tower.zero)
  joined := .sort (.max Tower.zero Tower.zero)
  universeTyped := .sort Tower.zero
  universeIs := .sort Tower.zero
  aboveIs := .sort (.succ Tower.zero)
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    intro valuation
    simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero,
      LevelTower.zero]
  sortLookup := by
    intro sort
    cases sort
    change (signature operators).typeOf? dataName = some (.head (.sort Tower.zero))
    rw [Signature.typeOf?, data_lookup]
    rfl

@[simp] theorem operator_type_lookup (operators : List (PatOp .pat))
    {operator : PatOp .pat} (present : operator ∈ operators) :
    (rules operators).constantType (operatorName operator) =
      some (BindingSignatureEmbedding.operatorType names operator) := by
  change (signature operators).typeOf? (operatorName operator) = _
  rw [Signature.typeOf?, operator_lookup operators present]
  rfl

/-- Every generated entry is opaque: the package cannot invent a delta step. -/
@[simp] theorem value_lookup (operators : List (PatOp .pat)) (name : DeclName) :
    (signature operators).valueOf? name = none := by
  cases selected : (signature operators).entries name with
  | none => simp [Signature.valueOf?, selected]
  | some entry =>
      have membership := Signature.entries_ofList_mem (declarationList operators) selected
      rcases List.mem_cons.mp membership with data | constructor
      · have same : entry = dataEntry := congrArg Prod.snd data
        simp [Signature.valueOf?, selected, same, dataEntry]
      · obtain ⟨operator, _, same⟩ := List.mem_map.mp constructor
        have entrySame : entry = operatorEntry operator := (congrArg Prod.snd same).symm
        simp [Signature.valueOf?, selected, entrySame, operatorEntry]

theorem wellFormed (operators : List (PatOp .pat)) :
    (signature operators).WellFormed Tower.rules where
  fresh := by intro name entry _selected; rfl
  types := by
    intro name type selected
    unfold Signature.typeOf? at selected
    cases entrySelected : (signature operators).entries name with
    | none => simp [entrySelected] at selected
    | some entry =>
        have typeSame : entry.type = type := by simpa [entrySelected] using selected
        have membership := Signature.entries_ofList_mem (declarationList operators) entrySelected
        rcases List.mem_cons.mp membership with data | constructor
        · have same : entry = dataEntry := congrArg Prod.snd data
          subst entry
          subst type
          exact ⟨.sort (.succ Tower.zero), .sort _, .headType (.sort Tower.zero)⟩
        · obtain ⟨operator, _, same⟩ := List.mem_map.mp constructor
          have entrySame : entry = operatorEntry operator := (congrArg Prod.snd same).symm
          subst entry
          subst type
          exact ⟨.sort Tower.zero, .sort _,
            ((sortRealization operators).operatorType_formed operator).toRaw⟩
  values := by
    intro name type value _selected impossible
    rw [value_lookup] at impossible
    cases impossible
  noSelfDelta := by
    intro name value impossible
    rw [value_lookup] at impossible
    cases impossible
  declaredPreserves := by
    intro n gamma left right type impossible _typed
    rw [signature, Signature.computation_ofList] at impossible
    exact impossible.elim

/-! ## Installation computed from finite source terms -/

private def originalOperator : Sigma PatOp → PatOp .pat
  | ⟨.pat, operator⟩ => operator

/-- The pattern presentation uses the common binding-signature inventory. -/
def usedOperators {gamma : Binding.Ctx patSig} {sort : PatSrt}
    (term : Binding.Term patSig gamma sort) : List (PatOp .pat) :=
  (BindingSignaturePackage.usedOperators term).map originalOperator

def usedArgumentOperators {gamma : Binding.Ctx patSig}
    {arguments : List (List PatSrt × PatSrt)}
    (values : Binding.Args patSig arguments gamma) : List (PatOp .pat) :=
  (BindingSignaturePackage.usedArgumentOperators values).map originalOperator


mutual

theorem installed (operators : List (PatOp .pat)) :
    ∀ {gamma : Binding.Ctx patSig} {sort : PatSrt}
      (term : Binding.Term patSig gamma sort),
      (∀ operator ∈ usedOperators term, operator ∈ operators) →
      BindingSignatureEmbedding.Installed names (rules operators) term
  | _, _, .var position, _present => .var position
  | _, .pat, .op operator arguments, present => by
      have present' : ∀ op ∈ operator :: usedArgumentOperators arguments, op ∈ operators := by
        simpa only [usedOperators, usedArgumentOperators, BindingSignaturePackage.usedOperators,
          List.map_cons, originalOperator] using present
      exact .op operator arguments (operator_type_lookup operators
        (present' operator List.mem_cons_self))
        (installedArgs operators arguments (fun op member =>
          present' op (List.mem_cons_of_mem operator member)))

theorem installedArgs (operators : List (PatOp .pat)) :
    ∀ {gamma : Binding.Ctx patSig} {arguments : List (List PatSrt × PatSrt)}
      (values : Binding.Args patSig arguments gamma),
      (∀ operator ∈ usedArgumentOperators values, operator ∈ operators) →
      BindingSignatureEmbedding.InstalledArgs names (rules operators) values
  | _, _, .nil, _present => .nil
  | _, _, .cons body rest, present => by
      have present' : ∀ op ∈ usedOperators body ++ usedArgumentOperators rest, op ∈ operators := by
        simpa only [usedArgumentOperators, usedOperators,
          BindingSignaturePackage.usedArgumentOperators, List.map_append] using present
      exact .cons (installed operators body (fun op member =>
        present' op (List.mem_append_left _ member)))
        (installedArgs operators rest (fun op member =>
          present' op (List.mem_append_right _ member)))

end

/-- Every source term earns a formed native judgment using exactly its
computed finite constructor inventory. This quantifies over all contexts,
operators, variadic arities and binder-spine lengths. -/
theorem source_judgment {gamma : Binding.Ctx patSig} {sort : PatSrt}
    (term : Binding.Term patSig gamma sort) :
    Judgment (rules (usedOperators term))
      (BindingSignatureEmbedding.context names gamma)
      (BindingSignatureEmbedding.encode names term)
      (BindingSignatureEmbedding.sortType names sort) :=
  (sortRealization (usedOperators term)).encode_judgment term
    (installed (usedOperators term) term (fun _ member => member))

theorem supported_judgment (operators : List (PatOp .pat))
    {gamma : Binding.Ctx patSig} {sort : PatSrt}
    (term : Binding.Term patSig gamma sort)
    (present : ∀ operator ∈ usedOperators term, operator ∈ operators) :
    Judgment (rules operators)
      (BindingSignatureEmbedding.context names gamma)
      (BindingSignatureEmbedding.encode names term)
      (BindingSignatureEmbedding.sortType names sort) :=
  (sortRealization operators).encode_judgment term (installed operators term present)

/-- A scoped authored pattern uses the pre-existing binding presentation;
there is no second source grammar in this embedding. -/
theorem scoped_pattern_judgment {n : Nat}
    (term : Mettapedia.OSLF.MeTTaIL.ScopedSyntax.Scoped n) :
    Judgment (rules (usedOperators (toTerm term)))
      (BindingSignatureEmbedding.context names (ctxOf n))
      (BindingSignatureEmbedding.encode names (toTerm term))
      (BindingSignatureEmbedding.sortType names .pat) := source_judgment (toTerm term)

@[simp] theorem declarationList_length (operators : List (PatOp .pat)) :
    (declarationList operators).length = operators.length + 1 := by
  simp [declarationList]

theorem usedOperators_rename {gamma delta : Binding.Ctx patSig} {sort : PatSrt}
    (action : Binding.Ren patSig gamma delta) (term : Binding.Term patSig gamma sort) :
    usedOperators (Binding.rename action term) = usedOperators term :=
  congrArg (List.map originalOperator) (BindingSignaturePackage.usedOperators_rename action term)

theorem usedArgumentOperators_rename
    {gamma delta : Binding.Ctx patSig} {arguments : List (List PatSrt × PatSrt)}
    (action : Binding.Ren patSig gamma delta) (values : Binding.Args patSig arguments gamma) :
    usedArgumentOperators (Binding.renameArgs action values) = usedArgumentOperators values :=
  congrArg (List.map originalOperator) (BindingSignaturePackage.usedArgumentOperators_rename action values)


theorem extends_append (prior suffix : List (PatOp .pat)) :
    (signature prior).Extends (signature (prior ++ suffix)) := by
  have extension := Signature.ofList_extends_append (declarationList prior)
    (suffix.map (fun operator => (operatorName operator, operatorEntry operator)))
  simpa only [signature, declarationList, List.map_append, List.cons_append] using extension

private theorem absent_constructor_lookup (operators : List (PatOp .pat))
    {operator : PatOp .pat} (absent : operator ∉ operators) :
    (Signature.ofList (operators.map (fun op => (operatorName op, operatorEntry op)))).entries
      (operatorName operator) = none := by
  induction operators with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have different : operatorName operator ≠ operatorName first :=
        fun same => absent (List.mem_cons.mpr (Or.inl (operatorName_injective same)))
      have notInRest : operator ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simpa [Signature.ofList, Signature.insert, different] using inductionHypothesis notInRest

@[simp] theorem missing_operator_lookup (operators : List (PatOp .pat))
    {operator : PatOp .pat} (absent : operator ∉ operators) :
    (rules operators).constantType (operatorName operator) = none := by
  change (signature operators).typeOf? (operatorName operator) = none
  unfold Signature.typeOf?
  have missing : (signature operators).entries (operatorName operator) = none := by
    simpa [signature, declarationList, Signature.ofList, Signature.insert,
      operatorName_ne_dataName] using absent_constructor_lookup operators absent
  rw [missing]
  rfl

/-- Generating other well-formed constructors does not silently authorize an
uninstalled constructor constant. -/
theorem missing_operator_not_typed (operators : List (PatOp .pat))
    {operator : PatOp .pat} (absent : operator ∉ operators)
    {n : Nat} (gamma : Tower.Ctx n) (type : Tower.Tm n) :
    ¬ Typing (rules operators) gamma (.const (operatorName operator)) type := by
  intro typed
  exact typed.toRaw.constantImpossibleWhenMissing (missing_operator_lookup operators absent)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.PatternBindingSignature
