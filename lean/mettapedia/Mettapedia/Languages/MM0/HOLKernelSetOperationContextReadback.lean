import Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback


/-!
# Canonical antecedents for the maintained material HOL profile

The six operation typings and every ordered source assumption reconstruct
as a mixed native judgment. Canonical source terms contain no occurrence of
the separately named Boolean-equivalence abbreviation, so its expansion
preserves those terms and their formation context.

The constructed context admission carries typed syntax and assumption
membership, without source derivations. It attaches this canonical antecedent
to an independently admitted native proof tree. Admission of every output of
the complete proof compiler remains a separate recursive obligation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback
open NamedElaboration (BinderNames)
open Embedding.ZFSetHenkinInterpretation (Symbol)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms}

theorem expandEquivalence_encodeType (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) (distinct : ∀ symbol, references symbol ≠ equivalenceReference)
    (type : Ty Unit) :
    expandEquivalence references equivalenceReference
      (encodeType references HOLKernelSetOperationInterpretation.typeCode type) =
      encodeType references HOLKernelSetOperationInterpretation.typeCode type := by
  exact expandEquivalence_encodeType_of_fixed references equivalenceReference distinct
    HOLKernelSetOperationInterpretation.typeCode
    (by intro name; simp [HOLKernelSetOperationInterpretation.typeCode, expandEquivalence]) type


theorem expandEquivalence_encodeTerm
    (references : HOLKernelSyntax.Symbol → Nat) (equivalenceReference : Nat)
    (distinct : ∀ symbol, references symbol ≠ equivalenceReference)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Symbol gamma type) :
    ∀ (names : Names gamma) (depth : Nat),
    expandEquivalence references equivalenceReference
      (HOLKernelSetOperationReadback.encode references names depth source) =
      HOLKernelSetOperationReadback.encode references names depth source := by
  intro names depth
  exact expandEquivalence_encodeTerm_of_fixed references equivalenceReference distinct
    HOLKernelSetOperationInterpretation.typeCode
    (fun {_} symbol => HOLKernelSetOperationInterpretation.symbolCode symbol)
    HOLKernelSetOperationInterpretation.binderName
    (by intro name; simp [HOLKernelSetOperationInterpretation.typeCode, expandEquivalence])
    (by intro type symbol; cases symbol <;> simp [HOLKernelSetOperationInterpretation.symbolCode, expandEquivalence])
    source names.nameOf depth


theorem readJudgmentWith_holds (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit}
    (reader : TermReader Symbol) (names : Names gamma) (native : Preterm) :
    readJudgmentWith reader references names (HOLKernelJudgment.holds references native) =
      ((reader names native).bind (expect .prop)).map Judgment.assertion := by
  simp [HOLKernelJudgment.holds, applySymbol, Preterm.applyArgs, readJudgmentWith,
    readHead_reference references faithful]

theorem readJudgmentWith_conjunction (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit}
    (reader : TermReader Symbol) (names : Names gamma) (first second : Preterm) :
    readJudgmentWith reader references names (HOLKernelJudgment.conjunction references first second) =
      ((readJudgmentWith reader references names first).bind fun left =>
        (readJudgmentWith reader references names second).bind fun right => some (.conjunction left right)) := by
  simp [HOLKernelJudgment.conjunction, applySymbol, Preterm.applyArgs, readJudgmentWith,
    readHead_reference references faithful]

theorem readJudgmentWith_entails (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit}
    (reader : TermReader Symbol) (names : Names gamma) (first second : Preterm) :
    readJudgmentWith reader references names (HOLKernelJudgment.entails references first second) =
      ((readJudgmentWith reader references names first).bind fun left =>
        (readJudgmentWith reader references names second).bind fun right => some (.consequence left right)) := by
  simp [HOLKernelJudgment.entails, applySymbol, Preterm.applyArgs, readJudgmentWith,
    readHead_reference references faithful]

theorem logical_reader_encode
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Symbol gamma type)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth) :
    HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7 names
      (HOLKernelSetOperationReadback.encode signature.symbol names depth source) = some ⟨type, source⟩ := by
  exact HOLKernelLogicalFunctionReadback.reader_encode logical
    HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    (fun symbol => HOLKernelSetOperationReadback.readConstant_symbol symbol)
    (fun symbol => HOLKernelSetOperationReadback.symbolIndex_bound symbol) source names depth scope

theorem AdmittedContext.mono {first second : List (ClosedFormula Symbol)}
    (weaken : ∀ formula ∈ first, formula ∈ second) {judgment : Judgment Symbol []}
    (admitted : AdmittedContext first judgment) : AdmittedContext second judgment := by
  induction admitted with
  | typing term => exact .typing term
  | top => exact .top
  | assumption member => exact .assumption (weaken _ member)
  | conjunction _ _ left right => exact .conjunction left right

def formationReading : Judgment Symbol [] :=
  HOLKernelSetOperationInterpretation.symbols.foldr
    (fun entry rest => .conjunction rest (.typing (.const entry.2))) (.assertion .top)

def sourceContext (assumptions : List (ClosedFormula Symbol)) : Judgment Symbol [] :=
  assumptions.foldr (fun formula rest => .conjunction rest (.assertion formula)) formationReading

theorem formationReading_admitted (assumptions : List (ClosedFormula Symbol)) :
    AdmittedContext assumptions formationReading := by
  unfold formationReading
  generalize HOLKernelSetOperationInterpretation.symbols = entries
  induction entries with
  | nil => exact .top
  | cons entry entries ih => exact .conjunction ih (.typing (.const entry.2))

theorem sourceContext_admitted (assumptions : List (ClosedFormula Symbol)) :
    AdmittedContext assumptions (sourceContext assumptions) := by
  induction assumptions with
  | nil => exact formationReading_admitted []
  | cons first rest ih =>
      exact .conjunction (ih.mono (fun _ mem => List.mem_cons_of_mem first mem))
        (.assumption List.mem_cons_self)

#print axioms expandEquivalence_encodeTerm
#print axioms logical_reader_encode

theorem logical_read_typing
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    {gamma : Ctx Unit} {type : Ty Unit} (source : Term Symbol gamma type)
    (names : Names gamma) (depth : Nat) (scope : InScope 7 names depth) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol names
      (HOLKernelJudgment.hasType signature.symbol
        (HOLKernelSetOperationReadback.encode signature.symbol names depth source)
        (encodeType signature.symbol HOLKernelSetOperationInterpretation.typeCode type)) =
      some (.typing source) := by
  simp [HOLKernelJudgment.hasType, applySymbol, Preterm.applyArgs, readJudgmentWith,
    readHead_reference signature.symbol signature.symbol_injective, readTypingWith,
    HOLKernelSetOperationReadback.readType_encode signature.symbol signature.symbol_injective,
    logical_reader_encode logical source names depth scope, expect_same]

theorem read_antecedent
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    {gamma : Ctx Unit} (reader : TermReader Symbol) (names : Names gamma)
    (formation : Preterm) (base : Judgment Symbol gamma)
    (baseRead : readJudgmentWith reader references names formation = some base)
    {native : List Preterm} {source : List (Judgment Symbol gamma)}
    (entries : List.Forall₂
      (fun expression judgment => readJudgmentWith reader references names expression = some judgment)
      native source) :
    readJudgmentWith reader references names (HOLKernelAssumptions.antecedent references formation native) =
      some (source.foldr (fun entry rest => .conjunction rest entry) base) := by
  induction entries with
  | nil => exact baseRead
  | cons head tail ih =>
      simp only [HOLKernelAssumptions.antecedent, List.foldr_cons,
        readJudgmentWith_conjunction references faithful, ih, head, Option.bind_some]

theorem formation_read
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol BinderNames.nil (HOLKernelSetOperationInterpretation.formation signature.symbol) =
      some formationReading := by
  have scope : InScope 7 (BinderNames.nil : Names []) 0 :=
    ⟨by simp [BinderNames.toList], by simp [BinderNames.toList]⟩
  have baseRead : readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol BinderNames.nil (HOLKernelSetOperationInterpretation.baseAntecedent signature.symbol) =
        some (.assertion .top) := by
    rw [HOLKernelSetOperationInterpretation.baseAntecedent, readJudgmentWith_holds
      signature.symbol signature.symbol_injective]
    change ((HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7
      BinderNames.nil (HOLKernelSetOperationReadback.encode signature.symbol BinderNames.nil 0
        (.top : ClosedFormula Symbol))).bind (expect .prop)).map Judgment.assertion = _
    rw [logical_reader_encode logical .top BinderNames.nil 0 scope]
    simp [expect_same]
  have entries : List.Forall₂
      (fun expression judgment => readJudgmentWith
        (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
        signature.symbol BinderNames.nil expression = some judgment)
      (HOLKernelSetOperationInterpretation.typingAssumptions signature.symbol)
      (HOLKernelSetOperationInterpretation.symbols.map fun entry => Judgment.typing (Term.const entry.2)) := by
    unfold HOLKernelSetOperationInterpretation.typingAssumptions
    generalize HOLKernelSetOperationInterpretation.symbols = symbols
    induction symbols with
    | nil => exact .nil
    | cons entry rest ih =>
        refine .cons ?_ ih
        exact logical_read_typing logical (.const entry.2) BinderNames.nil 0 scope
  exact read_antecedent signature.symbol signature.symbol_injective _ BinderNames.nil _ _ baseRead entries


theorem abbreviation_reference_distinct
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (named : signature.names abbreviation.reference = some "bi") :
    ∀ symbol, signature.symbol symbol ≠ abbreviation.reference := by
  intro symbol same
  have actual := signature.named symbol
  rw [same, named] at actual
  cases symbol <;> simp [HOLKernelSyntax.Symbol.name] at actual

theorem expandEquivalence_conjunction (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) (distinct : references .an ≠ equivalenceReference)
    (first second : Preterm) :
    expandEquivalence references equivalenceReference (HOLKernelJudgment.conjunction references first second) =
      HOLKernelJudgment.conjunction references
        (expandEquivalence references equivalenceReference first)
        (expandEquivalence references equivalenceReference second) := by
  simp [HOLKernelJudgment.conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, distinct]

theorem expandEquivalence_holds (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) (formula : Preterm) :
    expandEquivalence references equivalenceReference (HOLKernelJudgment.holds references formula) =
      HOLKernelJudgment.holds references (expandEquivalence references equivalenceReference formula) := by
  simp [HOLKernelJudgment.holds, applySymbol, Preterm.applyArgs, expandEquivalence]

theorem expandEquivalence_formation (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference : Nat) (distinct : ∀ symbol, references symbol ≠ equivalenceReference) :
    expandEquivalence references equivalenceReference (HOLKernelSetOperationInterpretation.formation references) =
      HOLKernelSetOperationInterpretation.formation references := by
  simp [HOLKernelSetOperationInterpretation.formation,
    HOLKernelSetOperationInterpretation.typingAssumptions,
    HOLKernelSetOperationInterpretation.symbols,
    HOLKernelSetOperationInterpretation.baseAntecedent,
    HOLKernelSetOperationInterpretation.symbolCode,
    HOLKernelAssumptions.antecedent, HOLKernelJudgment.conjunction, HOLKernelJudgment.hasType,
    HOLKernelJudgment.holds, applySymbol, Preterm.applyArgs, expandEquivalence, distinct,
    expandEquivalence_encodeType]

theorem logical_read_formula
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (formula : ClosedFormula Symbol) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol BinderNames.nil
      (HOLKernelJudgment.holds signature.symbol (HOLKernelSetOperationInterpretation.term signature.symbol formula)) =
      some (.assertion formula) := by
  have scope : InScope 7 (BinderNames.nil : Names []) 0 :=
    ⟨by simp [BinderNames.toList], by simp [BinderNames.toList]⟩
  rw [readJudgmentWith_holds signature.symbol signature.symbol_injective,
    ← HOLKernelSetOperationReadback.encode_closed signature.symbol formula,
    logical_reader_encode logical formula BinderNames.nil 0 scope]
  simp [expect_same]

theorem read_sourceAntecedent
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (assumptions : List (ClosedFormula Symbol)) :
    readJudgmentWith
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      signature.symbol BinderNames.nil
      (expandEquivalence signature.symbol abbreviation.reference
        (HOLKernelAssumptions.antecedent signature.symbol
          (HOLKernelSetOperationInterpretation.formation signature.symbol)
          (assumptions.map (fun source =>
            HOLKernelJudgment.holds signature.symbol
              (HOLKernelSetOperationInterpretation.term signature.symbol source))))) =
      some (sourceContext assumptions) := by
  induction assumptions with
  | nil =>
      simp only [List.map_nil, HOLKernelAssumptions.antecedent, sourceContext, List.foldr_nil,
        expandEquivalence_formation signature.symbol abbreviation.reference distinct]
      exact formation_read logical
  | cons first rest ih =>
      have expanded := expandEquivalence_encodeTerm signature.symbol abbreviation.reference distinct first BinderNames.nil 0
      rw [HOLKernelSetOperationReadback.encode_closed] at expanded
      simp only [List.map_cons, HOLKernelAssumptions.antecedent,
        expandEquivalence_conjunction signature.symbol abbreviation.reference (distinct .an),
        readJudgmentWith_conjunction signature.symbol signature.symbol_injective, ih,
        expandEquivalence_holds, expanded, logical_read_formula logical first,
        Option.bind_some, sourceContext, List.foldr_cons]

#print axioms read_sourceAntecedent
#print axioms abbreviation_reference_distinct


def AdmittedSourceProof.ofTree
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (named : signature.names abbreviation.reference = some "bi")
    {context : Context} {ruleAt : Nat → Option Rule}
    {bindingAt : Nat → Option HOLKernelBindingRules.Rule} {fuel : Nat} {witness : ProofWitness}
    (sequent : HOLKernelSetOperationReadback.SourceSequent)
    (accepted : witness.proof? terms definitions theorems context [] =
      some (HOLKernelSetOperationInterpretation.statement signature.symbol sequent.1 sequent.2))
    (tree : HOLKernelProofReadback.AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader logical HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel BinderNames.nil witness (.imp (sourceContext sequent.1).formula sequent.2)) :
    AdmittedSourceProof signature abbreviation theorems logical context ruleAt bindingAt fuel witness sequent :=
  ⟨sourceContext sequent.1,
    read_sourceAntecedent logical abbreviation (abbreviation_reference_distinct abbreviation named) sequent.1,
    sourceContext_admitted sequent.1, accepted, tree⟩

#print axioms AdmittedSourceProof.ofTree

#print axioms sourceContext_admitted

theorem term_sorted_in_layout (signature : Signature sorts terms)
    (layout : HOLKernelProofAllocation.Layout) {type : Ty Unit} (source : ClosedTerm Symbol type)
    (fits : source.binderDepth ≤ layout.width) :
    Preterm.HasType terms
      (layout.target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      (HOLKernelSetOperationInterpretation.term signature.symbol source) [] signature.ids.object := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let encoding : HOLKernelProofEnvironment.Encoding signature layout initial Unit Symbol :=
    HOLKernelProofEnvironment.Encoding.fromInitial signature layout initial
    (HOLKernelSetOperationInterpretation.initialContext_formed signature)
    HOLKernelSetOperationInterpretation.typeCode
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode symbol)
    (HOLKernelSetOperationInterpretation.typeCode_sorted signature)
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode_sorted signature symbol)
  exact HOLKernelTermAssignments.encode_sorted signature _
    HOLKernelSetOperationInterpretation.typeCode
    (fun {type} (symbol : Symbol type) => HOLKernelSetOperationInterpretation.symbolCode symbol)
    HOLKernelSetOperationInterpretation.binderName
    encoding.baseSorted encoding.constantSorted source HOLKernelSetOperationInterpretation.noAssignment 0
    (by intro type index; nomatch index)
    (by
      intro offset smaller
      simpa only [Nat.zero_add, HOLKernelSetOperationInterpretation.binderName_eq signature.ids] using
        layout.slot initial signature.ids.object offset (layout.source_slot_lt (Nat.lt_of_lt_of_le smaller fits)))


theorem sourceContext_formula (assumptions : List (ClosedFormula Symbol)) :
    (sourceContext assumptions).formula =
      assumptions.foldr (fun formula tail => .and tail formula) formationReading.formula := by
  induction assumptions with
  | nil => rfl
  | cons first rest ih =>
      simpa only [sourceContext, List.foldr_cons, Judgment.formula] using
        congrArg (fun formula => Term.and formula first) ih


#print axioms term_sorted_in_layout
#print axioms sourceContext_formula

end Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback

