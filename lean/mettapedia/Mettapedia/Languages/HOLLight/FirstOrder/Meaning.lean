import Mettapedia.Languages.HOLLight.FirstOrder.Builders
import Mettapedia.Languages.HOLLight.FirstOrder.Decoding
import Mettapedia.Languages.HOLLight.Rules

/-!
# What the judgments of HOL Light's calculus mean

Each judgment of the calculus says something about encoded data. Well-formedness says that a
pattern is an encoding; the order says that one encoded tree comes before another; the
computational judgments say that the model's function sends the encoded inputs to the
encoded output. This module states the meanings of the data judgments.

Instantiation of a rule by its arguments is computed through `substSchema`, which passes
through the label and list builders and leaves every encoded tree unchanged
(`substSchema_treeP`, `substSchema_groundP`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic
open Mettapedia.Languages.MM0.Translation.CalculusSimulation (substSchema substSchemas bindingValue)

/-! ## Substitution through the builders -/

theorem substSchema_numeralP (values : String → Pattern) : ∀ count, substSchema values (numeralP count) = numeralP count
  | 0 => rfl
  | count + 1 => by
      simp only [numeralP, succP, substSchema, substSchemas, substSchema_numeralP values count]

theorem substSchema_listP (values : String → Pattern) : ∀ items : List Pattern,
    substSchema values (listP items) = listP (items.map (substSchema values))
  | [] => rfl
  | item :: rest => by
      simp only [listP, consP, substSchema, substSchemas, List.map_cons, substSchema_listP values rest]

theorem substSchema_treeP (values : String → Pattern) (label : Nat) (children : List Pattern) :
    substSchema values (treeP label children) = treeP label (children.map (substSchema values)) := by
  simp only [treeP, nodeP, substSchema, substSchemas, substSchema_numeralP, substSchema_listP]

mutual
  theorem substSchema_toPattern (values : String → Pattern) : ∀ tree : LabeledTree,
      substSchema values tree.toPattern = tree.toPattern
    | .node label children => by
        simp only [LabeledTree.toPattern, nodeP, substSchema, substSchemas, substSchema_numeralP,
          substSchema_toPatternList values children]

  theorem substSchema_toPatternList (values : String → Pattern) : ∀ trees : List LabeledTree,
      substSchema values (LabeledTree.toPatternList trees) = LabeledTree.toPatternList trees
    | [] => rfl
    | tree :: rest => by
        simp only [LabeledTree.toPatternList, consP, substSchema, substSchemas,
          substSchema_toPattern values tree, substSchema_toPatternList values rest]
end

theorem substSchema_groundP (values : String → Pattern) (tree : LabeledTree) :
    substSchema values (groundP tree) = groundP tree := substSchema_toPattern values tree

theorem substSchema_nodeP (values : String → Pattern) (label children : Pattern) :
    substSchema values (nodeP label children) = nodeP (substSchema values label) (substSchema values children) := rfl

theorem substSchema_consP (values : String → Pattern) (head tail : Pattern) :
    substSchema values (consP head tail) = consP (substSchema values head) (substSchema values tail) := rfl

theorem substSchema_nilP (values : String → Pattern) : substSchema values nilP = nilP := rfl

theorem substSchema_fvar (values : String → Pattern) (name : String) :
    substSchema values (.fvar name) = values name := rfl

/-! ## Lists of encodings -/

def treesP (trees : List LabeledTree) : Pattern := listP (trees.map groundP)

def bindersP (binders : List SourceVar) : Pattern :=
  listP (binders.map fun sourceVar => groundP (encodeTerm (.free sourceVar)))

def termsP (terms : List DBTerm) : Pattern := listP (terms.map fun term => groundP (encodeTerm term))

def typeMapletsP (entries : List (Ty × Ty)) : Pattern :=
  listP (entries.map fun (replacement, key) => typeMapletP (groundP (encodeTy replacement)) (groundP (encodeTy key)))

/-- A free variable as the term pattern the rules compare it by. -/
def freeVarP (sourceVar : SourceVar) : Pattern := groundP (encodeTerm (.free sourceVar))

/-! ## The meanings -/

/-! ## Computational judgments -/

def NthMeaning (list index value : Pattern) : Prop :=
  ∀ context : List Ty, list = contextP context →
    ∃ position type, index = groundP (encodeUnary position) ∧ context[position]? = some type ∧
      value = groundP (encodeTy type)

def TypeOfMeaning (context term type : Pattern) : Prop :=
  ∀ types : List Ty, context = contextP types →
    ∃ termValue typeValue, term = groundP (encodeTerm termValue) ∧ type = groundP (encodeTy typeValue) ∧
      termValue.inferType types = some typeValue

def BoundIndexMeaning (binders needle index : Pattern) : Prop :=
  ∀ (binderList : List SourceVar) (sourceVar : SourceVar), binders = bindersP binderList →
    needle = freeVarP sourceVar →
      ∃ position, index = groundP (encodeUnary position) ∧ boundIndex sourceVar binderList = some position

def NotBoundMeaning (binders needle : Pattern) : Prop :=
  ∀ (binderList : List SourceVar) (sourceVar : SourceVar), binders = bindersP binderList →
    needle = freeVarP sourceVar → boundIndex sourceVar binderList = none

def ToDBMeaning (binders source term : Pattern) : Prop :=
  ∀ binderList : List SourceVar, binders = bindersP binderList →
    ∃ sourceValue termValue, source = groundP (encodeSourceTerm sourceValue) ∧
      term = groundP (encodeTerm termValue) ∧ sourceValue.toDB binderList = termValue

def NotFreeMeaning (needle term : Pattern) : Prop :=
  ∀ (sourceVar : SourceVar) (termValue : DBTerm), needle = freeVarP sourceVar →
    term = groundP (encodeTerm termValue) → DBTerm.hasFree sourceVar termValue = false

def NotFreeAllMeaning (needle terms : Pattern) : Prop :=
  ∀ (sourceVar : SourceVar) (termValues : List DBTerm), needle = freeVarP sourceVar →
    terms = termsP termValues → ∀ term ∈ termValues, DBTerm.hasFree sourceVar term = false

def CloseMeaning (needle depth term result : Pattern) : Prop :=
  ∀ (sourceVar : SourceVar) (level : Nat) (termValue : DBTerm), needle = freeVarP sourceVar →
    depth = groundP (encodeUnary level) → term = groundP (encodeTerm termValue) →
      result = groundP (encodeTerm (DBTerm.closeFreeAt sourceVar level termValue))

def InstantiateMeaning (replacement depth term result : Pattern) : Prop :=
  ∀ (replacementValue : DBTerm) (level : Nat) (termValue : DBTerm),
    replacement = groundP (encodeTerm replacementValue) → depth = groundP (encodeUnary level) →
      term = groundP (encodeTerm termValue) →
        result = groundP (encodeTerm (DBTerm.instantiateAt replacementValue level termValue))

/-! ## Finite sets as strictly increasing lists -/

/-- Strictly increasing in the order of trees. -/
def Increasing (trees : List LabeledTree) : Prop := trees.Pairwise (· < ·)

def UnionMeaning (first second result : Pattern) : Prop :=
  ∀ firstTrees secondTrees : List LabeledTree, first = treesP firstTrees → second = treesP secondTrees →
    Increasing firstTrees → Increasing secondTrees →
      ∃ resultTrees, result = treesP resultTrees ∧ Increasing resultTrees ∧
        ∀ tree, tree ∈ resultTrees ↔ tree ∈ firstTrees ∨ tree ∈ secondTrees

def EraseMeaning (term terms result : Pattern) : Prop :=
  ∀ (tree : LabeledTree) (trees : List LabeledTree), term = groundP tree → terms = treesP trees →
    Increasing trees →
      ∃ resultTrees, result = treesP resultTrees ∧ Increasing resultTrees ∧
        ∀ other, other ∈ resultTrees ↔ other ∈ trees ∧ other ≠ tree

def InsertMeaning (term terms result : Pattern) : Prop :=
  ∀ (tree : LabeledTree) (trees : List LabeledTree), term = groundP tree → terms = treesP trees →
    Increasing trees →
      ∃ resultTrees, result = treesP resultTrees ∧ Increasing resultTrees ∧
        ∀ other, other ∈ resultTrees ↔ other = tree ∨ other ∈ trees

def SortMeaning (terms result : Pattern) : Prop :=
  ∀ trees : List LabeledTree, terms = treesP trees →
    ∃ resultTrees, result = treesP resultTrees ∧ Increasing resultTrees ∧
      ∀ other, other ∈ resultTrees ↔ other ∈ trees

/-! ## Instantiation of types and terms -/

/-- The type action through every annotation of a de Bruijn term. -/
def termTypeAction (entries : List (Ty × Ty)) : DBTerm → DBTerm
  | .const constant type => .const constant (SourceSubstitution.typeAction entries type)
  | .free sourceVar => .free ⟨sourceVar.name, SourceSubstitution.typeAction entries sourceVar.ty⟩
  | .bound index => .bound index
  | .app function argument => .app (termTypeAction entries function) (termTypeAction entries argument)
  | .abs domain body => .abs (SourceSubstitution.typeAction entries domain) (termTypeAction entries body)

def VarTypeMeaning (entries name type : Pattern) : Prop :=
  ∀ (entryValues : List (Ty × Ty)) (nameValue : Name), entries = typeMapletsP entryValues →
    name = groundP (encodeName nameValue) →
      type = groundP (encodeTy (SourceSubstitution.variableType entryValues nameValue))

def TyActMeaning (entries type result : Pattern) : Prop :=
  ∀ (entryValues : List (Ty × Ty)) (typeValue : Ty), entries = typeMapletsP entryValues →
    type = groundP (encodeTy typeValue) →
      result = groundP (encodeTy (SourceSubstitution.typeAction entryValues typeValue))

def TyActListMeaning (entries types results : Pattern) : Prop :=
  ∀ (entryValues : List (Ty × Ty)) (typeValues : List Ty), entries = typeMapletsP entryValues →
    types = tysP typeValues → results = tysP (typeValues.map (SourceSubstitution.typeAction entryValues))

def TermTyActMeaning (entries term result : Pattern) : Prop :=
  ∀ (entryValues : List (Ty × Ty)) (termValue : DBTerm), entries = typeMapletsP entryValues →
    term = groundP (encodeTerm termValue) →
      result = groundP (encodeTerm (termTypeAction entryValues termValue))

def TermTyActListMeaning (entries terms results : Pattern) : Prop :=
  ∀ (entryValues : List (Ty × Ty)) (termValues : List DBTerm), entries = typeMapletsP entryValues →
    terms = termsP termValues → results = termsP (termValues.map (termTypeAction entryValues))

/-- Term maplets as the rules read them: the replacement's source, then the key. -/
def termMapletsP (maplets : List SourceSubstitution.TermMaplet) : Pattern :=
  listP (maplets.map fun (replacement, key) =>
    termMapletP (groundP (encodeSourceTerm replacement.source)) (groundP (encodeSourceTerm key)))

/-- A raw term table: each key as its free-variable term, each value as its canonical term. -/
def tableP (entries : List (SourceVar × CheckedSourceTerm)) : Pattern :=
  listP (entries.map fun (key, replacement) => pairP (freeVarP key) (groundP (encodeTerm replacement.canonical.term)))

def AdmitTmMeaning (maplets table : Pattern) : Prop :=
  ∃ mapletValues : List SourceSubstitution.TermMaplet, maplets = termMapletsP mapletValues ∧
    SourceSubstitution.TermMapletsAdmissible mapletValues ∧
      table = tableP (SourceSubstitution.termEntries mapletValues)

/-- The term action of a raw table, with the empty type substitution. -/
def tableAction (entries : List (SourceVar × CheckedSourceTerm)) (term : DBTerm) : DBTerm :=
  TermSubst.applyDB ⟨TypeSubst.empty, entries⟩ term

def TmLookupMeaning (table needle value : Pattern) : Prop :=
  ∀ (entries : List (SourceVar × CheckedSourceTerm)) (sourceVar : SourceVar), table = tableP entries →
    needle = freeVarP sourceVar →
      ∃ replacement, TermSubst.lookup ⟨TypeSubst.empty, entries⟩ sourceVar = some replacement ∧
        value = groundP (encodeTerm replacement.canonical.term)

def TmNoKeyMeaning (table needle : Pattern) : Prop :=
  ∀ (entries : List (SourceVar × CheckedSourceTerm)) (sourceVar : SourceVar), table = tableP entries →
    needle = freeVarP sourceVar → TermSubst.lookup ⟨TypeSubst.empty, entries⟩ sourceVar = none

def TmApplyMeaning (table term result : Pattern) : Prop :=
  ∀ (entries : List (SourceVar × CheckedSourceTerm)) (termValue : DBTerm), table = tableP entries →
    term = groundP (encodeTerm termValue) → result = groundP (encodeTerm (tableAction entries termValue))

def TmApplyListMeaning (table terms results : Pattern) : Prop :=
  ∀ (entries : List (SourceVar × CheckedSourceTerm)) (termValues : List DBTerm), table = tableP entries →
    terms = termsP termValues → results = termsP (termValues.map (tableAction entries))

/-! ## Theorems -/

/-- The sequent is the sequent of a theorem that HOL Light's rules derive. -/
def ThmMeaning (policy : AxiomPolicy) (hypotheses conclusion : Pattern) : Prop :=
  ∃ out : Theorem, Derives (Rule policy) out ∧ hypotheses = sequentHypothesesP out.sequent ∧
    conclusion = sequentConclusionP out.sequent

/-- **The meaning of every judgment of the calculus.** -/
def holMeaning (policy : AxiomPolicy) : Pattern → Prop
  | .apply "tree.Below" [first, second] => PBelow first second
  | .apply "tree.Lt" [first, second] => PLt first second
  | .apply "tree.LtList" [first, second] => PLtList first second
  | .apply "hol.Neq" [first, second] => first ≠ second
  | .apply "hol.WfBit" [datum] => datum = bitP 0 ∨ datum = bitP 1
  | .apply "hol.WfPlane" [datum] => ∃ plane, 1 ≤ plane ∧ plane ≤ 16 ∧ datum = groundP (encodeUnary plane)
  | .apply "hol.WfChar" [datum] => ∃ character : Char, datum = groundP (encodeChar character)
  | .apply "hol.WfChars" [datum] => ∃ characters : List Char, datum = charsP characters
  | .apply "hol.WfString" [datum] => ∃ text : String, datum = groundP (encodeString text)
  | .apply "hol.WfStrings" [datum] => ∃ texts : List String, datum = stringsP texts
  | .apply "hol.WfName" [datum] => ∃ name : Name, datum = groundP (encodeName name)
  | .apply "hol.WfNames" [datum] => ∃ names : List Name, datum = namesP names
  | .apply "hol.WfTy" [datum] => ∃ type : Ty, datum = groundP (encodeTy type)
  | .apply "hol.WfTys" [datum] => ∃ types : List Ty, datum = tysP types
  | .apply "hol.WfTypeOp" [datum] => ∃ operator : TypeOp, datum = groundP (encodeTypeOp operator)
  | .apply "hol.WfTypeOpProv" [datum] =>
      ∃ provenance : TypeOpProvenance, datum = groundP (encodeTypeOpProvenance provenance)
  | .apply "hol.WfConst" [datum] => ∃ constant : Const, datum = groundP (encodeConst constant)
  | .apply "hol.WfConstProv" [datum] =>
      ∃ provenance : ConstProvenance, datum = groundP (encodeConstProvenance provenance)
  | .apply "hol.WfSource" [datum] => ∃ source : SourceTerm, datum = groundP (encodeSourceTerm source)
  | .apply "hol.WfTypeMaplets" [datum] => ∃ entries : List (Ty × Ty), datum = typeMapletsP entries
  | .apply "hol.Nth" [list, index, value] => NthMeaning list index value
  | .apply "hol.TypeOf" [context, term, type] => TypeOfMeaning context term type
  | .apply "hol.BoundIndex" [binders, needle, index] => BoundIndexMeaning binders needle index
  | .apply "hol.NotBound" [binders, needle] => NotBoundMeaning binders needle
  | .apply "hol.ToDB" [binders, source, term] => ToDBMeaning binders source term
  | .apply "hol.NotFree" [needle, term] => NotFreeMeaning needle term
  | .apply "hol.NotFreeAll" [needle, terms] => NotFreeAllMeaning needle terms
  | .apply "hol.Close" [needle, depth, term, result] => CloseMeaning needle depth term result
  | .apply "hol.Instantiate" [replacement, depth, term, result] =>
      InstantiateMeaning replacement depth term result
  | .apply "hol.Union" [first, second, result] => UnionMeaning first second result
  | .apply "hol.Erase" [term, terms, result] => EraseMeaning term terms result
  | .apply "hol.Insert" [term, terms, result] => InsertMeaning term terms result
  | .apply "hol.Sort" [terms, result] => SortMeaning terms result
  | .apply "hol.VarType" [entries, name, type] => VarTypeMeaning entries name type
  | .apply "hol.TyAct" [entries, type, result] => TyActMeaning entries type result
  | .apply "hol.TyActList" [entries, types, results] => TyActListMeaning entries types results
  | .apply "hol.TermTyAct" [entries, term, result] => TermTyActMeaning entries term result
  | .apply "hol.TermTyActList" [entries, terms, results] => TermTyActListMeaning entries terms results
  | .apply "hol.AdmitTm" [maplets, table] => AdmitTmMeaning maplets table
  | .apply "hol.TmLookup" [table, needle, value] => TmLookupMeaning table needle value
  | .apply "hol.TmNoKey" [table, needle] => TmNoKeyMeaning table needle
  | .apply "hol.TmApply" [table, term, result] => TmApplyMeaning table term result
  | .apply "hol.TmApplyList" [table, terms, results] => TmApplyListMeaning table terms results
  | .apply "hol.Thm" [hypotheses, conclusion] => ThmMeaning policy hypotheses conclusion
  | _ => True

/-! ## Each judgment's meaning, by its head -/

theorem holMeaning_treeBelow (policy : AxiomPolicy) (first second : Pattern) :
    holMeaning policy (.apply "tree.Below" [first, second]) ↔ PBelow first second := Iff.rfl

theorem holMeaning_treeLt (policy : AxiomPolicy) (first second : Pattern) :
    holMeaning policy (.apply "tree.Lt" [first, second]) ↔ PLt first second := Iff.rfl

theorem holMeaning_treeLtList (policy : AxiomPolicy) (first second : Pattern) :
    holMeaning policy (.apply "tree.LtList" [first, second]) ↔ PLtList first second := Iff.rfl

theorem holMeaning_Neq (policy : AxiomPolicy) (first second : Pattern) :
    holMeaning policy (.apply "hol.Neq" [first, second]) ↔ first ≠ second := Iff.rfl

theorem holMeaning_WfBit (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfBit" [datum]) ↔ datum = bitP 0 ∨ datum = bitP 1 := Iff.rfl

theorem holMeaning_WfPlane (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfPlane" [datum]) ↔ ∃ plane, 1 ≤ plane ∧ plane ≤ 16 ∧ datum = groundP (encodeUnary plane) := Iff.rfl

theorem holMeaning_WfChar (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfChar" [datum]) ↔ ∃ character : Char, datum = groundP (encodeChar character) := Iff.rfl

theorem holMeaning_WfChars (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfChars" [datum]) ↔ ∃ characters : List Char, datum = charsP characters := Iff.rfl

theorem holMeaning_WfString (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfString" [datum]) ↔ ∃ text : String, datum = groundP (encodeString text) := Iff.rfl

theorem holMeaning_WfStrings (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfStrings" [datum]) ↔ ∃ texts : List String, datum = stringsP texts := Iff.rfl

theorem holMeaning_WfName (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfName" [datum]) ↔ ∃ name : Name, datum = groundP (encodeName name) := Iff.rfl

theorem holMeaning_WfNames (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfNames" [datum]) ↔ ∃ names : List Name, datum = namesP names := Iff.rfl

theorem holMeaning_WfTy (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfTy" [datum]) ↔ ∃ type : Ty, datum = groundP (encodeTy type) := Iff.rfl

theorem holMeaning_WfTys (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfTys" [datum]) ↔ ∃ types : List Ty, datum = tysP types := Iff.rfl

theorem holMeaning_WfTypeOp (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfTypeOp" [datum]) ↔ ∃ operator : TypeOp, datum = groundP (encodeTypeOp operator) := Iff.rfl

theorem holMeaning_WfTypeOpProv (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfTypeOpProv" [datum]) ↔ ∃ provenance : TypeOpProvenance, datum = groundP (encodeTypeOpProvenance provenance) := Iff.rfl

theorem holMeaning_WfConst (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfConst" [datum]) ↔ ∃ constant : Const, datum = groundP (encodeConst constant) := Iff.rfl

theorem holMeaning_WfConstProv (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfConstProv" [datum]) ↔ ∃ provenance : ConstProvenance, datum = groundP (encodeConstProvenance provenance) := Iff.rfl

theorem holMeaning_WfSource (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfSource" [datum]) ↔ ∃ source : SourceTerm, datum = groundP (encodeSourceTerm source) := Iff.rfl

theorem holMeaning_WfTypeMaplets (policy : AxiomPolicy) (datum : Pattern) :
    holMeaning policy (.apply "hol.WfTypeMaplets" [datum]) ↔ ∃ entries : List (Ty × Ty), datum = typeMapletsP entries := Iff.rfl

theorem holMeaning_Nth (policy : AxiomPolicy) (list index value : Pattern) :
    holMeaning policy (.apply "hol.Nth" [list, index, value]) ↔ NthMeaning list index value := Iff.rfl

theorem holMeaning_TypeOf (policy : AxiomPolicy) (context term type : Pattern) :
    holMeaning policy (.apply "hol.TypeOf" [context, term, type]) ↔ TypeOfMeaning context term type := Iff.rfl

theorem holMeaning_BoundIndex (policy : AxiomPolicy) (binders needle index : Pattern) :
    holMeaning policy (.apply "hol.BoundIndex" [binders, needle, index]) ↔ BoundIndexMeaning binders needle index := Iff.rfl

theorem holMeaning_NotBound (policy : AxiomPolicy) (binders needle : Pattern) :
    holMeaning policy (.apply "hol.NotBound" [binders, needle]) ↔ NotBoundMeaning binders needle := Iff.rfl

theorem holMeaning_ToDB (policy : AxiomPolicy) (binders source term : Pattern) :
    holMeaning policy (.apply "hol.ToDB" [binders, source, term]) ↔ ToDBMeaning binders source term := Iff.rfl

theorem holMeaning_NotFree (policy : AxiomPolicy) (needle term : Pattern) :
    holMeaning policy (.apply "hol.NotFree" [needle, term]) ↔ NotFreeMeaning needle term := Iff.rfl

theorem holMeaning_NotFreeAll (policy : AxiomPolicy) (needle terms : Pattern) :
    holMeaning policy (.apply "hol.NotFreeAll" [needle, terms]) ↔ NotFreeAllMeaning needle terms := Iff.rfl

theorem holMeaning_Close (policy : AxiomPolicy) (needle depth term result : Pattern) :
    holMeaning policy (.apply "hol.Close" [needle, depth, term, result]) ↔ CloseMeaning needle depth term result := Iff.rfl

theorem holMeaning_Instantiate (policy : AxiomPolicy) (replacement depth term result : Pattern) :
    holMeaning policy (.apply "hol.Instantiate" [replacement, depth, term, result]) ↔ InstantiateMeaning replacement depth term result := Iff.rfl

theorem holMeaning_Union (policy : AxiomPolicy) (first second result : Pattern) :
    holMeaning policy (.apply "hol.Union" [first, second, result]) ↔ UnionMeaning first second result := Iff.rfl

theorem holMeaning_Erase (policy : AxiomPolicy) (term terms result : Pattern) :
    holMeaning policy (.apply "hol.Erase" [term, terms, result]) ↔ EraseMeaning term terms result := Iff.rfl

theorem holMeaning_Insert (policy : AxiomPolicy) (term terms result : Pattern) :
    holMeaning policy (.apply "hol.Insert" [term, terms, result]) ↔ InsertMeaning term terms result := Iff.rfl

theorem holMeaning_Sort (policy : AxiomPolicy) (terms result : Pattern) :
    holMeaning policy (.apply "hol.Sort" [terms, result]) ↔ SortMeaning terms result := Iff.rfl

theorem holMeaning_VarType (policy : AxiomPolicy) (entries name type : Pattern) :
    holMeaning policy (.apply "hol.VarType" [entries, name, type]) ↔ VarTypeMeaning entries name type := Iff.rfl

theorem holMeaning_TyAct (policy : AxiomPolicy) (entries type result : Pattern) :
    holMeaning policy (.apply "hol.TyAct" [entries, type, result]) ↔ TyActMeaning entries type result := Iff.rfl

theorem holMeaning_TyActList (policy : AxiomPolicy) (entries types results : Pattern) :
    holMeaning policy (.apply "hol.TyActList" [entries, types, results]) ↔ TyActListMeaning entries types results := Iff.rfl

theorem holMeaning_TermTyAct (policy : AxiomPolicy) (entries term result : Pattern) :
    holMeaning policy (.apply "hol.TermTyAct" [entries, term, result]) ↔ TermTyActMeaning entries term result := Iff.rfl

theorem holMeaning_TermTyActList (policy : AxiomPolicy) (entries terms results : Pattern) :
    holMeaning policy (.apply "hol.TermTyActList" [entries, terms, results]) ↔ TermTyActListMeaning entries terms results := Iff.rfl

theorem holMeaning_AdmitTm (policy : AxiomPolicy) (maplets table : Pattern) :
    holMeaning policy (.apply "hol.AdmitTm" [maplets, table]) ↔ AdmitTmMeaning maplets table := Iff.rfl

theorem holMeaning_TmLookup (policy : AxiomPolicy) (table needle value : Pattern) :
    holMeaning policy (.apply "hol.TmLookup" [table, needle, value]) ↔ TmLookupMeaning table needle value := Iff.rfl

theorem holMeaning_TmNoKey (policy : AxiomPolicy) (table needle : Pattern) :
    holMeaning policy (.apply "hol.TmNoKey" [table, needle]) ↔ TmNoKeyMeaning table needle := Iff.rfl

theorem holMeaning_TmApply (policy : AxiomPolicy) (table term result : Pattern) :
    holMeaning policy (.apply "hol.TmApply" [table, term, result]) ↔ TmApplyMeaning table term result := Iff.rfl

theorem holMeaning_TmApplyList (policy : AxiomPolicy) (table terms results : Pattern) :
    holMeaning policy (.apply "hol.TmApplyList" [table, terms, results]) ↔ TmApplyListMeaning table terms results := Iff.rfl

theorem holMeaning_Thm (policy : AxiomPolicy) (hypotheses conclusion : Pattern) :
    holMeaning policy (.apply "hol.Thm" [hypotheses, conclusion]) ↔ ThmMeaning policy hypotheses conclusion := Iff.rfl

end Mettapedia.Languages.HOLLight.FirstOrder
