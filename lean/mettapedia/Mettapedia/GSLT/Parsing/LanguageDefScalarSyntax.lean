import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
import Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence

/-!
# Scalar syntax before and after structural compilation

The source judgment below reads the original `LanguageDef` syntax items,
parameter declarations and lexical profile directly. Its terminals consume
the actual scalar input; there is no pre-tokenized ledger. Structural row
positions, terminal spans and ordered CST children survive compilation.

This is a source/plan theorem, not a claim that a particular native parser
or UTF-8 decoder implements the plan.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

set_option autoImplicit true in
mutual
  /-- Exact-span source syntax over authored rows, before parser atoms exist. -/
  inductive DerivesAt (literalScalars? : String → Option (List Nat))
      (profile : ParserProfileLayer) (language : LanguageDef) (input : List Nat) :
      String → Nat → Nat → CST → Type where
    | lexical (row : Fin profile.states.length)
        (lookup : input[start]? = some codepoint)
        (evidence : profile.ClassEvidence (profile.states.get row).className codepoint) :
        DerivesAt literalScalars? profile language input
          (profile.states.get row).resultSort start (start + 1)
          (.node (profile.states.get row).ruleLabel start (start + 1)
            [.terminal [codepoint] start (start + 1)])
    | structural (row : Fin language.terms.length)
        (body : ItemsDeriveAt literalScalars? profile language input
          (language.terms.get row) (language.terms.get row).syntaxPattern
          start stop children) :
        DerivesAt literalScalars? profile language input
          (language.terms.get row).category start stop
          (.node (language.terms.get row).label start stop children)

  /-- Authored terminals are resolved to scalar sequences. Authored parameter
  names are looked up in their own row, not in the emitted parser atoms. -/
  inductive ItemsDeriveAt (literalScalars? : String → Option (List Nat))
      (profile : ParserProfileLayer) (language : LanguageDef) (input : List Nat) :
      GrammarRule → List SyntaxItem → Nat → Nat → List CST → Type where
    | nil : ItemsDeriveAt literalScalars? profile language input rule [] cursor cursor []
    | terminal (decoded : literalScalars? token = some codepoints)
        (matched : ScalarSequenceMatchesAt input codepoints start middle)
        (rest : ItemsDeriveAt literalScalars? profile language input rule
          items middle stop children) :
        ItemsDeriveAt literalScalars? profile language input rule
          (.terminal token :: items) start stop children
    | nonterminal (lookup : Mettapedia.OSLF.Framework.GrammarDerives.paramSort?
          rule parameter = some resultSort)
        (head : DerivesAt literalScalars? profile language input
          resultSort start middle tree)
        (rest : ItemsDeriveAt literalScalars? profile language input rule
          items middle stop children) :
        ItemsDeriveAt literalScalars? profile language input rule
          (.nonTerminal parameter :: items) start stop (tree :: children)
end

variable {binding : Binding} {language : LanguageDef} {rules : List CompiledRule}
  {literalScalars? : String → Option (List Nat)} {profile : ParserProfileLayer}
  {input : List Nat}

private theorem source_length (compiled : compileRules? binding language = some rules) :
    rules.length = language.terms.length := by
  have same := compileRules_sourceRules binding language rules compiled
  simpa using congrArg List.length same

/-- The original row corresponding to one emitted row has exactly the same
physical position. No search by rule label or payload occurs. -/
def sourceRow (compiled : compileRules? binding language = some rules)
    (row : Fin rules.length) : Fin language.terms.length :=
  ⟨row.val, by simp [← source_length compiled]⟩

def targetRow (compiled : compileRules? binding language = some rules)
    (row : Fin language.terms.length) : Fin rules.length :=
  ⟨row.val, by simp [source_length compiled]⟩

theorem source_get (compiled : compileRules? binding language = some rules)
    (row : Fin rules.length) :
    language.terms.get (sourceRow compiled row) = (rules.get row).source := by
  have same := compileRules_sourceRules binding language rules compiled
  have observed := congrArg (fun entries => entries[row.val]?) same
  have sourceValid : row.val < language.terms.length := (sourceRow compiled row).isLt
  simpa [sourceRow, List.getElem?_eq_getElem row.isLt,
    List.getElem?_eq_getElem sourceValid] using observed.symm

theorem target_get (compiled : compileRules? binding language = some rules)
    (row : Fin language.terms.length) :
    (rules.get (targetRow compiled row)).source = language.terms.get row := by
  have same := source_get compiled (targetRow compiled row)
  exact same.symm

mutual
  /-- Preservation consumes source syntax, not an assumed compiled run. -/
  theorem preserve (compiled : compileRules? binding language = some rules)
      {sort : String} {start stop : Nat} {tree : CST}
      (derivation : DerivesAt literalScalars? profile language input sort start stop tree) :
      Nonempty (SourcePlanDerivesAt literalScalars? profile rules input sort start stop tree) :=
    match derivation with
    | .lexical row lookup evidence => by
        exact ⟨.lexical row.val row.isLt rfl rfl ⟨.classMember lookup evidence, rfl⟩⟩
    | .structural row body => by
        let target := targetRow compiled row
        have same := target_get compiled row
        have items := compileRules_member_items compiled (List.get_mem rules target)
        rw [same] at items
        obtain ⟨targetBody⟩ := preserveItems compiled items body
        exact ⟨.structural target.val target.isLt (congrArg GrammarRule.category same)
          (congrArg GrammarRule.label same) targetBody⟩
    termination_by structural derivation

  theorem preserveItems (compiled : compileRules? binding language = some rules)
      {rule : GrammarRule} {items : List SyntaxItem} {atoms : List StructuralAtom}
      {start stop : Nat} {children : List CST}
      (compilation : ItemsCompile binding rule items atoms)
      (derivation : ItemsDeriveAt literalScalars? profile language input rule
        items start stop children) :
      Nonempty (SourcePlanItemsDeriveAt literalScalars? profile rules input atoms start stop children) :=
    match derivation with
    | .nil => by cases compilation; exact ⟨.nil⟩
    | .terminal decoded matched rest => by
        rename_i token codepoints middle items
        cases compilation with
        | cons compiledItem restCompilation =>
            cases parser : binding.literalRef token with
            | none => simp [compileItem?, parser] at compiledItem
            | some parserRef =>
                simp [compileItem?, parser] at compiledItem
                subst_vars
                obtain ⟨targetRest⟩ := preserveItems compiled restCompilation rest
                exact ⟨.terminal decoded matched targetRest⟩
    | .nonterminal lookup head rest => by
        cases compilation with
        | cons compiledItem restCompilation =>
            simp [compileItem?, lookup] at compiledItem
            subst_vars
            obtain ⟨targetHead⟩ := preserve compiled head
            obtain ⟨targetRest⟩ := preserveItems compiled restCompilation rest
            exact ⟨.nonterminal targetHead targetRest⟩
    termination_by structural derivation
end

mutual
  /-- Reflection reconstructs the original parameter lookup and row occurrence. -/
  theorem reflect (compiled : compileRules? binding language = some rules)
      {sort : String} {start stop : Nat} {tree : CST}
      (derivation : SourcePlanDerivesAt literalScalars? profile rules input sort start stop tree) :
      Nonempty (DerivesAt literalScalars? profile language input sort start stop tree) :=
    match derivation with
    | .lexical position valid sortExact labelExact matched => by
        subst_vars
        obtain ⟨recognized, result⟩ := matched
        cases recognized with
        | classMember lookup evidence =>
            subst_vars
            exact ⟨.lexical ⟨position, valid⟩ lookup evidence⟩
    | .structural position valid sortExact labelExact body => by
        let row : Fin rules.length := ⟨position, valid⟩
        have same := source_get compiled row
        have items := compileRules_member_items compiled (List.get_mem rules row)
        obtain ⟨sourceBody⟩ := reflectItems compiled items body
        rw [← same] at sourceBody
        have derived := DerivesAt.structural (sourceRow compiled row) sourceBody
        rw [same] at derived
        change DerivesAt literalScalars? profile language input
          (rules.get ⟨position, valid⟩).source.category start stop
          (.node (rules.get ⟨position, valid⟩).source.label start stop _) at derived
        rw [sortExact, labelExact] at derived
        exact ⟨derived⟩
    termination_by structural derivation

  theorem reflectItems (compiled : compileRules? binding language = some rules)
      {rule : GrammarRule} {items : List SyntaxItem} {atoms : List StructuralAtom}
      {start stop : Nat} {children : List CST}
      (compilation : ItemsCompile binding rule items atoms)
      (derivation : SourcePlanItemsDeriveAt literalScalars? profile rules input
        atoms start stop children) :
      Nonempty (ItemsDeriveAt literalScalars? profile language input rule items start stop children) :=
    match derivation with
    | .nil => by cases compilation; exact ⟨.nil⟩
    | .terminal decoded matched rest => by
        cases compilation with
        | cons compiledItem restCompilation =>
            have source := compileItem_sourceSyntax _ _ _ _ compiledItem
            cases source
            obtain ⟨sourceRest⟩ := reflectItems compiled restCompilation rest
            exact ⟨.terminal decoded matched sourceRest⟩
    | .nonterminal head rest => by
        rename_i resultSort middle tree atoms children parameter parserRef
        cases compilation with
        | cons compiledItem restCompilation =>
            have source := compileItem_sourceSyntax _ _ _ _ compiledItem
            cases source
            cases lookup : Mettapedia.OSLF.Framework.GrammarDerives.paramSort? rule parameter with
            | none => simp [compileItem?, StructuralAtom.sourceSyntax, lookup] at compiledItem
            | some decodedSort =>
                simp only [compileItem?, StructuralAtom.sourceSyntax, lookup,
                  ] at compiledItem
                cases compiledItem
                obtain ⟨sourceHead⟩ := reflect compiled head
                obtain ⟨sourceRest⟩ := reflectItems compiled restCompilation rest
                exact ⟨.nonterminal lookup sourceHead sourceRest⟩
    termination_by structural derivation
end

theorem source_plan_iff (compiled : compileRules? binding language = some rules)
    {sort : String} {start stop : Nat} {tree : CST} :
    Nonempty (DerivesAt literalScalars? profile language input sort start stop tree) ↔
      Nonempty (SourcePlanDerivesAt literalScalars? profile rules input sort start stop tree) :=
  ⟨fun ⟨derivation⟩ => preserve compiled derivation,
    fun ⟨derivation⟩ => reflect compiled derivation⟩

end Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax
