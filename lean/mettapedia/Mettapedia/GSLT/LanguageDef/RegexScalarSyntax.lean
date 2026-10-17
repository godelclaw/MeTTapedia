import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSyntaxAuthoring
import Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax
import Mettapedia.GSLT.Parsing.ClassAwareGroundedChart
import Mettapedia.GSLT.LanguageDef.RegexSourceProjection

/-!
# Authored regex scalars, prepared parser plans and complete forests

The plan is computed from the actual regex `LanguageDef` and lexical profile.
Its finite grounded chart is complete for the independent original-row scalar
syntax, including lexical-class evidence, source spans and ordered CSTs.
Packed membership alone is not admission: certificate replay excludes invented
parses. An explicit observer filters admitted trees only after forest creation.

The source input here is decoded Unicode scalars. UTF-8 decoding, native
frontend refinement and native search-start injection are separate boundaries.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.GSLT.LanguageDef.RegexScalarSyntax

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareGroundedChart
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSyntaxAuthoring
open Mettapedia.GSLT.Parsing

/-- Literal spellings are interpreted as their actual Unicode scalars. -/
def literalScalars (text : String) : Option (List Nat) :=
  some (text.toList.map Char.toNat)

theorem plan_compiles :
    (compileParserPackPlan? literalScalars profile compiledRules).isSome = true := by decide

/-- A prepared semantic plan, computed once from authored declarations. -/
def plan : CompiledParserPackPlan :=
  (compileParserPackPlan? literalScalars profile compiledRules).get plan_compiles

theorem plan_exact :
    compileParserPackPlan? literalScalars profile compiledRules = some plan :=
  (Option.some_get plan_compiles).symm

theorem agreement : ParserPackPlanAgreement literalScalars profile compiledRules plan :=
  .of_compilation plan_exact

theorem plan_start : plan.lexical.startSort = "RxPattern" := by
  rw [agreement.startSort_eq]
  rfl

abbrev DerivesAt (input : List Nat) (sort : String) (start stop : Nat) (tree : CST) :=
  LanguageDefScalarSyntax.DerivesAt literalScalars profile authored input sort start stop tree

abbrev RootDerives (input : List Nat) (tree : CST) :=
  DerivesAt input "RxPattern" 0 input.length tree

/-- Every original-row scalar derivation is preserved and reflected by the
actual prepared plan, not a caller-supplied adequacy assumption. -/
theorem parserPack_iff {input : List Nat} {sort : String}
    {start stop : Nat} {tree : CST} :
    Nonempty (DerivesAt input sort start stop tree) ↔
      Nonempty (ParserPackDerivesAt profile plan input sort start stop tree) :=
  (LanguageDefScalarSyntax.source_plan_iff compiled_exact).trans
    (sourcePlan_nonempty_iff_parserPack_nonempty agreement sort start stop tree)

/-- The computed whole-input entry adds its EOF check without introducing an
extra CST wrapper or changing a source occurrence. -/
theorem entry_iff {input : List Nat} {tree : CST} :
    Nonempty (RootDerives input tree) ↔
      Nonempty (ParserPackEntryDerivesAt profile plan input
        plan.entryProduction.resultState input.length tree) := by
  have original := LanguageDefScalarSyntax.source_plan_iff (literalScalars? := literalScalars)
    (profile := profile) (input := input) compiled_exact
    (sort := "RxPattern") (start := 0) (stop := input.length) (tree := tree)
  exact original.trans ⟨fun ⟨source⟩ =>
      ⟨(sourcePlanEntryDerivationEquiv agreement tree).toFun source⟩,
    fun ⟨target⟩ => ⟨(sourcePlanEntryDerivationEquiv agreement tree).invFun target⟩⟩

def forest (input : List Nat) : Forest := referenceForest profile plan input

/-- Grounding and saturation retain every exact certificate of every source
parse; the theorem is independent of a native backend's scheduling. -/
theorem forest_complete (input : List Nat) :
    RootParserComplete (forest input) profile plan input :=
  referenceForest_rootParserComplete profile plan input

def ParsedBy (target : Forest) (input : List Nat) (tree : CST) : Prop :=
  ∃ certificate, Nonempty (PackedReplays target profile plan input certificate
    "RxPattern" 0 input.length tree)

/-- Packed replay admits exactly the independently authored scalar syntax.
Membership without replay would not give the backward implication. -/
theorem packed_iff_source {input : List Nat} {tree : CST} :
    ParsedBy (forest input) input tree ↔ Nonempty (RootDerives input tree) := by
  constructor
  · rintro ⟨certificate, ⟨replay⟩⟩
    exact parserPack_iff.mpr ⟨replay.derivation⟩
  · intro source
    obtain ⟨derivation⟩ := parserPack_iff.mp source
    have complete := forest_complete input tree
    rw [plan_start] at complete
    exact ⟨Certificate.ofDerivation derivation,
      ⟨⟨⟨complete derivation⟩, Replays.ofDerivation derivation⟩⟩⟩

/-- A checked coverage packet can qualify another backend forest. This check
compares against an independently computed complete chart, not itself. -/
theorem covered_backend_iff_source {input : List Nat} {target : Forest}
    (covered : validateForestCovers (forest input) target = true) {tree : CST} :
    ParsedBy target input tree ↔ Nonempty (RootDerives input tree) := by
  constructor
  · rintro ⟨certificate, ⟨replay⟩⟩
    exact parserPack_iff.mpr ⟨replay.derivation⟩
  · intro source
    obtain ⟨certificate, ⟨replay⟩⟩ := packed_iff_source.mpr source
    exact ⟨certificate, ⟨⟨⟨rootUnfolds_of_covers
      (validateForestCovers_sound covered) replay.1.down⟩, replay.2⟩⟩⟩

/-- Selection is an explicit observation over admitted trees, never parser
descriptor order. It may retain more than one alternative. -/
def Observed (policy : CST → Prop) (target : Forest)
    (input : List Nat) (tree : CST) : Prop :=
  ParsedBy target input tree ∧ policy tree

theorem observed_iff {input : List Nat} {tree : CST} {policy : CST → Prop} :
    Observed policy (forest input) input tree ↔
      Nonempty (RootDerives input tree) ∧ policy tree := by
  rw [Observed, packed_iff_source]

def Ambiguous (parses : CST → Prop) : Prop :=
  ∃ first second, first ≠ second ∧ parses first ∧ parses second

/-- Completeness preserves ambiguity instead of silently deciding it. -/
theorem ambiguity_iff (input : List Nat) :
    Ambiguous (ParsedBy (forest input) input) ↔
      Ambiguous (fun tree => Nonempty (RootDerives input tree)) := by
  simp only [Ambiguous, packed_iff_source]

/- Encode the retained CST without dropping node locations or reordering
children. Admitted lexical leaves carry one scalar, encoded by native `cp`.
The total encoder also exposes any non-singleton terminal payload explicitly. -/
mutual
  def wire (tree : CST) : CettaWire.Term :=
    match tree with
    | .terminal codepoints _ _ => .application "cp" (codepoints.map .natural)
    | .node label start stop children =>
        RegexSourceProjection.cst label (wireChildren children) start stop
    termination_by structural tree

  def wireChildren (children : List CST) : List CettaWire.Term :=
    match children with
    | [] => []
    | head :: tail => wire head :: wireChildren tail
    termination_by structural children
end

theorem wire_scalar (scalar start stop : Nat) :
    wire (.terminal [scalar] start stop) = RegexSourceProjection.cp scalar := rfl

/-- Successful lowering is justified by a scalar source parse and the
independently stated attributed projection. Unsupported meanings remain at
that interpretation boundary, not mislabeled as absent input matches. -/
theorem selected_projection_iff
    (input : List Nat) (policy : CST → Prop)
    (view : RegexSourceProjection.Flags → CettaWire.Term → Option RegexSourceProjection.Form)
    (state : RegexSourceProjection.State) (answer : RegexSourceProjection.Output) :
    (∃ tree, Observed policy (forest input) input tree ∧
      ∃ fuel, RegexSourceProjection.project view fuel state (wire tree) = some answer) ↔
    ∃ tree, Nonempty (RootDerives input tree) ∧ policy tree ∧
      RegexSourceProjection.Projects view state (wire tree) answer := by
  constructor
  · rintro ⟨tree, admitted, computed⟩
    exact ⟨tree, (observed_iff.mp admitted).1, (observed_iff.mp admitted).2,
      (RegexSourceProjection.project_iff view state (wire tree) answer).mp computed⟩
  · rintro ⟨tree, source, retained, projected⟩
    exact ⟨tree, observed_iff.mpr ⟨source, retained⟩,
      (RegexSourceProjection.project_iff view state (wire tree) answer).mpr projected⟩

namespace Controls

def lexical (scalar : Nat) : CST :=
  .node "re-src:lex-scalar" 0 1 [.terminal [scalar] 0 1]

def literal (scalar : Nat) : CST := .node "re-src:literal" 0 1 [lexical scalar]

def literalDerivation (scalar : Nat)
    (allowed : profile.ClassEvidence "RxLiteralClass" scalar) :
    DerivesAt [scalar] "RxAtom" 0 1 (literal scalar) := by
  apply LanguageDefScalarSyntax.DerivesAt.structural ⟨17, by decide⟩
  apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal (by rfl)
  · exact .lexical ⟨0, by decide⟩ rfl allowed
  · exact .nil

def rootLiteral (scalar : Nat) : CST :=
  .node "re-src:pattern" 0 1 [
    .node "re-src:sequence" 0 1 [
      .node "re-src:atom" 0 1 [literal scalar], .node "re-src:empty" 1 1 []]]

def rootLiteralDerivation (scalar : Nat)
    (allowed : profile.ClassEvidence "RxLiteralClass" scalar) :
    RootDerives [scalar] (rootLiteral scalar) := by
  apply LanguageDefScalarSyntax.DerivesAt.structural ⟨0, by decide⟩
  apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
  · apply LanguageDefScalarSyntax.DerivesAt.structural ⟨3, by decide⟩
    apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
    · apply LanguageDefScalarSyntax.DerivesAt.structural ⟨4, by decide⟩
      exact .nonterminal rfl (literalDerivation scalar allowed) .nil
    · apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
      · exact .structural ⟨2, by decide⟩ .nil
      · exact .nil
  · exact .nil

def atomRoot (tree : CST) (stop : Nat) : CST :=
  .node "re-src:pattern" 0 stop [
    .node "re-src:sequence" 0 stop [
      .node "re-src:atom" 0 stop [tree], .node "re-src:empty" stop stop []]]

def atomRootDerivation {input : List Nat} {tree : CST} {stop : Nat}
    (atom : DerivesAt input "RxAtom" 0 stop tree) :
    DerivesAt input "RxPattern" 0 stop (atomRoot tree stop) := by
  apply LanguageDefScalarSyntax.DerivesAt.structural ⟨0, by decide⟩
  apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
  · apply LanguageDefScalarSyntax.DerivesAt.structural ⟨3, by decide⟩
    apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
    · apply LanguageDefScalarSyntax.DerivesAt.structural ⟨4, by decide⟩
      exact .nonterminal rfl atom .nil
    · apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
      · exact .structural ⟨2, by decide⟩ .nil
      · exact .nil
  · exact .nil

def hexInput : List Nat := [92, 120, 123, 52, 49, 125]

def hexTree : CST := .node "re-src:hex" 0 6 [
  .node "re-src:hex-more" 3 5 [
    .node "re-src:lex-hex" 3 4 [.terminal [52] 3 4],
    .node "re-src:hex-one" 4 5 [
      .node "re-src:lex-hex" 4 5 [.terminal [49] 4 5]]]]

def hexDerivation : DerivesAt hexInput "RxAtom" 0 6 hexTree := by
  apply LanguageDefScalarSyntax.DerivesAt.structural ⟨65, by decide⟩
  apply LanguageDefScalarSyntax.ItemsDeriveAt.terminal rfl
    (.cons rfl (.cons rfl (.cons rfl (.nil 3))))
  apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
  · apply LanguageDefScalarSyntax.DerivesAt.structural ⟨72, by decide⟩
    apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
    · apply LanguageDefScalarSyntax.DerivesAt.lexical ⟨7, by decide⟩ rfl
      change profile.classAccepts? "RxHexDigitClass" 52 = some true
      decide
    · apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
      · apply LanguageDefScalarSyntax.DerivesAt.structural ⟨71, by decide⟩
        apply LanguageDefScalarSyntax.ItemsDeriveAt.nonterminal rfl
        · apply LanguageDefScalarSyntax.DerivesAt.lexical ⟨7, by decide⟩ rfl
          change profile.classAccepts? "RxHexDigitClass" 49 = some true
          decide
        · exact .nil
      · exact .nil
  · exact .terminal rfl (.cons rfl (.nil 6)) .nil

theorem unicode_literal_has_complete_packed_witness :
    ParsedBy (forest [955]) [955] (rootLiteral 955) :=
  packed_iff_source.mpr ⟨rootLiteralDerivation 955 (by
    change profile.classAccepts? "RxLiteralClass" 955 = some true
    decide)⟩

theorem source_space_is_not_implicitly_erased :
    ParsedBy (forest [32]) [32] (rootLiteral 32) :=
  packed_iff_source.mpr ⟨rootLiteralDerivation 32 (by
    change profile.classAccepts? "RxLiteralClass" 32 = some true
    decide)⟩

/-- Multi-scalar source terminals are expanded but discarded from retained
CST children, while the exact two hex-digit occurrences remain. -/
theorem bracketed_hex_has_complete_packed_witness :
    ParsedBy (forest hexInput) hexInput (atomRoot hexTree 6) :=
  packed_iff_source.mpr ⟨atomRootDerivation hexDerivation⟩

/-- A forest can claim an arbitrary root, but exact replay still cannot
admit a lexical scalar excluded by the authored class. -/
theorem operator_cannot_be_a_literal_leaf :
    IsEmpty (DerivesAt [42] "RxScalar" 0 1 (lexical 42)) := by
  constructor
  intro derivation
  generalize sortExact : "RxScalar" = sort at derivation
  generalize treeExact : lexical 42 = tree at derivation
  cases derivation with
  | lexical row lookup evidence =>
      have only : ∀ row : Fin profile.states.length,
          (profile.states.get row).resultSort = "RxScalar" → row.val = 0 := by decide
      have rowExact : row = ⟨0, by decide⟩ := Fin.ext (only row sortExact.symm)
      subst row
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst_vars
      change profile.classAccepts? "RxLiteralClass" 42 = some true at evidence
      have refused := ModuleFormat.RegexSyntaxAuthoring.Controls.operator_is_not_a_literal_token
      rw [refused] at evidence
      cases evidence
  | structural row body =>
      have absent : ∀ row : Fin authored.terms.length,
          (authored.terms.get row).category ≠ "RxScalar" := by decide
      exact absent row sortExact.symm

end Controls

end Mettapedia.GSLT.LanguageDef.RegexScalarSyntax
