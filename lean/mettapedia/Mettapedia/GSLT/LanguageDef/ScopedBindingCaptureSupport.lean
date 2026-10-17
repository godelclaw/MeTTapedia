import Mettapedia.GSLT.LanguageDef.ScopedBindingElaboration
import Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
import Mettapedia.OSLF.Syntax.SignatureMorphismReadback
import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Rules
import Mathlib.Data.List.Nodup
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFlow
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalFlow
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQuantifierTotality

/-!
# Source capture support, selected interfaces and exact readback

Operational name support covers every authored rule field, including primitive
freshness and quantified-collection lookups, with lexical parameter shadowing.
Selected metadata retains original declaration ordinals and full binding arities.
The existing signature reader lowers schemas and the original explicit source
codec checks only supplied, genuinely used captured bodies. No body is invented
for an unused declaration. Internal metadata views preserve raw instantiation;
original admission and typed-assignment authority remain on the complete source.

The original output traversal is reused with its local primitive occurrence
reader exposed. This is not a normalization or arbitrary target conversion
reflection theorem. Whole-output readback restores the original named-free context, including
explicit substitution and raw collection-rest execution. Per-operation
capture selection respects actual query modes and lexical state. Native
conditional proof-family compilation remains separate.
-/


set_option autoImplicit false
namespace Mettapedia.OSLF.Binding
namespace MetaSelection
variable {S : Signature} {M : List (MetaArity S)}

/-- The original declaration ordinal is retained beside every selected row. -/
def rows (ordinals : List (Fin M.length)) : List (MetaArity S) := ordinals.map M.get

def sourceIndex (ordinals : List (Fin M.length)) (position : Fin (rows ordinals).length) : Fin M.length :=
  ordinals.get ⟨position.val, by simpa only [rows, List.length_map] using position.isLt⟩

theorem row_at (ordinals : List (Fin M.length)) (position : Fin (rows ordinals).length) :
    M.get (sourceIndex ordinals position) = (rows ordinals).get position := by
  exact (List.getElem_map M.get (l := ordinals) (i := position.val)).symm

def ordinal : {sort : S.Srt} → MetaOp M sort → Fin M.length
  | _, .mk index => index

theorem ordinal_cast {first second : MetaArity S} (same : first = second)
    (operator : MetaOp M first.2) : ordinal (castMetaOp same operator) = ordinal operator := by
  cases same
  rfl

theorem sigma_ordinal_injective :
    ∀ (first second : Sigma (MetaOp (S := S) M)), ordinal first.2 = ordinal second.2 → first = second
  | ⟨_, .mk first⟩, ⟨_, .mk second⟩, same => by
      change first = second at same
      subst second
      rfl

theorem ordinal_injective {sort : S.Srt} : Function.Injective (ordinal (M := M) (sort := sort)) := by
  intro first second same
  exact eq_of_heq (Sigma.mk.inj (sigma_ordinal_injective ⟨sort, first⟩ ⟨sort, second⟩ same)).2

def mapMeta (ordinals : List (Fin M.length)) :
    {sort : S.Srt} → MetaOp (rows ordinals) sort → MetaOp M sort
  | _, .mk position => castMetaOp (row_at ordinals position) (.mk (sourceIndex ordinals position))

theorem mapMeta_ordinal (ordinals : List (Fin M.length)) {sort : S.Srt}
    (operator : MetaOp (rows ordinals) sort) :
    ordinal (mapMeta ordinals operator) = sourceIndex ordinals (ordinal operator) := by
  cases operator with
  | mk position => exact ordinal_cast (row_at ordinals position) (.mk (sourceIndex ordinals position))

theorem mapMeta_arity (ordinals : List (Fin M.length)) {sort : S.Srt}
    (operator : MetaOp (rows ordinals) sort) :
    (withMetas S M).arity (.inr (mapMeta ordinals operator)) =
      (withMetas S (rows ordinals)).arity (.inr operator) := by
  cases operator with
  | mk position => exact castMetaOp_arity (sourceIndex ordinals position) (row_at ordinals position)

/-- This is the existing binding-signature map, including all original
ordinary constructors and the complete arity of each selected declaration. -/
@[reducible] def inclusion (ordinals : List (Fin M.length)) :
    SigMor (withMetas S (rows ordinals)) (withMetas S M) where
  sortMap := fun sort => sort
  opMap := fun operator => match operator with
    | .inl source => .inl source
    | .inr selected => .inr (mapMeta ordinals selected)
  carriesArity := by
    intro sort operator
    cases operator with
    | inl source => exact (mapArities_id (S.arity source)).symm
    | inr selected => exact (mapMeta_arity ordinals selected).trans (mapArities_id _).symm

/-- The inverse locates an original ordinal in the actual finite selection.
An absent declaration refuses rather than receiving a fabricated body. -/
def select? (ordinals : List (Fin M.length)) (original : Fin M.length) :
    Option {position : Fin (rows ordinals).length // sourceIndex ordinals position = original} :=
  if present : original ∈ ordinals then
    some ⟨⟨ordinals.idxOf original, by
      simpa only [rows, List.length_map] using List.idxOf_lt_length_iff.mpr present⟩,
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr present)⟩
  else none

def readMeta? (ordinals : List (Fin M.length)) :
    {sort : S.Srt} → MetaOp M sort → Option (MetaOp (rows ordinals) sort)
  | _, .mk original =>
      (select? ordinals original).map fun selected =>
        castMetaOp ((row_at ordinals selected.val).symm.trans (congrArg M.get selected.property)) (.mk selected.val)

theorem readMeta?_ordinal (ordinals : List (Fin M.length)) {sort : S.Srt}
    (original : MetaOp M sort) (selected : MetaOp (rows ordinals) sort)
    (found : readMeta? ordinals original = some selected) :
    sourceIndex ordinals (ordinal selected) = ordinal original := by
  cases original with
  | mk original =>
      obtain ⟨position, chosen, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      rw [ordinal_cast]
      exact position.property

theorem readMeta?_projects (ordinals : List (Fin M.length)) {sort : S.Srt}
    (original : MetaOp M sort) (selected : MetaOp (rows ordinals) sort)
    (found : readMeta? ordinals original = some selected) : mapMeta ordinals selected = original := by
  apply ordinal_injective
  rw [mapMeta_ordinal]
  exact readMeta?_ordinal ordinals original selected found


theorem sourceIndex_injective (ordinals : List (Fin M.length)) (unique : ordinals.Nodup) :
    Function.Injective (sourceIndex ordinals) := by
  intro first second same
  apply Fin.ext
  have position := congrArg (fun index => ordinals.idxOf index) same
  simpa only [sourceIndex, List.get_idxOf unique] using position

theorem select?_some_iff (ordinals : List (Fin M.length)) (original : Fin M.length) :
    (∃ selected, select? ordinals original = some selected) ↔ original ∈ ordinals := by
  unfold select?
  split <;> simp_all

theorem readMeta?_some_iff (ordinals : List (Fin M.length)) {sort : S.Srt}
    (original : MetaOp M sort) :
    (∃ selected, readMeta? ordinals original = some selected) ↔ ordinal original ∈ ordinals := by
  cases original with
  | mk original =>
      simp only [readMeta?, ordinal, Option.map_eq_some_iff]
      constructor
      · rintro ⟨_, selected, found, _⟩
        exact (select?_some_iff ordinals original).mp ⟨selected, found⟩
      · intro present
        obtain ⟨selected, found⟩ := (select?_some_iff ordinals original).mpr present
        exact ⟨_, selected, found, rfl⟩

theorem mapMeta_injective (ordinals : List (Fin M.length)) (unique : ordinals.Nodup)
    {sort : S.Srt} : Function.Injective (mapMeta ordinals (sort := sort)) := by
  intro first second same
  apply ordinal_injective
  apply sourceIndex_injective ordinals unique
  simpa only [mapMeta_ordinal] using congrArg ordinal same

theorem readMeta?_roundtrip (ordinals : List (Fin M.length)) (unique : ordinals.Nodup)
    {sort : S.Srt} (selected : MetaOp (rows ordinals) sort) :
    readMeta? ordinals (mapMeta ordinals selected) = some selected := by
  have present : ordinal (mapMeta ordinals selected) ∈ ordinals := by
    rw [mapMeta_ordinal]
    exact List.get_mem _ _
  obtain ⟨read, found⟩ := (readMeta?_some_iff ordinals _).mpr present
  have same := mapMeta_injective ordinals unique
    (readMeta?_projects ordinals _ _ found)
  simpa only [same] using found

/-- A primitive reader for the existing binding-signature inclusion. -/
def reader (ordinals : List (Fin M.length)) : (inclusion (S := S) ordinals).OperatorReader where
  read := fun operator => match operator with
    | .inl ordinary => some (.inl ordinary)
    | .inr original => (readMeta? ordinals original).map Sum.inr
  projects := by
    intro sort original selected found
    cases original with
    | inl ordinary =>
        cases found
        rfl
    | inr original =>
        change (readMeta? ordinals original).map Sum.inr = some selected at found
        obtain ⟨read, metaRead, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        exact congrArg Sum.inr (readMeta?_projects ordinals original read metaRead)

theorem reader_roundtrip (ordinals : List (Fin M.length)) (unique : ordinals.Nodup)
    {sort : S.Srt} (operator : (withMetas S (rows ordinals)).Op sort) :
    (reader ordinals).read ((inclusion ordinals).opMap operator) = some operator := by
  cases operator with
  | inl ordinary => rfl
  | inr selected =>
      change (readMeta? ordinals (mapMeta ordinals selected)).map Sum.inr = _
      rw [readMeta?_roundtrip ordinals unique]
      rfl

/-- Operator support records original declaration ordinals. Ordinary object
constructors need no additional metavariable body. -/
def Supported (ordinals : List (Fin M.length)) :
    {sort : S.Srt} → (withMetas S M).Op sort → Prop
  | _, .inl _ => True
  | _, .inr original => ordinal original ∈ ordinals

theorem supported_operator (ordinals : List (Fin M.length)) {sort : S.Srt}
    (operator : (withMetas S M).Op sort) (present : Supported ordinals operator) :
    SigMor.OperatorReader.SupportedOperator (inclusion ordinals) (reader ordinals) operator := by
  intro selectedSort same
  change selectedSort = sort at same
  cases same
  cases operator with
  | inl ordinary => exact ⟨.inl ordinary, rfl⟩
  | inr original =>
      obtain ⟨selected, found⟩ := (readMeta?_some_iff ordinals original).mpr present
      exact ⟨.inr selected, by change (readMeta? ordinals original).map Sum.inr = _; rw [found]; rfl⟩

variable [DecidableEq S.Srt]

/-- Reuse the generic reader. The only context transport removes `map id`. -/
def lower? (ordinals : List (Fin M.length)) {context : Ctx S} {sort : S.Srt}
    (original : Term (withMetas S M) context sort) :
    Option (Term (withMetas S (rows ordinals)) context sort) :=
  SigMor.OperatorReader.readTerm (inclusion ordinals) (reader ordinals)
    (castTermCtx (T := withMetas S M) (List.map_id context).symm original)

def embed (ordinals : List (Fin M.length)) {context : Ctx S} {sort : S.Srt}
    (selected : Term (withMetas S (rows ordinals)) context sort) :
    Term (withMetas S M) context sort :=
  castTermCtx (T := withMetas S M) (List.map_id context) ((inclusion ordinals).onTerm selected)

private theorem cancelContext {T : Signature} {first second : Ctx T} (same : first = second)
    {sort : T.Srt} (term : Term T second sort) :
    castTermCtx same (castTermCtx same.symm term) = term := by
  cases same
  rfl

theorem lower?_projects (ordinals : List (Fin M.length)) {context : Ctx S} {sort : S.Srt}
    (original : Term (withMetas S M) context sort)
    (selected : Term (withMetas S (rows ordinals)) context sort)
    (found : lower? ordinals original = some selected) : embed ordinals selected = original := by
  have projected := SigMor.OperatorReader.readTerm_projects (inclusion ordinals) (reader ordinals)
    _ selected found
  unfold embed
  rw [projected]
  exact cancelContext (T := withMetas S M) (List.map_id context) original

theorem lower?_roundtrip (ordinals : List (Fin M.length)) (unique : ordinals.Nodup)
    {context : Ctx S} {sort : S.Srt}
    (selected : Term (withMetas S (rows ordinals)) context sort) :
    lower? ordinals (embed ordinals selected) = some selected := by
  unfold lower? embed
  have cancel : castTermCtx (T := withMetas S M) (List.map_id context).symm
      (castTermCtx (T := withMetas S M) (List.map_id context) ((inclusion ordinals).onTerm selected)) =
      (inclusion ordinals).onTerm selected := by
    exact cancelContext (T := withMetas S M) (List.map_id context).symm _
  rw [cancel]
  exact SigMor.OperatorReader.readTerm_roundtrip (inclusion ordinals) (reader ordinals)
    (reader_roundtrip ordinals unique) selected

theorem embed_injective (ordinals : List (Fin M.length)) (unique : ordinals.Nodup)
    {context : Ctx S} {sort : S.Srt} :
    Function.Injective (embed ordinals (context := context) (sort := sort)) := by
  intro first second same
  have read := congrArg (lower? ordinals) same
  exact Option.some.inj (by simpa only [lower?_roundtrip ordinals unique] using read)

theorem lower?_complete (ordinals : List (Fin M.length))
    {context : Ctx S} {sort : S.Srt} (original : Term (withMetas S M) context sort)
    (supported : original.AllOperators (Supported ordinals)) :
    ∃ selected, lower? ordinals original = some selected := by
  apply SigMor.OperatorReader.readTerm_complete_on (inclusion ordinals) (reader ordinals)
    (fun _ _ same => same)
  exact (Term.AllOperators.castContext (S := withMetas S M)
      (List.map_id context).symm supported).mono
    (fun operator present => supported_operator ordinals operator present)


omit [DecidableEq S.Srt] in
/-- An inclusion introduces no reference to an omitted declaration. The
proof reuses the general map of actual primitive occurrences. -/
theorem embed_supported (ordinals : List (Fin M.length))
    {context : Ctx S} {sort : S.Srt}
    (selected : Term (withMetas S (rows ordinals)) context sort) :
    (embed ordinals selected).AllOperators (Supported ordinals) := by
  unfold embed
  apply Term.AllOperators.castContext
  apply Term.allOperators_mapTerm (inclusion ordinals)
  intro result operator
  cases operator with
  | inl ordinary => trivial
  | inr selected =>
      change ordinal (mapMeta ordinals selected) ∈ ordinals
      rw [mapMeta_ordinal]
      exact List.get_mem _ _

/-- The existing executable reader accepts exactly the terms supported by
the actual selected declaration ordinals. This is independent of whether
any body exists at an unselected result sort. -/
theorem lower?_exists_iff (ordinals : List (Fin M.length))
    {context : Ctx S} {sort : S.Srt} (original : Term (withMetas S M) context sort) :
    (∃ selected, lower? ordinals original = some selected) ↔ original.AllOperators (Supported ordinals) := by
  constructor
  · rintro ⟨selected, accepted⟩
    rw [← lower?_projects ordinals original selected accepted]
    exact embed_supported ordinals selected
  · exact lower?_complete ordinals original

end MetaSelection
end Mettapedia.OSLF.Binding


set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A lexical parameter is supplied locally and is not an outer capture. -/
def externalName (bound : List String) (name : String) : List String :=
  if name ∈ bound then [] else [name]

/-- Read every original premise field. Pattern names include collection rest
positions; freshness names and quantified collection inputs are additional
runtime lookups. A quantified parameter shadows its outer capture. -/
def premiseReadNames (bound : List String) : Premise → List String
  | .freshness condition => externalName bound condition.varName ++
      LanguageDef.patternFvarNames bound condition.term
  | .congruence source target => LanguageDef.patternFvarNames bound source ++
      LanguageDef.patternFvarNames bound target
  | .scopedStep step => LanguageDef.patternFvarNames bound step.source ++
      LanguageDef.patternFvarNames bound step.target
  | .relationQuery _ arguments => arguments.flatMap (LanguageDef.patternFvarNames bound)
  | .forAll collection parameter body => externalName bound collection ++
      premiseReadNames (parameter :: bound) body

/-- Occurrence in an original premise field, independently of enumeration.
The relation distinguishes primitive name reads from pattern occurrences. -/
inductive PremiseReads : List String → Premise → String → Prop where
  | freshnessName (bound : List String) (condition : FreshnessCondition)
      (outside : condition.varName ∉ bound) :
      PremiseReads bound (.freshness condition) condition.varName
  | freshnessTerm {bound : List String} {condition : FreshnessCondition} {name : String}
      (outside : name ∉ bound) (occurs : name ∈ condition.term.freeFvarNames) :
      PremiseReads bound (.freshness condition) name
  | congruenceSource {bound : List String} {source target : Pattern} {name : String}
      (outside : name ∉ bound) (occurs : name ∈ source.freeFvarNames) :
      PremiseReads bound (.congruence source target) name
  | congruenceTarget {bound : List String} {source target : Pattern} {name : String}
      (outside : name ∉ bound) (occurs : name ∈ target.freeFvarNames) :
      PremiseReads bound (.congruence source target) name
  | scopedSource {bound : List String} {step : ScopedStepPremise} {name : String}
      (outside : name ∉ bound) (occurs : name ∈ step.source.freeFvarNames) :
      PremiseReads bound (.scopedStep step) name
  | scopedTarget {bound : List String} {step : ScopedStepPremise} {name : String}
      (outside : name ∉ bound) (occurs : name ∈ step.target.freeFvarNames) :
      PremiseReads bound (.scopedStep step) name
  | queryArgument {bound : List String} {relation name : String} {arguments : List Pattern}
      (argument : Pattern) (member : argument ∈ arguments)
      (outside : name ∉ bound) (occurs : name ∈ argument.freeFvarNames) :
      PremiseReads bound (.relationQuery relation arguments) name
  | quantifiedCollection {bound : List String} {collection parameter : String} {body : Premise}
      (outside : collection ∉ bound) :
      PremiseReads bound (.forAll collection parameter body) collection
  | quantifiedBody {bound : List String} {collection parameter name : String} {body : Premise}
      (occurs : PremiseReads (parameter :: bound) body name) :
      PremiseReads bound (.forAll collection parameter body) name

private theorem mem_externalName {bound : List String} {name queried : String} :
    queried ∈ externalName bound name ↔ queried = name ∧ name ∉ bound := by
  unfold externalName
  split <;> simp_all

private theorem mem_patternFvarNames {bound : List String} {pattern : Pattern} {name : String} :
    name ∈ LanguageDef.patternFvarNames bound pattern ↔
      name ∈ pattern.freeFvarNames ∧ name ∉ bound := by
  simp [LanguageDef.patternFvarNames]

/-- Enumeration covers exactly the original operational fields and lexical
scope. In particular neither primitive name lookup is omitted. -/
theorem premiseReadNames_exact {bound : List String} {premise : Premise} {name : String} :
    name ∈ premiseReadNames bound premise ↔ PremiseReads bound premise name := by
  induction premise generalizing bound with
  | freshness condition =>
      simp only [premiseReadNames, List.mem_append, mem_externalName, mem_patternFvarNames]
      constructor
      · rintro (⟨same, outside⟩ | ⟨occurs, outside⟩)
        · subst name; exact .freshnessName bound condition outside
        · exact .freshnessTerm outside occurs
      · intro read
        cases read with
        | freshnessName _ _ outside => exact .inl ⟨rfl, outside⟩
        | freshnessTerm outside occurs => exact .inr ⟨occurs, outside⟩
  | congruence source target =>
      simp only [premiseReadNames, List.mem_append, mem_patternFvarNames]
      constructor
      · rintro (⟨occurs, outside⟩ | ⟨occurs, outside⟩)
        · exact .congruenceSource outside occurs
        · exact .congruenceTarget outside occurs
      · intro read
        cases read with
        | congruenceSource outside occurs => exact .inl ⟨occurs, outside⟩
        | congruenceTarget outside occurs => exact .inr ⟨occurs, outside⟩
  | scopedStep step =>
      simp only [premiseReadNames, List.mem_append, mem_patternFvarNames]
      constructor
      · rintro (⟨occurs, outside⟩ | ⟨occurs, outside⟩)
        · exact .scopedSource outside occurs
        · exact .scopedTarget outside occurs
      · intro read
        cases read with
        | scopedSource outside occurs => exact .inl ⟨occurs, outside⟩
        | scopedTarget outside occurs => exact .inr ⟨occurs, outside⟩
  | relationQuery relation arguments =>
      simp only [premiseReadNames, List.mem_flatMap, mem_patternFvarNames]
      constructor
      · rintro ⟨argument, member, occurs, outside⟩
        exact .queryArgument argument member outside occurs
      · intro read
        cases read with
        | queryArgument argument member outside occurs => exact ⟨argument, member, occurs, outside⟩
  | forAll collection parameter body inductionHypothesis =>
      simp only [premiseReadNames, List.mem_append, mem_externalName, inductionHypothesis]
      constructor
      · rintro (⟨same, outside⟩ | occurs)
        · subst name; exact .quantifiedCollection outside
        · exact .quantifiedBody occurs
      · intro read
        cases read with
        | quantifiedCollection outside => exact .inl ⟨rfl, outside⟩
        | quantifiedBody occurs => exact .inr occurs

/-- Support of all rule fields; unused metadata rows are not made into
runtime parameters merely by appearing in `typeContext`. -/
def ruleReadNames (rule : RewriteRule) : List String :=
  rule.left.freeFvarNames ++ rule.right.freeFvarNames ++
    rule.premises.flatMap (premiseReadNames [])

inductive RuleReads (rule : RewriteRule) (name : String) : Prop where
  | left (occurs : name ∈ rule.left.freeFvarNames)
  | right (occurs : name ∈ rule.right.freeFvarNames)
  | premise (premise : Premise) (member : premise ∈ rule.premises)
      (read : PremiseReads [] premise name)

theorem ruleReadNames_exact {rule : RewriteRule} {name : String} :
    name ∈ ruleReadNames rule ↔ RuleReads rule name := by
  simp only [ruleReadNames, List.mem_append, List.mem_flatMap, premiseReadNames_exact]
  constructor
  · rintro ((occurs | occurs) | ⟨premise, member, read⟩)
    · exact .left occurs
    · exact .right occurs
    · exact .premise premise member read
  · intro read
    cases read with
    | left occurs => exact .inl (.inl occurs)
    | right occurs => exact .inl (.inr occurs)
    | premise premise member read => exact .inr ⟨premise, member, read⟩

/-- Keep original declaration positions. The support is a selection rather
than a renumbering of the source metadata. -/
def usedRows (rule : RewriteRule) : List (Fin rule.typeContext.length) :=
  (List.finRange rule.typeContext.length).filter fun position =>
    (ruleReadNames rule).contains (rule.typeContext.get position).1

theorem mem_usedRows {rule : RewriteRule} {position : Fin rule.typeContext.length} :
    position ∈ usedRows rule ↔ RuleReads rule (rule.typeContext.get position).1 := by
  simp only [usedRows, List.mem_filter, List.mem_finRange, true_and,
    List.contains_iff_mem, ruleReadNames_exact]

theorem usedRows_nodup (rule : RewriteRule) : (usedRows rule).Nodup :=
  (List.nodup_finRange _).filter _



/-- Site-local parameters are supplied by lexical evaluation. They are
kept beside the outer captures, rather than demanded as global values. -/
def usedRowsAt (rule : RewriteRule) (parameters : List String) : List (Fin rule.typeContext.length) :=
  (List.finRange rule.typeContext.length).filter fun position =>
    (ruleReadNames rule ++ parameters).contains (rule.typeContext.get position).1

theorem mem_usedRowsAt {rule : RewriteRule} {parameters : List String}
    {position : Fin rule.typeContext.length} :
    position ∈ usedRowsAt rule parameters ↔
      RuleReads rule (rule.typeContext.get position).1 ∨ (rule.typeContext.get position).1 ∈ parameters := by
  simp only [usedRowsAt, List.mem_filter, List.mem_finRange, true_and,
    List.contains_iff_mem, List.mem_append, ruleReadNames_exact]

theorem usedRowsAt_nodup (rule : RewriteRule) (parameters : List String) :
    (usedRowsAt rule parameters).Nodup := (List.nodup_finRange _).filter _

/-- An internal metadata view keeps the original rule's operational fields.
It carries no assertion that its shorter context is independently admitted. -/
def captureViewFor (rule : RewriteRule) (positions : List (Fin rule.typeContext.length)) : RewriteRule :=
  { rule with typeContext := positions.map rule.typeContext.get }


def captureView (rule : RewriteRule) : RewriteRule :=
  captureViewFor rule (usedRows rule)

def captureViewIndex (rule : RewriteRule) (position : Fin (captureView rule).typeContext.length) :
    Fin rule.typeContext.length :=
  (usedRows rule).get ⟨position.val, by simpa only [captureView, captureViewFor, List.length_map] using position.isLt⟩

theorem captureView_source_row (rule : RewriteRule) (position : Fin (captureView rule).typeContext.length) :
    (captureView rule).typeContext.get position = rule.typeContext.get (captureViewIndex rule position) := by
  exact List.getElem_map _

theorem captureView_source_mem (rule : RewriteRule) (position : Fin (captureView rule).typeContext.length) :
    captureViewIndex rule position ∈ usedRows rule := List.get_mem _ _

theorem captureViewIndex_injective (rule : RewriteRule) : Function.Injective (captureViewIndex rule) := by
  intro first second same
  apply Fin.ext
  have positions := congrArg (fun original => (usedRows rule).idxOf original) same
  simpa only [captureViewIndex, List.get_idxOf (usedRows_nodup rule)] using positions

/-- Raw occurrence lookup observes these three source fields, not the
metadata ordinal used internally by an intrinsic compiler. -/
theorem arguments?_same_body (first second : RewriteRule) (spec : RuleBindingSpec)
    (same : first.left = second.left ∧ first.right = second.right ∧ first.premises = second.premises)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    arguments? first spec name site path = arguments? second spec name site path := by
  cases first
  cases second
  rcases same with ⟨left, right, premises⟩
  cases left
  cases right
  cases premises
  rfl

theorem arguments?_captureView (rule : RewriteRule) (spec : RuleBindingSpec)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    arguments? (captureView rule) spec name site path = arguments? rule spec name site path :=
  arguments?_same_body _ _ spec ⟨rfl, rfl, rfl⟩ name site path

end Mettapedia.OSLF.MeTTaIL.RuleBinding


set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Local named parameters are separate from object de Bruijn binders.
The existing authored parameter list supplies their lexical order. -/
def quantifiedParameters (count : Nat) (premise : Premise) : List String :=
  ((LanguageDef.premiseForAllParams premise).take count).reverse

theorem quantifiedBody?_reads : ∀ (count : Nat) (premise body : Premise),
    quantifiedBody? count premise = some body →
    ∀ (bound : List String) (name : String),
      PremiseReads (quantifiedParameters count premise ++ bound) body name →
      PremiseReads bound premise name
  | 0, premise, body, found, bound, name, read => by
      cases Option.some.inj found
      simpa only [quantifiedParameters, List.take_zero, List.reverse_nil, List.nil_append] using read
  | count + 1, .forAll collection parameter premise, body, found, bound, name, read => by
      apply PremiseReads.quantifiedBody
      apply quantifiedBody?_reads count premise body found (parameter :: bound) name
      simpa [quantifiedParameters, LanguageDef.premiseForAllParams, List.take_succ_cons,
        List.reverse_cons, List.append_assoc] using read
  | _ + 1, .freshness _, _, found, _, _, _ => by cases found
  | _ + 1, .congruence _ _, _, found, _, _, _ => by cases found
  | _ + 1, .scopedStep _, _, found, _, _, _ => by cases found
  | _ + 1, .relationQuery _ _, _, found, _, _, _ => by cases found

/-- The selected site's local named parameters. The actual quantified body
must exist; an excessive requested depth refuses. -/
def siteParameters? (rule : RewriteRule) : RulePatternSite → Option (List String)
  | .left | .right => some []
  | .premise index count _ => do
      let premise ← rule.premises[index]?
      let _ ← quantifiedBody? count premise
      pure (quantifiedParameters count premise)

/-- Every nonlocal name in an actual source site belongs to the whole-rule
support. Quantified local parameters are deliberately excluded here and are
supplied by their actual lexical iteration, not by a global capture. -/
theorem sitePattern?_reads (rule : RewriteRule) (site : RulePatternSite)
    (pattern : Pattern) (parameters : List String)
    (source : sitePattern? rule site = some pattern)
    (locals : siteParameters? rule site = some parameters)
    (name : String) (member : name ∈ pattern.freeFvarNames) (outside : name ∉ parameters) :
    RuleReads rule name := by
  cases site with
  | left =>
      have same := Option.some.inj source
      cases same
      exact .left member
  | right =>
      have same := Option.some.inj source
      cases same
      exact .right member
  | premise index count argument =>
      cases premiseFound : rule.premises[index]? with
      | none => simp only [sitePattern?, premiseFound, Option.bind_eq_bind, Option.bind_none] at source; cases source
      | some premise =>
        cases bodyFound : quantifiedBody? count premise with
        | none => simp only [sitePattern?, premiseFound, Option.bind_eq_bind, Option.bind_some, bodyFound, Option.bind_none] at source; cases source
        | some body =>
          have localNames : quantifiedParameters count premise = parameters := by
            simpa only [siteParameters?, premiseFound, Option.bind_eq_bind, Option.bind_some, bodyFound,
              pure, Option.some.injEq] using locals
          have out : name ∉ quantifiedParameters count premise := by simpa only [localNames] using outside
          apply RuleReads.premise premise (List.mem_of_getElem? premiseFound)
          apply quantifiedBody?_reads count premise body bodyFound [] name
          simp only [List.append_nil]
          simp only [sitePattern?, premiseFound, Option.bind_eq_bind, Option.bind_some, bodyFound] at source
          cases body with
          | freshness condition =>
              dsimp only at source
              split at source
              · cases Option.some.inj source
                exact .freshnessTerm out member
              · cases source
          | congruence left right =>
              dsimp only at source
              split at source
              · cases Option.some.inj source
                exact .congruenceSource out member
              · split at source
                · cases Option.some.inj source
                  exact .congruenceTarget out member
                · cases source
          | scopedStep step =>
              dsimp only at source
              split at source
              · cases Option.some.inj source
                exact .scopedSource out member
              · split at source
                · cases Option.some.inj source
                  exact .scopedTarget out member
                · cases source
          | relationQuery relation arguments =>
              dsimp only at source
              exact .queryArgument pattern (List.mem_of_getElem? source) out member
          | forAll collection parameter body =>
              dsimp only at source
              cases source

end Mettapedia.OSLF.MeTTaIL.RuleBinding


set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding

/-- Agreement is required only at the actual named occurrences. Literal
free names inside captured bodies remain data of the retained value. -/
def AgreeOn (first second : Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, lookup first name = lookup second name

theorem AgreeOn.mono {first second : Assignment} {small large : List String}
    (agree : AgreeOn first second large) (within : ∀ name ∈ small, name ∈ large) :
    AgreeOn first second small := fun name member => agree name (within name member)

theorem AgreeOn.append {first second : Assignment} {front back : List String} :
    AgreeOn first second (front ++ back) ↔ AgreeOn first second front ∧ AgreeOn first second back := by
  constructor
  · intro agree
    exact ⟨agree.mono (fun _ member => List.mem_append_left _ member),
      agree.mono (fun _ member => List.mem_append_right _ member)⟩
  · rintro ⟨frontAgree, backAgree⟩ name member
    rcases List.mem_append.mp member with member | member
    · exact frontAgree name member
    · exact backAgree name member

mutual
/-- The original instantiator depends only on the original operational rule
fields and actual source-name lookups. It retains site/path/binder depth and
the original binder-elimination operation, including collection rest. -/
theorem instantiateWith?_congr (operation : Pattern → Pattern → Pattern)
    (firstRule secondRule : RewriteRule) (spec : RuleBindingSpec)
    (sameBody : firstRule.left = secondRule.left ∧ firstRule.right = secondRule.right ∧
      firstRule.premises = secondRule.premises)
    (ambient : Nat) (site : RulePatternSite) (first second : Assignment) :
    ∀ (pattern : Pattern) (path : List Nat) (depth : Nat),
      AgreeOn first second pattern.freeFvarNames →
      instantiateWith? operation firstRule spec ambient site path depth first pattern =
        instantiateWith? operation secondRule spec ambient site path depth second pattern
  | .bvar _, _, _, _ => by simp only [instantiateWith?]
  | .fvar name, path, depth, agree => by
      simp only [instantiateWith?, agree name (by simp [Pattern.freeFvarNames]),
        arguments?_same_body firstRule secondRule spec sameBody name site path]
  | .apply constructor arguments, path, depth, agree => by
      simp only [Pattern.freeFvarNames] at agree
      simp only [instantiateWith?, instantiateArgsWith?_congr operation firstRule secondRule spec sameBody ambient site
        first second arguments path depth 0 agree]
  | .lambda binder body, path, depth, agree => by
      simp only [Pattern.freeFvarNames] at agree
      simp only [instantiateWith?, instantiateWith?_congr operation firstRule secondRule spec sameBody ambient site
        first second body (path ++ [0]) (depth + 1) agree]
  | .multiLambda count binders body, path, depth, agree => by
      simp only [Pattern.freeFvarNames] at agree
      simp only [instantiateWith?, instantiateWith?_congr operation firstRule secondRule spec sameBody ambient site
        first second body (path ++ [0]) (depth + count) agree]
  | .subst body replacement, path, depth, agree => by
      simp only [Pattern.freeFvarNames] at agree
      obtain ⟨bodyAgree, replacementAgree⟩ := AgreeOn.append.mp agree
      simp only [instantiateWith?, instantiateWith?_congr operation firstRule secondRule spec sameBody ambient site
        first second body (path ++ [0]) (depth + 1) bodyAgree,
        instantiateWith?_congr operation firstRule secondRule spec sameBody ambient site
          first second replacement (path ++ [1]) depth replacementAgree]
  | .collection kind elements rest, path, depth, agree => by
      simp only [Pattern.freeFvarNames] at agree
      obtain ⟨elementsAgree, restAgree⟩ := AgreeOn.append.mp agree
      have sameElements := instantiateArgsWith?_congr operation firstRule secondRule spec sameBody ambient site
        first second elements path depth 0 elementsAgree
      cases rest with
      | none => simp only [instantiateWith?, sameElements]
      | some name =>
          simp only [instantiateWith?, sameElements,
            restAgree name (by simp [Option.toList_some]),
            arguments?_same_body firstRule secondRule spec sameBody name site (path ++ [elements.length])]
termination_by pattern => sizeOf pattern

/-- Argument iteration reads every original position at its original address. -/
theorem instantiateArgsWith?_congr (operation : Pattern → Pattern → Pattern)
    (firstRule secondRule : RewriteRule) (spec : RuleBindingSpec)
    (sameBody : firstRule.left = secondRule.left ∧ firstRule.right = secondRule.right ∧
      firstRule.premises = secondRule.premises)
    (ambient : Nat) (site : RulePatternSite) (first second : Assignment) :
    ∀ (patterns : List Pattern) (path : List Nat) (depth index : Nat),
      AgreeOn first second (patterns.flatMap Pattern.freeFvarNames) →
      instantiateArgsWith? operation firstRule spec ambient site path depth first index patterns =
        instantiateArgsWith? operation secondRule spec ambient site path depth second index patterns
  | [], _, _, _, _ => by simp only [instantiateArgsWith?]
  | pattern :: patterns, path, depth, index, agree => by
      simp only [List.flatMap_cons] at agree
      obtain ⟨headAgree, tailAgree⟩ := AgreeOn.append.mp agree
      simp only [instantiateArgsWith?, instantiateWith?_congr operation firstRule secondRule spec sameBody ambient site
        first second pattern (path ++ [index]) depth headAgree,
        instantiateArgsWith?_congr operation firstRule secondRule spec sameBody ambient site
          first second patterns path depth (index + 1) tailAgree]
termination_by patterns => sizeOf patterns
end

theorem instantiateAt?_congr (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (first second : Assignment) (pattern : Pattern)
    (agree : AgreeOn first second pattern.freeFvarNames) :
    instantiateAt? rule spec ambient site path depth first pattern =
      instantiateAt? rule spec ambient site path depth second pattern :=
  instantiateWith?_congr _ rule rule spec ⟨rfl, rfl, rfl⟩ ambient site first second pattern path depth agree

/-- Changing only the internal metadata view cannot change source execution.
Original admission and typed-assignment checks still use the original rule. -/
theorem instantiateWith?_captureView (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern) :
    instantiateWith? operation (captureView rule) spec ambient site path depth assignment pattern =
      instantiateWith? operation rule spec ambient site path depth assignment pattern :=
  instantiateWith?_congr operation (captureView rule) rule spec ⟨rfl, rfl, rfl⟩ ambient site assignment assignment pattern path depth
    (fun _ _ => rfl)

theorem instantiateAt?_captureView (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) :
    instantiateAt? (captureView rule) spec ambient site path depth assignment pattern =
      instantiateAt? rule spec ambient site path depth assignment pattern :=
  instantiateWith?_captureView _ rule spec ambient site path depth assignment pattern

end Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching

/-- A freshness name really observes its lookup even when its unbound case
is interpreted as a literal atom. -/
theorem freshnessName?_congr (ambient : Nat) (first second : Assignment) (name : String)
    (agree : lookup first name = lookup second name) :
    freshnessName? ambient first name = freshnessName? ambient second name := by
  simp only [freshnessName?, agree]

theorem finiteCollection?_congr (ambient : Nat) (first second : Assignment) (name : String)
    (agree : lookup first name = lookup second name) :
    finiteCollection? ambient first name = finiteCollection? ambient second name := by
  simp only [finiteCollection?, agree]

/-- Lexical binding supplies the same local value on both sides; it removes
the need for an outer capture at that parameter name. -/
theorem AgreeOn.bindParameter {first second : Assignment} {parameter : String}
    {names : List String} (value : ContextualValue)
    (agree : AgreeOn first second (names.filter fun name => name != parameter)) :
    AgreeOn (bindParameter parameter value first) (bindParameter parameter value second) names := by
  intro name member
  by_cases same : name = parameter
  · subst name; simp only [lookup_bind_parameter]
  · rw [lookup_bind_other _ _ _ _ same, lookup_bind_other _ _ _ _ same]
    exact agree name (List.mem_filter.mpr ⟨member, by simp [same]⟩)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise


set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Certificates.Shared

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- One original declaration and its retained source packet. Only submitted
positions are decoded; unused declarations receive no body value. -/
structure SelectedEvidence (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (entries : List (String × TypeExpr)) (ambient : List TypeExpr) (assignment : Assignment)
    (index : Fin (metaArities (language := language) rule spec).length) where
  original : ContextualValue
  stored : lookup assignment (metaName rule spec index) = some original
  evidence : Data
  parsed : EvidenceCaptured language entries ((metaArities rule spec).get index).1 ambient
    original ((metaArities rule spec).get index).2 evidence

def selectEvidence? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (entries : List (String × TypeExpr)) (ambient : List TypeExpr) (assignment : Assignment)
    (submitted : List (Nat × Data)) (index : Fin (metaArities (language := language) rule spec).length) :
    Option (SelectedEvidence language rule spec entries ambient assignment index) :=
  match stored : lookup assignment (metaName rule spec index) with
  | none => none
  | some original => do
      let evidence ← submitted.lookup index.val
      let parsed ← captureEvidence? language entries ((metaArities rule spec).get index).1 ambient
        original ((metaArities rule spec).get index).2 evidence
      pure ⟨original, stored, evidence, parsed⟩

def SelectedEvidence.selected {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {index : Fin (metaArities (language := language) rule spec).length}
    (captured : SelectedEvidence language rule spec entries ambient assignment index) :
    SelectedCapture language rule spec entries ambient assignment index :=
  ⟨captured.original, captured.stored, captured.parsed.toCaptured⟩

/-- Successful decoding retains both the original runtime lookup and the
exact submitted ordinal/code, with the original source checker result. -/
theorem selectEvidence?_readout {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {submitted : List (Nat × Data)}
    {index : Fin (metaArities (language := language) rule spec).length}
    {captured : SelectedEvidence language rule spec entries ambient assignment index}
    (found : selectEvidence? language rule spec entries ambient assignment submitted index = some captured) :
    submitted.lookup index.val = some captured.evidence ∧
      captureEvidence? language entries ((metaArities rule spec).get index).1 ambient captured.original
        ((metaArities rule spec).get index).2 captured.evidence = some captured.parsed := by
  unfold selectEvidence? at found
  split at found
  · cases found
  · obtain ⟨evidence, provided, remaining⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨parsed, checked, same⟩ := Option.bind_eq_some_iff.mp remaining
    cases Option.some.inj same
    exact ⟨provided, checked⟩

/-- A family indexed only by the selected original declaration ordinals. -/
abbrev SelectedFamily (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (entries : List (String × TypeExpr)) (ambient : List TypeExpr) (assignment : Assignment)
    (ordinals : List (Fin (metaArities (language := language) rule spec).length)) :=
  (position : Fin (MetaSelection.rows ordinals).length) →
    SelectedEvidence language rule spec entries ambient assignment (MetaSelection.sourceIndex ordinals position)

def selectedFamily? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (entries : List (String × TypeExpr)) (ambient : List TypeExpr) (assignment : Assignment)
    (submitted : List (Nat × Data))
    (ordinals : List (Fin (metaArities (language := language) rule spec).length)) :
    Option (SelectedFamily language rule spec entries ambient assignment ordinals) :=
  allFin? _ (fun position => selectEvidence? language rule spec entries ambient assignment submitted
    (MetaSelection.sourceIndex ordinals position))

/-- Every selected value was actually looked up and decoded at its original
ordinal. No neighboring declaration or unsubmitted value is substituted. -/
theorem selectedFamily?_at {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {submitted : List (Nat × Data)}
    {ordinals : List (Fin (metaArities (language := language) rule spec).length)}
    {family : SelectedFamily language rule spec entries ambient assignment ordinals}
    (found : selectedFamily? language rule spec entries ambient assignment submitted ordinals = some family)
    (position : Fin (MetaSelection.rows ordinals).length) :
    selectEvidence? language rule spec entries ambient assignment submitted
      (MetaSelection.sourceIndex ordinals position) = some (family position) :=
  allFin?_some found position

theorem selectedFamily?_exists_iff {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {submitted : List (Nat × Data)}
    (ordinals : List (Fin (metaArities (language := language) rule spec).length)) :
    (∃ family, selectedFamily? language rule spec entries ambient assignment submitted ordinals = some family) ↔
      ∀ index ∈ ordinals, ∃ captured,
        selectEvidence? language rule spec entries ambient assignment submitted index = some captured := by
  constructor
  · rintro ⟨family, found⟩ index member
    obtain ⟨⟨position, same⟩, _⟩ := (MetaSelection.select?_some_iff ordinals index).mpr member
    cases same
    exact ⟨family position, selectedFamily?_at found position⟩
  · intro available
    have allAvailable : ∀ position : Fin (MetaSelection.rows ordinals).length,
        (selectEvidence? language rule spec entries ambient assignment submitted
          (MetaSelection.sourceIndex ordinals position)).isSome = true := by
      intro position
      obtain ⟨captured, found⟩ := available (MetaSelection.sourceIndex ordinals position) (List.get_mem _ _)
      rw [found]
      rfl
    have complete := allFin?_complete allAvailable
    change (selectedFamily? language rule spec entries ambient assignment submitted ordinals).isSome = true at complete
    cases found : selectedFamily? language rule spec entries ambient assignment submitted ordinals with
    | none => rw [found] at complete; cases complete
    | some family => exact ⟨family, rfl⟩

/-- Actual checked source bodies become a total assignment on the selected
interface, with the original ambient and finite-name suffix retained. -/
def SelectedFamily.bodies {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {ordinals : List (Fin (metaArities (language := language) rule spec).length)}
    (family : SelectedFamily language rule spec entries ambient assignment ordinals) :
    ContextualAssignment (signatureOf language) (MetaSelection.rows ordinals)
      (ambient ++ NamedFreeContext.contextSorts entries) :=
  fun position =>
    castContextualMetaBody (MetaSelection.row_at ordinals position)
      (family position).parsed.toCaptured.extendedBody

/-- Selected capture evidence feeds the original runtime occurrence observer.
This is a source execution fact, not merely equality of packet encoders. -/
theorem SelectedFamily.observes {entries : List (String × TypeExpr)} {ambient locals : List TypeExpr}
    {assignment : Assignment} {ordinals : List (Fin (metaArities (language := language) rule spec).length)}
    (family : SelectedFamily language rule spec entries ambient assignment ordinals)
    (position : Fin (MetaSelection.rows ordinals).length)
    (arguments : DependencyArguments (language := language)
      ((metaArities rule spec).get (MetaSelection.sourceIndex ordinals position)).1
      (locals ++ (ambient ++ NamedFreeContext.contextSorts entries))) :
    (lookup assignment (metaName rule spec (MetaSelection.sourceIndex ordinals position))).bind
      (fun value => instantiateValue? value ambient.length locals.length
        (openedArguments entries (locals ++ ambient) (eraseArguments arguments))) =
      some ((family position).parsed.toCaptured.occurrenceReadback arguments) :=
  (family position).selected.instantiateValue?_stored arguments

/-- Independent source coverage at one actual used ordinal. The original
body judgment, dependency types and ambient count earn explicit evidence. -/
theorem selectEvidence?_complete {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} (index : Fin (metaArities (language := language) rule spec).length)
    (unique : (entries.map Prod.fst).Nodup)
    (source : ContextualValue) (stored : lookup assignment (metaName rule spec index) = some source)
    (typed : OpenPatternWellSorted language (FreeTypeContext.ofList entries)
      (((metaArities rule spec).get index).1 ++ ambient) ((metaArities rule spec).get index).2 source.body)
    (dependencies : source.dependencies = ((metaArities rule spec).get index).1)
    (ambientEq : source.ambient = ambient.length) :
    ∃ (evidence : Data) (captured : SelectedEvidence language rule spec entries ambient assignment index),
      selectEvidence? language rule spec entries ambient assignment [(index.val, evidence)] index = some captured := by
  obtain ⟨evidence, parsed, accepted⟩ := captureEvidence?_complete unique typed dependencies ambientEq
  refine ⟨evidence, ⟨source, stored, evidence, parsed⟩, ?_⟩
  unfold selectEvidence?
  split
  · rename_i absent
    rw [stored] at absent
    cases absent
  · rename_i original read
    have same : original = source := Option.some.inj (read.symm.trans stored)
    cases same
    simp only [List.lookup_cons_self, Option.bind_eq_bind, Option.bind_some, accepted]
    rfl


theorem lookup_of_mem_unique {Key Value : Type} [BEq Key] [LawfulBEq Key]
    {entries : List (Key × Value)}
    (unique : (entries.map Prod.fst).Nodup) {key : Key} {value : Value}
    (member : (key, value) ∈ entries) : entries.lookup key = some value := by
  induction entries with
  | nil => cases member
  | cons first rest inductionHypothesis =>
      rcases first with ⟨firstKey, firstValue⟩
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with same | member
      · cases same; exact List.lookup_cons_self
      · have different : key ≠ firstKey := by
          intro same
          apply unique.1
          rw [← same]
          exact List.mem_map.mpr ⟨(key, value), member, rfl⟩
        simp only [List.lookup_cons, show (key == firstKey) = false from by simp [different]]
        exact inductionHypothesis unique.2 member

/-- Serialization contains just the selected original ordinals. Inference
occurrences remain in their original source/certificate structures. -/
def SelectedFamily.submitted {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {ordinals : List (Fin (metaArities (language := language) rule spec).length)}
    (family : SelectedFamily language rule spec entries ambient assignment ordinals) : List (Nat × Data) :=
  List.ofFn fun position => ((MetaSelection.sourceIndex ordinals position).val, (family position).evidence)

theorem SelectedFamily.submitted_lookup {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {ordinals : List (Fin (metaArities (language := language) rule spec).length)}
    (family : SelectedFamily language rule spec entries ambient assignment ordinals)
    (unique : ordinals.Nodup) (position : Fin (MetaSelection.rows ordinals).length) :
    family.submitted.lookup (MetaSelection.sourceIndex ordinals position).val = some (family position).evidence := by
  apply lookup_of_mem_unique
  · simp only [SelectedFamily.submitted, List.map_ofFn]
    apply List.nodup_ofFn_ofInjective
    intro first second same
    exact MetaSelection.sourceIndex_injective ordinals unique (Fin.ext same)
  · exact List.mem_ofFn.mpr ⟨position, rfl⟩

private theorem evidenceCaptured_replay {entries : List (String × TypeExpr)}
    {dependencies ambient : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    {evidence : Data} (captured : EvidenceCaptured language entries dependencies ambient source sort evidence) :
    captureEvidence? language entries dependencies ambient source sort evidence = some captured := by
  cases captured with
  | mk captured encoded =>
      cases encoded
      exact captureEvidence?_put captured

theorem selectEvidence?_replay {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {index : Fin (metaArities (language := language) rule spec).length}
    (captured : SelectedEvidence language rule spec entries ambient assignment index)
    (submitted : List (Nat × Data))
    (provided : submitted.lookup index.val = some captured.evidence) :
    selectEvidence? language rule spec entries ambient assignment submitted index = some captured := by
  have checked : captureEvidence? language entries ((metaArities rule spec).get index).1 ambient
      captured.original ((metaArities rule spec).get index).2 captured.evidence = some captured.parsed := by
    exact evidenceCaptured_replay captured.parsed
  unfold selectEvidence?
  split
  · rename_i absent
    rw [captured.stored] at absent
    cases absent
  · rename_i original read
    have same : original = captured.original := Option.some.inj (read.symm.trans captured.stored)
    cases same
    simp only [provided, Option.bind_eq_bind, Option.bind_some, checked]
    rfl

/-- All submitted source bytes replay. Completeness is inherited from the
same finite sequencing procedure used by the common certificate kernel. -/
theorem selectedFamily?_replay {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment} {ordinals : List (Fin (metaArities (language := language) rule spec).length)}
    (family : SelectedFamily language rule spec entries ambient assignment ordinals)
    (unique : ordinals.Nodup) :
    selectedFamily? language rule spec entries ambient assignment family.submitted ordinals = some family := by
  have atEvery : ∀ position,
      selectEvidence? language rule spec entries ambient assignment family.submitted
        (MetaSelection.sourceIndex ordinals position) = some (family position) :=
    fun position => selectEvidence?_replay (family position) family.submitted (family.submitted_lookup unique position)
  have complete := allFin?_complete
    (select := fun position => selectEvidence? language rule spec entries ambient assignment
      family.submitted (MetaSelection.sourceIndex ordinals position))
    (fun position => by rw [atEvery position]; rfl)
  change (selectedFamily? language rule spec entries ambient assignment family.submitted ordinals).isSome = true at complete
  cases found : selectedFamily? language rule spec entries ambient assignment family.submitted ordinals with
  | none => rw [found] at complete; cases complete
  | some decoded =>
      have same : decoded = family := by
        funext position
        exact Option.some.inj ((selectedFamily?_at found position).symm.trans (atEvery position))
      rw [same]

/-- A finite accepted family exists for exactly the actual selected source
captures supplied by the original open-object judgment. No original total
metavariable assignment is required, even when an unused sort is empty. -/
theorem selectedFamily?_complete {entries : List (String × TypeExpr)} {ambient : List TypeExpr}
    {assignment : Assignment}
    (ordinals : List (Fin (metaArities (language := language) rule spec).length))
    (uniqueOrdinals : ordinals.Nodup) (uniqueNames : (entries.map Prod.fst).Nodup)
    (source : ∀ index ∈ ordinals, ∃ value,
      lookup assignment (metaName rule spec index) = some value ∧
      OpenPatternWellSorted language (FreeTypeContext.ofList entries)
        (((metaArities rule spec).get index).1 ++ ambient) ((metaArities rule spec).get index).2 value.body ∧
      value.dependencies = ((metaArities rule spec).get index).1 ∧ value.ambient = ambient.length) :
    ∃ submitted family, selectedFamily? language rule spec entries ambient assignment submitted ordinals = some family := by
  classical
  have available : ∀ position : Fin (MetaSelection.rows ordinals).length,
      Nonempty (SelectedEvidence language rule spec entries ambient assignment (MetaSelection.sourceIndex ordinals position)) := by
    intro position
    obtain ⟨value, stored, typed, dependencies, ambientEq⟩ :=
      source (MetaSelection.sourceIndex ordinals position) (List.get_mem _ _)
    obtain ⟨_, captured, _⟩ := selectEvidence?_complete _ uniqueNames value stored typed dependencies ambientEq
    exact ⟨captured⟩
  let family : SelectedFamily language rule spec entries ambient assignment ordinals :=
    fun position => Classical.choice (available position)
  exact ⟨family.submitted, family, selectedFamily?_replay family uniqueOrdinals⟩

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies


set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open AmbientCorrespondence

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- Source field support selects original metadata ordinals, retaining their
order and the original attached binding specification. -/
def captureOrdinalsFor (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (positions : List (Fin rule.typeContext.length)) :
    List (Fin (metaArities (language := language) rule spec).length) :=
  positions.map (metaIndex rule spec)


def captureOrdinals (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :
    List (Fin (metaArities (language := language) rule spec).length) :=
  captureOrdinalsFor language rule spec (usedRows rule)

theorem captureOrdinals_nodup (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :
    (captureOrdinals language rule spec).Nodup := by
  apply (usedRows_nodup rule).map
  intro first second same
  have values : (metaIndex (language := language) rule spec first).val = (metaIndex rule spec second).val :=
    congrArg Fin.val same
  exact Fin.ext values

theorem captureOrdinals_rows (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :
    MetaSelection.rows (captureOrdinals language rule spec) = metaArities (language := language) (captureView rule) spec := by
  simp only [MetaSelection.rows, captureOrdinals, captureOrdinalsFor, List.map_map, Function.comp_def]
  simp only [metaArities, captureView, captureViewFor, List.map_map, Function.comp_def, metaIndex,
    List.get_eq_getElem, List.getElem_map]

theorem mem_captureOrdinals {index : Fin (metaArities (language := language) rule spec).length} :
    index ∈ captureOrdinals language rule spec ↔ RuleReads rule (metaName rule spec index) := by
  constructor
  · intro present
    obtain ⟨original, used, same⟩ := List.mem_map.mp present
    cases same
    simpa only [metaName, metaIndex] using (mem_usedRows.mp used)
  · intro read
    let original : Fin rule.typeContext.length := ⟨index.val, by simpa only [metaArities_length] using index.isLt⟩
    exact List.mem_map.mpr ⟨original, by simpa only [metaName, original] using (mem_usedRows.mpr read), rfl⟩

/-- The internal compiler's position maps to the exact original source row.
This comparison is independent of whether two rows have equal types. -/
def captureSourceIndex (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Fin (metaArities (language := language) (captureView rule) spec).length) :
    Fin (metaArities (language := language) rule spec).length :=
  metaIndex rule spec (captureViewIndex rule ⟨index.val, by simpa only [metaArities_length] using index.isLt⟩)

theorem captureSourceIndex_name (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Fin (metaArities (language := language) (captureView rule) spec).length) :
    metaName (captureView rule) spec index = metaName rule spec (captureSourceIndex rule spec index) := by
  unfold metaName captureSourceIndex
  exact congrArg Prod.fst (captureView_source_row rule _)

theorem captureSourceIndex_row (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Fin (metaArities (language := language) (captureView rule) spec).length) :
    (metaArities (language := language) rule spec).get (captureSourceIndex rule spec index) =
      (metaArities (language := language) (captureView rule) spec).get index := by
  let position : Fin (captureView rule).typeContext.length :=
    ⟨index.val, by simpa only [metaArities_length] using index.isLt⟩
  have same : index = metaIndex (captureView rule) spec position := Fin.ext rfl
  rw [same]
  change (metaArities (language := language) rule spec).get
    (metaIndex rule spec (captureViewIndex rule position)) = _
  rw [metaArities_get, metaArities_get, captureView_source_row rule position]

/-- Actual retained bodies have only the selected interface, not the
original all-declaration interface. No value at an unused row is requested. -/
def captureBodies {ambient : List TypeExpr}
    (bodies : ContextualAssignment (signatureOf language)
      (MetaSelection.rows (captureOrdinals language rule spec)) ambient) :
    AmbientBodies language (captureView rule) spec ambient :=
  Eq.mp (congrArg (fun interface => ContextualAssignment (signatureOf language) interface ambient)
    (captureOrdinals_rows language rule spec)) bodies

/-- Reuse the original output traversal with its primitive selected-row
lookup exposed. Original full-rule admission is checked separately, rather
than incorrectly asserted for the projected internal metadata view. -/
def outputLocalAssembly (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) : Assembly (OutputSchema language rule spec) :=
  { groundOutputAssembly language rule spec site with
    free := fun locals path name sort => do
      let occurrence ← (List.finRange rule.typeContext.length).findSome?
        (outputOccurrenceCandidate? language rule spec locals site path name sort)
      pure (OutputSchema.ofOccurrence occurrence) }

/-- All constructor, binder, substitution and collection proofs are the
existing compiler's proofs. Only primitive occurrence selection is separated
from the original full-interface admission guard. -/
theorem outputLocalAssemblyInvariant (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) (ambient : List TypeExpr) :
    (outputLocalAssembly language rule spec site).Invariant
      (fun _ path _ _ compiled => OutputInstantiatesAt (ambient := ambient) compiled site path) where
  bound := (outputAssemblyInvariant language rule spec site ambient).bound
  constructor := (outputAssemblyInvariant language rule spec site ambient).constructor
  abstraction := (outputAssemblyInvariant language rule spec site ambient).abstraction
  multiAbstraction := (outputAssemblyInvariant language rule spec site ambient).multiAbstraction
  substitution := (outputAssemblyInvariant language rule spec site ambient).substitution
  vector := (outputAssemblyInvariant language rule spec site ambient).vector
  free locals path name sort compiled found := by
    cases selected : (List.finRange rule.typeContext.length).findSome?
        (outputOccurrenceCandidate? language rule spec locals site path name sort) with
    | none => simp only [outputLocalAssembly, selected, Option.bind_eq_bind, Option.bind_none] at found; cases found
    | some occurrence =>
      simp only [outputLocalAssembly, selected, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at found
      cases found
      exact output_free_instantiates occurrence

theorem outputLocalAssembly_walk_instantiates (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (site : RulePatternSite) (ambient : List TypeExpr)
    {fuel : Nat} {locals : List TypeExpr} {path : List Nat} {source : Pattern} {sort : TypeExpr}
    (compiled : OutputSchema language rule spec locals source sort)
    (found : (outputLocalAssembly language rule spec site).walk fuel locals path source sort = some compiled) :
    OutputInstantiatesAt (ambient := ambient) compiled site path :=
  Assembly.walk_invariant (outputLocalAssemblyInvariant language rule spec site ambient)
    fuel locals path source sort compiled found

/-- The original raw output is recovered from a supplied assignment on the
internal projected interface alone. This theorem requests no original total
assignment and does not change source authority. -/
theorem local_output_instantiates (site : RulePatternSite) (ambient : List TypeExpr)
    {fuel : Nat} {locals : List TypeExpr} {path : List Nat} {source : Pattern} {sort : TypeExpr}
    (compiled : OutputSchema language (captureView rule) spec locals source sort)
    (found : (outputLocalAssembly language (captureView rule) spec site).walk fuel locals path source sort = some compiled)
    (raw : Assignment) (bodies : AmbientBodies language (captureView rule) spec ambient)
    (captured : CapturesOutputs compiled.occurrences raw bodies) :
    instantiateAt? rule spec ambient.length site path locals.length raw source =
      some (erase (outputInstantiation bodies compiled.term)) := by
  rw [← instantiateAt?_captureView rule spec ambient.length site path locals.length raw source]
  exact outputLocalAssembly_walk_instantiates language (captureView rule) spec site ambient compiled found raw bodies captured

/-- The existing output compiler executes through the projected internal
interface and still earns the ORIGINAL raw source instantiation. Admission,
source IDs and typed-assignment authority are not projected. -/
theorem selected_output_instantiates (site : RulePatternSite) (ambient : List TypeExpr)
    {fuel : Nat} {locals : List TypeExpr} {path : List Nat} {source : Pattern} {sort : TypeExpr}
    (compiled : OutputSchema language (captureView rule) spec locals source sort)
    (found : (outputLocalAssembly language (captureView rule) spec site).walk fuel locals path source sort = some compiled)
    (raw : Assignment)
    (bodies : ContextualAssignment (signatureOf language)
      (MetaSelection.rows (captureOrdinals language rule spec)) ambient)
    (captured : CapturesOutputs compiled.occurrences raw (captureBodies bodies)) :
    instantiateAt? rule spec ambient.length site path locals.length raw source =
      some (erase (outputInstantiation (captureBodies bodies) compiled.term)) := by
  exact local_output_instantiates site ambient compiled found raw (captureBodies bodies) captured

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration


set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.CaptureSupportControls
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open SchemaElaboration NamedBodies

private inductive PairOp : Bool → Type where
  | pair : PairOp false
  deriving DecidableEq
private def emptySortSignature : Signature where
  Srt := Bool
  Op := PairOp
  arity := fun operator => match operator with | .pair => [([], false), ([], false)]
private instance : DecidableEq emptySortSignature.Srt := inferInstanceAs (DecidableEq Bool)
private def pairOpEq : {sort : Bool} → DecidableEq (PairOp sort)
  | _, .pair, .pair => isTrue rfl
private def metaOpEq (metas : List (MetaArity emptySortSignature)) (sort : Bool) :
    DecidableEq (MetaOp (S := emptySortSignature) metas sort) := fun first second =>
  if same : MetaSelection.ordinal first = MetaSelection.ordinal second then
    isTrue (MetaSelection.ordinal_injective same)
  else isFalse (fun equal => same (congrArg MetaSelection.ordinal equal))
private instance (metas : List (MetaArity emptySortSignature)) :
    DecidableEq ((withMetas emptySortSignature metas).Srt) := inferInstanceAs (DecidableEq Bool)
private instance (metas : List (MetaArity emptySortSignature)) :
    (sort : (withMetas emptySortSignature metas).Srt) → DecidableEq ((withMetas emptySortSignature metas).Op sort) :=
  fun sort => @instDecidableEqSum (PairOp sort) (MetaOp (S := emptySortSignature) metas sort)
    pairOpEq (metaOpEq metas sort)

private def interface : List (MetaArity emptySortSignature) := [([], true), ([false], false)]
private def onlyUsed : List (Fin interface.length) := [⟨1, by decide⟩]
private def usedSchema : Term (withMetas emptySortSignature interface) [false] false :=
  .op (.inr (.mk ⟨1, by decide⟩)) (.cons (.var .zero) .nil)
private def sharedSchema : Term (withMetas emptySortSignature interface) [false] false :=
  .op (.inl .pair) (.cons usedSchema (.cons usedSchema .nil))
private def unusedSchema : Term (withMetas emptySortSignature interface) [] true :=
  .op (.inr (.mk ⟨0, by decide⟩)) .nil
private def lowerUsed : Term (withMetas emptySortSignature (MetaSelection.rows onlyUsed)) [false] false :=
  .op (.inr (.mk ⟨0, by decide⟩)) (.cons (.var .zero) .nil)

private def fixtureTermEq (metas : List (MetaArity emptySortSignature)) :
    {context : List Bool} → {sort : Bool} → DecidableEq (Term (withMetas emptySortSignature metas) context sort) :=
  @decEqTerm (withMetas emptySortSignature metas)
    (fun sort => @instDecidableEqSum (PairOp sort) (MetaOp (S := emptySortSignature) metas sort)
      pairOpEq (metaOpEq metas sort))
private instance : DecidableEq (Term (withMetas emptySortSignature interface) [false] false) :=
  fixtureTermEq interface
private instance : DecidableEq (Term (withMetas emptySortSignature (MetaSelection.rows onlyUsed)) [false] false) :=
  fixtureTermEq (MetaSelection.rows onlyUsed)

/-- This fixture genuinely has no object term at the unused result sort in
an empty context; selection never asks for one. -/
theorem unused_sort_has_no_body : ¬ Nonempty (Term emptySortSignature [] true) := by
  rintro ⟨term⟩
  cases term with
  | var position => nomatch position
  | op operator arguments => nomatch operator

example : MetaSelection.lower? onlyUsed usedSchema = some lowerUsed := by decide +kernel
example : MetaSelection.embed onlyUsed lowerUsed = usedSchema := by decide +kernel
example : Function.Injective (MetaSelection.embed onlyUsed (context := [false]) (sort := false)) :=
  MetaSelection.embed_injective onlyUsed (by decide)

private def a : TypeExpr := .base "A"
private def e : TypeExpr := .base "Empty"
private def language : LanguageDef where
  name := "selected-original-captures"
  types := [{ name := "A" }, { name := "Empty" }]
  terms := []
  equations := []
  rewrites := []
private def rule : RewriteRule where
  name := "source-row-one"
  typeContext := [("unused", e), ("P", a)]
  premises := []
  left := .fvar "P"
  right := .fvar "P"
private def spec : RuleBindingSpec where
  dependencies := [("unused", []), ("P", [])]
private def entries : List (String × TypeExpr) := [("z", a)]
private def original : ContextualValue := ⟨[], 0, .fvar "z"⟩
private def assignment : Assignment := [("P", original)]
private def originalIndex : Fin (metaArities (language := language) rule spec).length := ⟨1, by decide⟩
private def ordinals : List (Fin (metaArities (language := language) rule spec).length) := [originalIndex]
private theorem originalOrdinals : captureOrdinals language rule spec = ordinals := by cbv
private def term : Term (signatureOf language) [a] a := .var .zero
private def evidence := (Wire.termCodec language [a] a).put term
private def submitted : List (Nat × WireCodec.Data) := [(1, evidence)]
private def captured : SelectedFamily language rule spec entries [] assignment ordinals :=
  (selectedFamily? language rule spec entries [] assignment submitted ordinals).get (by cbv)
private def noArguments : DependencyArguments (language := language)
    ((metaArities rule spec).get (MetaSelection.sourceIndex ordinals ⟨0, by cbv⟩)).1
    ([] ++ ([] ++ NamedFreeContext.contextSorts entries)) := by
  change DependencyArguments [] [a]
  exact .nil

example : (lookup assignment "P").bind (fun value => instantiateValue? value 0 0 []) =
    some ((captured ⟨0, by cbv⟩).parsed.toCaptured.occurrenceReadback noArguments) := by
  simpa [metaName, MetaSelection.sourceIndex, ordinals, originalIndex, rule,
    noArguments, id, openedArguments, eraseArguments] using
    captured.observes (locals := []) ⟨0, by decide⟩ noArguments

example : selectedFamily? language rule spec entries [] assignment captured.submitted ordinals = some captured :=
  selectedFamily?_replay captured (by decide)

private def fullRule : RewriteRule where
  name := "all-operational-fields"
  typeContext := [("unused", e), ("P", a), ("guard", a), ("atom", a),
    ("items", .collection .vec a), ("local", a), ("child", a), ("tail", .collection .vec a)]
  left := .fvar "P"
  right := .fvar "P"
  premises := [
    .relationQuery "allowed" [.fvar "guard", .fvar "P"],
    .freshness ⟨"atom", .fvar "P"⟩,
    .scopedStep ⟨[a], a, .fvar "child", .fvar "P"⟩,
    .forAll "items" "local" (.relationQuery "inside" [.fvar "local", .fvar "P"]),
    .congruence (.collection .vec [.fvar "P"] (some "tail")) (.fvar "P")]
private def shadowed : Premise :=
  .forAll "items" "local" (.forAll "local" "inner"
    (.relationQuery "inside" [.fvar "local", .fvar "inner", .fvar "guard"]))
private def sourceView : RewriteRule := captureView fullRule

example : RuleReads fullRule "atom" := .premise (.freshness ⟨"atom", .fvar "P"⟩) (by decide) (.freshnessName [] _ (by simp))
example : RuleReads fullRule "items" := .premise
  (.forAll "items" "local" (.relationQuery "inside" [.fvar "local", .fvar "P"]))
  (by decide) (.quantifiedCollection (by simp))
example : RuleReads fullRule "child" :=
  sitePattern?_reads fullRule (.premise 2 0 0) (.fvar "child") [] (by decide) (by decide)
    "child" (by simp [Pattern.freeFvarNames]) (by simp)

private def typedRule : RewriteRule := { rule with typeContext := [("unused", a), ("P", a)] }
private def typedAssignment : Assignment := [("unused", original), ("P", original)]
private def typedSpec : RuleBindingSpec := { spec with dependencies := [("unused", []), ("P", [])] }
private def changedName : Assignment := [("P", ⟨[], 0, .fvar "w"⟩)]
private def wrongAmbient : Assignment := [("P", ⟨[], 1, .fvar "z"⟩)]
private def wrongDependency : Assignment := [("P", ⟨[a], 0, .fvar "z"⟩)]
private def invalidScope : Assignment := [("P", ⟨[], 0, .bvar 0⟩)]

private def rawRule : RewriteRule where
  name := "rest-source-operation"
  typeContext := [("unused", e), ("tail", .collection .vec a)]
  premises := []
  left := .collection .vec [] (some "tail")
  right := .collection .vec [] (some "tail")
private def rawSpec : RuleBindingSpec where
  dependencies := [("unused", []), ("tail", [])]
private def rawAssignment : Assignment := [("tail", ⟨[], 0, .collection .vec [.fvar "z", .fvar "z"] none⟩)]

/-- Exact source operations agree even for a raw rest shape that the compact
output parser currently refuses. Source evidence retains that distinction. -/
example : instantiateAt? (captureView rawRule) rawSpec 0 .right [] 0 rawAssignment rawRule.right =
    instantiateAt? rawRule rawSpec 0 .right [] 0 rawAssignment rawRule.right :=
  instantiateAt?_captureView rawRule rawSpec 0 .right [] 0 rawAssignment rawRule.right

/-- The existing parser and proof are reused at the internal selected view. -/
private def compiled : OutputSchema language (captureView rule) spec [] rule.right a :=
  ((outputLocalAssembly language (captureView rule) spec .right).walk (sourceHeight rule.right) [] [] rule.right a).get
    (by
      have view : captureView rule = { rule with typeContext := [("P", a)] } := by cbv
      rw [view]
      cbv)
private def selectedBodies : ContextualAssignment (signatureOf language)
    (MetaSelection.rows ordinals) [a] := captured.bodies

private def admittedRule : RewriteRule := { rule with bindings := some spec }
private def originalView : AmbientCorrespondence.AmbientBodies language (captureView rule) spec [a] := by
  change ContextualAssignment (signatureOf language) (metaArities (captureView rule) spec) [a]
  have rows : metaArities (language := language) (captureView rule) spec = [([], a)] := by cbv
  rw [rows]
  exact fun position => Fin.cases (.var .zero) (fun impossible => Fin.elim0 impossible) position
private def closedAssignment : Assignment := [("P", ⟨[], 1, .bvar 0⟩)]

private def checks : List (String × Bool) := [
  ("selected-primitive-original-index", (MetaSelection.sourceIndex onlyUsed ⟨0, by decide⟩).val == 1),
  ("selected-head-lowers", (MetaSelection.lower? onlyUsed usedSchema).isSome),
  ("repeated-occurrences-lower", (MetaSelection.lower? onlyUsed sharedSchema).isSome),
  ("omitted-actually-used-head-refuses", (MetaSelection.lower? ([] : List (Fin interface.length)) usedSchema).isNone),
  ("unused-sort-reference-refuses", (MetaSelection.lower? onlyUsed unusedSchema).isNone),
  ("source-image-readback", MetaSelection.embed onlyUsed lowerUsed == usedSchema),
  ("all-rule-fields-keep-source-ordinals", (usedRows fullRule).map Fin.val == [1, 2, 3, 4, 6, 7]),
  ("outer-support-excludes-quantified-parameter", !(ruleReadNames fullRule).contains "local"),
  ("site-local-parameter-is-supplied-locally", (usedRowsAt fullRule ["local"]).map Fin.val == [1, 2, 3, 4, 5, 6, 7]),
  ("freshness-name-read-included", (ruleReadNames fullRule).contains "atom"),
  ("quantifier-collection-read-included", (ruleReadNames fullRule).contains "items"),
  ("rest-capture-read-included", (ruleReadNames fullRule).contains "tail"),
  ("scoped-child-read-included", (ruleReadNames fullRule).contains "child"),
  ("query-output-schema-read-included", (ruleReadNames fullRule).contains "guard"),
  ("unused-declaration-not-parameterized", !(ruleReadNames fullRule).contains "unused"),
  ("nested-lexical-shadows", premiseReadNames [] shadowed == ["items", "guard"]),
  ("quantified-site-local-context", siteParameters? fullRule (.premise 3 1 0) == some ["local"]),
  ("excess-quantifier-depth-refuses", (siteParameters? fullRule (.premise 3 2 0)).isNone),
  ("exact-source-field-read", sitePattern? fullRule (.premise 2 0 0) == some (.fvar "child")),
  ("selected-original-capture-evidence", (selectedFamily? language rule spec entries [] assignment submitted ordinals).isSome),
  ("unused-empty-sort-needs-no-body", ordinals.map Fin.val == [1]),
  ("original-ordinal-is-not-new-local-index", (selectedFamily? language rule spec entries [] assignment [(0, evidence)] ordinals).isNone),
  ("missing-used-evidence-refuses", (selectedFamily? language rule spec entries [] assignment [] ordinals).isNone),
  ("changed-original-body-refuses", (selectedFamily? language rule spec entries [] changedName submitted ordinals).isNone),
  ("wrong-original-ambient-refuses", (selectedFamily? language rule spec entries [] wrongAmbient submitted ordinals).isNone),
  ("wrong-original-dependencies-refuse", (selectedFamily? language rule spec entries [] wrongDependency submitted ordinals).isNone),
  ("original-out-of-scope-body-refuses", (selectedFamily? language rule spec entries [] invalidScope submitted ordinals).isNone),
  ("named-free-readback-is-source-value", (captured ⟨0, by cbv⟩).parsed.toCaptured.readValue == original),
  ("actual-open-original-occurrence", instantiateValue? original 0 0 [] == some (.fvar "z")),
  ("full-original-typed-assignment-accepted", Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.checkAssignment language
    (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList entries) [] typedRule typedSpec typedAssignment),
  ("projected-typed-assignment-is-different-authority", !(Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.checkAssignment language
    (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList entries) [] (captureView typedRule) typedSpec typedAssignment)),
  ("raw-rest-original-computation", instantiateAt? rawRule rawSpec 0 .right [] 0 rawAssignment rawRule.right ==
    some (.collection .vec [.fvar "z", .fvar "z"] none)),
  ("raw-rest-view-computation", instantiateAt? (captureView rawRule) rawSpec 0 .right [] 0 rawAssignment rawRule.right ==
    instantiateAt? rawRule rawSpec 0 .right [] 0 rawAssignment rawRule.right),
  ("raw-rest-compact-parser-does-not-invent-support", ((outputAssembly language (captureView rawRule) rawSpec .right).walk
    (sourceHeight rawRule.right) [] [] rawRule.right (.collection .vec a)).isNone),
  ("original-source-admission-accepted", admittedFor admittedRule spec),
  ("projected-source-admission-not-assumed", !(admittedFor (captureView admittedRule) spec)),
  ("original-guarded-parser-accepts", ((outputAssembly language admittedRule spec .right).walk
    (sourceHeight admittedRule.right) [] [] admittedRule.right a).isSome),
  ("projected-guarded-parser-refuses", ((outputAssembly language (captureView admittedRule) spec .right).walk
    (sourceHeight admittedRule.right) [] [] admittedRule.right a).isNone),
  ("selected-interface-actual-original-output", instantiateAt? rule spec 1 .right [] 0 closedAssignment rule.right ==
    some (erase (outputInstantiation originalView compiled.term))),
  ("selected-parser-original-source-name", readback compiled.representation == rule.right),
  ("selected-body-restores-original-source-value", captured.submitted == submitted)]

#guard checks.all Prod.snd

def run : IO Unit := do
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  IO.println s!"{checks.length} source capture-support controls"

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.CaptureSupportControls


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

theorem openNames_fvar (depth : Nat) (names : List String) (name : String) :
    openNames depth names (.fvar name) = .fvar name := by
  induction names generalizing depth with
  | nil => rfl
  | cons head rest ih => simp only [openNames, ih, Substitution.openBVar]

theorem openNames_apply (depth : Nat) (names : List String) (head : String)
    (arguments : List Pattern) :
    openNames depth names (.apply head arguments) =
      .apply head (arguments.map (openNames depth names)) := by
  induction names generalizing depth arguments with
  | nil => exact congrArg (Pattern.apply head) (List.map_id arguments).symm
  | cons name rest ih =>
      simp only [openNames, ih, Substitution.openBVar, List.map_map, Function.comp_def]

theorem openNames_lambda (depth : Nat) (names : List String)
    (binder : Option String) (body : Pattern) :
    openNames depth names (.lambda binder body) =
      .lambda binder (openNames (depth + 1) names body) := by
  induction names generalizing depth body with
  | nil => rfl
  | cons name rest ih => simp only [openNames, ih, Substitution.openBVar]

theorem openNames_multiLambda (depth : Nat) (names : List String)
    (arity : Nat) (binders : List String) (body : Pattern) :
    openNames depth names (.multiLambda arity binders body) =
      .multiLambda arity binders (openNames (depth + arity) names body) := by
  induction names generalizing depth body with
  | nil => rfl
  | cons name rest ih =>
      simp only [openNames, ih, Substitution.openBVar, Nat.add_right_comm depth 1 arity]

theorem openNames_subst_syntax (depth : Nat) (names : List String)
    (body replacement : Pattern) :
    openNames depth names (.subst body replacement) =
      .subst (openNames (depth + 1) names body) (openNames depth names replacement) := by
  induction names generalizing depth body replacement with
  | nil => rfl
  | cons name rest ih => simp only [openNames, ih, Substitution.openBVar]

theorem openNames_collection (depth : Nat) (names : List String)
    (kind : CollType) (elements : List Pattern) (rest : Option String) :
    openNames depth names (.collection kind elements rest) =
      .collection kind (elements.map (openNames depth names)) rest := by
  induction names generalizing depth elements with
  | nil =>
      exact congrArg (fun values => Pattern.collection kind values rest) (List.map_id elements).symm
  | cons name tail ih =>
      simp only [openNames, ih, Substitution.openBVar, List.map_map, Function.comp_def]

theorem openNames_eq_self (depth : Nat) (names : List String) (pattern : Pattern)
    (wellScoped : pattern.isWellScopedAt depth = true) :
    openNames depth names pattern = pattern := by
  have enlarged : pattern.isWellScopedAt (depth + names.length) = true := by
    rw [Substitution.isWellScopedAt_eq_lc_at] at wellScoped ⊢
    exact Substitution.lc_at_mono wellScoped (Nat.le_add_right _ _)
  rw [openNames_as_substitute depth names pattern enlarged]
  calc
    substitute (openingAssignment depth names) pattern = substitute Pattern.bvar pattern :=
      substitute_eq_of_agree_on_scope _ _ pattern depth wellScoped
        (fun index inside => openingAssignment_before depth names index inside)
    _ = pattern := substitute_id pattern

theorem openNames_instantiateBVar (depth : Nat) (names : List String)
    (replacement body : Pattern)
    (bodyScoped : body.isWellScopedAt ((depth + 1) + names.length) = true)
    (replacementScoped : replacement.isWellScopedAt (depth + names.length) = true) :
    openNames depth names (Substitution.instantiateBVar replacement body) =
      Substitution.instantiateBVar (openNames depth names replacement)
        (openNames (depth + 1) names body) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar]
  apply openNames_substitute (depth + 1) depth names
    (single replacement) (single (openNames depth names replacement)) body bodyScoped
  · intro index inside
    cases index with
    | zero => exact replacementScoped
    | succ index =>
        simp only [single, Pattern.isWellScopedAt, decide_eq_true_eq]
        omega
  · intro index inside
    cases index with
    | zero => rfl
    | succ index =>
        simpa only [single] using openNames_before depth names index (by omega)
  · intro position
    have shifted : (depth + 1) + position.val = Nat.succ (depth + position.val) := by omega
    rw [shifted, single]

example : openNames 0 ["x"] (.lambda (some "local") (.bvar 1)) =
    .lambda (some "local") (.fvar "x") := by simp [openNames, Substitution.openBVar]

example : openNames 0 ["x"] (.lambda (some "local") (.bvar 0)) ≠
    .lambda (some "local") (.fvar "x") := by simp [openNames, Substitution.openBVar]

example : openNames 1 ["a"] (Substitution.instantiateBVar
    (.apply "r" [.bvar 0, .bvar 1])
    (.lambda (some "x") (.apply "p" [.bvar 0, .bvar 1, .bvar 2, .bvar 3]))) =
      .lambda (some "x") (.apply "p"
        [.bvar 0, .apply "r" [.bvar 1, .fvar "a"], .bvar 1, .fvar "a"]) := by cbv

example : Substitution.instantiateBVar
    (openNames 1 ["a"] (.apply "r" [.bvar 0, .bvar 1]))
    (openNames 1 ["a"]
      (.lambda (some "x") (.apply "p" [.bvar 0, .bvar 1, .bvar 2, .bvar 3]))) ≠
      .lambda (some "x") (.apply "p"
        [.bvar 0, .apply "r" [.bvar 1, .fvar "a"], .bvar 1, .fvar "a"]) := by
  cbv
  simp


end Mettapedia.GSLT.LanguageDef.NamedFreeContext


set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Syntax
open ContextSubstitution

/-- The actual occurrence vector is a scoped raw substitution after its
original arity and argument checks, independently of a typed body parser. -/
theorem occurrenceAssignment_scoped (dependencies ambient depth : Nat)
    (arguments : List Pattern) (count : arguments.length = dependencies)
    (argumentScopes : arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true) :
    WellScopedAssignment (dependencies + ambient) (depth + ambient)
      (occurrenceAssignment dependencies depth arguments) := by
  intro index inside
  by_cases dependency : index < dependencies
  · have within : index < arguments.length := by omega
    have present : arguments[index]? = some (arguments.get ⟨index, within⟩) :=
      List.getElem?_eq_getElem within
    simp only [occurrenceAssignment, if_pos dependency, List.getD_eq_getElem?_getD,
      present, Option.getD_some]
    exact List.all_eq_true.mp argumentScopes _ (List.get_mem _ _)
  · simp only [occurrenceAssignment, if_neg dependency, Pattern.isWellScopedAt]
    exact decide_eq_true (by omega)

/-- The original raw checks suffice to compute a contextual value. -/
theorem instantiateValue?_of_scoped (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (ambientEq : value.ambient = ambient)
    (count : arguments.length = value.dependencies.length)
    (bodyScoped : value.body.isWellScopedAt (value.dependencies.length + ambient) = true)
    (argumentsScoped : arguments.all
      (fun argument => argument.isWellScopedAt (depth + ambient)) = true) :
    instantiateValue? value ambient depth arguments = some
      (substitute (occurrenceAssignment value.dependencies.length depth arguments) value.body) := by
  have resultScoped := substitute_wellScoped
    (occurrenceAssignment_scoped value.dependencies.length ambient depth arguments count argumentsScoped)
    bodyScoped
  simp [instantiateValue?, ambientEq, count, bodyScoped, argumentsScoped, resultScoped]

theorem instantiateValue?_readout (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern)
    (success : instantiateValue? value ambient depth arguments = some result) :
    value.ambient = ambient ∧ arguments.length = value.dependencies.length ∧
      value.body.isWellScopedAt (value.dependencies.length + ambient) = true ∧
      arguments.all (fun argument => argument.isWellScopedAt (depth + ambient)) = true ∧
      result = substitute (occurrenceAssignment value.dependencies.length depth arguments) value.body := by
  unfold instantiateValue? at success
  split at success <;> try cases success
  split at success <;> try cases success
  split at success <;> try cases success
  split at success <;> try cases success
  dsimp only at success
  split at success <;> cases success
  simp_all

/-- Successful argument lookup retains the original admitted local scope.
The inferred empty vector and an explicitly authored vector are both covered. -/
theorem arguments?_scoped (rule : RewriteRule) (spec : RuleBindingSpec)
    (admitted : admittedFor rule spec = true) (name : String) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (depthFound : occurrenceDepthAtSite? rule site path = some depth)
    (arguments : List Pattern) (found : arguments? rule spec name site path = some arguments) :
    arguments.all (fun argument => argument.isWellScopedAt depth) = true := by
  cases rows : spec.occurrences.filter
      (fun row => row.name == name && row.site == site && row.path == path) with
  | nil =>
    simp only [arguments?, rows, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
    rcases found with ⟨dependencies, _, _, _, found⟩
    split at found <;> cases found
    rfl
  | cons row tail =>
    cases tail with
    | cons next rest =>
      simp only [arguments?, rows, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      rcases found with ⟨_, _, _, _, impossible⟩
      cases impossible
    | nil =>
      have member : row ∈ spec.occurrences := (List.mem_filter.mp (by rw [rows]; simp)).1
      have selected : (row.name = name ∧ row.site = site) ∧ row.path = path := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using
          (List.mem_filter.mp (show row ∈ spec.occurrences.filter
            (fun row => row.name == name && row.site == site && row.path == path) by rw [rows]; simp)).2
      simp only [admittedFor, Bool.and_eq_true] at admitted
      have rowAccepted := List.all_eq_true.mp admitted.2 row member
      have rowDepth : occurrenceDepthAtSite? rule row.site row.path = some depth := by
        simpa only [selected.1.2, selected.2] using depthFound
      simp only [arguments?, rows, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      rcases found with ⟨dependencies, _, _, _, found⟩
      split at found <;> try cases found
      cases rowDependencies : dependencies? spec row.name with
      | none => simp [rowDepth, rowDependencies] at rowAccepted
      | some actualDependencies =>
        simp only [rowDepth, rowDependencies, Bool.and_eq_true] at rowAccepted
        apply List.all_eq_true.mpr
        intro argument occurs
        exact Substitution.isWellScopedAt_of_isGroundAt
          (List.all_eq_true.mp rowAccepted.2.2 argument occurs)

end Mettapedia.OSLF.MeTTaIL.RuleBinding

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-- A raw context action closes precisely the outer name suffix. Invalid
original values retain refusal through an incompatible ambient count. This
auxiliary map does not supply intrinsic terms for unused metadata rows. -/
def closeValue (ambient : Nat) (names : List String) (value : ContextualValue) :
    ContextualValue :=
  if value.ambient = ambient ∧
      value.body.isWellScopedAt (value.dependencies.length + ambient) = true then
    { dependencies := value.dependencies, ambient := ambient + names.length,
      body := NamedFreeContext.closeNames (value.dependencies.length + ambient) names value.body }
  else { value with ambient := ambient + names.length + 1 }

theorem closeValue_dependencies (ambient : Nat) (names : List String) (value : ContextualValue) :
    (closeValue ambient names value).dependencies = value.dependencies := by
  unfold closeValue
  split <;> rfl

/-- Source lookup keeps its original first occurrence, including repeated
names; closing cannot expose a later duplicate. -/
def closeAssignment (ambient : Nat) (names : List String) (assignment : ScopedRuleMatching.Assignment) : ScopedRuleMatching.Assignment :=
  assignment.map (fun entry => (entry.1, closeValue ambient names entry.2))

theorem lookup_closeAssignment (ambient : Nat) (names : List String)
    (assignment : ScopedRuleMatching.Assignment) (name : String) :
    lookup (closeAssignment ambient names assignment) name =
      (lookup assignment name).map (closeValue ambient names) := by
  simp [lookup, closeAssignment, List.find?_map, Option.map_map, Function.comp_def]

/-- Original dependency arguments live before the appended name suffix. -/
theorem occurrenceAssignment_open_fixed (dependencies ambient depth : Nat)
    (names : List String) (arguments : List Pattern)
    (count : arguments.length = dependencies)
    (argumentScopes : arguments.all
      (fun argument => argument.isWellScopedAt (depth + ambient)) = true)
    (index : Nat) (inside : index < dependencies + ambient) :
    NamedFreeContext.openNames (depth + ambient) names
        (occurrenceAssignment dependencies depth arguments index) =
      occurrenceAssignment dependencies depth arguments index := by
  by_cases dependency : index < dependencies
  · have within : index < arguments.length := by omega
    have present : arguments[index]? = some (arguments.get ⟨index, within⟩) :=
      List.getElem?_eq_getElem within
    simp only [occurrenceAssignment, if_pos dependency, List.getD_eq_getElem?_getD,
      present, Option.getD_some]
    exact NamedFreeContext.openNames_eq_self _ _ _
      (List.all_eq_true.mp argumentScopes _ (List.get_mem _ _))
  · simp only [occurrenceAssignment, if_neg dependency]
    exact NamedFreeContext.openNames_before _ _ _ (by omega)

/-- A successful closed occurrence reconstructs exactly the original raw
occurrence, including its ambient count. No invalid original value is admitted. -/
theorem closeValue_success (ambient depth : Nat) (names : List String)
    (value : ContextualValue) (arguments : List Pattern)
    (argumentScopes : arguments.all
      (fun argument => argument.isWellScopedAt (depth + ambient)) = true)
    (result : Pattern)
    (success : instantiateValue? (closeValue ambient names value) (ambient + names.length)
      depth arguments = some result) :
    instantiateValue? value ambient depth arguments =
      some (NamedFreeContext.openNames (depth + ambient) names result) := by
  unfold closeValue at success
  split at success
  · rename_i valid
    have facts := instantiateValue?_readout _ _ _ _ _ success
    have count : arguments.length = value.dependencies.length := facts.2.1
    have actualScopes := occurrenceAssignment_scoped value.dependencies.length
      (ambient + names.length) depth arguments count facts.2.2.2.1
    have readback := NamedFreeContext.closeNames_substitution_readback
      (value.dependencies.length + ambient) (depth + ambient) names
      (occurrenceAssignment value.dependencies.length depth arguments)
      (occurrenceAssignment value.dependencies.length depth arguments) value.body valid.2
      (by simpa only [Nat.add_assoc] using actualScopes)
      (occurrenceAssignment_open_fixed value.dependencies.length ambient depth names arguments
        count argumentScopes)
      (by
        intro position
        have later : ¬ value.dependencies.length + ambient + position.val <
            value.dependencies.length := by omega
        simp only [occurrenceAssignment, if_neg later]
        congr 1
        omega)
    have original := instantiateValue?_of_scoped value ambient depth arguments valid.1 count
      valid.2 argumentScopes
    have resultEq : result = substitute (occurrenceAssignment value.dependencies.length depth arguments)
        (NamedFreeContext.closeNames (value.dependencies.length + ambient) names value.body) :=
      facts.2.2.2.2
    rw [resultEq, readback]
    exact original
  · have impossible := (instantiateValue?_readout _ _ _ _ _ success).1
    dsimp only at impossible
    omega

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

private theorem scopedList_append (depth : Nat) (first second : List Pattern)
    (firstScoped : Pattern.isWellScopedListAt depth first = true)
    (secondScoped : Pattern.isWellScopedListAt depth second = true) :
    Pattern.isWellScopedListAt depth (first ++ second) = true := by
  induction first with
  | nil => exact secondScoped
  | cons head tail ih =>
    simp only [List.cons_append, Pattern.isWellScopedListAt, Bool.and_eq_true] at firstScoped ⊢
    exact ⟨firstScoped.1, ih firstScoped.2⟩

mutual
/-- Running the original interpreter in the closed finite name context,
then restoring that context, gives its original source execution. The same
induction proves scope and retains every original occurrence address. -/
theorem instantiate_closed_readback (rule : RewriteRule) (spec : RuleBindingSpec)
    (admitted : admittedFor rule spec = true) (ambient : Nat) (names : List String)
    (raw : ScopedRuleMatching.Assignment) (site : RulePatternSite) :
    ∀ (source : Pattern) (path : List Nat) (depth : Nat),
      DepthCoherent rule site path depth source → source.isWellScopedAt depth = true →
      ∀ result,
        instantiateAt? rule spec (ambient + names.length) site path depth
          (closeAssignment ambient names raw) source = some result →
        result.isWellScopedAt (depth + (ambient + names.length)) = true ∧
          instantiateAt? rule spec ambient site path depth raw source =
            some (NamedFreeContext.openNames (depth + ambient) names result)
  | .bvar index, path, depth, _, scopeProof, result, success => by
    simp only [instantiateAt?, instantiateWith?, Option.some.injEq] at success
    cases success
    have inside : index < depth := of_decide_eq_true scopeProof
    constructor
    · exact decide_eq_true (by omega)
    · rw [NamedFreeContext.openNames_before _ _ _ (by omega)]
      simp only [instantiateAt?, instantiateWith?]
  | .fvar name, path, depth, coherent, _, result, success => by
    cases stored : lookup raw name with
    | none =>
      simp only [instantiateAt?, instantiateWith?, lookup_closeAssignment, stored,
        Option.map_none, Option.bind_eq_bind, Option.bind_none] at success
      cases success
    | some value =>
      simp only [instantiateAt?, instantiateWith?, lookup_closeAssignment, stored,
        Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at success
      rcases success with ⟨arguments, argumentsFound, success⟩
      have localScopes := arguments?_scoped rule spec admitted name site path depth
        coherent.fvar arguments argumentsFound
      have argumentScopes : arguments.all
          (fun argument => argument.isWellScopedAt (depth + ambient)) = true := by
        apply List.all_eq_true.mpr
        intro argument member
        exact ScopedPattern.isWellScopedAt_mono (List.all_eq_true.mp localScopes argument member)
          (Nat.le_add_right _ _)
      refine ⟨instantiateValue?_scoped _ _ _ _ _ success, ?_⟩
      have restored := closeValue_success ambient depth names value arguments argumentScopes result success
      simp only [instantiateAt?, instantiateWith?, stored, argumentsFound,
        Option.bind_eq_bind, Option.bind_some, restored]
  | .apply head arguments, path, depth, coherent, scopeProof, result, success => by
    simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at success
    rcases success with ⟨results, childRun, rfl⟩
    have children := instantiateArgs_closed_readback rule spec admitted ambient names raw site
      arguments path depth 0 coherent.constructorArguments scopeProof results childRun
    simp only [instantiateArgsAt?] at children
    refine ⟨children.1, ?_⟩
    rw [NamedFreeContext.openNames_apply]
    simp only [instantiateAt?, instantiateWith?, children.2, Option.bind_eq_bind, Option.bind_some]
  | .lambda display body, path, depth, coherent, scopeProof, result, success => by
    simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at success
    rcases success with ⟨bodyResult, bodyRun, rfl⟩
    have child := instantiate_closed_readback rule spec admitted ambient names raw site
      body (path ++ [0]) (depth + 1) coherent.lambda scopeProof bodyResult bodyRun
    simp only [instantiateAt?] at child
    constructor
    · simpa only [Pattern.isWellScopedAt, Nat.add_right_comm depth 1] using child.1
    · rw [NamedFreeContext.openNames_lambda]
      rw [show depth + ambient + 1 = depth + 1 + ambient by omega]
      simp only [instantiateAt?, instantiateWith?, child.2, Option.bind_eq_bind, Option.bind_some]
  | .multiLambda count display body, path, depth, coherent, scopeProof, result, success => by
    simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at success
    rcases success with ⟨bodyResult, bodyRun, rfl⟩
    have child := instantiate_closed_readback rule spec admitted ambient names raw site
      body (path ++ [0]) (depth + count) coherent.multiLambda scopeProof bodyResult bodyRun
    simp only [instantiateAt?] at child
    constructor
    · simpa only [Pattern.isWellScopedAt, Nat.add_right_comm depth count] using child.1
    · rw [NamedFreeContext.openNames_multiLambda]
      rw [show depth + ambient + count = depth + count + ambient by omega]
      simp only [instantiateAt?, instantiateWith?, child.2, Option.bind_eq_bind, Option.bind_some]
  | .subst body replacement, path, depth, coherent, scopeProof, result, success => by
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at scopeProof
    simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at success
    rcases success with ⟨bodyResult, bodyRun, replacementResult, replacementRun, rfl⟩
    have actualBody := instantiate_closed_readback rule spec admitted ambient names raw site
      body (path ++ [0]) (depth + 1) coherent.substitutionBody scopeProof.1 bodyResult bodyRun
    have actualReplacement := instantiate_closed_readback rule spec admitted ambient names raw site
      replacement (path ++ [1]) depth coherent.substitutionReplacement scopeProof.2
      replacementResult replacementRun
    simp only [instantiateAt?] at actualBody actualReplacement
    constructor
    · simpa only [Substitution.instantiateBVar, Nat.add_zero] using
        (Substitution.instantiateBVarAt_isWellScopedAt
          (ambient := depth + (ambient + names.length)) (depth := 0)
          (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using actualBody.1)
          actualReplacement.1)
    · rw [NamedFreeContext.openNames_instantiateBVar _ _ _ _
        (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using actualBody.1)
        (by simpa only [Nat.add_assoc] using actualReplacement.1)]
      rw [show depth + ambient + 1 = depth + 1 + ambient by omega]
      simp only [instantiateAt?, instantiateWith?, actualBody.2, actualReplacement.2,
        Option.bind_eq_bind, Option.bind_some]
  | .collection kind elements rest, path, depth, coherent, scopeProof, result, success => by
    simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at success
    rcases success with ⟨explicit, explicitRun, success⟩
    have children := instantiateArgs_closed_readback rule spec admitted ambient names raw site
      elements path depth 0 coherent.collectionArguments scopeProof explicit explicitRun
    simp only [instantiateArgsAt?] at children
    cases rest with
    | none =>
      simp only [Option.some.injEq] at success
      cases success
      refine ⟨children.1, ?_⟩
      rw [NamedFreeContext.openNames_collection]
      simp only [instantiateAt?, instantiateWith?, children.2, Option.bind_eq_bind, Option.bind_some]
    | some name =>
      cases stored : lookup raw name with
      | none =>
        simp only [lookup_closeAssignment, stored, Option.map_none, Option.bind_none] at success
        cases success
      | some value =>
        simp only [lookup_closeAssignment, stored, Option.map_some, Option.bind_some,
          Option.bind_eq_some_iff] at success
        rcases success with ⟨arguments, argumentsFound, residual, residualRun, success⟩
        have localScopes := arguments?_scoped rule spec admitted name site
          (path ++ [elements.length]) depth coherent.collectionRest arguments argumentsFound
        have argumentScopes : arguments.all
            (fun argument => argument.isWellScopedAt (depth + ambient)) = true := by
          apply List.all_eq_true.mpr
          intro argument member
          exact ScopedPattern.isWellScopedAt_mono (List.all_eq_true.mp localScopes argument member)
            (Nat.le_add_right _ _)
        have residualScope := instantiateValue?_scoped _ _ _ _ _ residualRun
        have restored := closeValue_success ambient depth names value arguments argumentScopes residual residualRun
        cases residual with
        | bvar index => cases success
        | fvar tailName => cases success
        | apply head values => cases success
        | lambda display body => cases success
        | multiLambda count display body => cases success
        | subst body replacement => cases success
        | collection actualKind values residualRest =>
          cases residualRest with
          | some tailName => cases success
          | none =>
            dsimp only at success
            split at success <;> cases success
            refine ⟨scopedList_append _ explicit values children.1 residualScope, ?_⟩
            rw [NamedFreeContext.openNames_collection] at restored ⊢
            simp only [instantiateAt?, instantiateWith?, children.2, stored, argumentsFound, restored,
              Option.bind_eq_bind, Option.bind_some]
            simp_all only [List.map_append, ite_true]
termination_by source => sizeOf source

/-- Rows retain their physical source indices while the same outer name
context is restored at every produced element. -/
theorem instantiateArgs_closed_readback (rule : RewriteRule) (spec : RuleBindingSpec)
    (admitted : admittedFor rule spec = true) (ambient : Nat) (names : List String)
    (raw : ScopedRuleMatching.Assignment) (site : RulePatternSite) :
    ∀ (sources : List Pattern) (path : List Nat) (depth index : Nat),
      ArgumentsDepthCoherent rule site path depth index sources →
      Pattern.isWellScopedListAt depth sources = true → ∀ results,
        instantiateArgsAt? rule spec (ambient + names.length) site path depth
          (closeAssignment ambient names raw) index sources = some results →
        Pattern.isWellScopedListAt (depth + (ambient + names.length)) results = true ∧
          instantiateArgsAt? rule spec ambient site path depth raw index sources =
            some (results.map (NamedFreeContext.openNames (depth + ambient) names))
  | [], path, depth, index, _, _, results, success => by
    simp only [instantiateArgsAt?, instantiateArgsWith?, Option.some.injEq] at success
    cases success
    exact ⟨rfl, by simp only [instantiateArgsAt?, instantiateArgsWith?, List.map_nil]⟩
  | source :: sources, path, depth, index, coherent, scopeProof, results, success => by
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at scopeProof
    simp only [instantiateArgsAt?, instantiateArgsWith?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at success
    rcases success with ⟨head, headRun, tail, tailRun, rfl⟩
    have first := instantiate_closed_readback rule spec admitted ambient names raw site
      source (path ++ [index]) depth coherent.head scopeProof.1 head headRun
    have remaining := instantiateArgs_closed_readback rule spec admitted ambient names raw site
      sources path depth (index + 1) coherent.tail scopeProof.2 tail tailRun
    simp only [instantiateAt?] at first
    simp only [instantiateArgsAt?] at remaining
    refine ⟨by simpa only [Pattern.isWellScopedListAt, Bool.and_eq_true] using And.intro first.1 remaining.1, ?_⟩
    simp only [instantiateArgsAt?, instantiateArgsWith?, first.2, remaining.2,
      Option.bind_eq_bind, Option.bind_some, List.map_cons]
termination_by sources => sizeOf sources
end

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open AmbientCorrespondence

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

private theorem erase_cast_context {first second : List TypeExpr} {sort : TypeExpr}
    (same : first = second) (term : Term (signatureOf language) first sort) :
    erase (castTermCtx same term) = erase term := by
  cases same
  rfl

/-- The checked intrinsic source body is precisely the guarded raw closure,
with the original dependency types and source ambient count retained. -/
theorem Captured.closed_contextualValue {entries : List (String × TypeExpr)}
    {dependencies ambient : List TypeExpr} {source : ContextualValue} {sort : TypeExpr}
    (captured : Captured language entries dependencies ambient source sort) :
    closeValue ambient.length (entries.map Prod.fst) source =
      contextualValue captured.extendedBody := by
  have sourceScope : source.body.isWellScopedAt (source.dependencies.length + ambient.length) = true := by
    simpa only [captured.dependencies_eq, List.length_append] using captured.body.source_scope
  rw [closeValue, if_pos ⟨captured.ambient_eq, sourceScope⟩]
  unfold contextualValue Captured.extendedBody
  rw [erase_cast_context, captured.body.closed_readback]
  simp only [captured.dependencies_eq, NamedFreeContext.closeContext,
    NamedFreeContext.contextSorts, List.length_append, List.length_map]

theorem contextualValue_cast_meta {first second : MetaArity (signatureOf language)}
    (same : first = second) {ambient : List TypeExpr}
    (term : Term (signatureOf language) (first.1 ++ ambient) first.2) :
    contextualValue (castContextualMetaBody same term) = contextualValue term := by
  cases same
  rfl

theorem contextualValue_transfer {first second : List (MetaArity (signatureOf language))}
    (same : first = second) {ambient : List TypeExpr}
    (bodies : ContextualAssignment (signatureOf language) first ambient)
    (position : Fin second.length) :
    contextualValue
      ((Eq.mp (congrArg (fun interface => ContextualAssignment (signatureOf language)
        interface ambient) same) bodies) position) =
      contextualValue (bodies (Fin.cast (congrArg List.length same.symm) position)) := by
  cases same
  rfl

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies


set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Select an internal interface by original declaration positions. The raw
rule fields and binding declaration remain unchanged and retain authority. -/

theorem captureViewFor_usedRows (rule : RewriteRule) :
    captureViewFor rule (usedRows rule) = captureView rule := rfl

def captureViewForIndex (rule : RewriteRule) (positions : List (Fin rule.typeContext.length))
    (position : Fin (captureViewFor rule positions).typeContext.length) : Fin rule.typeContext.length :=
  positions.get ⟨position.val, by simpa only [captureViewFor, List.length_map] using position.isLt⟩

theorem captureViewFor_source_row (rule : RewriteRule) (positions : List (Fin rule.typeContext.length))
    (position : Fin (captureViewFor rule positions).typeContext.length) :
    (captureViewFor rule positions).typeContext.get position =
      rule.typeContext.get (captureViewForIndex rule positions position) :=
  List.getElem_map _

/-- The exact read set selects original rows without requiring produced
output holes, unrelated fields or lexical shadowed values to be available. -/
def captureRowsFor (rule : RewriteRule) (names : List String) : List (Fin rule.typeContext.length) :=
  (List.finRange rule.typeContext.length).filter
    (fun position => names.contains (rule.typeContext.get position).1)

theorem mem_captureRowsFor {rule : RewriteRule} {names : List String}
    {position : Fin rule.typeContext.length} :
    position ∈ captureRowsFor rule names ↔ (rule.typeContext.get position).1 ∈ names := by
  simp only [captureRowsFor, List.mem_filter, List.mem_finRange, true_and, List.contains_iff_mem]

theorem captureRowsFor_nodup (rule : RewriteRule) (names : List String) :
    (captureRowsFor rule names).Nodup := (List.nodup_finRange _).filter _

end Mettapedia.OSLF.MeTTaIL.RuleBinding

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open NamedBodies AmbientCorrespondence

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}


theorem captureOrdinalsFor_rows (positions : List (Fin rule.typeContext.length)) :
    MetaSelection.rows (captureOrdinalsFor language rule spec positions) =
      metaArities (language := language) (captureViewFor rule positions) spec := by
  simp only [MetaSelection.rows, captureOrdinalsFor, List.map_map, Function.comp_def]
  simp only [metaArities, captureViewFor, List.map_map, Function.comp_def, metaIndex,
    List.get_eq_getElem, List.getElem_map]

theorem captureOrdinalsFor_nodup (positions : List (Fin rule.typeContext.length))
    (unique : positions.Nodup) : (captureOrdinalsFor language rule spec positions).Nodup := by
  apply unique.map
  intro first second same
  have values : (metaIndex (language := language) rule spec first).val =
      (metaIndex rule spec second).val := congrArg Fin.val same
  exact Fin.ext values

def captureSelectedPositionFor (positions : List (Fin rule.typeContext.length))
    (position : Fin (metaArities (language := language) (captureViewFor rule positions) spec).length) :
    Fin (MetaSelection.rows (captureOrdinalsFor language rule spec positions)).length :=
  Fin.cast (congrArg List.length (captureOrdinalsFor_rows positions).symm) position

def captureSourceIndexFor (positions : List (Fin rule.typeContext.length))
    (position : Fin (metaArities (language := language) (captureViewFor rule positions) spec).length) :
    Fin (metaArities (language := language) rule spec).length :=
  metaIndex rule spec (captureViewForIndex rule positions
    ⟨position.val, by simpa only [metaArities_length] using position.isLt⟩)

theorem captureSelectedPositionFor_source (positions : List (Fin rule.typeContext.length))
    (position : Fin (metaArities (language := language) (captureViewFor rule positions) spec).length) :
    MetaSelection.sourceIndex (captureOrdinalsFor language rule spec positions)
      (captureSelectedPositionFor positions position) = captureSourceIndexFor positions position := by
  apply Fin.ext
  simp only [MetaSelection.sourceIndex, captureOrdinalsFor, captureSelectedPositionFor,
    List.get_eq_getElem, List.getElem_map, captureSourceIndexFor, captureViewForIndex, metaIndex]
  rfl

theorem captureSourceIndexFor_name (positions : List (Fin rule.typeContext.length))
    (position : Fin (metaArities (language := language) (captureViewFor rule positions) spec).length) :
    metaName (captureViewFor rule positions) spec position =
      metaName rule spec (captureSourceIndexFor positions position) := by
  unfold metaName captureSourceIndexFor
  exact congrArg Prod.fst (captureViewFor_source_row rule positions _)

def captureBodiesFor (positions : List (Fin rule.typeContext.length)) {ambient : List TypeExpr}
    (bodies : ContextualAssignment (signatureOf language)
      (MetaSelection.rows (captureOrdinalsFor language rule spec positions)) ambient) :
    AmbientBodies language (captureViewFor rule positions) spec ambient :=
  Eq.mp (congrArg (fun interface => ContextualAssignment (signatureOf language) interface ambient)
    (captureOrdinalsFor_rows positions)) bodies

theorem captureBodiesFor_contextualValue (positions : List (Fin rule.typeContext.length))
    {ambient : List TypeExpr}
    (bodies : ContextualAssignment (signatureOf language)
      (MetaSelection.rows (captureOrdinalsFor language rule spec positions)) ambient)
    (position : Fin (metaArities (language := language) (captureViewFor rule positions) spec).length) :
    contextualValue (captureBodiesFor positions bodies position) =
      contextualValue (bodies (captureSelectedPositionFor positions position)) :=
  contextualValue_transfer (captureOrdinalsFor_rows positions) bodies position

theorem NamedBodies.SelectedFamily.captureBodiesFor_lookup
    (positions : List (Fin rule.typeContext.length)) {entries : List (String × TypeExpr)}
    {ambient : List TypeExpr} {raw : ScopedRuleMatching.Assignment}
    (family : SelectedFamily language rule spec entries ambient raw
      (captureOrdinalsFor language rule spec positions))
    (position : Fin (metaArities (language := language) (captureViewFor rule positions) spec).length) :
    lookup (closeAssignment ambient.length (entries.map Prod.fst) raw)
        (metaName (captureViewFor rule positions) spec position) =
      some (contextualValue (captureBodiesFor positions family.bodies position)) := by
  let selected := captureSelectedPositionFor (language := language) positions position
  have nameEq : metaName (captureViewFor rule positions) spec position =
      metaName rule spec (MetaSelection.sourceIndex (captureOrdinalsFor language rule spec positions) selected) := by
    rw [captureSourceIndexFor_name, captureSelectedPositionFor_source]
  rw [lookup_closeAssignment, nameEq, (family selected).stored, Option.map_some,
    captureBodiesFor_contextualValue]
  change some (closeValue ambient.length (entries.map Prod.fst) (family selected).original) =
    some (contextualValue (castContextualMetaBody _ (family selected).parsed.toCaptured.extendedBody))
  rw [contextualValue_cast_meta, (family selected).parsed.toCaptured.closed_contextualValue]

theorem NamedBodies.SelectedFamily.capturesOutputsFor
    (positions : List (Fin rule.typeContext.length)) {entries : List (String × TypeExpr)}
    {ambient : List TypeExpr} {raw : ScopedRuleMatching.Assignment}
    (family : SelectedFamily language rule spec entries ambient raw
      (captureOrdinalsFor language rule spec positions))
    (occurrences : List (OutputEvidence language (captureViewFor rule positions) spec)) :
    CapturesOutputs occurrences (closeAssignment ambient.length (entries.map Prod.fst) raw)
      (captureBodiesFor positions family.bodies) := by
  intro occurrence _
  rcases occurrence with ⟨site, locals, path, name, sort, compiled⟩
  have named : metaName (language := language) (captureViewFor rule positions) spec
      (metaIndex (captureViewFor rule positions) spec compiled.index) = name := by
    simpa only [metaName, metaIndex] using compiled.named
  change lookup _ name = some (contextualValue
    (captureBodiesFor positions family.bodies (metaIndex (captureViewFor rule positions) spec compiled.index)))
  simpa only [named] using family.captureBodiesFor_lookup positions
    (metaIndex (captureViewFor rule positions) spec compiled.index)

/-- A selected per-operation interface uses exactly the original raw rule
and captures. No admission claim for the projected metadata is required. -/
theorem selected_named_outputFor_instantiates (positions : List (Fin rule.typeContext.length))
    (site : RulePatternSite) (ambient : List TypeExpr)
    {entries : List (String × TypeExpr)} {fuel : Nat} {locals : List TypeExpr}
    {path : List Nat} {source : Pattern} {sort : TypeExpr}
    (admitted : admittedFor rule spec = true)
    (coherent : DepthCoherent rule site path locals.length source)
    (scopeProof : source.isWellScopedAt locals.length = true)
    (compiled : OutputSchema language (captureViewFor rule positions) spec locals source sort)
    (found : (outputLocalAssembly language (captureViewFor rule positions) spec site).walk
      fuel locals path source sort = some compiled)
    {raw : ScopedRuleMatching.Assignment}
    (family : SelectedFamily language rule spec entries ambient raw
      (captureOrdinalsFor language rule spec positions)) :
    instantiateAt? rule spec ambient.length site path locals.length raw source =
      some (NamedFreeContext.openContext (locals ++ ambient).length entries
        (erase (outputInstantiation (captureBodiesFor positions family.bodies) compiled.term))) := by
  have closedRun := outputLocalAssembly_walk_instantiates language (captureViewFor rule positions)
    spec site (ambient ++ NamedFreeContext.contextSorts entries) compiled found
    (closeAssignment ambient.length (entries.map Prod.fst) raw)
    (captureBodiesFor positions family.bodies) (family.capturesOutputsFor positions compiled.occurrences)
  have sameRun := ScopedRuleMatching.instantiateWith?_congr Substitution.instantiateBVar
    (captureViewFor rule positions) rule spec ⟨rfl, rfl, rfl⟩
    (ambient ++ NamedFreeContext.contextSorts entries).length site
    (closeAssignment ambient.length (entries.map Prod.fst) raw)
    (closeAssignment ambient.length (entries.map Prod.fst) raw) source path locals.length
    (fun _ _ => rfl)
  change instantiateAt? _ _ _ _ _ _ _ _ = instantiateAt? _ _ _ _ _ _ _ _ at sameRun
  rw [sameRun] at closedRun
  have restored := instantiate_closed_readback rule spec admitted ambient.length (entries.map Prod.fst)
    raw site source path locals.length coherent scopeProof
    (erase (outputInstantiation (captureBodiesFor positions family.bodies) compiled.term))
    (by simpa only [NamedFreeContext.contextSorts, List.length_append, List.length_map] using closedRun)
  simpa only [NamedFreeContext.openContext, List.length_append] using restored.2

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration


namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open NamedBodies

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- The unchanged output compiler and actual selected source evidence earn
the ORIGINAL whole output, after exact finite named-free restoration. This
uses the original ambient count, not the auxiliary closed-context length. -/
theorem selected_named_output_instantiates (site : RulePatternSite) (ambient : List TypeExpr)
    {entries : List (String × TypeExpr)} {fuel : Nat} {locals : List TypeExpr}
    {path : List Nat} {source : Pattern} {sort : TypeExpr}
    (admitted : admittedFor rule spec = true)
    (coherent : DepthCoherent rule site path locals.length source)
    (scopeProof : source.isWellScopedAt locals.length = true)
    (compiled : OutputSchema language (captureView rule) spec locals source sort)
    (found : (outputLocalAssembly language (captureView rule) spec site).walk
      fuel locals path source sort = some compiled)
    {raw : ScopedRuleMatching.Assignment}
    (family : SelectedFamily language rule spec entries ambient raw
      (captureOrdinals language rule spec)) :
    instantiateAt? rule spec ambient.length site path locals.length raw source =
      some (NamedFreeContext.openContext (locals ++ ambient).length entries
        (erase (outputInstantiation (captureBodies family.bodies) compiled.term))) := by
  exact selected_named_outputFor_instantiates (usedRows rule) site ambient admitted coherent
    scopeProof compiled found family

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration


set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding GeneralPremise

mutual
/-- Successful instantiation actually reads every source metavariable; this
does not infer availability from syntax alone. -/
theorem instantiateWith?_requires (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (raw : Assignment) :
    ∀ (source : Pattern) (path : List Nat) (depth : Nat) (result : Pattern),
      instantiateWith? operation rule spec ambient site path depth raw source = some result →
        BoundNames raw source.freeFvarNames
  | .bvar _, _, _, _, _ => by intro name member; simp [Pattern.freeFvarNames] at member
  | .fvar name, path, depth, result, success => by
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    rcases success with ⟨value, stored, _⟩
    intro selected member
    have same : selected = name := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using member
    cases same
    exact ⟨value, stored⟩
  | .apply head arguments, path, depth, result, success => by
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨values, run, _⟩ := success
    simpa only [Pattern.freeFvarNames] using
      instantiateArgsWith?_requires operation rule spec ambient site raw arguments path depth 0 values run
  | .lambda display body, path, depth, result, success => by
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨value, run, _⟩ := success
    simpa only [Pattern.freeFvarNames] using
      instantiateWith?_requires operation rule spec ambient site raw body (path ++ [0]) (depth + 1) value run
  | .multiLambda count display body, path, depth, result, success => by
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨value, run, _⟩ := success
    simpa only [Pattern.freeFvarNames] using
      instantiateWith?_requires operation rule spec ambient site raw body (path ++ [0]) (depth + count) value run
  | .subst body replacement, path, depth, result, success => by
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨bodyValue, bodyRun, replacementValue, replacementRun, _⟩ := success
    simpa only [Pattern.freeFvarNames] using
      (instantiateWith?_requires operation rule spec ambient site raw body (path ++ [0])
        (depth + 1) bodyValue bodyRun).append
        (instantiateWith?_requires operation rule spec ambient site raw replacement (path ++ [1])
          depth replacementValue replacementRun)
  | .collection kind elements rest, path, depth, result, success => by
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨explicit, explicitRun, success⟩ := success
    have front := instantiateArgsWith?_requires operation rule spec ambient site raw
      elements path depth 0 explicit explicitRun
    cases rest with
    | none => simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using front
    | some name =>
      simp only [Option.bind_eq_some_iff] at success
      rcases success with ⟨value, stored, _⟩
      simp only [Pattern.freeFvarNames]
      apply front.append
      intro selected member
      have same : selected = name := by simpa only [Option.toList_some, List.mem_singleton] using member
      cases same
      exact ⟨value, stored⟩
termination_by source => sizeOf source

theorem instantiateArgsWith?_requires (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (raw : Assignment) :
    ∀ (sources : List Pattern) (path : List Nat) (depth index : Nat) (results : List Pattern),
      instantiateArgsWith? operation rule spec ambient site path depth raw index sources = some results →
        BoundNames raw (sources.flatMap Pattern.freeFvarNames)
  | [], _, _, _, _, _ => by intro name member; simp at member
  | source :: sources, path, depth, index, results, success => by
    simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨head, headRun, tail, tailRun, _⟩ := success
    exact (instantiateWith?_requires operation rule spec ambient site raw source (path ++ [index])
      depth head headRun).append
      (instantiateArgsWith?_requires operation rule spec ambient site raw sources path depth
        (index + 1) tail tailRun)
termination_by sources => sizeOf sources
end

theorem instantiateAt?_requires {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {raw : Assignment} {source : Pattern} {path : List Nat}
    {depth : Nat} {result : Pattern}
    (success : instantiateAt? rule spec ambient site path depth raw source = some result) :
    BoundNames raw source.freeFvarNames :=
  instantiateWith?_requires _ rule spec ambient site raw source path depth result success

end Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding ScopedRuleMatching

/-- Only INPUT schemas are resolved before a dynamic service call. Output
holes remain original schemas and are bound by the later row matcher. -/
theorem DynamicInputs.inputs_bound {context : Context} {index : Nat} {raw : Assignment}
    {schemas resolved : List Pattern} {modes : List RelationArgMode}
    (actual : DynamicInputs context index raw schemas modes resolved) :
    BoundNames raw (queryInputNames schemas modes) := by
  induction actual with
  | nil => intro name member; simp [queryInputNames] at member
  | input interpreted _ ih =>
    simpa only [queryInputNames, List.zip_cons_cons, List.flatMap_cons] using
      (instantiateAt?_requires interpreted).append ih
  | output _ ih =>
    simpa only [queryInputNames, List.zip_cons_cons, List.flatMap_cons, List.nil_append] using ih

/-- Metadata selection uses the signature the ORIGINAL provider actually
selects. Unavailable and ambiguous signatures remain unavailable. -/
def queryCaptureRows? (provider : ProviderSnapshot) (rule : RewriteRule)
    (relation : String) (schemas : List Pattern) : Option (List (Fin rule.typeContext.length)) := do
  let signature ← signature? provider relation schemas.length
  pure (captureRowsFor rule (queryInputNames schemas signature.modes))

theorem queryCaptureRows?_exact (provider : ProviderSnapshot) (rule : RewriteRule)
    (relation : String) (schemas : List Pattern) (positions : List (Fin rule.typeContext.length)) :
    queryCaptureRows? provider rule relation schemas = some positions ↔
      ∃ signature, signature? provider relation schemas.length = some signature ∧
        positions = captureRowsFor rule (queryInputNames schemas signature.modes) := by
  simp only [queryCaptureRows?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    pure, Option.some.injEq]
  constructor <;> rintro ⟨signature, found, same⟩ <;> exact ⟨signature, found, same.symm⟩

theorem DynamicInputs.selected_inputs_bound {context : Context} {index : Nat} {raw : Assignment}
    {schemas resolved : List Pattern} {modes : List RelationArgMode}
    (actual : DynamicInputs context index raw schemas modes resolved)
    (position : Fin context.rule.typeContext.length)
    (selected : position ∈ captureRowsFor context.rule (queryInputNames schemas modes)) :
    ∃ value, lookup raw (context.rule.typeContext.get position).1 = some value :=
  actual.inputs_bound _ (mem_captureRowsFor.mp selected)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Original typing, canonical source values and actual lookup availability
earn finite source packets for exactly this operation's selected rows. -/
theorem selectedFamily?_complete_of_state {environment : Environment} {context : Context}
    {raw : ScopedRuleMatching.Assignment} {entries : List (String × TypeExpr)}
    (admitted : admittedFor context.rule context.spec = true)
    (typed : TypedAssignment environment context raw) (canonical : CanonicalValues raw)
    (freeContext : environment.free = FreeTypeContext.ofList entries)
    (uniqueNames : (entries.map Prod.fst).Nodup) (names : List String)
    (available : BoundNames raw names) :
    ∃ submitted family, selectedFamily? environment.language context.rule context.spec entries
      context.bound raw submitted
      (captureOrdinalsFor environment.language context.rule context.spec (captureRowsFor context.rule names)) =
        some family := by
  apply selectedFamily?_complete _
    (captureOrdinalsFor_nodup _ (captureRowsFor_nodup context.rule names)) uniqueNames
  intro index selected
  rcases List.mem_map.mp selected with ⟨position, member, same⟩
  cases same
  have named : metaName (language := environment.language) context.rule context.spec
      (metaIndex context.rule context.spec position) = (context.rule.typeContext.get position).1 := rfl
  obtain ⟨value, stored⟩ := available _ (mem_captureRowsFor.mp member)
  obtain ⟨dependencies, expected, dependencyFound, sortFound, dependencyEq, ambientEq, bodyTyped⟩ :=
    typed.1 _ value (ConditionalEquationExecution.lookup_assignment_member _ _ _ stored)
  have rowFound := lookup_of_mem_unique (RawMatching.admitted_meta_names admitted)
    (List.get_mem context.rule.typeContext position)
  have expectedEq : expected = (context.rule.typeContext.get position).2 :=
    Option.some.inj (sortFound.symm.trans rowFound)
  cases expectedEq
  refine ⟨value, ?_, ?_, ?_, ambientEq⟩
  · simpa only [named] using stored
  · simp only [metaArities_get, dependencyFound, Option.getD_some]
    refine ⟨?_, canonical _ _ stored, typed.2 _ _
      (ConditionalEquationExecution.lookup_assignment_member _ _ _ stored), bodyTyped.isWellScopedAt⟩
    rw [← freeContext]
    exact bodyTyped
  · simpa only [metaArities_get, dependencyFound, Option.getD_some] using dependencyEq

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.NamedBodies

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef
open BindingSyntax.ScopedElaboration.SchemaElaboration
open NamedBodies Mettapedia.GSLT.LanguageDef.WellSorted

/-- The original query's INPUT execution earns its actual selected native
function environment. An output hole never becomes an input-body obligation. -/
theorem DynamicInputs.selected_captures {environment : Environment} {context : Context}
    {index : Nat} {raw : ScopedRuleMatching.Assignment}
    {schemas resolved : List Pattern} {modes : List RelationArgMode}
    (actual : DynamicInputs context index raw schemas modes resolved)
    {entries : List (String × TypeExpr)}
    (admitted : admittedFor context.rule context.spec = true)
    (typed : TypedAssignment environment context raw) (canonical : CanonicalValues raw)
    (freeContext : environment.free = FreeTypeContext.ofList entries)
    (uniqueNames : (entries.map Prod.fst).Nodup) :
    ∃ submitted family, selectedFamily? environment.language context.rule context.spec entries
      context.bound raw submitted (captureOrdinalsFor environment.language context.rule context.spec
        (captureRowsFor context.rule (queryInputNames schemas modes))) = some family :=
  selectedFamily?_complete_of_state admitted typed canonical freeContext uniqueNames _ actual.inputs_bound

end Mettapedia.OSLF.MeTTaIL.GeneralPremise


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.NamedOutputControls
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open SchemaElaboration SchemaElaboration.NamedBodies

private def a : TypeExpr := .base "A"
private def emptySort : TypeExpr := .base "Empty"
private def language : LanguageDef where
  name := "named-output"
  types := [{ name := "A" }, { name := "Empty" }]
  terms := [{ label := "triple", category := "A", params := [.simple "x" a, .simple "y" a, .simple "z" a], syntaxPattern := [] }]
  equations := []
  rewrites := []
private def spec : RuleBindingSpec where
  dependencies := [("unused", []), ("f", [a])]
  occurrences := [
    { name := "f", site := .left, path := [0], arguments := [.bvar 0] },
    { name := "f", site := .right, path := [0, 0], arguments := [.bvar 0] }]
private def rule : RewriteRule where
  name := "named-beta"
  typeContext := [("unused", emptySort), ("f", a)]
  premises := []
  left := .lambda none (.fvar "f")
  right := .lambda none (.subst (.fvar "f") (.bvar 0))
  bindings := some spec
private def entries : List (String × TypeExpr) := [("external", a)]
private def body : Pattern := .apply "triple" [.fvar "external", .bvar 0, .bvar 1]
private def value : ContextualValue := ⟨[a], 1, body⟩
private def raw : ScopedRuleMatching.Assignment := [("f", value)]
private def parsed : Parsed language entries [a, a] body a :=
  (parse? language rule spec .right entries [a, a] body a).get (by decide +kernel)
private def evidence : Data :=
  (Wire.termCodec language ([a, a] ++ NamedFreeContext.contextSorts entries) a).put parsed.term
private def submitted : List (Nat × Data) := [(1, evidence)]
private def originalIndex : Fin (metaArities (language := language) rule spec).length := ⟨1, by decide +kernel⟩
private def ordinals := [originalIndex]
private theorem selectionEq : captureOrdinals language rule spec = ordinals := by cbv
private def selected : SelectedEvidence language rule spec entries [a] raw originalIndex :=
  (selectEvidence? language rule spec entries [a] raw submitted originalIndex).get (by decide +kernel)
private def literalFamily : SelectedFamily language rule spec entries [a] raw ordinals :=
  fun position => Fin.cases selected (fun rest => Fin.elim0 rest) position
private def family : SelectedFamily language rule spec entries [a] raw
    (captureOrdinals language rule spec) :=
  Eq.mp (congrArg (fun chosen => SelectedFamily language rule spec entries [a] raw chosen)
    selectionEq.symm) literalFamily
private def selectedRule : RewriteRule := { rule with typeContext := [("f", a)] }
private theorem viewEq : captureView rule = selectedRule := by
  have rowsEq : usedRows rule = [⟨1, by decide +kernel⟩] := by cbv
  unfold captureView selectedRule
  rw [rowsEq]
  rfl
private def literalCompiled : OutputSchema language selectedRule spec [] rule.right (.arrow a a) :=
  ((outputLocalAssembly language selectedRule spec .right).walk
    (sourceHeight rule.right) [] [] rule.right (.arrow a a)).get (by decide +kernel)
private def compiled : OutputSchema language (captureView rule) spec [] rule.right (.arrow a a) :=
  Eq.mp (congrArg (fun current => OutputSchema language current spec [] rule.right (.arrow a a))
    viewEq.symm) literalCompiled
private theorem compiledFound :
    (outputLocalAssembly language (captureView rule) spec .right).walk
      (sourceHeight rule.right) [] [] rule.right (.arrow a a) = some compiled := by
  have transport : ∀ (first second : RewriteRule) (same : first = second)
      (term : OutputSchema language second spec [] rule.right (.arrow a a)),
      (outputLocalAssembly language second spec .right).walk
        (sourceHeight rule.right) [] [] rule.right (.arrow a a) = some term →
      (outputLocalAssembly language first spec .right).walk
        (sourceHeight rule.right) [] [] rule.right (.arrow a a) =
          some (Eq.mp (congrArg (fun current => OutputSchema language current spec [] rule.right
            (.arrow a a)) same.symm) term) := by
    intro first second same term found
    cases same
    exact found
  exact transport _ _ viewEq literalCompiled (Option.some_get _).symm
private def expected : Pattern :=
  .lambda none (.apply "triple" [.fvar "external", .bvar 0, .bvar 1])
private def closedResult : Pattern :=
  erase (outputInstantiation (captureBodies family.bodies) compiled.term)

example : instantiateAt? rule spec 1 .right [] 0 raw rule.right =
    some (NamedFreeContext.openContext 1 entries closedResult) := by
  exact selected_named_output_instantiates .right [a]
    (by decide +kernel) (depthCoherent_right rule) (by decide +kernel) compiled
    compiledFound family

private def tailSpec : RuleBindingSpec where
  dependencies := [("tail", [])]
private def tailRule : RewriteRule where
  name := "named-rest"
  typeContext := [("tail", .collection .hashBag a)]
  premises := []
  left := .fvar "tail"
  right := .collection .hashBag [.apply "unit" []] (some "tail")
  bindings := some tailSpec
private def tailRaw : ScopedRuleMatching.Assignment :=
  [("tail", ⟨[], 0, .collection .hashBag [.fvar "external", .fvar "external"] none⟩)]
private def closedTail : Pattern :=
  .collection .hashBag [.apply "unit" [], .bvar 0, .bvar 0] none

example : instantiateAt? tailRule tailSpec 0 .right [] 0 tailRaw tailRule.right =
    some (NamedFreeContext.openNames 0 ["external"] closedTail) := by
  exact (instantiate_closed_readback tailRule tailSpec (by decide +kernel) 0 ["external"]
    tailRaw .right tailRule.right [] 0 (depthCoherent_right tailRule) (by decide +kernel)
    closedTail (by decide +kernel)).2

private def evaluate (assignment : ScopedRuleMatching.Assignment) : Option Pattern :=
  instantiateAt? rule spec 1 .right [] 0 assignment rule.right

def checks : List (String × Bool) := [
  ("actual-admitted-rule", admittedFor rule spec),
  ("unused-source-row-retained", rule.typeContext.length == 2),
  ("only-original-used-row-selected", (captureOrdinals language rule spec).map Fin.val == [1]),
  ("actual-named-body-packet", (selectedFamily? language rule spec entries [a] raw submitted
    (captureOrdinals language rule spec)).isSome),
  ("original-named-beta-output", evaluate raw == some expected),
  ("closed-beta-output-retains-all-three-context-roles", closedResult ==
    .lambda none (.apply "triple" [.bvar 2, .bvar 0, .bvar 1])),
  ("whole-output-original-ambient-restoration", NamedFreeContext.openContext 1 entries closedResult == expected),
  ("wrong-opening-depth-is-different", !(NamedFreeContext.openContext 0 entries closedResult == expected)),
  ("first-duplicate-source-capture-retained", evaluate (raw ++ [("f", ⟨[a], 9, .bvar 20⟩)]) == some expected),
  ("bad-original-ambient-refuses", (evaluate [("f", ⟨[a], 0, body⟩)]).isNone),
  ("closing-keeps-bad-ambient-refusal", (instantiateAt? rule spec 2 .right [] 0
    (closeAssignment 1 ["external"] [("f", ⟨[a], 0, body⟩)]) rule.right).isNone),
  ("bad-original-body-scope-refuses", (evaluate [("f", ⟨[a], 1, .bvar 2⟩)]).isNone),
  ("name-slot-cannot-repair-invalid-original-body", (instantiateAt? rule spec 2 .right [] 0
    (closeAssignment 1 ["external"] [("f", ⟨[a], 1, .bvar 2⟩)]) rule.right).isNone),
  ("missing-used-capture-refuses", (evaluate []).isNone),
  ("rest-keeps-source-multiplicity", instantiateAt? tailRule tailSpec 0 .right [] 0 tailRaw tailRule.right ==
    some (.collection .hashBag [.apply "unit" [], .fvar "external", .fvar "external"] none)),
  ("closed-rest-keeps-physical-occurrences", instantiateAt? tailRule tailSpec 1 .right [] 0
    (closeAssignment 0 ["external"] tailRaw) tailRule.right == some closedTail),
  ("wrong-rest-kind-refuses", (instantiateAt? tailRule tailSpec 0 .right [] 0
    [("tail", ⟨[], 0, .collection .hashSet [.fvar "external"] none⟩)] tailRule.right).isNone)
]

#guard checks.all Prod.snd

def run : IO Unit := do
  for (label, okay) in checks do
    unless okay do throw (IO.userError ("FAILED " ++ label))
  IO.println s!"{checks.length} named whole-output controls PASS"

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.NamedOutputControls


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.OperationCaptureControls
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding ScopedRuleMatching GeneralPremise

private def a : TypeExpr := .base "A"
private def schemas : List Pattern := [.fvar "input", .fvar "output"]
private def spec : RuleBindingSpec :=
  { dependencies := [("input", []), ("output", []), ("local", [])] }
private def rule : RewriteRule where
  name := "input-output"
  typeContext := [("input", a), ("output", a), ("local", a)]
  premises := [.relationQuery "relation" schemas]
  left := .fvar "input"
  right := .fvar "input"
  bindings := some spec
private def provider : ProviderSnapshot :=
  { signatures := [⟨"relation", [a, a], [.input, .output]⟩], rows := [],
    dynamicRelations := ["relation"] }
private def value : ContextualValue := ⟨[], 0, .fvar "external"⟩
private def raw : Assignment := [("input", value)]
private def context : Context :=
  { rule := rule, spec := spec, bound := [], premiseIndex := 0, quantifierDepth := 0, ruleIndex := 0 }

example : DynamicInputs context 0 raw schemas [.input, .output]
    [.fvar "external", .fvar "output"] := by
  exact .input (by decide +kernel) (.output .nil)

example : BoundNames raw (queryInputNames schemas [.input, .output]) :=
  (show DynamicInputs context 0 raw schemas [.input, .output]
    [.fvar "external", .fvar "output"] from
    .input (by decide +kernel) (.output .nil)).inputs_bound

private def before : Assignment := raw ++ [("local", ⟨[], 0, .fvar "saved"⟩)]
private def firstLocal := localValue [] (.fvar "first")
private def secondLocal := localValue [] (.fvar "second")
private def shadowed := bindParameter "local" firstLocal before
private def nested := bindParameter "local" secondLocal shadowed

def checks : List (String × Bool) := [
  ("selected-signature-input-rows", (queryCaptureRows? provider rule "relation" schemas).map
    (List.map Fin.val) == some [0]),
  ("output-hole-is-not-an-input-capture", lookup raw "output" == none),
  ("actual-input-instantiation", instantiateAt? rule spec 0 (context.site 0) [] 0 raw (.fvar "input") ==
    some (.fvar "external")),
  ("missing-input-refuses", (instantiateAt? rule spec 0 (context.site 0) [] 0 [] (.fvar "input")).isNone),
  ("reversed-role-selects-other-original-row", (queryCaptureRows?
    { provider with signatures := [⟨"relation", [a, a], [.output, .input]⟩] }
    rule "relation" schemas).map (List.map Fin.val) == some [1]),
  ("unknown-signature-refuses", (queryCaptureRows? provider rule "unknown" schemas).isNone),
  ("ambiguous-signature-refuses", (queryCaptureRows?
    { provider with signatures := provider.signatures ++ provider.signatures }
    rule "relation" schemas).isNone),
  ("local-selection-keeps-original-position", (captureRowsFor rule ["local"]).map Fin.val == [2]),
  ("lexical-binding-uses-current-value", lookup shadowed "local" == some firstLocal),
  ("nested-parameter-shadows-current-value", lookup nested "local" == some secondLocal),
  ("inner-restore-retains-outer-local", lookup (restoreParameter "local" shadowed nested) "local" == some firstLocal),
  ("outer-restore-retains-original-value", lookup (restoreParameter "local" before shadowed) "local" ==
    some ⟨[], 0, .fvar "saved"⟩),
  ("local-binding-keeps-other-captures", lookup nested "input" == lookup raw "input")
]

#guard checks.all Prod.snd

def run : IO Unit := do
  for (label, okay) in checks do
    unless okay do throw (IO.userError ("FAILED " ++ label))
  IO.println s!"{checks.length} operation capture controls PASS"

end Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.OperationCaptureControls


namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open ScopedElaboration SchemaElaboration NamedBodies
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- The finite source rule interface is decoded in the full independently
admitted TypeExpr carrier, preserving its original row order. -/
structure Metadata (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    extends SortArityDecoder.Interface (sort? language) (metaArities (language := language) rule spec)

def metadata? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :
    Option (Metadata language rule spec) :=
  (SortArityDecoder.decodeInterface? (sort? language) (metaArities rule spec)).map fun decoded => ⟨decoded⟩

/-- This source admission predicate mentions only the original type
expressions and authored declaration inventory. -/
def MetadataDeclared (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) : Prop :=
  ∀ entry ∈ metaArities (language := language) rule spec,
    (∀ type ∈ entry.1, DeclaredType language type) ∧ DeclaredType language entry.2

theorem metadata?_exact :
    (∃ metadata, metadata? language rule spec = some metadata) ↔ MetadataDeclared language rule spec := by
  constructor
  · rintro ⟨metadata, _⟩ entry member
    obtain ⟨dependencies, result⟩ := SortArityDecoder.decodeInterface?_available metadata.toInterface entry member
    exact ⟨fun type present => (sort?_exact language type).mp (dependencies type present),
      (sort?_exact language entry.2).mp result⟩
  · intro admitted
    obtain ⟨decoded, accepted⟩ := SortArityDecoder.decodeInterface?_complete
      (decode := sort? language) (original := metaArities (language := language) rule spec)
      (fun entry member => ⟨fun type present => (sort?_exact language type).mpr ((admitted entry member).1 type present),
        (sort?_exact language entry.2).mpr (admitted entry member).2⟩)
    exact ⟨⟨decoded⟩, by unfold metadata?; rw [accepted]; rfl⟩

def projection (language : LanguageDef) : SigMor (sourceSignature language) (signatureOf language) :=
  (signatureOf language).reindexProjection (fun sort : DeclaredSort language => sort.val)

def operatorReader (language : LanguageDef) : (projection language).OperatorReader :=
  (signatureOf language).reindexOperatorReader (fun sort : DeclaredSort language => sort.val)
    (sort? language) (fun _ _ read => sort?_source read)

theorem operator_roundtrip {sort : DeclaredSort language}
    (operator : (sourceSignature language).Op sort) :
    (operatorReader language).read ((projection language).opMap operator) = some operator :=
  (signatureOf language).reindexOperator?_roundtrip
    (fun sort : DeclaredSort language => sort.val) (sort? language)
    (fun _ _ read => sort?_source read) sort?_readback operator

theorem Metadata.projects (metadata : Metadata language rule spec) :
    (projection language).mapMetas metadata.entries = metaArities rule spec :=
  SortArityDecoder.Interface.projects metadata.toInterface (projection language).sortMap (fun _ _ read => sort?_source read)

theorem Metadata.source_length (metadata : Metadata language rule spec) :
    metadata.entries.length = rule.typeContext.length := by
  have lengths := SortArityDecoder.Interface.length metadata.toInterface
    (fun sort : DeclaredSort language => sort.val) (fun _ _ read => sort?_source read)
  exact lengths.trans (metaArities_length (language := language) rule spec)

/-- The source schema is literal, including every scoped constructor and
metavariable argument; the operational function interpretation is separate. -/
def Metadata.sourceSchema (metadata : Metadata language rule spec)
    {context : List (DeclaredSort language)} {sort : DeclaredSort language}
    (term : Term (withMetas (sourceSignature language) metadata.entries) context sort) :
    Term (withMetas (signatureOf language) (metaArities rule spec))
      (context.map Subtype.val) sort.val :=
  SortArityDecoder.Interface.schemaSource (S := signatureOf language) (T := sourceSignature language) metadata.toInterface (projection language) (fun _ _ read => sort?_source read) term

def Metadata.readSchema? (metadata : Metadata language rule spec)
    {context : List (DeclaredSort language)} {sort : DeclaredSort language}
    (source : Term (withMetas (signatureOf language) (metaArities rule spec))
      (context.map Subtype.val) sort.val) :
    Option (Term (withMetas (sourceSignature language) metadata.entries) context sort) :=
  SortArityDecoder.Interface.schema? (S := signatureOf language) (T := sourceSignature language) metadata.toInterface (projection language) (fun _ _ read => sort?_source read) (operatorReader language) source

theorem Metadata.readSchema?_projects (metadata : Metadata language rule spec)
    {context : List (DeclaredSort language)} {sort : DeclaredSort language}
    (source : Term (withMetas (signatureOf language) (metaArities rule spec))
      (context.map Subtype.val) sort.val)
    (selected : Term (withMetas (sourceSignature language) metadata.entries) context sort)
    (accepted : metadata.readSchema? source = some selected) :
    metadata.sourceSchema selected = source := by
  unfold Metadata.readSchema? at accepted
  unfold Metadata.sourceSchema
  exact SortArityDecoder.Interface.schema?_projects (S := signatureOf language) (T := sourceSignature language) metadata.toInterface (projection language) (fun _ _ read => sort?_source read)
    (operatorReader language) source selected accepted

theorem Metadata.readSchema?_roundtrip (metadata : Metadata language rule spec)
    {context : List (DeclaredSort language)} {sort : DeclaredSort language}
    (term : Term (withMetas (sourceSignature language) metadata.entries) context sort) :
    metadata.readSchema? (metadata.sourceSchema term) = some term := by
  unfold Metadata.readSchema? Metadata.sourceSchema
  exact SortArityDecoder.Interface.schema?_roundtrip (S := signatureOf language) (T := sourceSignature language) metadata.toInterface (projection language) (fun _ _ read => sort?_source read)
    (operatorReader language) operator_roundtrip term

theorem Metadata.sourceSchema_injective (metadata : Metadata language rule spec)
    {context : List (DeclaredSort language)} {sort : DeclaredSort language} :
    Function.Injective (metadata.sourceSchema (context := context) (sort := sort)) := by
  unfold Metadata.sourceSchema
  exact SortArityDecoder.Interface.schemaSource_injective (S := signatureOf language) (T := sourceSignature language) metadata.toInterface (projection language) (fun _ _ read => sort?_source read)
    (operatorReader language) operator_roundtrip

/-- Declaration positions survive reindexing. Duplicate or unused rows do not
collapse into a set of function types. -/
def Metadata.sourceIndex (metadata : Metadata language rule spec)
    (index : Fin metadata.entries.length) : Fin rule.typeContext.length :=
  ⟨index.val, by rw [← metadata.source_length]; exact index.isLt⟩

theorem Metadata.source_row (metadata : Metadata language rule spec)
    (index : Fin metadata.entries.length) :
    mapArity Subtype.val (metadata.entries.get index) =
      ((Mettapedia.OSLF.MeTTaIL.RuleBinding.dependencies? spec
        (rule.typeContext.get (metadata.sourceIndex index)).1).getD [],
        (rule.typeContext.get (metadata.sourceIndex index)).2) := by
  have row := SortArityDecoder.Interface.row metadata.toInterface
    (fun sort : DeclaredSort language => sort.val) (fun _ _ read => sort?_source read) index
  have sameIndex : metadata.toInterface.sourceIndex Subtype.val
      (fun _ _ read => sort?_source read) index = metaIndex rule spec (metadata.sourceIndex index) :=
    Fin.ext rfl
  rw [sameIndex, metaArities_get] at row
  exact row

theorem Metadata.readSchema?_complete_on (metadata : Metadata language rule spec)
    {context : List (DeclaredSort language)} {sort : DeclaredSort language}
    (source : Term (withMetas (signatureOf language) (metaArities rule spec))
      (context.map Subtype.val) sort.val)
    (supported : (SortArityDecoder.castSchemaRows metadata.projects.symm source).AllOperators
      (SigMor.OperatorReader.ConstructorSupport (projection language) (operatorReader language) metadata.entries)) :
    ∃ selected, metadata.readSchema? source = some selected := by
  unfold Metadata.readSchema?
  exact SortArityDecoder.Interface.schema?_complete_on
    (S := signatureOf language) (T := sourceSignature language)
    metadata.toInterface (projection language) (fun _ _ read => sort?_source read)
    (operatorReader language) Subtype.val_injective source supported

private theorem dependencies_declared {name : String} {dependencies : List TypeExpr}
    (checked : Mettapedia.OSLF.MeTTaIL.RuleBinding.dependencySortsDeclared language spec = true)
    (found : Mettapedia.OSLF.MeTTaIL.RuleBinding.dependencies? spec name = some dependencies) :
    ∀ type ∈ dependencies, DeclaredType language type := by
  unfold Mettapedia.OSLF.MeTTaIL.RuleBinding.dependencies? at found
  split at found
  · rename_i rowName rowDependencies rows
    have same : rowDependencies = dependencies := Option.some.inj found
    subst rowDependencies
    have selected : (rowName, dependencies) ∈ spec.dependencies := by
      apply List.mem_of_mem_filter
      rw [rows]
      exact List.mem_singleton_self _
    have types := List.all_eq_true.mp checked (rowName, dependencies) selected
    intro type present
    apply (declaredType_iff_baseNames type).mpr
    intro base member
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp types type present) base member)
  · contradiction

/-- Actual binding admission supplies dependency-sort authority; result-sort
formation is checked on each original rule-context row independently. -/
theorem metadataDeclared_of_source_checks
    (results : ∀ entry ∈ rule.typeContext, DeclaredType language entry.2)
    (checked : Mettapedia.OSLF.MeTTaIL.RuleBinding.dependencySortsDeclared language spec = true) :
    MetadataDeclared language rule spec := by
  intro entry present
  obtain ⟨row, member, same⟩ := List.mem_map.mp present
  cases same
  refine ⟨?_, results row member⟩
  intro type inDependencies
  cases found : Mettapedia.OSLF.MeTTaIL.RuleBinding.dependencies? spec row.1 with
  | none => simp only [found, Option.getD_none, List.not_mem_nil] at inDependencies
  | some dependencies =>
      exact dependencies_declared checked found type (by simpa only [found, Option.getD_some] using inDependencies)

/-- This is the actual elaborated plan's interface, including inferred type
rows. Authored declaration identity is retained by the surrounding plan. -/
def rulePlanMetadata? (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (plan : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.RulePlan) :=
  metadata? snapshot.language plan.rule plan.binding.spec

theorem rulePlanMetadata?_complete
    {snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot}
    {index : Nat} {source : RewriteRule}
    {plan : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.RulePlan}
    (compiled : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.rulePlan? snapshot index source = some plan)
    (results : ∀ entry ∈ plan.rule.typeContext, DeclaredType snapshot.language entry.2) :
    ∃ metadata, rulePlanMetadata? snapshot plan = some metadata := by
  apply metadata?_exact.mpr
  exact metadataDeclared_of_source_checks results
    (Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.rulePlan_readout compiled).2.2.2.2.1


/-- Completed source captures are read after original rule admission. This
record preserves the original authored declaration and its complete metadata;
only the runtime body family is selected by actual operational support. -/
structure CapturedEnvironment (snapshot : Snapshot) (index : Nat)
    (ambient : List TypeExpr) (assignment : Assignment) (submitted : List (Nat × Data)) where
  namesAdmitted : checkFreeContext snapshot = true
  authored : RewriteRule
  sourceDeclared : snapshot.language.rewrites[index]? = some authored
  plan : RulePlan
  sourceAdmitted : rulePlan? snapshot index authored = some plan
  family : SelectedFamily snapshot.language plan.rule plan.binding.spec snapshot.freeTypes ambient assignment
    (captureOrdinals snapshot.language plan.rule plan.binding.spec)
  decoded : selectedFamily? snapshot.language plan.rule plan.binding.spec snapshot.freeTypes ambient assignment submitted
    (captureOrdinals snapshot.language plan.rule plan.binding.spec) = some family

/-- The original plan compiler and original source body checker both run.
Captures alone do not discharge a rule's match or conditional premises. -/
def readCapturedEnvironment? (snapshot : Snapshot) (index : Nat)
    (ambient : List TypeExpr) (assignment : Assignment) (submitted : List (Nat × Data)) :
    Option (CapturedEnvironment snapshot index ambient assignment submitted) :=
  if namesAdmitted : checkFreeContext snapshot = true then
    match sourceDeclared : snapshot.language.rewrites[index]? with
    | none => none
    | some authored =>
      match sourceAdmitted : rulePlan? snapshot index authored with
      | none => none
      | some plan =>
          match decoded : selectedFamily? snapshot.language plan.rule plan.binding.spec snapshot.freeTypes ambient assignment submitted
              (captureOrdinals snapshot.language plan.rule plan.binding.spec) with
          | none => none
          | some family => some ⟨namesAdmitted, authored, sourceDeclared, plan, sourceAdmitted, family, decoded⟩
  else none

variable {snapshot : Snapshot} {index : Nat}
variable {ambient : List TypeExpr} {assignment : Assignment} {submitted : List (Nat × Data)}

theorem CapturedEnvironment.original_authority
    (checked : CapturedEnvironment snapshot index ambient assignment submitted) :
    snapshot.language.rewrites[index]? = some checked.authored ∧
      checked.plan.declarationIndex = index ∧ checked.plan.authored = checked.authored ∧
      admittedFor checked.plan.rule checked.plan.binding.spec = true ∧
      dependencySortsDeclared snapshot.language checked.plan.binding.spec = true ∧
      GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider
        checked.plan.rule checked.plan.binding.spec = true := by
  have source := rulePlan_readout checked.sourceAdmitted
  exact ⟨checked.sourceDeclared, source.1, source.2.1, source.2.2.2.1, source.2.2.2.2.1, source.2.2.2.2.2⟩

/-- Accepted values retain their exact source name, original ordinal,
submitted bytes, original dependency types and ambient count. -/
theorem CapturedEnvironment.source_values
    (checked : CapturedEnvironment snapshot index ambient assignment submitted)
    (original : Fin (metaArities (language := snapshot.language) checked.plan.rule checked.plan.binding.spec).length)
    (used : original ∈ captureOrdinals snapshot.language checked.plan.rule checked.plan.binding.spec) :
    ∃ (value : ContextualValue) (evidence : Data),
      lookup assignment (metaName checked.plan.rule checked.plan.binding.spec original) = some value ∧
      submitted.lookup original.val = some evidence ∧
      HasType snapshot.language snapshot.free
        (((metaArities checked.plan.rule checked.plan.binding.spec).get original).1 ++ ambient)
        value.body ((metaArities checked.plan.rule checked.plan.binding.spec).get original).2 ∧
      value.dependencies = ((metaArities checked.plan.rule checked.plan.binding.spec).get original).1 ∧
      value.ambient = ambient.length := by
  obtain ⟨⟨position, same⟩, _⟩ := (MetaSelection.select?_some_iff _ original).mpr used
  cases same
  let captured := checked.family position
  have decoded := selectedFamily?_at checked.decoded position
  have source := selectEvidence?_readout decoded
  exact ⟨captured.original, captured.evidence, captured.stored, source.1,
    captured.parsed.body.typed_snapshot, captured.parsed.dependencies_eq, captured.parsed.ambient_eq⟩

/-- Source support is the actual complete elaborated rule, including query,
scoped-step, freshness-name and quantified collection fields. Local lexical
parameters have the separate site support already proved by the source layer. -/
theorem CapturedEnvironment.support_exact
    (checked : CapturedEnvironment snapshot index ambient assignment submitted)
    (original : Fin (metaArities (language := snapshot.language) checked.plan.rule checked.plan.binding.spec).length) :
    original ∈ captureOrdinals snapshot.language checked.plan.rule checked.plan.binding.spec ↔
      RuleReads checked.plan.rule (metaName checked.plan.rule checked.plan.binding.spec original) :=
  mem_captureOrdinals

/-- Every independently typed actual selected capture has finite source
bytes. Unused original declarations require no body or inhabitant. -/
theorem readCapturedEnvironment?_complete
    (snapshot : Snapshot) (index : Nat) (authored : RewriteRule) (ambient : List TypeExpr) (assignment : Assignment)
    (namesAdmitted : checkFreeContext snapshot = true)
    (sourceDeclared : snapshot.language.rewrites[index]? = some authored) (plan : RulePlan)
    (sourceAdmitted : rulePlan? snapshot index authored = some plan)
    (values : ∀ original ∈ captureOrdinals snapshot.language plan.rule plan.binding.spec, ∃ value,
      lookup assignment (metaName plan.rule plan.binding.spec original) = some value ∧
      OpenPatternWellSorted snapshot.language snapshot.free
        (((metaArities plan.rule plan.binding.spec).get original).1 ++ ambient)
        ((metaArities plan.rule plan.binding.spec).get original).2 value.body ∧
      value.dependencies = ((metaArities plan.rule plan.binding.spec).get original).1 ∧ value.ambient = ambient.length) :
    ∃ submitted checked, readCapturedEnvironment? snapshot index ambient assignment submitted = some checked := by
  have originalValues : ∀ original ∈ captureOrdinals snapshot.language plan.rule plan.binding.spec, ∃ value,
      lookup assignment (metaName plan.rule plan.binding.spec original) = some value ∧
      OpenPatternWellSorted snapshot.language (FreeTypeContext.ofList snapshot.freeTypes)
        (((metaArities plan.rule plan.binding.spec).get original).1 ++ ambient)
        ((metaArities plan.rule plan.binding.spec).get original).2 value.body ∧
      value.dependencies = ((metaArities plan.rule plan.binding.spec).get original).1 ∧ value.ambient = ambient.length := by
    simpa only [snapshot_free_eq_ofList] using values
  obtain ⟨submitted, family, decoded⟩ := selectedFamily?_complete _
    (captureOrdinals_nodup snapshot.language plan.rule plan.binding.spec)
    (snapshot_names_unique namesAdmitted) originalValues
  refine ⟨submitted, ⟨namesAdmitted, authored, sourceDeclared, plan, sourceAdmitted, family, decoded⟩, ?_⟩
  unfold readCapturedEnvironment?
  rw [dif_pos namesAdmitted]
  split
  · rename_i absent
    rw [sourceDeclared] at absent
    cases absent
  · rename_i actualSource actualDeclared
    have same : actualSource = authored := Option.some.inj (actualDeclared.symm.trans sourceDeclared)
    cases same
    split
    · rename_i absent
      rw [sourceAdmitted] at absent
      cases absent
    · rename_i actual actualRead
      have same : actual = plan := Option.some.inj (actualRead.symm.trans sourceAdmitted)
      cases same
      split
      · rename_i absent
        rw [decoded] at absent
        cases absent
      · rename_i actualFamily actualDecoded
        have same : actualFamily = family := Option.some.inj (actualDecoded.symm.trans decoded)
        cases same
        rfl

end Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata


namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata.CapturedEnvironment.Controls
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open ScopedElaboration SchemaElaboration NamedBodies

private def a : TypeExpr := .base "A"
private def e : TypeExpr := .base "Empty"
private def spec : RuleBindingSpec where
  dependencies := [("unused", []), ("P", [])]
private def source : RewriteRule where
  name := "original-source-rule"
  typeContext := [("unused", e), ("P", a)]
  premises := []
  left := .fvar "P"
  right := .fvar "P"
  bindings := some spec
private def language : LanguageDef where
  name := "original-source-snapshot"
  types := [{ name := "A" }, { name := "Empty" }]
  terms := []
  equations := []
  rewrites := [source]
private def snapshot : Snapshot := ⟨language, [("z", a)], { signatures := [], rows := [] }⟩
private def assignment : Assignment := [("P", ⟨[], 0, .fvar "z"⟩)]
private def body : Term (signatureOf language) [a] a := .var .zero
private def evidence : Data := (Wire.termCodec language [a] a).put body
private def submitted : List (Nat × Data) := [(1, evidence)]
private def result := readCapturedEnvironment? snapshot 0 [] assignment submitted
private def absentSource : Snapshot := { snapshot with language := { language with rewrites := [] } }
private def invalidSource : Snapshot :=
  { snapshot with language := { language with rewrites := [{ source with bindings := some { dependencies := [] } }] } }
private def badFreeNames : Snapshot := { snapshot with freeTypes := [("z", a), ("z", a)] }

def checks : List (String × Bool) := [
  ("actual-original-plan-and-captures", (readCapturedEnvironment? snapshot 0 [] assignment submitted).isSome),
  ("original-declaration-index-retained", (result.map (fun checked => checked.plan.declarationIndex)) == some 0),
  ("original-unused-metadata-retained", (result.map (fun checked => checked.plan.rule.typeContext.map Prod.fst)) == some ["unused", "P"]),
  ("actual-selected-family-has-one-function", (result.map (fun checked => (captureOrdinals language checked.plan.rule checked.plan.binding.spec).length)) == some 1),
  ("unknown-original-declaration-refuses", (readCapturedEnvironment? snapshot 1 [] assignment submitted).isNone),
  ("no-original-row-refuses", (readCapturedEnvironment? absentSource 0 [] assignment submitted).isNone),
  ("invalid-original-binding-admission-refuses", (readCapturedEnvironment? invalidSource 0 [] assignment submitted).isNone),
  ("invalid-original-free-context-refuses", (readCapturedEnvironment? badFreeNames 0 [] assignment submitted).isNone),
  ("new-local-index-cannot-replace-original-ordinal", (readCapturedEnvironment? snapshot 0 [] assignment [(0, evidence)]).isNone),
  ("missing-used-original-capture-refuses", (readCapturedEnvironment? snapshot 0 [] [] submitted).isNone)]

#guard checks.all Prod.snd

def run : IO Unit := do
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  IO.println s!"{checks.length} actual authored capture-environment controls"

end Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceMetadata.CapturedEnvironment.Controls
