import Mettapedia.Logic.HOL.DefinitionExtensionSemantics
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution

/-!
# Actual Henkin models for finite histories of definitions

Each new symbol has a closed body in the preceding signature. Freshness and
acyclicity follow from the disjoint signature extension, not from a promise
that a recursively defined constant has a meaning. Bodies may use all older
definitions and may be functions with bound arguments.

The model is built by extending the preceding model at each entry. A separate
syntactic expansion is proved to give exactly that model's reduct. Old open
terms keep their denotation; all admitted domains and their extensionality
properties are retained. This is fixed-simple-type HOL. Carrier-changing
definitions in the dependent calculus have a separate checking contract.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u}

/-- Uniform signature bounds are closed under adjoining typed symbols. -/
inductive DefinitionHistory (source : Ty Base → Type (max u v)) :
    (Ty Base → Type (max u v)) → Type (max u v + 1) where
  | nil : DefinitionHistory source source
  | add {prior : Ty Base → Type (max u v)}
      (history : DefinitionHistory source prior) (type : Ty Base)
      (body : ClosedTerm prior type) :
      DefinitionHistory source (DefinedConst prior type)

namespace DefinitionHistory

variable {source target middle : Ty Base → Type (max u v)}

def embedding {source target : Ty Base → Type (max u v)} : DefinitionHistory source target →
    ∀ {type}, source type → target type
  | .nil, _, constant => constant
  | .add history _ _, _, constant => .old (history.embedding constant)

/-- Expand the newest symbol and then its older dependencies. -/
def images {source target : Ty Base → Type (max u v)} : DefinitionHistory source target →
    ∀ {type}, target type → ClosedTerm source type
  | .nil, _, constant => .const constant
  | .add history _ body, _, constant =>
      HOL.substConst history.images (DefinedConst.expansion body constant)

def embed (history : DefinitionHistory source target)
    {context : Ctx Base} {type : Ty Base} (term : Term source context type) :
    Term target context type := HOL.mapConst history.embedding term

def erase (history : DefinitionHistory source target)
    {context : Ctx Base} {type : Ty Base} (term : Term target context type) :
    Term source context type := HOL.substConst history.images term

theorem images_embedding (history : DefinitionHistory source target)
    {type : Ty Base} (constant : source type) :
    history.images (history.embedding constant) = .const constant := by
  induction history with
  | nil => rfl
  | add history type body ih => exact ih

theorem erase_embed (history : DefinitionHistory source target)
    {context : Ctx Base} {type : Ty Base} (term : Term source context type) :
    history.erase (history.embed term) = term := by
  rw [erase, embed, substConst_mapConst]
  exact (substConst_ext (fun constant => history.images_embedding constant) term).trans
    (substConst_id term)

theorem erase_rename (history : DefinitionHistory source target)
    {context context' : Ctx Base} {type : Ty Base}
    (ρ : Rename Base context context') (term : Term target context type) :
    history.erase (HOL.rename ρ term) = HOL.rename ρ (history.erase term) :=
  substConst_rename history.images ρ term

theorem erase_subst (history : DefinitionHistory source target)
    {context context' : Ctx Base} {type : Ty Base}
    (substitution : Subst target context context') (term : Term target context type) :
    history.erase (HOL.subst substitution term) =
      HOL.subst (fun index => history.erase (substitution index)) (history.erase term) :=
  (substConst_subst history.images substitution term).symm

/-- Each stage is constructed using the previous model and the actual body. -/
def extendModel {source target : Ty Base → Type (max u v)}
    (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source) :
    HenkinModel.{u, max u v, w} Base target :=
  match history with
  | .nil => model
  | .add prior _ body => (prior.extendModel model).definitionExtension body

/-- Incremental construction agrees with the independently expanded syntax. -/
theorem extendModel_eq_reduct (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source) :
    history.extendModel model = model.constantSubstitutionReduct history.images := by
  induction history with
  | nil => exact model.constantSubstitutionReduct_id.symm
  | add prior type body ih =>
      change (prior.extendModel model).constantSubstitutionReduct
        (DefinedConst.expansion body) = _
      rw [ih]
      exact HenkinModel.constantSubstitutionReduct_comp _ _ model

/-- Valuations use the unchanged carriers, with the model equality made explicit. -/
def extendValuation (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source) {context : Ctx Base}
    (valuation : model.Valuation context) : (history.extendModel model).Valuation context :=
  (history.extendModel_eq_reduct model).symm ▸ valuation

private theorem denote_transport {Const : Ty Base → Type (max u v)}
    {first second : HenkinModel.{u, max u v, w} Base Const}
    (equal : first = second) {context : Ctx Base} {type : Ty Base}
    (term : Term Const context type) (valuation : second.Valuation context) :
    HEq (first.denote term (equal.symm ▸ valuation)) (second.denote term valuation) := by
  cases equal
  rfl

/-- Denotation of every open term commutes with dependency expansion. -/
theorem denote_erasure (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source)
    {context : Ctx Base} {type : Ty Base} (term : Term target context type)
    (valuation : model.Valuation context) :
    HEq ((history.extendModel model).denote term (history.extendValuation model valuation))
      (model.denote (history.erase term) valuation) :=
  (denote_transport (history.extendModel_eq_reduct model) term valuation).trans
    (heq_of_eq (model.denote_substConst history.images term valuation).symm)

theorem denote_embed (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source)
    {context : Ctx Base} {type : Ty Base} (term : Term source context type)
    (valuation : model.Valuation context) :
    HEq ((history.extendModel model).denote (history.embed term)
      (history.extendValuation model valuation)) (model.denote term valuation) := by
  have preserved := history.denote_erasure model (history.embed term) valuation
  simpa only [history.erase_embed term] using preserved

theorem models_erasure (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source) (formula : ClosedFormula target) :
    (history.extendModel model).models formula ↔ model.models (history.erase formula) := by
  rw [history.extendModel_eq_reduct model]
  exact (model.models_substConst history.images formula).symm

theorem models_embed (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source) (formula : ClosedFormula source) :
    (history.extendModel model).models (history.embed formula) ↔ model.models formula := by
  rw [history.models_erasure model, history.erase_embed]

theorem fullDomains_iff (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source) :
    (history.extendModel model).FullDomains ↔ model.FullDomains := by
  rw [history.extendModel_eq_reduct model]
  exact model.constantSubstitutionReduct_fullDomains_iff history.images

theorem functionsRespectEqv_iff (history : DefinitionHistory source target)
    (model : HenkinModel.{u, max u v, w} Base source) :
    (history.extendModel model).FunctionsRespectEqv ↔ model.FunctionsRespectEqv := by
  rw [history.extendModel_eq_reduct model]
  exact model.constantSubstitutionReduct_functionsRespectEqv_iff history.images

/-- Retain supplied derivations rather than select a proof of the erased claim. -/
def eraseProof (history : DefinitionHistory source target)
    {context : Ctx Base} {assumptions : List (Formula target context)}
    {conclusion : Formula target context} (proof : ProofSyntax target assumptions conclusion) :
    ProofSyntax source (assumptions.map history.erase) (history.erase conclusion) :=
  ProofSyntax.substConst history.images proof

theorem eraseProof_nodeCount (history : DefinitionHistory source target)
    {context : Ctx Base} {assumptions : List (Formula target context)}
    {conclusion : Formula target context} (proof : ProofSyntax target assumptions conclusion) :
    (history.eraseProof proof).nodeCount = proof.nodeCount :=
  ProofSyntax.substConst_nodeCount history.images proof

theorem eraseProof_ruleTree (history : DefinitionHistory source target)
    {context : Ctx Base} {assumptions : List (Formula target context)}
    {conclusion : Formula target context} (proof : ProofSyntax target assumptions conclusion) :
    ProofSyntax.ruleTree (history.eraseProof proof).observe =
      ProofSyntax.ruleTree proof.observe :=
  ProofSyntax.substConst_ruleTree history.images proof

def append {source middle target : Ty Base → Type (max u v)}
    (first : DefinitionHistory source middle) :
    DefinitionHistory middle target → DefinitionHistory source target
  | .nil => first
  | .add prior type body => .add (append first prior) type body

theorem images_append (first : DefinitionHistory source middle)
    (second : DefinitionHistory middle target) {type : Ty Base} (constant : target type) :
    (first.append second).images constant =
      HOL.substConst first.images (second.images constant) := by
  induction second generalizing type with
  | nil => rfl
  | add prior type body ih =>
      change HOL.substConst (first.append prior).images (DefinedConst.expansion body constant) =
        HOL.substConst first.images
          (HOL.substConst prior.images (DefinedConst.expansion body constant))
      rw [substConst_comp]
      exact substConst_ext ih _

theorem erase_append (first : DefinitionHistory source middle)
    (second : DefinitionHistory middle target)
    {context : Ctx Base} {type : Ty Base} (term : Term target context type) :
    (first.append second).erase term = first.erase (second.erase term) := by
  change HOL.substConst (first.append second).images term =
    HOL.substConst first.images (HOL.substConst second.images term)
  rw [substConst_comp]
  exact substConst_ext (first.images_append second) term

theorem extendModel_append (first : DefinitionHistory source middle)
    (second : DefinitionHistory middle target)
    (model : HenkinModel.{u, max u v, w} Base source) :
    (first.append second).extendModel model = second.extendModel (first.extendModel model) := by
  induction second with
  | nil => rfl
  | add prior type body ih =>
      change ((first.append prior).extendModel model).definitionExtension body =
        (prior.extendModel (first.extendModel model)).definitionExtension body
      rw [ih]

/-! ## Instantiating a whole dependent declaration history -/

variable {Base' : Type u}

/-- The instantiated signature retains one distinct fresh symbol for each
entry. Earlier symbols remain available to later defining bodies. -/
def instanceSignature {source target : Ty Base → Type (max u v)}
    (history : DefinitionHistory source target) (substitution : Base → Ty Base')
    (source' : Ty Base' → Type (max u v)) : Ty Base' → Type (max u v) :=
  match history with
  | .nil => source'
  | .add prior type _ =>
      DefinedConst (prior.instanceSignature substitution source') (Ty.substitute substitution type)

def instanceSymbols {source target : Ty Base → Type (max u v)}
    (history : DefinitionHistory source target) (substitution : Base → Ty Base')
    {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type)) :
    ∀ {type}, target type →
      history.instanceSignature substitution source' (Ty.substitute substitution type) :=
  match history with
  | .nil => symbols
  | .add prior _ _ => DefinedConst.typeInstance substitution
      (prior.instanceSymbols substitution symbols)

/-- Instantiate each actual body against the already instantiated preceding
signature. This constructs the target history, rather than supplying a
semantic compatibility premise for it. -/
def instantiate {source target : Ty Base → Type (max u v)}
    (history : DefinitionHistory source target) (substitution : Base → Ty Base')
    {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type)) :
    DefinitionHistory source' (history.instanceSignature substitution source') :=
  match history with
  | .nil => .nil
  | .add prior type body => .add (prior.instantiate substitution symbols)
      (Ty.substitute substitution type)
      (mapTypes substitution (prior.instanceSymbols substitution symbols) body)

/-- Instantiation and inheritance agree on every old symbol, including
symbols that pass through several intervening definitions. -/
theorem instanceSymbols_embedding (history : DefinitionHistory source target)
    (substitution : Base → Ty Base') {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type))
    {type : Ty Base} (constant : source type) :
    history.instanceSymbols substitution symbols (history.embedding constant) =
      (history.instantiate substitution symbols).embedding (symbols constant) := by
  induction history with
  | nil => rfl
  | add prior type body ih => exact congrArg DefinedConst.old ih

/-- Every fresh definition, including its older dependencies, expands to
the instantiated image of its original body. The compatibility required by
general constant substitution is proved from the constructed history. -/
theorem images_instanceSymbols (history : DefinitionHistory source target)
    (substitution : Base → Ty Base') {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type))
    {type : Ty Base} (constant : target type) :
    (history.instantiate substitution symbols).images
        (history.instanceSymbols substitution symbols constant) =
      mapTypes substitution symbols (history.images constant) := by
  induction history generalizing type with
  | nil => rfl
  | add prior type body ih =>
      cases constant with
      | old constant => exact ih constant
      | defined =>
          change substConst (prior.instantiate substitution symbols).images
              (mapTypes substitution (prior.instanceSymbols substitution symbols) body) =
            mapTypes substitution symbols (substConst prior.images body)
          exact (mapTypes_substConst substitution
            (prior.instanceSymbols substitution symbols) symbols prior.images
            (prior.instantiate substitution symbols).images ih body).symm

/-- Dependency expansion and instantiation commute on every open term,
including arguments substituted beneath binders. -/
theorem erase_instantiate (history : DefinitionHistory source target)
    (substitution : Base → Ty Base') {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type))
    {context : Ctx Base} {type : Ty Base} (term : Term target context type) :
    (history.instantiate substitution symbols).erase
        (mapTypes substitution (history.instanceSymbols substitution symbols) term) =
      mapTypes substitution symbols (history.erase term) :=
  (mapTypes_substConst substitution (history.instanceSymbols substitution symbols)
    symbols history.images (history.instantiate substitution symbols).images
    (history.images_instanceSymbols substitution symbols) term).symm

/-- Old syntax reaches the same instantiated signature through either
embedding route, with its bound-variable positions retained. -/
theorem embed_instantiate (history : DefinitionHistory source target)
    (substitution : Base → Ty Base') {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type))
    {context : Ctx Base} {type : Ty Base} (term : Term source context type) :
    mapTypes substitution (history.instanceSymbols substitution symbols) (history.embed term) =
      (history.instantiate substitution symbols).embed (mapTypes substitution symbols term) := by
  induction term with
  | const constant =>
      simp only [embed, mapConst, mapTypes, history.instanceSymbols_embedding]
  | _ => simp_all only [embed, mapConst, mapTypes] <;> rfl

/-- Extending through the whole instantiated history commutes with the type
reduct. Equality includes all newly interpreted constants, not just the old
language. Full domains are needed by this particular type-reduct construction. -/
theorem extendModel_typeReduct (history : DefinitionHistory source target)
    (substitution : Base → Ty Base') {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type))
    (model : HenkinModel.{u, max u v, w} Base' source') (full : model.FullDomains) :
    history.extendModel (HenkinModel.standardTypeReduct substitution symbols model) =
      HenkinModel.standardTypeReduct substitution (history.instanceSymbols substitution symbols)
        ((history.instantiate substitution symbols).extendModel model) := by
  induction history with
  | nil => rfl
  | add prior type body ih =>
    change (prior.extendModel (HenkinModel.standardTypeReduct substitution symbols model)).definitionExtension
      body = _
    rw [ih]
    exact HenkinModel.definitionExtension_typeReduct substitution
      (prior.instanceSymbols substitution symbols)
      ((prior.instantiate substitution symbols).extendModel model)
      ((prior.instantiate substitution symbols).fullDomains_iff model |>.mpr full) body

/-- Every sentence in the extended signature has the same truth after
instantiating its entire definition history. -/
theorem models_typeReduct (history : DefinitionHistory source target)
    (substitution : Base → Ty Base') {source' : Ty Base' → Type (max u v)}
    (symbols : ∀ {type}, source type → source' (Ty.substitute substitution type))
    (model : HenkinModel.{u, max u v, w} Base' source') (full : model.FullDomains)
    (sentence : ClosedFormula target) :
    (history.extendModel (HenkinModel.standardTypeReduct substitution symbols model)).models
      sentence ↔
      ((history.instantiate substitution symbols).extendModel model).models
        (mapTypes substitution (history.instanceSymbols substitution symbols) sentence) := by
  rw [history.extendModel_typeReduct substitution symbols model full]
  exact HenkinModel.models_mapTypes substitution (history.instanceSymbols substitution symbols)
    ((history.instantiate substitution symbols).extendModel model)
    ((history.instantiate substitution symbols).fullDomains_iff model |>.mpr full) sentence

namespace Controls

abbrev Initial : Ty Unit → Type := fun _ => Empty
abbrev Parameter : Ty Unit := .base ()
abbrev First := DefinedConst Initial (Parameter ⇒ Parameter)
abbrev Second := DefinedConst First (Parameter ⇒ Parameter)

def firstBody : ClosedTerm Initial (Parameter ⇒ Parameter) := .lam (.var .vz)

/-- The second definition uses the retained first declaration twice. -/
def secondBody : ClosedTerm First (Parameter ⇒ Parameter) :=
  .lam (.app (.const .defined) (.app (.const .defined) (.var .vz)))

def twoDefinitions : DefinitionHistory Initial Second :=
  .add (.add .nil _ firstBody) _ secondBody

def repeatedBody : ClosedTerm Initial (Parameter ⇒ Parameter) :=
  .lam (.app (.lam (.var .vz)) (.app (.lam (.var .vz)) (.var .vz)))

def singleBody : ClosedTerm Initial (Parameter ⇒ Parameter) :=
  .lam (.app (.lam (.var .vz)) (.var .vz))

theorem expansion_retains_repeated_dependency :
    twoDefinitions.erase (.const .defined) = repeatedBody := rfl

abbrev FunctionInitial : Ty Unit → Type := fun _ => Empty

def functionInstance : Unit → Ty Unit := fun _ => .prop ⇒ .prop

def initialSymbols : ∀ {type}, Initial type →
    FunctionInitial (Ty.substitute functionInstance type) := fun constant => nomatch constant

/-- A parameter is replaced by a function type, while the two defining
applications remain separate beneath the new function-valued binder. -/
theorem instantiated_expansion_retains_repeated_dependency :
    (twoDefinitions.instantiate functionInstance initialSymbols).erase
        (.const (twoDefinitions.instanceSymbols functionInstance initialSymbols
          (DefinedConst.defined : Second (Parameter ⇒ Parameter)))) =
      (mapTypes functionInstance initialSymbols repeatedBody :
        ClosedTerm FunctionInitial ((.prop ⇒ .prop) ⇒ (.prop ⇒ .prop))) := by
  simpa only [mapTypes, expansion_retains_repeated_dependency] using
    twoDefinitions.erase_instantiate functionInstance initialSymbols
      (.const .defined : ClosedTerm Second (Parameter ⇒ Parameter))

/-- Removing one dependency occurrence changes the retained syntax, even
though both bodies compute the identity function extensionally. -/
theorem dependency_occurrence_cannot_be_dropped : repeatedBody ≠ singleBody := by
  intro equal
  have count : (8 : Nat) = 5 := congrArg Term.nodeCount equal
  exact (by decide : (8 : Nat) ≠ 5) count

end Controls

end DefinitionHistory

end Mettapedia.Logic.HOL
