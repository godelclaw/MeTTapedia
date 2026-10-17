import Mettapedia.OSLF.Syntax.SignatureMorphismReadback
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSubstitution
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment
import Mettapedia.OSLF.Syntax.VariablePosition
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity

/-!
# Binding signatures interpreted by declared native constructors

Source variables become native variables. Each source argument's complete
declared binding spine becomes actual native lambdas, innermost binder first.
Constructor names and source sorts are supplied by a concrete declaration
package. Formation is derived from its literal declaration lookups.

This interpretation preserves syntax and formation. Fresh constructor names
make its literal images injective and normal when declared root computation
is absent. Operational source equations and artifact execution require their
own comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace BindingSignatureEmbedding

open Mettapedia.OSLF

variable {S : Binding.Signature} {Head : Type}

/-- Names are supplied by the actual authored declaration package. Distinct
sorts or constructors need not be identified by the interpretation. -/
structure Names (S : Binding.Signature) where
  sort : S.Srt → DeclName
  operator : {sort : S.Srt} → S.Op sort → DeclName

def sortType (names : Names S) (sort : S.Srt) {n : Nat} : Tm Head n :=
  .const (names.sort sort)

/-- Source contexts list the innermost position first; native telescopes add
that position last. -/
def context (names : Names S) : (gamma : Binding.Ctx S) → Ctx Head gamma.length
  | [] => .nil
  | sort :: gamma => .snoc (context names gamma) (sortType names sort)

/-- Close precisely the source argument's declared binder spine. No source
body is hidden in a quoted or opaque literal. -/
def abstract {gamma : Binding.Ctx S} : (bound : List S.Srt) →
    Tm Head (bound ++ gamma).length → Tm Head gamma.length
  | [], body => body
  | _ :: bound, body => abstract bound (.lam body)

mutual

def encode (names : Names S) : {gamma : Binding.Ctx S} → {sort : S.Srt} →
    Binding.Term S gamma sort → Tm Head gamma.length
  | _, _, .var position => .var (Binding.varIdx position)
  | _, _, .op operator arguments =>
      applyArguments names (.const (names.operator operator)) arguments

def applyArguments (names : Names S) :
    {gamma : Binding.Ctx S} → {arguments : List (List S.Srt × S.Srt)} →
    Tm Head gamma.length → Binding.Args S arguments gamma → Tm Head gamma.length
  | _, _, head, .nil => head
  | _, _, head, .cons (bs := bound) body rest =>
      applyArguments names (.app head (abstract bound (encode names body))) rest

end

/-- Erase sort indices while retaining the exact positional position map. -/
def encodeRen : {gamma delta : Binding.Ctx S} → Binding.Ren S gamma delta →
    Ren gamma.length delta.length
  | [], _, _, index => Fin.elim0 index
  | sort :: _, _, action, index =>
      Fin.cases (Binding.varIdx (action sort .zero))
        (encodeRen (fun other position => action other (.succ position))) index

theorem encodeRen_variable : ∀ {gamma delta : Binding.Ctx S}
    (action : Binding.Ren S gamma delta) {sort : S.Srt}
    (position : Binding.Var gamma sort),
    encodeRen action (Binding.varIdx position) = Binding.varIdx (action sort position)
  | _, _, _, _, .zero => rfl
  | _, _, action, _, .succ position =>
      encodeRen_variable (fun sort index => action sort (.succ index)) position

/-- Lift the actual native position map under a complete source spine. -/
def liftRenSpine {gamma delta : Binding.Ctx S}
    (action : Ren gamma.length delta.length) : (bound : List S.Srt) →
    Ren (bound ++ gamma).length (bound ++ delta).length
  | [] => action
  | _ :: bound => liftRen (liftRenSpine action bound)

theorem encodeRen_lift {gamma delta : Binding.Ctx S}
    (action : Binding.Ren S gamma delta) (bound : List S.Srt) :
    encodeRen (Binding.liftRen action bound) = liftRenSpine (encodeRen action) bound := by
  induction bound with
  | nil => rfl
  | cons sort bound inductionHypothesis =>
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · let position := Binding.varOfIdx (S := S) (bound ++ gamma) prior
        have source := encodeRen_variable (Binding.liftRen action (sort :: bound))
          (Binding.Var.succ position)
        have target := encodeRen_variable (Binding.liftRen action bound) position
        have index : Binding.varIdx position = prior :=
          Binding.varIdx_varOfIdx _ _
        simp only [Binding.varIdx, Binding.liftRen, index] at source
        rw [index, inductionHypothesis] at target
        exact source.trans (congrArg Fin.succ target.symm)

theorem rename_abstract {gamma delta : Binding.Ctx S}
    (action : Ren gamma.length delta.length) (bound : List S.Srt)
    (body : Tm Head (bound ++ gamma).length) :
    rename action (abstract bound body) =
      abstract bound (rename (liftRenSpine action bound) body) := by
  induction bound with
  | nil => rfl
  | cons sort bound inductionHypothesis =>
      exact inductionHypothesis (.lam body)

mutual

theorem encode_rename (names : Names S) :
    ∀ {gamma delta : Binding.Ctx S} {sort : S.Srt}
      (action : Binding.Ren S gamma delta) (term : Binding.Term S gamma sort),
      rename (encodeRen action) (encode (Head := Head) names term) =
        encode names (Binding.rename action term)
  | _, _, _, action, .var position => by
      simp only [encode, rename, Binding.rename, encodeRen_variable]
  | _, _, _, action, .op operator arguments =>
      applyArguments_rename names action (.const (names.operator operator)) arguments

theorem applyArguments_rename (names : Names S) :
    ∀ {gamma delta : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (action : Binding.Ren S gamma delta) (head : Tm Head gamma.length)
      (values : Binding.Args S arguments gamma),
      rename (encodeRen action) (applyArguments names head values) =
        applyArguments names (rename (encodeRen action) head)
          (Binding.renameArgs action values)
  | _, _, _, _, _, .nil => rfl
  | _, _, _, action, head, .cons (bs := bound) body rest => by
      simp only [applyArguments, Binding.renameArgs,
        applyArguments_rename names action, rename, rename_abstract,
        ← encodeRen_lift action bound, encode_rename names]

end

theorem encodeRen_weaken {gamma : Binding.Ctx S} {sort : S.Srt} :
    encodeRen (fun _ position => Binding.Var.succ position :
      Binding.Ren S gamma (sort :: gamma)) = wk := by
  funext index
  have law := encodeRen_variable
    (fun _ position => Binding.Var.succ position : Binding.Ren S gamma (sort :: gamma))
    (Binding.varOfIdx (S := S) gamma index)
  simpa only [Binding.varIdx, Binding.varIdx_varOfIdx, wk] using law

def encodeSub (names : Names S) :
    {gamma delta : Binding.Ctx S} → Binding.Sub S gamma delta →
      Sub Head gamma.length delta.length
  | [], _, _, index => Fin.elim0 index
  | sort :: _, _, action, index =>
      Fin.cases (encode names (action sort .zero))
        (encodeSub names (fun other position => action other (.succ position))) index

theorem encodeSub_variable (names : Names S) : ∀ {gamma delta : Binding.Ctx S}
    (action : Binding.Sub S gamma delta) {sort : S.Srt}
    (position : Binding.Var gamma sort),
    encodeSub (Head := Head) names action (Binding.varIdx position) =
      encode names (action sort position)
  | _, _, _, _, .zero => rfl
  | _, _, action, _, .succ position =>
      encodeSub_variable names (fun sort index => action sort (.succ index)) position

def liftSubSpine {gamma delta : Binding.Ctx S}
    (action : Sub Head gamma.length delta.length) : (bound : List S.Srt) →
    Sub Head (bound ++ gamma).length (bound ++ delta).length
  | [] => action
  | _ :: bound => liftSub (liftSubSpine action bound)

theorem encodeSub_lift (names : Names S) {gamma delta : Binding.Ctx S}
    (action : Binding.Sub S gamma delta) (bound : List S.Srt) :
    encodeSub (Head := Head) names (Binding.liftSub action bound) =
      liftSubSpine (encodeSub names action) bound := by
  induction bound with
  | nil => rfl
  | cons sort bound inductionHypothesis =>
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · let position := Binding.varOfIdx (S := S) (bound ++ gamma) prior
        have source := encodeSub_variable (Head := Head) names
          (Binding.liftSub action (sort :: bound)) (Binding.Var.succ position)
        have target := encodeSub_variable (Head := Head) names
          (Binding.liftSub action bound) position
        have index : Binding.varIdx position = prior := Binding.varIdx_varOfIdx _ _
        simp only [Binding.varIdx, Binding.liftSub, index] at source
        rw [Binding.weaken, ← encode_rename, encodeRen_weaken] at source
        rw [index, inductionHypothesis] at target
        exact source.trans (congrArg (rename wk) target.symm)

theorem subst_abstract {gamma delta : Binding.Ctx S}
    (action : Sub Head gamma.length delta.length) (bound : List S.Srt)
    (body : Tm Head (bound ++ gamma).length) :
    subst action (abstract bound body) =
      abstract bound (subst (liftSubSpine action bound) body) := by
  induction bound with
  | nil => rfl
  | cons sort bound inductionHypothesis =>
      exact inductionHypothesis (.lam body)

mutual

theorem encode_substitution (names : Names S) :
    ∀ {gamma delta : Binding.Ctx S} {sort : S.Srt}
      (action : Binding.Sub S gamma delta) (term : Binding.Term S gamma sort),
      subst (encodeSub names action) (encode (Head := Head) names term) =
        encode names (Binding.bind action term)
  | _, _, _, action, .var position => by
      simp only [encode, subst, Binding.bind, encodeSub_variable]
  | _, _, _, action, .op operator arguments =>
      applyArguments_substitution names action (.const (names.operator operator)) arguments

theorem applyArguments_substitution (names : Names S) :
    ∀ {gamma delta : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (action : Binding.Sub S gamma delta) (head : Tm Head gamma.length)
      (values : Binding.Args S arguments gamma),
      subst (encodeSub names action) (applyArguments names head values) =
        applyArguments names (subst (encodeSub names action) head)
          (Binding.bindArgs action values)
  | _, _, _, _, _, .nil => rfl
  | _, _, _, action, head, .cons (bs := bound) body rest => by
      simp only [applyArguments, Binding.bindArgs,
        applyArguments_substitution names action, subst, subst_abstract,
        ← encodeSub_lift names action bound, encode_substitution names]

end

/-! ## Constructor types and their actual declaration requirements -/

def closedArrow (domain codomain : Tm Head 0) : Tm Head 0 :=
  .pi domain (liftClosed codomain)

@[simp] theorem liftClosed_closedArrow (domain codomain : Tm Head 0) {n : Nat} :
    (liftClosed (closedArrow domain codomain) : Tm Head n) =
      .pi (liftClosed domain) (liftClosed codomain) := by
  simp only [closedArrow, liftClosed, rename]
  exact congrArg (Tm.pi _) (rename_liftClosed _ codomain)

/-- Abstracting an innermost-first source spine produces the corresponding
outermost-first native function telescope. -/
def telescopeType (names : Names S) : List S.Srt → Tm Head 0 → Tm Head 0
  | [], result => result
  | sort :: bound, result =>
      telescopeType names bound (closedArrow (sortType names sort) result)

def bindingType (names : Names S) (bound : List S.Srt) (result : S.Srt) : Tm Head 0 :=
  telescopeType names bound (sortType names result)

def argumentsType (names : Names S) :
    List (List S.Srt × S.Srt) → Tm Head 0 → Tm Head 0
  | [], result => result
  | (bound, sort) :: rest, result =>
      closedArrow (bindingType names bound sort) (argumentsType names rest result)

def operatorType (names : Names S) {sort : S.Srt} (operator : S.Op sort) : Tm Head 0 :=
  argumentsType names (S.arity operator) (sortType names sort)

/-- Universe rules shared by total and finitely supported sort declarations. -/
structure SortUniverse (rules : Rules Head) where
  typeUniverse : Head
  above : Head
  joined : Head
  universeTyped : rules.headTyping typeUniverse above
  universeIs : rules.isUniverse typeUniverse
  aboveIs : rules.isUniverse above
  joinSelf : rules.join typeUniverse typeUniverse joined
  collapseSelf : rules.cumulative joined typeUniverse

/-- Literal lookups for every source sort. Finite packages over infinite sort
families use `SupportedSortRealization` instead. -/
structure SortRealization (names : Names S) (rules : Rules Head) where
  typeUniverse : Head
  above : Head
  joined : Head
  universeTyped : rules.headTyping typeUniverse above
  universeIs : rules.isUniverse typeUniverse
  aboveIs : rules.isUniverse above
  joinSelf : rules.join typeUniverse typeUniverse joined
  collapseSelf : rules.cumulative joined typeUniverse
  sortLookup : ∀ sort,
    rules.constantType (names.sort sort) = some (.head typeUniverse)

/-- Forget the total lookup policy without changing the established
realization's declaration layout. -/
def SortRealization.toSortUniverse {names : Names S} {rules : Rules Head}
    (realization : SortRealization names rules) : SortUniverse rules where
  typeUniverse := realization.typeUniverse
  above := realization.above
  joined := realization.joined
  universeTyped := realization.universeTyped
  universeIs := realization.universeIs
  aboveIs := realization.aboveIs
  joinSelf := realization.joinSelf
  collapseSelf := realization.collapseSelf

/-- A complete constructor interpretation adds the actual operator lookups to
the sort declarations. -/
structure Realization (names : Names S) (rules : Rules Head)
    extends SortRealization names rules where
  operatorLookup : ∀ {sort} (operator : S.Op sort),
    rules.constantType (names.operator operator) = some (operatorType names operator)

/-- Only the named sorts in the selected support require declarations. The
support describes primitive lookup, not an assumed preservation theorem. -/
structure SupportedSortRealization (names : Names S) (rules : Rules Head)
    (support : S.Srt → Prop) extends SortUniverse rules where
  sortLookup : ∀ sort, support sort →
    rules.constantType (names.sort sort) = some (.head typeUniverse)

def SortRealization.onSupport {names : Names S} {rules : Rules Head}
    (realization : SortRealization names rules) (support : S.Srt → Prop) :
    SupportedSortRealization names rules support :=
  { realization.toSortUniverse with
    sortLookup := fun sort _ => realization.sortLookup sort }

def aritySorts : List (List S.Srt × S.Srt) → List S.Srt
  | [] => []
  | (bound, sort) :: rest => bound ++ sort :: aritySorts rest

mutual

/-- The finite sort support retains each result and complete binder spine,
including sorts of operators occurring inside arguments. -/
def usedSorts : {gamma : Binding.Ctx S} → {sort : S.Srt} →
    Binding.Term S gamma sort → List S.Srt
  | _, sort, .var _ => [sort]
  | _, sort, .op _ arguments => sort :: usedArgumentSorts arguments

def usedArgumentSorts : {gamma : Binding.Ctx S} →
    {arguments : List (List S.Srt × S.Srt)} →
    Binding.Args S arguments gamma → List S.Srt
  | _, _, .nil => []
  | _, _, .cons (bs := bound) (s := sort) body rest =>
      bound ++ sort :: (usedSorts body ++ usedArgumentSorts rest)

end

theorem aritySorts_subset_usedArgumentSorts :
    ∀ {gamma : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (values : Binding.Args S arguments gamma) {sort : S.Srt},
      sort ∈ aritySorts arguments → sort ∈ usedArgumentSorts values
  | _, _, .nil, _, impossible => False.elim (List.not_mem_nil impossible)
  | _, _, .cons (bs := bound) (s := result) body rest, sort, member => by
      rcases List.mem_append.mp member with boundMember | member
      · exact List.mem_append_left _ boundMember
      · rcases List.mem_cons.mp member with same | member
        · exact List.mem_append_right _ (List.mem_cons.mpr (.inl same))
        · exact List.mem_append_right _ (List.mem_cons.mpr (.inr
            (List.mem_append_right _ (aritySorts_subset_usedArgumentSorts rest member))))

namespace SortRealization

variable {names : Names S}

theorem context_lookup : ∀ {gamma : Binding.Ctx S} {sort : S.Srt}
    (position : Binding.Var gamma sort),
    Ctx.lookup (context (Head := Head) names gamma) (Binding.varIdx position) =
      sortType names sort
  | _, _, .zero => rfl
  | _, _, .succ position => by
      simp only [context, Binding.varIdx, Ctx.lookup_snoc_succ, context_lookup,
        sortType, rename]

end SortRealization

namespace SupportedSortRealization

open FormationSensitive

variable {names : Names S} {rules : Rules Head} {support : S.Srt → Prop}

theorem sortType_formed (realization : SupportedSortRealization names rules support)
    {n : Nat} (gamma : Ctx Head n) (sort : S.Srt) (covered : support sort) :
    Typing rules gamma (sortType names sort) (.head realization.typeUniverse) :=
  .const (realization.sortLookup sort covered)
    (.headType realization.universeTyped) realization.aboveIs

private theorem closedArrow_formed
    (realization : SupportedSortRealization names rules support)
    {domain codomain : Tm Head 0}
    (domainFormed : Typing rules .nil domain (.head realization.typeUniverse))
    (codomainFormed : Typing rules .nil codomain (.head realization.typeUniverse)) :
    Typing rules .nil (closedArrow domain codomain) (.head realization.typeUniverse) := by
  exact .cumul
    (.piForm domainFormed realization.universeIs
      (FormationCheckedTelescopePrograms.liftClosed_typing codomainFormed (.snoc .nil domain))
      realization.universeIs realization.joinSelf) realization.collapseSelf

theorem telescopeType_formed
    (realization : SupportedSortRealization names rules support)
    (bound : List S.Srt) (covered : ∀ sort ∈ bound, support sort) {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse)) :
    Typing rules .nil (telescopeType names bound result) (.head realization.typeUniverse) := by
  induction bound generalizing result with
  | nil => exact formed
  | cons sort bound inductionHypothesis =>
      exact inductionHypothesis (fun s member => covered s (List.mem_cons_of_mem _ member))
        (realization.closedArrow_formed
          (realization.sortType_formed .nil sort (covered sort List.mem_cons_self)) formed)

theorem bindingType_formed
    (realization : SupportedSortRealization names rules support)
    (bound : List S.Srt) (covered : ∀ sort ∈ bound, support sort)
    (sort : S.Srt) (resultCovered : support sort) :
    Typing rules .nil (bindingType names bound sort) (.head realization.typeUniverse) :=
  realization.telescopeType_formed bound covered
    (realization.sortType_formed .nil sort resultCovered)

theorem argumentsType_formed
    (realization : SupportedSortRealization names rules support)
    (arguments : List (List S.Srt × S.Srt))
    (covered : ∀ sort ∈ aritySorts arguments, support sort) {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse)) :
    Typing rules .nil (argumentsType names arguments result) (.head realization.typeUniverse) := by
  induction arguments with
  | nil => exact formed
  | cons argument rest inductionHypothesis =>
      exact realization.closedArrow_formed
        (realization.bindingType_formed argument.1
          (fun sort member => covered sort (List.mem_append_left _ member)) argument.2
          (covered argument.2 (List.mem_append_right _ List.mem_cons_self)))
        (inductionHypothesis (fun sort member => covered sort
          (List.mem_append_right _ (List.mem_cons_of_mem _ member))))

theorem operatorType_formed
    (realization : SupportedSortRealization names rules support)
    {sort : S.Srt} (operator : S.Op sort) (resultCovered : support sort)
    (covered : ∀ s ∈ aritySorts (S.arity operator), support s) :
    Typing rules .nil (operatorType names operator) (.head realization.typeUniverse) :=
  realization.argumentsType_formed (S.arity operator) covered
    (realization.sortType_formed .nil sort resultCovered)

theorem context_formed (realization : SupportedSortRealization names rules support)
    (gamma : Binding.Ctx S) (covered : ∀ sort ∈ gamma, support sort) :
    ContextFormation rules (context names gamma) := by
  induction gamma with
  | nil => exact .nil
  | cons sort gamma inductionHypothesis =>
      exact .snoc
        (inductionHypothesis (fun s member => covered s (List.mem_cons_of_mem _ member)))
        (realization.sortType_formed _ sort (covered sort List.mem_cons_self)) realization.universeIs

theorem abstract_typing (realization : SupportedSortRealization names rules support)
    {gamma : Binding.Ctx S} (bound : List S.Srt)
    (covered : ∀ sort ∈ bound, support sort) {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse))
    (body : Tm Head (bound ++ gamma).length)
    (typed : Typing rules (context names (bound ++ gamma)) body (liftClosed result)) :
    Typing rules (context names gamma) (abstract bound body)
      (liftClosed (telescopeType names bound result)) := by
  induction bound generalizing result with
  | nil => exact typed
  | cons sort bound inductionHypothesis =>
      have functionType := realization.closedArrow_formed
        (realization.sortType_formed .nil sort (covered sort List.mem_cons_self)) formed
      have functionFormed := FormationCheckedTelescopePrograms.liftClosed_typing functionType
        (context names (bound ++ gamma))
      rw [liftClosed_closedArrow] at functionFormed
      have function := Typing.lamIntro functionFormed realization.universeIs typed
      apply inductionHypothesis
        (fun s member => covered s (List.mem_cons_of_mem _ member)) functionType (.lam body)
      simpa only [liftClosed_closedArrow] using function

end SupportedSortRealization

namespace SortRealization

open FormationSensitive

variable {names : Names S} {rules : Rules Head}

theorem sortType_formed (realization : SortRealization names rules)
    {n : Nat} (gamma : Ctx Head n) (sort : S.Srt) :
    Typing rules gamma (sortType names sort) (.head realization.typeUniverse) :=
  (realization.onSupport (fun _ => True)).sortType_formed gamma sort True.intro

theorem telescopeType_formed (realization : SortRealization names rules)
    (bound : List S.Srt) {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse)) :
    Typing rules .nil (telescopeType names bound result) (.head realization.typeUniverse) :=
  (realization.onSupport (fun _ => True)).telescopeType_formed bound (fun _ _ => True.intro) formed

theorem bindingType_formed (realization : SortRealization names rules)
    (bound : List S.Srt) (sort : S.Srt) :
    Typing rules .nil (bindingType names bound sort) (.head realization.typeUniverse) :=
  (realization.onSupport (fun _ => True)).bindingType_formed bound (fun _ _ => True.intro)
    sort True.intro

theorem argumentsType_formed (realization : SortRealization names rules)
    (arguments : List (List S.Srt × S.Srt)) {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse)) :
    Typing rules .nil (argumentsType names arguments result) (.head realization.typeUniverse) :=
  (realization.onSupport (fun _ => True)).argumentsType_formed arguments
    (fun _ _ => True.intro) formed

theorem operatorType_formed (realization : SortRealization names rules)
    {sort : S.Srt} (operator : S.Op sort) :
    Typing rules .nil (operatorType names operator) (.head realization.typeUniverse) :=
  (realization.onSupport (fun _ => True)).operatorType_formed operator True.intro
    (fun _ _ => True.intro)

theorem context_formed (realization : SortRealization names rules) (gamma : Binding.Ctx S) :
    ContextFormation rules (context names gamma) :=
  (realization.onSupport (fun _ => True)).context_formed gamma (fun _ _ => True.intro)

theorem abstract_typing (realization : SortRealization names rules)
    {gamma : Binding.Ctx S} (bound : List S.Srt) {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse))
    (body : Tm Head (bound ++ gamma).length)
    (typed : Typing rules (context names (bound ++ gamma)) body (liftClosed result)) :
    Typing rules (context names gamma) (abstract bound body)
      (liftClosed (telescopeType names bound result)) :=
  (realization.onSupport (fun _ => True)).abstract_typing bound
    (fun _ _ => True.intro) formed body typed

end SortRealization

/- Formation support records literal declaration lookup at every constructor
occurrence. It permits finite packages to install precisely their used heads. -/
mutual

inductive Installed (names : Names S) (rules : Rules Head) :
    {gamma : Binding.Ctx S} → {sort : S.Srt} → Binding.Term S gamma sort → Prop where
  | var {gamma : Binding.Ctx S} {sort : S.Srt} (position : Binding.Var gamma sort) :
      Installed names rules (.var position)
  | op {gamma : Binding.Ctx S} {sort : S.Srt} (operator : S.Op sort)
      (arguments : Binding.Args S (S.arity operator) gamma)
      (known : rules.constantType (names.operator operator) =
        some (operatorType names operator))
      (children : InstalledArgs names rules arguments) :
      Installed names rules (.op operator arguments)

inductive InstalledArgs (names : Names S) (rules : Rules Head) :
    {gamma : Binding.Ctx S} → {arguments : List (List S.Srt × S.Srt)} →
      Binding.Args S arguments gamma → Prop where
  | nil {gamma : Binding.Ctx S} : InstalledArgs names rules (.nil (Γ := gamma))
  | cons {gamma : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      {bound : List S.Srt} {sort : S.Srt}
      {body : Binding.Term S (bound ++ gamma) sort}
      {rest : Binding.Args S arguments gamma}
      (head : Installed names rules body) (tail : InstalledArgs names rules rest) :
      InstalledArgs names rules (.cons body rest)

end
namespace SupportedSortRealization

open FormationSensitive

variable {names : Names S} {rules : Rules Head} {support : S.Srt → Prop}

mutual

theorem encode_typing (realization : SupportedSortRealization names rules support) :
    ∀ {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort),
      Installed names rules term → (∀ s ∈ usedSorts term, support s) →
      Typing rules (context names gamma) (encode names term) (sortType names sort)
  | gamma, _, .var position, .var _, _ => by
      simpa only [encode, SortRealization.context_lookup] using
        Typing.var (R := rules) (Γ := context names gamma) (Binding.varIdx position)
  | gamma, sort, .op operator arguments, .op _ _ known children, covered => by
      have resultCovered := covered sort List.mem_cons_self
      have argsCovered : ∀ s ∈ usedArgumentSorts arguments, support s :=
        fun s member => covered s (List.mem_cons_of_mem _ member)
      have constructor := Typing.const (Γ := context names gamma) known
        (realization.operatorType_formed operator resultCovered
          (fun s member => argsCovered s (aritySorts_subset_usedArgumentSorts arguments member)))
        realization.universeIs
      exact applyArguments_typing realization arguments children argsCovered
        (realization.sortType_formed .nil sort resultCovered) constructor

theorem applyArguments_typing (realization : SupportedSortRealization names rules support) :
    ∀ {gamma : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (values : Binding.Args S arguments gamma), InstalledArgs names rules values →
      (∀ s ∈ usedArgumentSorts values, support s) → ∀ {result : Tm Head 0},
      Typing rules .nil result (.head realization.typeUniverse) →
      ∀ {head : Tm Head gamma.length},
      Typing rules (context names gamma) head
          (liftClosed (argumentsType names arguments result)) →
        Typing rules (context names gamma) (applyArguments names head values) (liftClosed result)
  | _, _, .nil, .nil, _, _, _, _, typed => typed
  | _, _, .cons (bs := bound) (s := sort) body rest, .cons headInstalled tailInstalled,
      covered, result, formed, head, typed => by
      have boundCovered : ∀ s ∈ bound, support s :=
        fun s member => covered s (List.mem_append_left _ member)
      have sortCovered := covered sort (List.mem_append_right _ List.mem_cons_self)
      have bodyCovered : ∀ s ∈ usedSorts body, support s := fun s member =>
        covered s (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_append_left _ member)))
      have restCovered : ∀ s ∈ usedArgumentSorts rest, support s := fun s member =>
        covered s (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
      have bodyTyped := realization.abstract_typing bound boundCovered
        (realization.sortType_formed .nil sort sortCovered) (encode names body)
        (encode_typing realization body headInstalled bodyCovered)
      have functionTyped := typed
      change Typing rules _ head (liftClosed (closedArrow _ _)) at functionTyped
      rw [liftClosed_closedArrow] at functionTyped
      have applied := Typing.appElim functionTyped bodyTyped
      apply applyArguments_typing realization rest tailInstalled restCovered formed
      simpa only [inst0, subst_liftClosed] using applied

end

theorem encode_judgment (realization : SupportedSortRealization names rules support)
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort)
    (installed : Installed names rules term)
    (contextCovered : ∀ s ∈ gamma, support s)
    (termCovered : ∀ s ∈ usedSorts term, support s) :
    Judgment rules (context names gamma) (encode names term) (sortType names sort) :=
  ⟨realization.context_formed gamma contextCovered,
    realization.encode_typing term installed termCovered⟩

end SupportedSortRealization

namespace SortRealization

open FormationSensitive

variable {names : Names S} {rules : Rules Head}

theorem encode_typing (realization : SortRealization names rules)
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort)
    (installed : Installed names rules term) :
    Typing rules (context names gamma) (encode names term) (sortType names sort) :=
  (realization.onSupport (fun _ => True)).encode_typing term installed (fun _ _ => True.intro)

theorem applyArguments_typing (realization : SortRealization names rules)
    {gamma : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
    (values : Binding.Args S arguments gamma) (installed : InstalledArgs names rules values)
    {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse))
    {head : Tm Head gamma.length}
    (typed : Typing rules (context names gamma) head
      (liftClosed (argumentsType names arguments result))) :
    Typing rules (context names gamma) (applyArguments names head values) (liftClosed result) :=
  (realization.onSupport (fun _ => True)).applyArguments_typing values installed
    (fun _ _ => True.intro) formed typed

theorem encode_judgment (realization : SortRealization names rules)
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort)
    (installed : Installed names rules term) :
    Judgment rules (context names gamma) (encode names term) (sortType names sort) :=
  (realization.onSupport (fun _ => True)).encode_judgment term installed
    (fun _ _ => True.intro) (fun _ _ => True.intro)

end SortRealization


namespace Realization

variable {names : Names S} {rules : Rules Head}

mutual

theorem installed (realization : Realization names rules) :
    ∀ {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort),
      Installed names rules term
  | _, _, .var position => .var position
  | _, _, .op operator arguments =>
      .op operator arguments (realization.operatorLookup operator)
        (installedArgs realization arguments)

theorem installedArgs (realization : Realization names rules) :
    ∀ {gamma : Binding.Ctx S} {arguments : List (List S.Srt × S.Srt)}
      (values : Binding.Args S arguments gamma), InstalledArgs names rules values
  | _, _, .nil => .nil
  | _, _, .cons body rest =>
      .cons (installed realization body) (installedArgs realization rest)

end

theorem encode_typing (realization : Realization names rules)
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort) :
    FormationSensitive.Typing rules (context names gamma)
      (encode names term) (sortType names sort) :=
  realization.toSortRealization.encode_typing term (realization.installed term)

theorem encode_judgment (realization : Realization names rules)
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort) :
    FormationSensitive.Judgment rules (context names gamma)
      (encode names term) (sortType names sort) :=
  realization.toSortRealization.encode_judgment term (realization.installed term)

end Realization

open TelescopeAbstraction

/-- A metavariable occurrence is an actual native program: abstract its
dependency and ambient context, then apply the submitted values in telescope
order. The body is neither pre-instantiated nor stored as a syntax literal. -/
def contextualApplication (names : Names S) {M : List (Binding.MetaArity S)}
    {gamma delta : Binding.Ctx S} (body : Binding.ContextualAssignment S M gamma)
    (index : Fin M.length) (arguments : Binding.Sub S (M.get index).1 delta)
    (ambient : Binding.Sub S gamma delta) : Tm Head delta.length :=
  applyClosed (context names ((M.get index).1 ++ gamma))
    (encodeSub names (Binding.ContextualAssignment.joinSub arguments ambient))
    (liftClosed (closeTerm (context names ((M.get index).1 ++ gamma))
      (encode names (body index))))

theorem contextualApplication_beta (names : Names S) {M : List (Binding.MetaArity S)}
    {gamma delta : Binding.Ctx S} (body : Binding.ContextualAssignment S M gamma)
    (index : Fin M.length) (arguments : Binding.Sub S (M.get index).1 delta)
    (ambient : Binding.Sub S gamma delta) :
    BetaSteps (Head := Head) (contextualApplication names body index arguments ambient)
      (encode names (Binding.ContextualAssignment.apply body index arguments ambient)) := by
  simpa only [contextualApplication, encode_substitution, Binding.ContextualAssignment.apply]
    using applyClosed_beta (context names ((M.get index).1 ++ gamma))
      (encodeSub names (Binding.ContextualAssignment.joinSub arguments ambient))
      (encode names (body index))

/-- Emit explicit finite evidence for the same native metavariable program. -/
def contextualApplicationCode (names : Names S) {M : List (Binding.MetaArity S)}
    {gamma delta : Binding.Ctx S} (body : Binding.ContextualAssignment S M gamma)
    (index : Fin M.length) (arguments : Binding.Sub S (M.get index).1 delta)
    (ambient : Binding.Sub S gamma delta) :
    StructuralConversionCode.Code Head (fun _ => Empty) delta.length :=
  FormationCheckedTelescopePrograms.applicationCode
    (context names ((M.get index).1 ++ gamma))
    (encodeSub names (Binding.ContextualAssignment.joinSub arguments ambient))
    (encode names (body index))

theorem contextualApplicationCode_checked [DecidableEq Head]
    (names : Names S) {M : List (Binding.MetaArity S)}
    {gamma delta : Binding.Ctx S} (body : Binding.ContextualAssignment S M gamma)
    (index : Fin M.length) (arguments : Binding.Sub S (M.get index).1 delta)
    (ambient : Binding.Sub S gamma delta) :
    (contextualApplicationCode (Head := Head) names body index arguments ambient).check
      (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (contextualApplication names body index arguments ambient)
      (encode names (Binding.ContextualAssignment.apply body index arguments ambient)) = true := by
  simpa only [contextualApplicationCode, contextualApplication, encode_substitution,
    Binding.ContextualAssignment.apply] using
    FormationCheckedTelescopePrograms.applicationCode_checked
      (context names ((M.get index).1 ++ gamma))
      (encodeSub names (Binding.ContextualAssignment.joinSub arguments ambient))
      (encode names (body index))

/-- Only the selected beta occurrences are counted here. Code construction,
copied payload storage and executable decoding have separate resource costs. -/
theorem contextualApplicationCode_stepCount
    (names : Names S) {M : List (Binding.MetaArity S)}
    {gamma delta : Binding.Ctx S} (body : Binding.ContextualAssignment S M gamma)
    (index : Fin M.length) (arguments : Binding.Sub S (M.get index).1 delta)
    (ambient : Binding.Sub S gamma delta) :
    (contextualApplicationCode (Head := Head) names body index arguments ambient).stepCount =
      (M.get index).1.length + gamma.length := by
  simp only [contextualApplicationCode,
    FormationCheckedTelescopePrograms.applicationCode_stepCount, List.length_append]

namespace SortRealization

open FormationSensitive

variable {names : Names S} {rules : Rules Head}

/-- Actual declaration lookup for each supplied value earns the existing
formation-sensitive context morphism. -/
theorem encodeSub_typed (realization : SortRealization names rules)
    {gamma delta : Binding.Ctx S} (action : Binding.Sub S gamma delta)
    (installed : ∀ sort position, Installed names rules (action sort position)) :
    FormationSensitive.CtxMor rules (context names gamma) (context names delta)
      (encodeSub names action) := by
  intro index
  let position := Binding.varOfIdx (S := S) gamma index
  have encoded := realization.encode_typing (action _ position) (installed _ position)
  have indexLaw : Binding.varIdx position = index := Binding.varIdx_varOfIdx _ _
  have substitutionLaw := encodeSub_variable (Head := Head) names action position
  have lookupLaw := context_lookup (Head := Head) (names := names) position
  rw [indexLaw] at substitutionLaw lookupLaw
  simpa only [substitutionLaw, lookupLaw, sortType, subst] using encoded

/-- All source sorts live in the installed universe. Its actual self-join
and cumulativity suffice to close these source telescopes; no general
normalization or arbitrary universe-join oracle is required. -/
theorem closeTerm_typing (realization : SortRealization names rules)
    {gamma : Binding.Ctx S} {result : Tm Head 0}
    (formed : Typing rules .nil result (.head realization.typeUniverse))
    (body : Tm Head gamma.length)
    (typed : Typing rules (context names gamma) body (liftClosed result)) :
    Typing rules .nil (closeTerm (context names gamma) body)
      (closeType (context names gamma) (liftClosed result)) := by
  induction gamma generalizing result with
  | nil => simpa only [context, closeTerm, closeType] using typed
  | cons sort gamma ih =>
      have functionFormed := realization.telescopeType_formed [sort] formed
      change Typing rules .nil (closedArrow (sortType names sort) result)
        (.head realization.typeUniverse) at functionFormed
      have inContext := functionFormed.renameTyping
        (Δ := context names gamma) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
      change Typing rules (context names gamma)
        (liftClosed (closedArrow (sortType names sort) result))
        (.head realization.typeUniverse) at inContext
      rw [liftClosed_closedArrow] at inContext
      have functionTyped := Typing.lamIntro inContext realization.universeIs typed
      have closed := ih functionFormed (.lam body)
        (by simpa only [liftClosed_closedArrow] using functionTyped)
      rw [liftClosed_closedArrow] at closed
      simpa only [context, closeTerm, closeType, sortType,
        liftClosed, rename] using closed

/-- Compiled arguments may themselves still contain computation. Their
actual refined context morphism types the closed source body application
before any reduction; no subject-expansion principle is assumed. -/
theorem applyClosed_judgment (realization : SortRealization names rules)
    {gamma : Binding.Ctx S} {sort : S.Srt} (body : Binding.Term S gamma sort)
    (installed : Installed names rules body) {m : Nat} {target : Ctx Head m}
    (targetFormed : ContextFormation rules target) (sigma : Sub Head gamma.length m)
    (valuesTyped : FormationSensitive.CtxMor rules (context names gamma) target sigma) :
    Judgment rules target
      (applyClosed (context names gamma) sigma
        (liftClosed (closeTerm (context names gamma) (encode names body))))
      (sortType names sort) := by
  have closed := realization.closeTerm_typing
    (realization.sortType_formed .nil sort) _ (realization.encode_typing body installed)
  have lifted := closed.renameTyping
    (Δ := target) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
  refine ⟨targetFormed, ?_⟩
  simpa only [sortType, subst_liftClosed, liftClosed, rename, subst] using
    FormationCheckedTelescopePrograms.apply_typed valuesTyped lifted

/-- A submitted body and substitution retain their declaration authority
through both the native application and its computed source value. -/
theorem contextualApplication_judgments (realization : SortRealization names rules)
    {M : List (Binding.MetaArity S)} {gamma delta : Binding.Ctx S}
    (body : Binding.ContextualAssignment S M gamma) (index : Fin M.length)
    (arguments : Binding.Sub S (M.get index).1 delta) (ambient : Binding.Sub S gamma delta)
    (bodyInstalled : Installed names rules (body index))
    (valuesInstalled : ∀ sort position, Installed names rules
      (Binding.ContextualAssignment.joinSub arguments ambient sort position)) :
    Judgment rules (context names delta) (contextualApplication names body index arguments ambient)
        (sortType names (M.get index).2) ∧
      Judgment rules (context names delta)
        (encode names (Binding.ContextualAssignment.apply body index arguments ambient))
        (sortType names (M.get index).2) := by
  let action := Binding.ContextualAssignment.joinSub arguments ambient
  have source := realization.encode_judgment (body index) bodyInstalled
  have substitutionTyped := realization.encodeSub_typed action valuesInstalled
  have program := realization.applyClosed_judgment (body index) bodyInstalled
    (realization.context_formed delta) (encodeSub names action) substitutionTyped
  have result := source.typing.substitute substitutionTyped
  refine ⟨?_, ⟨realization.context_formed delta, ?_⟩⟩
  · exact program
  · simpa only [action, encode_substitution, Binding.ContextualAssignment.apply,
      sortType, subst] using result

end SortRealization

namespace Realization

variable {names : Names S} {rules : Rules Head}

theorem encodeSub_typed (realization : Realization names rules)
    {gamma delta : Binding.Ctx S} (action : Binding.Sub S gamma delta) :
    FormationSensitive.CtxMor rules (context names gamma) (context names delta)
      (encodeSub names action) :=
  realization.toSortRealization.encodeSub_typed action
    (fun _ _ => realization.installed _)

theorem contextualApplication_judgments (realization : Realization names rules)
    {M : List (Binding.MetaArity S)} {gamma delta : Binding.Ctx S}
    (body : Binding.ContextualAssignment S M gamma) (index : Fin M.length)
    (arguments : Binding.Sub S (M.get index).1 delta) (ambient : Binding.Sub S gamma delta) :
    FormationSensitive.Judgment rules (context names delta)
        (contextualApplication names body index arguments ambient) (sortType names (M.get index).2) ∧
      FormationSensitive.Judgment rules (context names delta)
        (encode names (Binding.ContextualAssignment.apply body index arguments ambient))
        (sortType names (M.get index).2) :=
  realization.toSortRealization.contextualApplication_judgments body index arguments ambient
    (realization.installed _) (fun _ _ => realization.installed _)

end Realization

#print axioms contextualApplication_beta
#print axioms SortRealization.encodeSub_typed
#print axioms SortRealization.closeTerm_typing
#print axioms SortRealization.applyClosed_judgment
#print axioms SortRealization.contextualApplication_judgments
#print axioms Realization.contextualApplication_judgments


/-! ## Contextual schema programs and explicit native replay

The original `withMetas` binding syntax is compiled directly. Metavariable
bodies retain a declared dependency prefix and a separate ambient suffix;
ordinary schema variables have their own source assignment. Constructors
become native constants/applications, binding arguments become lambdas, and
metavariable calls apply the actual closed source body to the compiled values.

Directed computation agrees with the independently defined contextual source
instantiator. A constructive finite structural code earns both original
endpoints through the existing decoder. Formation is proved before reduction
from actual declaration lookups and refined context morphisms. Substitution
of emitted code and recompilation have checked evidence to a common source
result; literal emitted syntax need not be identified.

These are schema interpretation and computation laws. A concrete authored
language must still install its finite declaration family and connect its
matching, premises, contextual positions and equation authority. Arbitrary
ambient conversion reflection, implementation refinement and executed resource
bounds are not inferred from this interpretation.
-/

namespace Schema

open Mettapedia.OSLF
open TelescopeAbstraction

variable {S : Binding.Signature} {M : List (Binding.MetaArity S)} {Head : Type}

def concatSub {Value : Type} {ambient : Binding.Ctx S} :
    (dependencies : Binding.Ctx S) → (Fin dependencies.length → Value) →
      (Fin ambient.length → Value) → Fin (dependencies ++ ambient).length → Value
  | [], _, environment => environment
  | _ :: dependencies, arguments, environment =>
      Fin.cases (arguments 0) (concatSub dependencies (fun i => arguments i.succ) environment)

theorem concatSub_encode (names : Names S) {ambient delta : Binding.Ctx S} :
    ∀ {dependencies : Binding.Ctx S} (arguments : Binding.Sub S dependencies delta)
      (environment : Binding.Sub S ambient delta),
      concatSub dependencies (encodeSub names arguments) (encodeSub names environment) =
        encodeSub (Head := Head) names (Binding.ContextualAssignment.joinSub arguments environment) := by
  intro dependencies
  induction dependencies with
  | nil => intros; rfl
  | cons sort dependencies inductionHypothesis =>
      intro arguments environment
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · exact congrFun (inductionHypothesis
          (fun other position => arguments other (.succ position)) environment) prior

theorem concatSub_map {S : Binding.Signature} {Value Target : Type}
    {ambient : Binding.Ctx S} (map : Value → Target) :
    ∀ (dependencies : Binding.Ctx S) (arguments : Fin dependencies.length → Value)
      (environment : Fin ambient.length → Value),
      (fun index => map (concatSub dependencies arguments environment index)) =
        concatSub dependencies (fun index => map (arguments index))
          (fun index => map (environment index))
  | [], _, _ => rfl
  | _ :: dependencies, arguments, environment => by
      funext index
      refine Fin.cases rfl (fun prior => ?_) index
      exact congrFun (concatSub_map map dependencies (fun index => arguments index.succ) environment) prior

/-- Closed native functions for the original metavariable dependency and
ambient telescopes. The table does not contain a new source term grammar. -/
abbrev bodyPrograms (names : Names S) {ambient : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient) : Fin M.length → Tm Head 0 :=
  fun index => closeTerm (context names ((M.get index).1 ++ ambient)) (encode names (bodies index))

/- The executable schema traversal receives literal native body functions.
The original source-body compiler is its specialization below. -/
mutual
  def compileWithPrograms (names : Names S) {ambient : Binding.Ctx S}
      (programs : Fin M.length → Tm Head 0) :
      {source target : Binding.Ctx S} → {sort : S.Srt} →
      Binding.Sub S ambient target → Binding.Sub S source target →
      Binding.Term (Binding.withMetas S M) source sort → Tm Head target.length
    | _, _, _, _, valuation, .var position => encode names (valuation _ position)
    | _, _, _, environment, valuation, .op (.inl operator) arguments =>
        compileArgumentsWithPrograms names programs environment valuation (.const (names.operator operator)) arguments
    | _, _, _, environment, valuation, .op (.inr (.mk index)) arguments =>
        applyClosed (context names ((M.get index).1 ++ ambient))
          (concatSub (M.get index).1
            (compileMetaArgumentsWithPrograms names programs environment valuation (M.get index).1 arguments)
            (encodeSub names environment))
          (liftClosed (programs index))

  termination_by _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  def compileArgumentsWithPrograms (names : Names S) {ambient : Binding.Ctx S}
      (programs : Fin M.length → Tm Head 0) :
      {source target : Binding.Ctx S} → {arity : List (List S.Srt × S.Srt)} →
      Binding.Sub S ambient target → Binding.Sub S source target → Tm Head target.length →
      Binding.Args (Binding.withMetas S M) arity source → Tm Head target.length
    | _, _, _, _, _, head, .nil => head
    | _, _, _, environment, valuation, head, .cons (bs := bound) body rest =>
        compileArgumentsWithPrograms names programs environment valuation
          (.app head (abstract bound (compileWithPrograms names programs
            (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
            (Binding.liftSub (S := S) valuation bound) body))) rest

  termination_by _ _ _ _ _ _ arguments => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  def compileMetaArgumentsWithPrograms (names : Names S) {ambient : Binding.Ctx S}
      (programs : Fin M.length → Tm Head 0) :
      {source target : Binding.Ctx S} → Binding.Sub S ambient target → Binding.Sub S source target →
      (dependencies : List S.Srt) →
      Binding.Args (Binding.withMetas S M) (dependencies.map fun sort => ([], sort)) source →
      Sub Head dependencies.length target.length
    | _, _, _, _, [], .nil => fun index => Fin.elim0 index
    | _, _, environment, valuation, _ :: dependencies, .cons body rest =>
        Fin.cases
          (compileWithPrograms names programs (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
            (Binding.liftSub (S := S) valuation []) body)
          (compileMetaArgumentsWithPrograms names programs environment valuation dependencies rest)
  termination_by _ _ _ _ _ arguments => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

/-- Compile the original contextual source bodies through the shared native
body-function traversal. -/
abbrev compile (names : Names S) {ambient : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient)
    {source target : Binding.Ctx S} {sort : S.Srt}
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (term : Binding.Term (Binding.withMetas S M) source sort) : Tm Head target.length :=
  compileWithPrograms names (bodyPrograms names bodies) environment valuation term

abbrev compileArguments (names : Names S) {ambient : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient)
    {source target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (head : Tm Head target.length) (arguments : Binding.Args (Binding.withMetas S M) arity source) :
    Tm Head target.length :=
  compileArgumentsWithPrograms names (bodyPrograms names bodies) environment valuation head arguments

abbrev compileMetaArguments (names : Names S) {ambient : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient)
    {source target : Binding.Ctx S}
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (dependencies : List S.Srt)
    (arguments : Binding.Args (Binding.withMetas S M) (dependencies.map fun sort => ([], sort)) source) :
    Sub Head dependencies.length target.length :=
  compileMetaArgumentsWithPrograms names (bodyPrograms names bodies) environment valuation dependencies arguments

private theorem app_beta {n : Nat} {first next argument later : Tm Head n}
    (function : BetaSteps first next) (value : BetaSteps argument later) :
    BetaSteps (.app first argument) (.app next later) :=
  (function.lift (fun f => Tm.app f argument) (fun _ _ step => StepCore.congAppFun step)).trans
    (value.lift (fun a => Tm.app next a) (fun _ _ step => StepCore.congAppArg step))

private theorem abstract_beta {gamma : Binding.Ctx S} (bound : List S.Srt)
    {first second : Tm Head (bound ++ gamma).length} (steps : BetaSteps first second) :
    BetaSteps (abstract bound first) (abstract bound second) := by
  induction bound with
  | nil => exact steps
  | cons sort bound inductionHypothesis =>
      exact inductionHypothesis
        (steps.lift Tm.lam (fun _ _ step => StepCore.congLam step))

private theorem applyClosed_beta_congr {n m : Nat} (telescope : Ctx Head n)
    {first second : Sub Head n m} {function later : Tm Head m}
    (arguments : ∀ index, BetaSteps (first index) (second index))
    (functions : BetaSteps function later) :
    BetaSteps (applyClosed telescope first function) (applyClosed telescope second later) := by
  induction telescope with
  | nil => exact functions
  | snoc prior domain inductionHypothesis =>
      exact app_beta (inductionHypothesis (fun index => arguments index.succ)) (arguments 0)

private theorem concatSub_beta {ambient delta : Binding.Ctx S}
    (dependencies : Binding.Ctx S) {first second : Sub Head dependencies.length delta.length}
    (environment : Sub Head ambient.length delta.length)
    (steps : ∀ index, BetaSteps (first index) (second index)) :
    ∀ index, BetaSteps (concatSub dependencies first environment index)
      (concatSub dependencies second environment index) := by
  induction dependencies with
  | nil => intro index; exact .refl
  | cons sort dependencies inductionHypothesis =>
      intro index
      refine Fin.cases (steps 0) (fun prior => ?_) index
      exact inductionHypothesis (fun index => steps index.succ) prior

mutual
  theorem compile_beta (names : Names S) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S} {sort : S.Srt}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (term : Binding.Term (Binding.withMetas S M) source sort),
        BetaSteps (compile (Head := Head) names bodies environment valuation term)
          (encode names (Binding.ContextualAssignment.instantiate bodies environment valuation term))
    | _, _, _, _, valuation, .var position => by
        simpa only [compile, compileWithPrograms, Binding.ContextualAssignment.instantiate] using
          (Relation.ReflTransGen.refl (a := encode (Head := Head) names (valuation _ position)))
    | _, _, _, environment, valuation, .op (.inl operator) arguments => by
        simpa only [compile, compileWithPrograms, Binding.ContextualAssignment.instantiate, encode] using
          compileArguments_beta names bodies environment valuation
            (.const (names.operator operator)) (.const (names.operator operator)) arguments .refl
    | _, _, _, environment, valuation, .op (.inr (.mk index)) arguments => by
        let actual := Binding.ContextualAssignment.instantiateArgs bodies environment valuation arguments
        have dependencies := compileMetaArguments_beta names bodies environment valuation
          (M.get index).1 arguments
        have normalized := applyClosed_beta_congr
          (context names ((M.get index).1 ++ ambient))
          (concatSub_beta (M.get index).1 (encodeSub names environment) dependencies)
          (Relation.ReflTransGen.refl (a :=
            liftClosed (closeTerm (context names ((M.get index).1 ++ ambient))
              (encode names (bodies index)))))
        have contracted := contextualApplication_beta (Head := Head) names bodies index
          (Binding.argsToSub actual) environment
        rw [concatSub_encode] at normalized
        simpa only [compile, compileWithPrograms, Binding.ContextualAssignment.instantiate, contextualApplication] using
          normalized.trans contracted
  termination_by _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem compileArguments_beta (names : Names S) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (first second : Tm Head target.length)
        (arguments : Binding.Args (Binding.withMetas S M) arity source),
        BetaSteps first second →
        BetaSteps (compileArguments names bodies environment valuation first arguments)
          (applyArguments names second
            (Binding.ContextualAssignment.instantiateArgs bodies environment valuation arguments))
    | _, _, _, _, _, _, _, .nil, steps => by
        simpa only [compileArguments, compileArgumentsWithPrograms, Binding.ContextualAssignment.instantiateArgs,
          applyArguments] using steps
    | _, _, _, environment, valuation, first, second, .cons (bs := bound) body rest, steps => by
        simpa only [compileArguments, compileArgumentsWithPrograms, Binding.ContextualAssignment.instantiateArgs,
          applyArguments] using compileArguments_beta names bodies environment valuation
          (.app first (abstract bound (compile names bodies
            (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
            (Binding.liftSub (S := S) valuation bound) body)))
          (.app second (abstract bound (encode names
            (Binding.ContextualAssignment.instantiate bodies
              (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
              (Binding.liftSub (S := S) valuation bound) body)))) rest
          (app_beta steps (abstract_beta (S := S) bound (compile_beta names bodies _ _ body)))
  termination_by _ _ _ _ _ _ _ arguments _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  theorem compileMetaArguments_beta (names : Names S) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S M)
          (dependencies.map fun sort => ([], sort)) source),
        ∀ index, BetaSteps
          (compileMetaArguments (Head := Head) names bodies environment valuation dependencies arguments index)
          (encodeSub names (Binding.argsToSub
            (Binding.ContextualAssignment.instantiateArgs bodies environment valuation arguments)) index)
    | _, _, _, _, [], .nil, index => Fin.elim0 index
    | _, _, environment, valuation, _ :: dependencies, .cons body rest, index => by
        refine Fin.cases ?_ (fun prior => ?_) index
        · simpa only [compileMetaArguments, compileMetaArgumentsWithPrograms, Binding.ContextualAssignment.instantiateArgs,
            Binding.argsToSub, encodeSub, Fin.cases_zero] using
            compile_beta names bodies
              (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
              (Binding.liftSub (S := S) valuation []) body
        · simpa only [compileMetaArguments, compileMetaArgumentsWithPrograms, Binding.ContextualAssignment.instantiateArgs,
            Binding.argsToSub, encodeSub, Fin.cases_succ] using
            compileMetaArguments_beta names bodies environment valuation dependencies rest prior
  termination_by _ _ _ _ _ arguments _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

open StructuralConversionCode FormationCheckedTelescopePrograms

abbrev Evidence (Head : Type) (scope : Nat) := Code Head (fun _ => Empty) scope

private def abstractEvidence {gamma : Binding.Ctx S} : (bound : List S.Srt) →
    Evidence Head (bound ++ gamma).length → Evidence Head gamma.length
  | [], code => code
  | _ :: bound, code => abstractEvidence bound (Code.mapContext Tm.lam StepCode.congLam code)

private theorem abstractEvidence_checked [DecidableEq Head] {gamma : Binding.Ctx S}
    (bound : List S.Srt) {code : Evidence Head (bound ++ gamma).length}
    {first second : Tm Head (bound ++ gamma).length}
    (accepted : code.check (fun _ _ => False) noRoot first second = true) :
    (abstractEvidence bound code).check (fun _ _ => False) noRoot
      (abstract bound first) (abstract bound second) = true := by
  induction bound with
  | nil => exact accepted
  | cons sort bound inductionHypothesis =>
      exact inductionHypothesis
        (Code.check_mapContext (fun _ _ => False) noRoot Tm.lam StepCode.congLam
          (fun _ => rfl) accepted)

private def applyArgumentsEvidence : {n m : Nat} → (telescope : Ctx Head n) →
    Sub Head n m → Sub Head n m → Tm Head m → (Fin n → Evidence Head m) → Evidence Head m
  | _, _, .nil, _, _, function, _ => .refl function
  | _, _, .snoc prior _, first, second, function, codes =>
      Code.congApp (applyClosed prior (fun i => second i.succ) function) (first 0)
        (applyArgumentsEvidence prior (fun i => first i.succ) (fun i => second i.succ)
          function (fun i => codes i.succ)) (codes 0)

private theorem applyArgumentsEvidence_checked [DecidableEq Head] {n m : Nat}
    (telescope : Ctx Head n) (first second : Sub Head n m) (function : Tm Head m)
    (codes : Fin n → Evidence Head m)
    (accepted : ∀ index, (codes index).check (fun _ _ => False) noRoot
      (first index) (second index) = true) :
    (applyArgumentsEvidence telescope first second function codes).check (fun _ _ => False) noRoot
      (applyClosed telescope first function) (applyClosed telescope second function) = true := by
  induction telescope with
  | nil => exact Code.check_refl (fun _ _ => False) noRoot function
  | snoc prior domain inductionHypothesis =>
      exact Code.check_congApp (fun _ _ => False) noRoot
        (inductionHypothesis (fun index => first index.succ) (fun index => second index.succ)
          (fun index => codes index.succ) (fun index => accepted index.succ)) (accepted 0)

private theorem concatEvidence_checked [DecidableEq Head] {ambient delta : Binding.Ctx S}
    (dependencies : Binding.Ctx S) {first second : Sub Head dependencies.length delta.length}
    (environment : Sub Head ambient.length delta.length)
    (codes : Fin dependencies.length → Evidence Head delta.length)
    (accepted : ∀ index, (codes index).check (fun _ _ => False) noRoot
      (first index) (second index) = true) :
    ∀ index, (concatSub dependencies codes (fun i => .refl (environment i)) index).check
      (fun _ _ => False) noRoot (concatSub dependencies first environment index)
        (concatSub dependencies second environment index) = true := by
  induction dependencies with
  | nil => intro index; exact Code.check_refl (fun _ _ => False) noRoot (environment index)
  | cons sort dependencies inductionHypothesis =>
      intro index
      refine Fin.cases (accepted 0) (fun prior => ?_) index
      exact inductionHypothesis (fun i => codes i.succ) (fun i => accepted i.succ) prior

mutual
  def compileEvidence (names : Names S) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      {source target : Binding.Ctx S} → {sort : S.Srt} →
      Binding.Sub S ambient target → Binding.Sub S source target →
      Binding.Term (Binding.withMetas S M) source sort → Evidence Head target.length
    | _, _, _, _, valuation, .var position => .refl (encode names (valuation _ position))
    | _, _, _, environment, valuation, .op (.inl operator) arguments =>
        compileArgumentsEvidence names bodies environment valuation
          (.const (names.operator operator)) (.const (names.operator operator))
          arguments (.refl (.const (names.operator operator)))
    | _, _, _, environment, valuation, .op (.inr (.mk index)) arguments =>
        let actual := Binding.ContextualAssignment.instantiateArgs bodies environment valuation arguments
        let actualSub := encodeSub names (Binding.argsToSub actual)
        let compiledSub := compileMetaArguments names bodies environment valuation (M.get index).1 arguments
        let environmentSub := encodeSub names environment
        let telescope := context names ((M.get index).1 ++ ambient)
        .trans
          (applyArgumentsEvidence telescope
            (concatSub (M.get index).1 compiledSub environmentSub)
            (concatSub (M.get index).1 actualSub environmentSub)
            (liftClosed (closeTerm telescope (encode names (bodies index))))
            (concatSub (M.get index).1
              (compileMetaEvidence names bodies environment valuation (M.get index).1 arguments)
              (fun i => .refl (environmentSub i))))
          (applicationCode telescope
            (encodeSub names (Binding.ContextualAssignment.joinSub (Binding.argsToSub actual) environment))
            (encode names (bodies index)))
  termination_by _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  def compileArgumentsEvidence (names : Names S) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      {source target : Binding.Ctx S} → {arity : List (List S.Srt × S.Srt)} →
      Binding.Sub S ambient target → Binding.Sub S source target → Tm Head target.length →
      Tm Head target.length → Binding.Args (Binding.withMetas S M) arity source →
      Evidence Head target.length → Evidence Head target.length
    | _, _, _, _, _, _, _, .nil, code => code
    | _, _, _, environment, valuation, first, second, .cons (bs := bound) body rest, code =>
        let rawBody := compile names bodies
          (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
          (Binding.liftSub (S := S) valuation bound) body
        let actualBody := encode names (Binding.ContextualAssignment.instantiate bodies
          (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
          (Binding.liftSub (S := S) valuation bound) body)
        compileArgumentsEvidence names bodies environment valuation
          (.app first (abstract bound rawBody)) (.app second (abstract bound actualBody)) rest
          (Code.congApp second (abstract bound rawBody) code
            (abstractEvidence (S := S) bound (compileEvidence names bodies
              (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
              (Binding.liftSub (S := S) valuation bound) body)))
  termination_by _ _ _ _ _ _ _ arguments _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  def compileMetaEvidence (names : Names S) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      {source target : Binding.Ctx S} → Binding.Sub S ambient target → Binding.Sub S source target →
      (dependencies : List S.Srt) →
      Binding.Args (Binding.withMetas S M) (dependencies.map fun sort => ([], sort)) source →
      Fin dependencies.length → Evidence Head target.length
    | _, _, _, _, [], .nil, index => Fin.elim0 index
    | _, _, environment, valuation, _ :: dependencies, .cons body rest, index =>
        Fin.cases
          (compileEvidence names bodies (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
            (Binding.liftSub (S := S) valuation []) body)
          (compileMetaEvidence names bodies environment valuation dependencies rest) index
  termination_by _ _ _ _ _ arguments _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

mutual
  theorem compileEvidence_checked [DecidableEq Head] (names : Names S) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S} {sort : S.Srt}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (term : Binding.Term (Binding.withMetas S M) source sort),
        (compileEvidence names bodies environment valuation term).check (fun _ _ => False) noRoot
          (compile (Head := Head) names bodies environment valuation term)
          (encode names (Binding.ContextualAssignment.instantiate bodies environment valuation term)) = true
    | _, _, _, _, valuation, .var position => by
        simpa only [compileEvidence, compile, compileWithPrograms, Binding.ContextualAssignment.instantiate] using
          Code.check_refl (fun _ _ : Head => False) noRoot (encode names (valuation _ position))
    | _, _, _, environment, valuation, .op (.inl operator) arguments => by
        simpa only [compileEvidence, compile, compileWithPrograms, Binding.ContextualAssignment.instantiate, encode] using
          compileArgumentsEvidence_checked names bodies environment valuation
            (.const (names.operator operator)) (.const (names.operator operator)) arguments
            (.refl (.const (names.operator operator)))
            (Code.check_refl (fun _ _ : Head => False) noRoot (.const (names.operator operator)))
    | _, _, _, environment, valuation, .op (.inr (.mk index)) arguments => by
        let actual := Binding.ContextualAssignment.instantiateArgs bodies environment valuation arguments
        let actualSub := encodeSub (Head := Head) names (Binding.argsToSub actual)
        let compiledSub := compileMetaArguments (Head := Head) names bodies environment valuation
          (M.get index).1 arguments
        let environmentSub := encodeSub (Head := Head) names environment
        let telescope := context (Head := Head) names ((M.get index).1 ++ ambient)
        let body := encode (Head := Head) names (bodies index)
        let codes := compileMetaEvidence (Head := Head) names bodies environment valuation
          (M.get index).1 arguments
        have dependencies := compileMetaEvidence_checked names bodies environment valuation
          (M.get index).1 arguments
        have normalized := applyArgumentsEvidence_checked telescope
          (concatSub (M.get index).1 compiledSub environmentSub)
          (concatSub (M.get index).1 actualSub environmentSub)
          (liftClosed (closeTerm telescope body))
          (concatSub (M.get index).1 codes (fun i => .refl (environmentSub i)))
          (concatEvidence_checked (M.get index).1 environmentSub codes dependencies)
        have contracted := applicationCode_checked telescope
          (encodeSub names (Binding.ContextualAssignment.joinSub (Binding.argsToSub actual) environment)) body
        change Code.check (fun _ _ => False) noRoot _
          (applyClosed telescope (concatSub (M.get index).1 compiledSub environmentSub)
            (liftClosed (closeTerm telescope body)))
          (applyClosed telescope (concatSub (M.get index).1 actualSub environmentSub)
            (liftClosed (closeTerm telescope body))) = true at normalized
        dsimp only [actualSub, environmentSub] at normalized
        rw [concatSub_encode] at normalized
        rw [encode_substitution] at contracted
        simpa only [compileEvidence, compile, compileWithPrograms, Binding.ContextualAssignment.instantiate,
          Binding.ContextualAssignment.apply, concatSub_encode] using
          Code.check_trans (fun _ _ => False) noRoot normalized contracted
  termination_by _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem compileArgumentsEvidence_checked [DecidableEq Head] (names : Names S)
      {ambient : Binding.Ctx S} (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (first second : Tm Head target.length)
        (arguments : Binding.Args (Binding.withMetas S M) arity source)
        (code : Evidence Head target.length),
        code.check (fun _ _ => False) noRoot first second = true →
        (compileArgumentsEvidence names bodies environment valuation first second arguments code).check
          (fun _ _ => False) noRoot (compileArguments names bodies environment valuation first arguments)
          (applyArguments names second
            (Binding.ContextualAssignment.instantiateArgs bodies environment valuation arguments)) = true
    | _, _, _, _, _, _, _, .nil, _, accepted => by
        simpa only [compileArgumentsEvidence, compileArguments, compileArgumentsWithPrograms,
          Binding.ContextualAssignment.instantiateArgs, applyArguments] using accepted
    | _, _, _, environment, valuation, first, second, .cons (bs := bound) body rest, code, accepted => by
        have bodyChecked := compileEvidence_checked names bodies
          (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
          (Binding.liftSub (S := S) valuation bound) body
        have abstractChecked := abstractEvidence_checked (S := S) bound bodyChecked
        have applied := Code.check_congApp (fun _ _ => False) noRoot accepted abstractChecked
        simpa only [compileArgumentsEvidence, compileArguments, compileArgumentsWithPrograms,
          Binding.ContextualAssignment.instantiateArgs, applyArguments] using
          compileArgumentsEvidence_checked names bodies environment valuation _ _ rest _ applied
  termination_by _ _ _ _ _ _ _ arguments _ _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  theorem compileMetaEvidence_checked [DecidableEq Head] (names : Names S)
      {ambient : Binding.Ctx S} (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S M)
          (dependencies.map fun sort => ([], sort)) source),
        ∀ index, (compileMetaEvidence names bodies environment valuation dependencies arguments index).check
          (fun _ _ => False) noRoot
          (compileMetaArguments (Head := Head) names bodies environment valuation dependencies arguments index)
          (encodeSub names (Binding.argsToSub
            (Binding.ContextualAssignment.instantiateArgs bodies environment valuation arguments)) index) = true
    | _, _, _, _, [], .nil, index => Fin.elim0 index
    | _, _, environment, valuation, _ :: dependencies, .cons body rest, index => by
        refine Fin.cases ?_ (fun prior => ?_) index
        · simpa only [compileMetaEvidence, compileMetaArguments, compileMetaArgumentsWithPrograms,
            Binding.ContextualAssignment.instantiateArgs, Binding.argsToSub,
            encodeSub, Fin.cases_zero] using
            compileEvidence_checked names bodies
              (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
              (Binding.liftSub (S := S) valuation []) body
        · simpa only [compileMetaEvidence, compileMetaArguments, compileMetaArgumentsWithPrograms,
            Binding.ContextualAssignment.instantiateArgs, Binding.argsToSub,
            encodeSub, Fin.cases_succ] using
            compileMetaEvidence_checked names bodies environment valuation dependencies rest prior
  termination_by _ _ _ _ _ arguments _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

theorem concatSub_typed (names : Names S) {rules : Rules Head}
    {ambient target : Binding.Ctx S} (dependencies : Binding.Ctx S)
    {arguments : Sub Head dependencies.length target.length}
    {environment : Sub Head ambient.length target.length}
    (argumentsTyped : FormationSensitive.CtxMor rules
      (context names dependencies) (context names target) arguments)
    (environmentTyped : FormationSensitive.CtxMor rules
      (context names ambient) (context names target) environment) :
    FormationSensitive.CtxMor rules (context names (dependencies ++ ambient))
      (context names target) (concatSub dependencies arguments environment) := by
  induction dependencies with
  | nil => exact environmentTyped
  | cons sort dependencies inductionHypothesis =>
      have prior := inductionHypothesis argumentsTyped.dropNewest
      have newest := argumentsTyped 0
      simp only [context, Ctx.lookup_snoc_zero, sortType, rename, subst] at newest
      change FormationSensitive.CtxMor rules
        (.snoc (context names (dependencies ++ ambient)) (sortType names sort))
        (context names target)
        (consSub (arguments 0) (concatSub dependencies (fun i => arguments i.succ) environment))
      exact prior.extend newest

open FormationSensitive

mutual
  theorem compile_typing {names : Names S} {rules : Rules Head}
      (realization : Realization names rules) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S} {sort : S.Srt}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (term : Binding.Term (Binding.withMetas S M) source sort),
        Typing rules (context names target) (compile names bodies environment valuation term)
          (sortType names sort)
    | _, _, _, _, valuation, .var position => by
        simpa only [compile, compileWithPrograms] using realization.encode_typing (valuation _ position)
    | _, target, sort, environment, valuation, .op (.inl operator) arguments => by
        have constructor := Typing.const (Γ := context names target)
          (realization.operatorLookup operator)
          (realization.toSortRealization.operatorType_formed operator) realization.universeIs
        simpa only [compile, compileWithPrograms, sortType, liftClosed, rename] using
          compileArguments_typing realization bodies environment valuation arguments
            (realization.toSortRealization.sortType_formed .nil sort) constructor
    | _, target, _, environment, valuation, .op (.inr (.mk index)) arguments => by
        have dependencies := compileMetaArguments_typing realization bodies environment valuation
          (M.get index).1 arguments
        have environmentTyped := realization.encodeSub_typed environment
        have combined := concatSub_typed names (M.get index).1 dependencies environmentTyped
        have applied := realization.toSortRealization.applyClosed_judgment (bodies index)
          (realization.installed _) (realization.toSortRealization.context_formed target)
          (concatSub (M.get index).1
            (compileMetaArguments names bodies environment valuation (M.get index).1 arguments)
            (encodeSub names environment)) combined
        simpa only [compile, compileWithPrograms] using applied.typing
  termination_by _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem compileArguments_typing {names : Names S} {rules : Rules Head}
      (realization : Realization names rules) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (arguments : Binding.Args (Binding.withMetas S M) arity source),
        ∀ {result : Tm Head 0}, Typing rules .nil result (.head realization.typeUniverse) →
        ∀ {head : Tm Head target.length},
        Typing rules (context names target) head (liftClosed (argumentsType names arity result)) →
        Typing rules (context names target)
          (compileArguments names bodies environment valuation head arguments) (liftClosed result)
    | _, _, _, _, _, .nil, _, _, _, typed => by
        simpa only [compileArguments, compileArgumentsWithPrograms, argumentsType] using typed
    | _, _, _, environment, valuation, .cons (bs := bound) (s := sort) body rest,
        result, formed, head, typed => by
        have bodyTyped := realization.toSortRealization.abstract_typing bound
          (realization.toSortRealization.sortType_formed .nil sort)
          (compile names bodies (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
            (Binding.liftSub (S := S) valuation bound) body)
          (compile_typing realization bodies _ _ body)
        have functionTyped := typed
        change Typing rules _ head (liftClosed (closedArrow _ _)) at functionTyped
        rw [liftClosed_closedArrow] at functionTyped
        have applied := Typing.appElim functionTyped bodyTyped
        simp only [inst0, subst_liftClosed] at applied
        simpa only [compileArguments, compileArgumentsWithPrograms] using
          compileArguments_typing realization bodies environment valuation rest formed applied
  termination_by _ _ _ _ _ arguments _ _ _ _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  theorem compileMetaArguments_typing {names : Names S} {rules : Rules Head}
      (realization : Realization names rules) {ambient : Binding.Ctx S}
      (bodies : Binding.ContextualAssignment S M ambient) :
      ∀ {source target : Binding.Ctx S}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S M)
          (dependencies.map fun sort => ([], sort)) source),
        FormationSensitive.CtxMor rules (context names dependencies) (context names target)
          (compileMetaArguments names bodies environment valuation dependencies arguments)
    | _, _, _, _, [], .nil => by intro index; exact Fin.elim0 index
    | _, _, environment, valuation, sort :: dependencies, .cons body rest => by
        have previous := compileMetaArguments_typing realization bodies environment valuation dependencies rest
        have newest := compile_typing realization bodies
          (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
          (Binding.liftSub (S := S) valuation []) body
        rw [compileMetaArguments, compileMetaArgumentsWithPrograms]
        change FormationSensitive.CtxMor rules
          (.snoc (context names dependencies) (sortType names sort)) _
          (consSub _ (compileMetaArguments names bodies environment valuation dependencies rest))
        apply previous.extend
        simpa only [sortType, subst, List.nil_append] using newest
  termination_by _ _ _ _ _ arguments => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

/-- The emitted schema program is formed before computation. Its independent
finite replay then returns the existing scoped source instantiation. -/
theorem compile_judgment {names : Names S} {rules : Rules Head}
    (realization : Realization names rules) {ambient source target : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort) :
    Judgment rules (context names target) (compile names bodies environment valuation term)
      (sortType names sort) :=
  ⟨realization.toSortRealization.context_formed target,
    compile_typing realization bodies environment valuation term⟩

private def noRootSubstitute {n m : Nat} (_ : Sub Head n m) (code : Empty) : Empty := nomatch code

/-- The existing structural code substitution transports the computed replay.
The source bodies remain fixed; both submitted source assignments compose
with the new ambient substitution. -/
def reindexedEvidence (names : Names S) {ambient source target destination : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort)
    (action : Binding.Sub S target destination) : Evidence Head destination.length :=
  (compileEvidence names bodies environment valuation term).substitute noRootSubstitute
    (encodeSub names action)

theorem reindexedEvidence_checked [DecidableEq Head] (names : Names S)
    {ambient source target destination : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort)
    (action : Binding.Sub S target destination) :
    (reindexedEvidence names bodies environment valuation term action).check (fun _ _ => False) noRoot
      (subst (encodeSub names action) (compile (Head := Head) names bodies environment valuation term))
      (encode names (Binding.ContextualAssignment.instantiate bodies
        (fun sort position => Binding.bind action (environment sort position))
        (fun sort position => Binding.bind action (valuation sort position)) term)) = true := by
  have original := compileEvidence_checked (Head := Head) names bodies environment valuation term
  have transported := Code.check_substitute noRootSubstitute (fun _ _ : Head => False) noRoot
    (fun _ empty => nomatch empty) (encodeSub names action) _ original
  simpa only [reindexedEvidence, encode_substitution, Binding.ContextualAssignment.bind_instantiate]
    using transported

/-- Recompilation and substitution of an emitted proof both have finite
accepted evidence to the same independently specified source value. This
states naturality at the computation observation, rather than identifying
raw compiled syntax after a change of context. -/
theorem substitution_common_value [DecidableEq Head] (names : Names S)
    {ambient source target destination : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort)
    (action : Binding.Sub S target destination) :
    let nextEnvironment := fun sort position => Binding.bind action (environment sort position)
    let nextValuation := fun sort position => Binding.bind action (valuation sort position)
    let result := encode names (Binding.ContextualAssignment.instantiate bodies nextEnvironment nextValuation term)
    (reindexedEvidence names bodies environment valuation term action).check (fun _ _ => False) noRoot
      (subst (encodeSub names action) (compile (Head := Head) names bodies environment valuation term)) result = true ∧
    (compileEvidence names bodies nextEnvironment nextValuation term).check (fun _ _ => False) noRoot
      (compile names bodies nextEnvironment nextValuation term) result = true :=
  ⟨reindexedEvidence_checked names bodies environment valuation term action,
    compileEvidence_checked names bodies _ _ term⟩

end Schema

end BindingSignatureEmbedding
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.Schema
open Mettapedia.OSLF
open TelescopeAbstraction
set_option autoImplicit false
variable {S : Binding.Signature} {Head : Type} {scope : Nat}

/-- The existing compiler's full call first applies the ambient suffix,
then the declared dependency prefix. No argument is copied or permuted. -/
theorem applyClosed_concat (names : Names S) {ambient : Binding.Ctx S}
    (dependencies : Binding.Ctx S)
    (arguments : Sub Head dependencies.length scope)
    (environment : Sub Head ambient.length scope) (function : Tm Head scope) :
    applyClosed (context names (dependencies ++ ambient))
        (concatSub dependencies arguments environment) function =
      applyClosed (context names dependencies) arguments
        (applyClosed (context names ambient) environment function) := by
  induction dependencies with
  | nil => rfl
  | cons sort dependencies inductionHypothesis =>
      change Tm.app
          (applyClosed (context names (dependencies ++ ambient))
            (concatSub dependencies (fun index => arguments index.succ) environment) function)
          (arguments 0) =
        Tm.app
          (applyClosed (context names dependencies) (fun index => arguments index.succ)
            (applyClosed (context names ambient) environment function)) (arguments 0)
      exact congrArg (fun nextFunction => Tm.app nextFunction (arguments 0))
        (inductionHypothesis (arguments := fun index => arguments index.succ))

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.Schema


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.Schema

open Mettapedia.OSLF TelescopeAbstraction ConstantSubstitution

variable {S : Binding.Signature} {Head : Type}

def liftValuesSpine {target : Binding.Ctx S} (values : Values Head target.length) :
    (bound : Binding.Ctx S) → Values Head (bound ++ target).length
  | [] => values
  | _ :: bound => liftValues (liftValuesSpine values bound)

theorem interpret_abstract {source target : Binding.Ctx S}
    (values : Values Head target.length) (assignment : Sub Head source.length target.length)
    (bound : Binding.Ctx S) (body : Tm Head (bound ++ source).length) :
    interpret values assignment (abstract bound body) =
      abstract bound (interpret (liftValuesSpine values bound) (liftSubSpine assignment bound) body) := by
  induction bound with
  | nil => rfl
  | cons sort bound ih =>
      simpa only [abstract, interpret, liftValuesSpine, liftSubSpine] using ih (.lam body)

theorem interpret_applyClosed {source target count : Nat}
    (values : Values Head target) (assignment : Sub Head source target)
    (telescope : Ctx Head count) (arguments : Sub Head count source)
    (function : Tm Head source) :
    interpret values assignment (applyClosed telescope arguments function) =
      applyClosed telescope (fun index => interpret values assignment (arguments index))
        (interpret values assignment function) := by
  induction telescope with
  | nil => rfl
  | snoc prior type ih =>
      simpa only [applyClosed, interpret] using congrArg₂ Tm.app
        (ih (fun index => arguments index.succ)) (rfl :
          interpret values assignment (arguments 0) = interpret values assignment (arguments 0))

theorem rename_applyClosed {source target count : Nat} (action : Ren source target)
    (telescope : Ctx Head count) (arguments : Sub Head count source)
    (function : Tm Head source) :
    rename action (applyClosed telescope arguments function) =
      applyClosed telescope (fun index => rename action (arguments index)) (rename action function) := by
  induction telescope with
  | nil => rfl
  | snoc prior type ih =>
      simpa only [applyClosed, rename] using congrArg₂ Tm.app
        (ih (fun index => arguments index.succ)) (rfl :
          rename action (arguments 0) = rename action (arguments 0))

theorem interpret_closed_lift {target : Nat} (values : Values Head target) (term : Tm Head 0) :
    interpret (liftValues values) Fin.elim0 term = rename wk (interpret values Fin.elim0 term) := by
  exact (rename_interpret_closed values wk term).symm

theorem encode_weaken (names : Names S) {target : Binding.Ctx S} {sort binder : S.Srt}
    (term : Binding.Term S target sort) :
    encode names (Binding.weaken (t := binder) term) = rename wk (encode (Head := Head) names term) := by
  rw [Binding.weaken, ← encode_rename, encodeRen_weaken]

theorem encodeSub_weaken_one (names : Names S) {ambient target : Binding.Ctx S}
    (environment : Binding.Sub S ambient target) (binder : S.Srt) :
    encodeSub (Head := Head) names (Binding.ContextualAssignment.weakenSub (S := S) [binder] environment) =
      fun index => rename wk (encodeSub names environment index) := by
  funext index
  let position := Binding.varOfIdx (S := S) ambient index
  have read := encodeSub_variable (Head := Head) names environment position
  have readWeaken := encodeSub_variable (Head := Head) names
    (Binding.ContextualAssignment.weakenSub (S := S) [binder] environment) position
  rw [Binding.varIdx_varOfIdx] at read readWeaken
  rw [readWeaken, Binding.ContextualAssignment.weakenSub_cons,
    Binding.ContextualAssignment.weakenSub_nil, encode_weaken, read]

theorem operators_lift {target : Binding.Ctx S} (names : Names S)
    (values : Values Head target.length)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort), values (names.operator operator) = .const (names.operator operator))
    (bound : Binding.Ctx S) :
    ∀ {sort : S.Srt} (operator : S.Op sort),
      liftValuesSpine values bound (names.operator operator) = .const (names.operator operator) := by
  induction bound with
  | nil => exact operators
  | cons binder bound ih => intro sort operator; simp only [liftValuesSpine, liftValues, ih, rename]

theorem programs_lift {M : List (Binding.MetaArity S)} {ambient target : Binding.Ctx S}
    (names : Names S) (templates programs : Fin M.length → Tm Head 0)
    (environment : Binding.Sub S ambient target) (values : Values Head target.length)
    (bodies : ∀ index, interpret values Fin.elim0 (templates index) =
      applyClosed (context names ambient) (encodeSub names environment) (liftClosed (programs index)))
    (bound : Binding.Ctx S) :
    ∀ index, interpret (liftValuesSpine values bound) Fin.elim0 (templates index) =
      applyClosed (context names ambient)
        (encodeSub names (Binding.ContextualAssignment.weakenSub (S := S) bound environment))
        (liftClosed (programs index)) := by
  induction bound with
  | nil => simpa only [liftValuesSpine, Binding.ContextualAssignment.weakenSub_nil] using bodies
  | cons binder bound ih =>
      intro index
      rw [liftValuesSpine, interpret_closed_lift, ih, rename_applyClosed, rename_liftClosed]
      have weak := encodeSub_weaken_one (Head := Head) names
        (Binding.ContextualAssignment.weakenSub (S := S) bound environment) binder
      rw [Binding.ContextualAssignment.weakenSub_cons, Binding.ContextualAssignment.weakenSub_nil] at weak
      rw [Binding.ContextualAssignment.weakenSub_cons]
      rw [weak]

theorem variables_lift {source template target : Binding.Ctx S}
    (names : Names S) (values : Values Head target.length)
    (assignment : Sub Head template.length target.length)
    (templateValuation : Binding.Sub S source template) (actualValuation : Binding.Sub S source target)
    (variablesAgree : ∀ {sort : S.Srt} (position : Binding.Var source sort),
      interpret values assignment (encode names (templateValuation _ position)) =
        encode names (actualValuation _ position))
    (bound : Binding.Ctx S) :
    ∀ {sort : S.Srt} (position : Binding.Var (bound ++ source) sort),
      interpret (liftValuesSpine values bound) (liftSubSpine assignment bound)
        (encode names (Binding.liftSub templateValuation bound _ position)) =
          encode names (Binding.liftSub actualValuation bound _ position) := by
  induction bound with
  | nil => exact variablesAgree
  | cons binder bound ih =>
      intro sort position
      cases position with
      | zero => rfl
      | succ position =>
          simp only [liftValuesSpine, liftSubSpine, Binding.liftSub, encode_weaken,
            interpret_weaken, ih]

def emptyEnvironment {target : Binding.Ctx S} : Binding.Sub S [] target :=
  fun _ position => nomatch position

theorem emptyEnvironment_weaken {target : Binding.Ctx S} (bound : Binding.Ctx S) :
    Binding.ContextualAssignment.weakenSub (S := S) bound (emptyEnvironment (target := target)) =
      emptyEnvironment := by
  funext sort position
  exact nomatch position

mutual
  theorem interpret_compileTemplate {M : List (Binding.MetaArity S)}
      (names : Names S) (templates programs : Fin M.length → Tm Head 0) {ambient : Binding.Ctx S} :
      ∀ {source template target : Binding.Ctx S} {sort : S.Srt}
        (environment : Binding.Sub S ambient target)
        (templateValuation : Binding.Sub S source template) (actualValuation : Binding.Sub S source target)
        (values : Values Head target.length) (assignment : Sub Head template.length target.length),
        (∀ {sort : S.Srt} (operator : S.Op sort), values (names.operator operator) = .const (names.operator operator)) →
        (∀ index, interpret values Fin.elim0 (templates index) =
          applyClosed (context names ambient) (encodeSub names environment) (liftClosed (programs index))) →
        (∀ {sort : S.Srt} (position : Binding.Var source sort),
          interpret values assignment (encode names (templateValuation _ position)) = encode names (actualValuation _ position)) →
        ∀ (term : Binding.Term (Binding.withMetas S M) source sort),
        interpret values assignment
          (compileWithPrograms names templates emptyEnvironment templateValuation term) =
            compileWithPrograms names programs environment actualValuation term
    | _, _, _, _, _, _, _, _, _, _, _, variablesAgree, .var position => by
        simpa only [compileWithPrograms] using variablesAgree position
    | _, _, _, _, environment, templateValuation, actualValuation, values, assignment,
        operators, bodies, variablesAgree, .op (.inl operator) arguments => by
        simpa only [compileWithPrograms, interpret, operators] using
          interpret_compileTemplateArguments names templates programs environment templateValuation actualValuation
            values assignment operators bodies variablesAgree (.const (names.operator operator))
            (.const (names.operator operator)) arguments (by simp only [interpret, operators])
    | _, _, _, _, environment, templateValuation, actualValuation, values, assignment,
        operators, bodies, variablesAgree, .op (.inr (.mk index)) arguments => by
        have dependencies := interpret_compileTemplateMetaArguments names templates programs environment
          templateValuation actualValuation values assignment operators bodies variablesAgree
          (M.get index).1 arguments
        simp only [compileWithPrograms, applyClosed_concat, context, applyClosed,
          interpret_applyClosed, interpret_liftClosed, bodies, dependencies]
  termination_by _ _ _ _ _ _ _ _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem interpret_compileTemplateArguments {M : List (Binding.MetaArity S)}
      (names : Names S) (templates programs : Fin M.length → Tm Head 0) {ambient : Binding.Ctx S} :
      ∀ {source template target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (environment : Binding.Sub S ambient target)
        (templateValuation : Binding.Sub S source template) (actualValuation : Binding.Sub S source target)
        (values : Values Head target.length) (assignment : Sub Head template.length target.length),
        (∀ {sort : S.Srt} (operator : S.Op sort), values (names.operator operator) = .const (names.operator operator)) →
        (∀ index, interpret values Fin.elim0 (templates index) =
          applyClosed (context names ambient) (encodeSub names environment) (liftClosed (programs index))) →
        (∀ {sort : S.Srt} (position : Binding.Var source sort),
          interpret values assignment (encode names (templateValuation _ position)) = encode names (actualValuation _ position)) →
        ∀ (templateHead : Tm Head template.length) (actualHead : Tm Head target.length)
        (arguments : Binding.Args (Binding.withMetas S M) arity source),
        interpret values assignment templateHead = actualHead →
        interpret values assignment
          (compileArgumentsWithPrograms names templates emptyEnvironment templateValuation templateHead arguments) =
            compileArgumentsWithPrograms names programs environment actualValuation actualHead arguments
    | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil, heads => by
        simpa only [compileArgumentsWithPrograms] using heads
    | source, template, target, _, environment, templateValuation, actualValuation, values, assignment,
        operators, bodies, variablesAgree, templateHead, actualHead, .cons (bs := bound) body rest, heads => by
        have bodyAgreement := interpret_compileTemplate names templates programs
          (ambient := ambient) (source := bound ++ source) (template := bound ++ template) (target := bound ++ target)
          (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
          (Binding.liftSub templateValuation bound) (Binding.liftSub actualValuation bound)
          (liftValuesSpine values bound) (liftSubSpine assignment bound)
          (operators_lift names values operators bound)
          (programs_lift names templates programs environment values bodies bound)
          (variables_lift names values assignment templateValuation actualValuation variablesAgree bound) body
        have next := congrArg₂ Tm.app heads (congrArg (abstract (S := S) bound) bodyAgreement)
        simp only [compileArgumentsWithPrograms, emptyEnvironment_weaken]
        apply interpret_compileTemplateArguments names templates programs environment templateValuation actualValuation
          values assignment operators bodies variablesAgree _ _ rest
        simpa only [interpret, interpret_abstract, emptyEnvironment_weaken] using next
  termination_by _ _ _ _ _ _ _ _ _ _ _ _ _ _ arguments _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  theorem interpret_compileTemplateMetaArguments {M : List (Binding.MetaArity S)}
      (names : Names S) (templates programs : Fin M.length → Tm Head 0) {ambient : Binding.Ctx S} :
      ∀ {source template target : Binding.Ctx S}
        (environment : Binding.Sub S ambient target)
        (templateValuation : Binding.Sub S source template) (actualValuation : Binding.Sub S source target)
        (values : Values Head target.length) (assignment : Sub Head template.length target.length),
        (∀ {sort : S.Srt} (operator : S.Op sort), values (names.operator operator) = .const (names.operator operator)) →
        (∀ index, interpret values Fin.elim0 (templates index) =
          applyClosed (context names ambient) (encodeSub names environment) (liftClosed (programs index))) →
        (∀ {sort : S.Srt} (position : Binding.Var source sort),
          interpret values assignment (encode names (templateValuation _ position)) = encode names (actualValuation _ position)) →
        ∀ (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S M) (dependencies.map fun sort => ([], sort)) source),
        (fun index => interpret values assignment
          (compileMetaArgumentsWithPrograms names templates emptyEnvironment templateValuation dependencies arguments index)) =
            compileMetaArgumentsWithPrograms names programs environment actualValuation dependencies arguments
    | _, _, _, _, _, _, _, _, _, _, _, [], .nil => by funext index; exact Fin.elim0 index
    | _, _, _, environment, templateValuation, actualValuation, values, assignment,
        operators, bodies, variablesAgree, _ :: dependencies, .cons body rest => by
        funext index
        refine Fin.cases ?_ (fun prior => ?_) index
        · simpa only [compileMetaArgumentsWithPrograms, Fin.cases_zero,
            Binding.ContextualAssignment.weakenSub_nil, Binding.liftSub, emptyEnvironment_weaken] using
            interpret_compileTemplate names templates programs environment templateValuation actualValuation
              values assignment operators bodies variablesAgree body
        · simpa only [compileMetaArgumentsWithPrograms, Fin.cases_succ] using
            congrFun (interpret_compileTemplateMetaArguments names templates programs environment
              templateValuation actualValuation values assignment operators bodies variablesAgree dependencies rest) prior
  termination_by _ _ _ _ _ _ _ _ _ _ _ dependencies arguments => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

/-- The native syntax of an authored rule field, independent of the caller's
ambient context and the supplied metavariable bodies. Ordinary schema variables
retain their original source positions. -/
def fixedTemplate {M : List (Binding.MetaArity S)} (names : Names S)
    (templates : Fin M.length → Tm Head 0) {source : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term (Binding.withMetas S M) source sort) : Tm Head source.length :=
  compileWithPrograms names templates emptyEnvironment (fun _ position => .var position) term

theorem fixedTemplate_interpret {M : List (Binding.MetaArity S)} (names : Names S)
    (templates programs : Fin M.length → Tm Head 0) {ambient source target : Binding.Ctx S}
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (values : Values Head target.length)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      values (names.operator operator) = .const (names.operator operator))
    (bodies : ∀ index, interpret values Fin.elim0 (templates index) =
      applyClosed (context names ambient) (encodeSub names environment) (liftClosed (programs index)))
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort) :
    interpret values (encodeSub names valuation) (fixedTemplate names templates term) =
      compileWithPrograms names programs environment valuation term := by
  apply interpret_compileTemplate names templates programs environment
    (fun _ position => .var position) valuation values (encodeSub names valuation) operators bodies
  intro sort position
  exact encodeSub_variable names valuation position

/-- A metavariable's actual native body function first receives its ambient
arguments. The result has only the original dependency arguments left to take. -/
def ambientFunctions {M : List (Binding.MetaArity S)} (names : Names S)
    (programs : Fin M.length → Tm Head 0) {ambient target : Binding.Ctx S}
    (environment : Binding.Sub S ambient target) : Fin M.length → Tm Head target.length :=
  fun index => applyClosed (context names ambient) (encodeSub names environment) (liftClosed (programs index))

/-- A fixed authored template, containing only finite metavariable function
names, specializes to the original contextual source-body compiler in every
caller context. The finite declaration-position facts earn all primitive
interpretation obligations. -/
theorem fixedTemplate_specialize {M : List (Binding.MetaArity S)}
    (names : Names S) (metavariableNames : Fin M.length → DeclName)
    (positions : DeclName → Option (Fin M.length))
    (operatorPositions : ∀ {sort : S.Srt} (operator : S.Op sort), positions (names.operator operator) = none)
    (metavariablePositions : ∀ index, positions (metavariableNames index) = some index)
    {ambient source target : Binding.Ctx S} (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort) :
    interpret (specializedValues positions (ambientFunctions names (bodyPrograms names bodies) environment))
        (encodeSub names valuation)
        (fixedTemplate names (fun index => .const (metavariableNames index)) term) =
      compile (Head := Head) names bodies environment valuation term := by
  refine fixedTemplate_interpret names (fun index => .const (metavariableNames index))
    (bodyPrograms names bodies) environment valuation _ ?_ ?_ term
  · intro sort operator
    simp only [specializedValues, operatorPositions]
  · intro index
    simp only [interpret, specializedValues, metavariablePositions, ambientFunctions]

/-- The original source compiler's certificate checks the specialized fixed
template against the independently defined contextual source instantiation. -/
theorem fixedTemplate_evidence_checked [DecidableEq Head] {M : List (Binding.MetaArity S)}
    (names : Names S) (metavariableNames : Fin M.length → DeclName)
    (positions : DeclName → Option (Fin M.length))
    (operatorPositions : ∀ {sort : S.Srt} (operator : S.Op sort), positions (names.operator operator) = none)
    (metavariablePositions : ∀ index, positions (metavariableNames index) = some index)
    {ambient source target : Binding.Ctx S} (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort) :
    (compileEvidence (Head := Head) names bodies environment valuation term).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (interpret (specializedValues positions (ambientFunctions names (bodyPrograms names bodies) environment))
        (encodeSub names valuation) (fixedTemplate names (fun index => .const (metavariableNames index)) term))
      (encode names (Binding.ContextualAssignment.instantiate bodies environment valuation term)) = true := by
  rw [fixedTemplate_specialize names metavariableNames positions operatorPositions metavariablePositions]
  exact compileEvidence_checked names bodies environment valuation term

#print axioms fixedTemplate_specialize

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.Schema

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding

open Mettapedia.OSLF

variable {S : Binding.Signature} {Head : Type}

/-- The literal declared head of an application spine. Other native syntax
does not pretend to be a declared source constructor. -/
private def constructorHead {scope : Nat} : Tm Head scope → Option DeclName
  | .const name => some name
  | .app function _ => constructorHead function
  | _ => none

private theorem constructorHead_applyArguments (names : Names S) :
    ∀ {source : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
      (function : Tm Head source.length) (arguments : Binding.Args S arity source),
      constructorHead (applyArguments names function arguments) = constructorHead function
  | _, _, _, .nil => rfl
  | _, _, function, .cons (bs := bound) body rest => by
      simpa only [applyArguments, constructorHead] using
        constructorHead_applyArguments names (.app function (abstract bound (encode names body))) rest

theorem abstract_injective {source : Binding.Ctx S} (bound : Binding.Ctx S) :
    Function.Injective (abstract (Head := Head) (gamma := source) bound) := by
  induction bound with
  | nil => intro first last equal; exact equal
  | cons sort bound ih =>
      intro first last equal
      exact Tm.lam.inj (ih equal)

mutual
  theorem encode_injective_of_operator_names (names : Names S)
      (operators : ∀ {sort : S.Srt}, Function.Injective (names.operator (sort := sort))) :
      ∀ {source : Binding.Ctx S} {sort : S.Srt} (first last : Binding.Term S source sort),
      encode (Head := Head) names first = encode names last → first = last
    | _, _, .var first, .var last, equal => by
        exact congrArg Binding.Term.var (Binding.varIdx_injective first last (Tm.var.inj equal))
    | _, _, .var first, .op operator arguments, equal => by
        have heads := congrArg constructorHead equal
        simp only [encode, constructorHead, constructorHead_applyArguments] at heads
        contradiction
    | _, _, .op operator arguments, .var last, equal => by
        have heads := congrArg constructorHead equal
        simp only [encode, constructorHead, constructorHead_applyArguments] at heads
        contradiction
    | _, _, .op first firstArguments, .op last lastArguments, equal => by
        have heads := congrArg constructorHead equal
        simp only [encode, constructorHead_applyArguments, constructorHead, Option.some.injEq] at heads
        have same := operators heads
        cases same
        have arguments := applyArguments_injective_of_operator_names names @operators
          (.const (names.operator first)) (.const (names.operator first)) firstArguments lastArguments equal
        exact congrArg (Binding.Term.op first) arguments.1
  termination_by _ _ first _ _ => 2 * Binding.termSize first
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem applyArguments_injective_of_operator_names (names : Names S)
      (operators : ∀ {sort : S.Srt}, Function.Injective (names.operator (sort := sort))) :
      ∀ {source : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (firstHead lastHead : Tm Head source.length)
        (first last : Binding.Args S arity source),
        applyArguments names firstHead first = applyArguments names lastHead last →
          first = last ∧ firstHead = lastHead
    | _, _, _, _, .nil, .nil, equal => ⟨rfl, equal⟩
    | _, _, firstHead, lastHead, .cons (bs := bound) firstBody firstRest,
        .cons lastBody lastRest, equal => by
        have rest := applyArguments_injective_of_operator_names names @operators
          (.app firstHead (abstract bound (encode names firstBody)))
          (.app lastHead (abstract bound (encode names lastBody))) firstRest lastRest equal
        have applied := Tm.app.inj rest.2
        have bodies := encode_injective_of_operator_names names @operators firstBody lastBody
          (abstract_injective bound applied.2)
        cases bodies
        cases rest.1
        exact ⟨rfl, applied.1⟩
  termination_by _ _ _ _ first _ _ => 2 * Binding.argsSize first + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos firstBody; omega
end


open ConstantSubstitution

private theorem app_noStep {root : RootComputation Head} {headEq : Head → Head → Prop}
    (empty : RootFree root) {scope : Nat} {function argument : Tm Head scope}
    (functionNormal : ∀ {target}, ¬ Step headEq function target root)
    (argumentNormal : ∀ {target}, ¬ Step headEq argument target root)
    (notLambda : ∀ body, function ≠ .lam body) :
    ∀ {target}, ¬ Step headEq (.app function argument) target root := by
  intro target step
  cases step with
  | betaPi body _ => exact notLambda body rfl
  | root step => exact empty step
  | congAppFun inner => exact functionNormal inner
  | congAppArg inner => exact argumentNormal inner

private theorem lam_noStep {root : RootComputation Head} {headEq : Head → Head → Prop}
    (empty : RootFree root) {scope : Nat} {body : Tm Head (scope + 1)}
    (normal : ∀ {target}, ¬ Step headEq body target root) :
    ∀ {target}, ¬ Step headEq (.lam body) target root := by
  intro target step
  cases step with
  | root step => exact empty step
  | congLam inner => exact normal inner

theorem abstract_noStep {root : RootComputation Head} {headEq : Head → Head → Prop}
    (empty : RootFree root) {source : Binding.Ctx S} (bound : Binding.Ctx S)
    (body : Tm Head (bound ++ source).length)
    (normal : ∀ {target}, ¬ Step headEq body target root) :
    ∀ {target}, ¬ Step headEq (abstract bound body) target root := by
  induction bound with
  | nil => exact normal
  | cons sort bound ih => exact ih (.lam body) (lam_noStep empty normal)

mutual
  theorem encode_noStep (names : Names S) {root : RootComputation Head} {headEq : Head → Head → Prop}
      (empty : RootFree root) :
      ∀ {source : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S source sort)
        {target : Tm Head source.length}, ¬ Step headEq (encode names term) target root
    | _, _, .var position, _, step => by
        cases step with
        | root step => exact empty step
    | _, _, .op operator arguments, _, step => by
        exact applyArguments_noStep names (headEq := headEq) empty (.const (names.operator operator))
          (by intro target step; cases step with | root step => exact empty step)
          (by intro body equal; cases equal) arguments step
  termination_by _ _ term _ _ => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem applyArguments_noStep (names : Names S) {root : RootComputation Head} {headEq : Head → Head → Prop}
      (empty : RootFree root) :
      ∀ {source : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (function : Tm Head source.length),
        (∀ {target}, ¬ Step headEq function target root) →
        (∀ body, function ≠ .lam body) →
        ∀ (arguments : Binding.Args S arity source) {target : Tm Head source.length},
          ¬ Step headEq (applyArguments names function arguments) target root
    | _, _, _, normal, _, .nil, _, step => normal step
    | _, _, function, normal, notLambda, .cons (bs := bound) body rest, _, step => by
        have bodyNormal : ∀ {target}, ¬ Step headEq (abstract bound (encode names body)) target root :=
          abstract_noStep empty bound (encode names body) (encode_noStep names empty body)
        exact applyArguments_noStep names (headEq := headEq) empty (.app function (abstract bound (encode names body)))
          (app_noStep empty normal bodyNormal notLambda) (by intro body equal; cases equal) rest step
  termination_by _ _ _ _ _ arguments _ _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding


set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.Schema
open Mettapedia.OSLF
open FormationSensitive TelescopeAbstraction
variable {S : Binding.Signature} {M : List (Binding.MetaArity S)} {Head : Type}

/-- Local authority of a constructor or a submitted function primitive. The
second branch uses the compiler's actual dependency telescope order. -/
def ProgramPrimitive (names : Names S) (rules : Rules Head) (programs : Fin M.length → Tm Head 0) :
    {sort : S.Srt} → (Binding.withMetas S M).Op sort → Prop
  | _, .inl operator => rules.constantType (names.operator operator) = some (operatorType names operator)
  | _, .inr (.mk index) => Typing rules .nil (programs index)
      (closeType (context names ((M.get index).1 ++ [])) (liftClosed (sortType names (M.get index).2)))

theorem aritySorts_withMetas (arity : List (List S.Srt × S.Srt)) :
    aritySorts (S := Binding.withMetas S M) arity = aritySorts (S := S) arity := by
  induction arity with
  | nil => rfl
  | cons head tail ih => simp only [aritySorts, ih]

mutual
  theorem fixedTemplate_typing_supported {names : Names S} {rules : Rules Head} {support : S.Srt → Prop}
      (realization : SupportedSortRealization names rules support) (programs : Fin M.length → Tm Head 0) :
      ∀ {source : Binding.Ctx S} {sort : S.Srt}
        (term : Binding.Term (Binding.withMetas S M) source sort),
        term.AllOperators (ProgramPrimitive names rules programs) →
        (∀ used ∈ usedSorts term, support used) →
        Typing rules (context names source) (fixedTemplate names programs term) (sortType names sort)
    | _, _, .var position, .var _, _ => by
        simpa only [fixedTemplate, compileWithPrograms, encode, SortRealization.context_lookup] using
          (Typing.var (R := rules) (Γ := context names _) (Binding.varIdx position))
    | source, sort, .op (.inl operator) arguments, .op _ _ known children, covered => by
        have resultCovered := covered sort List.mem_cons_self
        have argsCovered : ∀ used ∈ usedArgumentSorts arguments, support used :=
          fun used member => covered used (List.mem_cons_of_mem _ member)
        have constructor := Typing.const (Γ := context names source) known
          (realization.operatorType_formed operator resultCovered
            (fun used member => argsCovered used (aritySorts_subset_usedArgumentSorts arguments (by change used ∈ aritySorts (S := Binding.withMetas S M) (S.arity operator); rw [aritySorts_withMetas]; exact member))))
          realization.universeIs
        simpa only [fixedTemplate, compileWithPrograms, sortType, liftClosed, rename] using
          fixedArguments_typing_supported realization programs arguments children argsCovered
            (realization.sortType_formed .nil sort resultCovered) constructor
    | source, _, .op (.inr (.mk index)) arguments, .op _ _ known children, covered => by
        have argsCovered : ∀ used ∈ usedArgumentSorts arguments, support used :=
          fun used member => covered used (List.mem_cons_of_mem _ member)
        have dependencies := fixedMetaArguments_typing_supported realization programs (M.get index).1 arguments
          children argsCovered
        have environmentTyped : FormationSensitive.CtxMor rules (context names ([] : Binding.Ctx S)) (context names source)
            (encodeSub (Head := Head) names emptyEnvironment) := by
          intro position
          exact Fin.elim0 position
        have combined := concatSub_typed (S := S) (Head := Head) names (rules := rules) (ambient := []) (target := source)
          (M.get index).1 dependencies environmentTyped
        change Typing rules .nil (programs index)
          (closeType (context names ((M.get index).1 ++ [])) (liftClosed (sortType names (M.get index).2))) at known
        have closed := known.renameTyping (Δ := context names source) (ρ := Fin.elim0) (fun position => Fin.elim0 position)
        have applied := FormationCheckedTelescopePrograms.apply_typed combined closed
        simpa only [fixedTemplate, compileWithPrograms, sortType, subst_liftClosed, liftClosed, rename, subst] using applied
  termination_by _ _ term _ _ => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem fixedArguments_typing_supported {names : Names S} {rules : Rules Head} {support : S.Srt → Prop}
      (realization : SupportedSortRealization names rules support) (programs : Fin M.length → Tm Head 0) :
      ∀ {source : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (arguments : Binding.Args (Binding.withMetas S M) arity source),
        arguments.AllOperators (ProgramPrimitive names rules programs) →
        (∀ used ∈ usedArgumentSorts arguments, support used) →
        ∀ {result : Tm Head 0}, Typing rules .nil result (.head realization.typeUniverse) →
        ∀ {head : Tm Head source.length},
        Typing rules (context names source) head (liftClosed (argumentsType names arity result)) →
        Typing rules (context names source)
          (compileArgumentsWithPrograms names programs emptyEnvironment (fun _ position => .var position) head arguments)
          (liftClosed result)
    | _, _, .nil, .nil, _, _, _, _, typed => by
        simpa only [compileArgumentsWithPrograms, argumentsType] using typed
    | _, _, .cons (bs := bound) (s := sort) body rest, .cons _ _ bodyInstalled restInstalled, covered,
        result, formed, head, typed => by
        have boundCovered : ∀ used ∈ bound, support used := fun used member => covered used (List.mem_append_left _ member)
        have sortCovered := covered sort (List.mem_append_right _ List.mem_cons_self)
        have bodyCovered : ∀ used ∈ usedSorts body, support used := fun used member => covered used
          (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ member)))
        have restCovered : ∀ used ∈ usedArgumentSorts rest, support used := fun used member => covered used
          (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
        have bodyTyped := realization.abstract_typing bound boundCovered
          (realization.sortType_formed .nil sort sortCovered) (fixedTemplate names programs body)
          (fixedTemplate_typing_supported realization programs body bodyInstalled bodyCovered)
        have functionTyped := typed
        change Typing rules _ head (liftClosed (closedArrow _ _)) at functionTyped
        rw [liftClosed_closedArrow] at functionTyped
        have applied := Typing.appElim functionTyped bodyTyped
        simp only [inst0, subst_liftClosed] at applied
        simpa only [compileArgumentsWithPrograms, emptyEnvironment_weaken, Binding.liftSub_var, fixedTemplate] using
          fixedArguments_typing_supported realization programs rest restInstalled restCovered formed applied
  termination_by _ _ arguments _ _ _ _ _ _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  theorem fixedMetaArguments_typing_supported {names : Names S} {rules : Rules Head} {support : S.Srt → Prop}
      (realization : SupportedSortRealization names rules support) (programs : Fin M.length → Tm Head 0) :
      ∀ {source : Binding.Ctx S} (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S M) (dependencies.map fun sort => ([], sort)) source),
        arguments.AllOperators (ProgramPrimitive names rules programs) →
        (∀ used ∈ usedArgumentSorts arguments, support used) →
        FormationSensitive.CtxMor rules (context names dependencies) (context names source)
          (compileMetaArgumentsWithPrograms names programs emptyEnvironment (fun _ position => .var position) dependencies arguments)
    | _, [], .nil, .nil, _ => by intro position; exact Fin.elim0 position
    | _, sort :: dependencies, .cons body rest, .cons _ _ bodyInstalled restInstalled, covered => by
        have bodyCovered : ∀ used ∈ usedSorts body, support used := fun used member => covered used
          (List.mem_cons_of_mem _ (List.mem_append_left _ member))
        have restCovered : ∀ used ∈ usedArgumentSorts rest, support used := fun used member => covered used
          (List.mem_cons_of_mem _ (List.mem_append_right _ member))
        have previous := fixedMetaArguments_typing_supported realization programs dependencies rest restInstalled restCovered
        have newest := fixedTemplate_typing_supported realization programs body bodyInstalled bodyCovered
        simp only [compileMetaArgumentsWithPrograms, emptyEnvironment_weaken, Binding.liftSub_var]
        apply previous.extend
        simpa only [sortType, subst, fixedTemplate, List.nil_append] using newest
  termination_by _ _ arguments _ _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.Schema
