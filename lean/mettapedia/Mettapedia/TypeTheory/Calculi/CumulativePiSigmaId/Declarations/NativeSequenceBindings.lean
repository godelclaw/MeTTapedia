import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeJoins
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity

/-!
# Native natural sequences and finite binding prefixes

A sequence has the actual native function type `Nat → A`. A finite
multiple-binder program receives its body closure and a sequence, then feeds
the required prefix to the closure in lexical lambda order. Sequence index
zero denotes the innermost source binder. No finite list replaces the full
sequence carrier, and no sequence evaluator or unification oracle is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeSequenceBindings

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open BindingSignatureEmbedding
open NativeNaturalVectorFamilies (natName zeroName succName natTm zeroTm succApp
  natType zeroType succType)

variable {n m k : Nat}

/-- The actual three original natural-number declarations are retained. -/
structure NaturalLookups (signature : Signature Tower.Head) : Prop where
  natural : signature.typeOf? natName = some natType
  zero : signature.typeOf? zeroName = some zeroType
  successor : signature.typeOf? succName = some succType

theorem originalNaturals : NaturalLookups NativeNaturalVectorFamilies.rawSignature where
  natural := NativeNaturalVectorFamilies.typeOf_nat
  zero := NativeNaturalVectorFamilies.typeOf_zero
  successor := NativeNaturalVectorFamilies.typeOf_succ

abbrev rules (signature : Signature Tower.Head) : Rules Tower.Head :=
  extendRules Tower.rules signature

abbrev Typing (signature : Signature Tower.Head) {n : Nat} :=
  FormationSensitive.Typing (rules signature) (n := n)

private theorem constant_known {signature : Signature Tower.Head}
    {name : DeclName} {type : Tower.Tm 0}
    (read : signature.typeOf? name = some type) :
    (rules signature).constantType name = some type :=
  combinedType_of_signature Tower.rules signature rfl read

/-- The native Nat type receives formation from its actual declaration. -/
theorem natural_formed {signature : Signature Tower.Head}
    (lookups : NaturalLookups signature) {context : Tower.Ctx n} :
    Typing signature context natTm (sortTm Tower.zero) := by
  have declared := FormationSensitive.Typing.const (Γ := context)
    (constant_known lookups.natural)
    (FormationSensitive.Typing.headType (R := rules signature) (.sort Tower.zero))
    (.sort (.succ Tower.zero))
  simpa only [natTm, natType, NativeNaturalVectorFamilies.natLevel,
    liftClosed, sortTm, Presentation.rename] using declared

theorem zero_typed {signature : Signature Tower.Head}
    (lookups : NaturalLookups signature) {context : Tower.Ctx n} :
    Typing signature context zeroTm natTm := by
  have declared := FormationSensitive.Typing.const (Γ := context)
    (constant_known lookups.zero) (natural_formed lookups) (.sort Tower.zero)
  simpa only [zeroTm, zeroType, natTm, liftClosed, Presentation.rename] using declared

/-- Product formation uses the actual cumulative zero-level join. -/
theorem closedArrow_formed {signature : Signature Tower.Head}
    {domain codomain : Tower.Tm 0}
    (domainFormed : Typing signature .nil domain (sortTm Tower.zero))
    (codomainFormed : Typing signature .nil codomain (sortTm Tower.zero)) :
    Typing signature .nil (closedArrow domain codomain) (sortTm Tower.zero) := by
  have inside := FormationCheckedTelescopePrograms.liftClosed_typing
    codomainFormed (.snoc .nil domain)
  change Typing signature (.snoc .nil domain) (liftClosed codomain) (sortTm Tower.zero) at inside
  exact .cumul (.piForm domainFormed (.sort Tower.zero) inside (.sort Tower.zero)
    (.sorts Tower.zero Tower.zero)) (by
      intro valuation
      simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero])

theorem successor_typed {signature : Signature Tower.Head}
    (lookups : NaturalLookups signature) {context : Tower.Ctx n} :
    Typing signature context (.const succName) (liftClosed succType) := by
  have natural := natural_formed lookups (context := .nil)
  have formed : Typing signature .nil succType (sortTm Tower.zero) :=
    closedArrow_formed natural natural
  exact .const (constant_known lookups.successor) formed (.sort Tower.zero)

/-- Application retains the exact displayed closed codomain. -/
theorem apply_closedArrow {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {function argument : Tower.Tm n} {domain codomain : Tower.Tm 0}
    (functionTyped : Typing signature context function (liftClosed (closedArrow domain codomain)))
    (argumentTyped : Typing signature context argument (liftClosed domain)) :
    Typing signature context (.app function argument) (liftClosed codomain) := by
  rw [liftClosed_closedArrow] at functionTyped
  simpa only [inst0, subst_liftClosed] using
    (FormationSensitive.Typing.appElim functionTyped argumentTyped)

/-- Constructor numerals use the original native Nat constants. -/
def numeral : Nat → Tower.Tm n
  | 0 => zeroTm
  | number + 1 => succApp (numeral number)

@[simp] theorem numeral_rename (action : Ren n m) (number : Nat) :
    Presentation.rename action (numeral number) = numeral number := by
  induction number with
  | zero => rfl
  | succ number ih => simp only [numeral, succApp, Presentation.rename, ih]

@[simp] theorem numeral_substitute (action : Sub Tower.Head n m) (number : Nat) :
    Presentation.subst action (numeral number) = numeral number := by
  induction number with
  | zero => rfl
  | succ number ih => simp only [numeral, succApp, Presentation.subst, ih]

theorem numeral_typed {signature : Signature Tower.Head}
    (lookups : NaturalLookups signature) (number : Nat) {context : Tower.Ctx n} :
    Typing signature context (numeral number) natTm := by
  induction number with
  | zero => exact zero_typed lookups
  | succ number ih => exact apply_closedArrow (domain := natTm) (codomain := natTm) (successor_typed lookups) ih

def sequenceType (element : Tower.Tm 0) : Tower.Tm 0 :=
  closedArrow natTm element

/-- The body closure receives the outermost binder first. -/
def curriedType (count : Nat) (domain codomain : Tower.Tm 0) : Tower.Tm 0 :=
  (List.replicate count domain).foldr closedArrow codomain

@[simp] theorem curriedType_zero (domain codomain : Tower.Tm 0) :
    curriedType 0 domain codomain = codomain := rfl

@[simp] theorem curriedType_succ (count : Nat) (domain codomain : Tower.Tm 0) :
    curriedType (count + 1) domain codomain = closedArrow domain (curriedType count domain codomain) := by
  simp only [curriedType, List.replicate_succ, List.foldr_cons]

private theorem curriedType_tail (count : Nat) (domain codomain : Tower.Tm 0) :
    curriedType count domain (closedArrow domain codomain) =
      closedArrow domain (curriedType count domain codomain) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [curriedType_succ, ih]

/-- The existing binding-spine type supplies exactly this closure type;
no second source binder representation is introduced. -/
theorem curriedType_bindingSpine {source : Mettapedia.OSLF.Binding.Signature}
    (types : ClosedOperators.Types source Tower.Head) (domain : source.Srt)
    (codomain : Tower.Tm 0) (count : Nat) :
    ClosedOperators.spineType types (List.replicate count domain) codomain =
      curriedType count (types domain) codomain := by
  induction count generalizing codomain with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, ClosedOperators.spineType, ih,
        curriedType_succ, curriedType_tail]

theorem sequenceType_formed {signature : Signature Tower.Head}
    (lookups : NaturalLookups signature) {element : Tower.Tm 0}
    (formed : Typing signature .nil element (sortTm Tower.zero)) :
    Typing signature .nil (sequenceType element) (sortTm Tower.zero) :=
  closedArrow_formed (natural_formed lookups) formed

theorem curriedType_formed {signature : Signature Tower.Head}
    (count : Nat) {domain codomain : Tower.Tm 0}
    (domainFormed : Typing signature .nil domain (sortTm Tower.zero))
    (codomainFormed : Typing signature .nil codomain (sortTm Tower.zero)) :
    Typing signature .nil (curriedType count domain codomain) (sortTm Tower.zero) := by
  induction count with
  | zero => exact codomainFormed
  | succ count ih =>
      rw [curriedType_succ]
      exact closedArrow_formed domainFormed ih

/-- A count of k reads precisely sequence positions k-1,...,0. Feeding
that order to nested lambdas assigns position zero to the innermost binder. -/
def applyPrefix : Nat → Tower.Tm n → Tower.Tm n → Tower.Tm n
  | 0, body, _ => body
  | count + 1, body, sequence =>
      applyPrefix count (.app body (.app sequence (numeral count))) sequence

@[simp] theorem applyPrefix_rename (action : Ren n m) (count : Nat)
    (body sequence : Tower.Tm n) :
    Presentation.rename action (applyPrefix count body sequence) =
      applyPrefix count (Presentation.rename action body) (Presentation.rename action sequence) := by
  induction count generalizing body with
  | zero => rfl
  | succ count ih => simp only [applyPrefix, ih, Presentation.rename, numeral_rename]

@[simp] theorem applyPrefix_substitute (action : Sub Tower.Head n m) (count : Nat)
    (body sequence : Tower.Tm n) :
    Presentation.subst action (applyPrefix count body sequence) =
      applyPrefix count (Presentation.subst action body) (Presentation.subst action sequence) := by
  induction count generalizing body with
  | zero => rfl
  | succ count ih => simp only [applyPrefix, ih, Presentation.subst, numeral_substitute]

/-- The finite prefix application is typed for every native context and
all closures, not only closures compiled from selected source fixtures. -/
theorem applyPrefix_typed {signature : Signature Tower.Head}
    (lookups : NaturalLookups signature) {context : Tower.Ctx n}
    (count : Nat) {domain codomain : Tower.Tm 0} {body sequence : Tower.Tm n}
    (bodyTyped : Typing signature context body (liftClosed (curriedType count domain codomain)))
    (sequenceTyped : Typing signature context sequence (liftClosed (sequenceType domain))) :
    Typing signature context (applyPrefix count body sequence) (liftClosed codomain) := by
  induction count generalizing body with
  | zero => exact bodyTyped
  | succ count ih =>
      rw [curriedType_succ] at bodyTyped
      have selected : Typing signature context (.app sequence (numeral count)) (liftClosed domain) :=
        apply_closedArrow sequenceTyped (numeral_typed lookups count)
      exact ih (apply_closedArrow bodyTyped selected)

/-- This independent list view makes every read position explicit. -/
theorem applyPrefix_spine (count : Nat) (body sequence : Tower.Tm n) :
    applyPrefix count body sequence =
      ((List.range count).reverse.map (fun index => Tm.app sequence (numeral index))).foldl Tm.app body := by
  induction count generalizing body with
  | zero => rfl
  | succ count ih =>
      simp only [applyPrefix, ih, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.map_append, List.map_singleton,
        List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The finite source binder prefix is filled from the selected values;
all remaining ambient positions retain the supplied simultaneous action. -/
def prefixSub {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source}
    (bound : List source.Srt) (values : Nat → Tower.Tm m)
    (action : Sub Tower.Head ambient.length m) :
    Sub Tower.Head (bound ++ ambient).length m :=
  match bound with
  | [] => action
  | _ :: rest => Fin.cases (values 0)
      (prefixSub rest (fun index => values (index + 1)) action)

/-- Every original binder position reads its same numbered sequence value. -/
theorem prefixSub_bound {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source}
    (bound : List source.Srt) (values : Nat → Tower.Tm m)
    (action : Sub Tower.Head ambient.length m) (index : Fin bound.length) :
    prefixSub bound values action
      ⟨index.val, by simp only [List.length_append]; omega⟩ = values index.val := by
  induction bound generalizing values with
  | nil => exact Fin.elim0 index
  | cons sort rest ih =>
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · have position :
            (⟨prior.succ.val, by simp only [List.length_append, List.length_cons, Fin.val_succ]; omega⟩ :
              Fin ((sort :: rest) ++ ambient).length) =
            (⟨prior.val, by simp only [List.length_append]; omega⟩ :
              Fin (rest ++ ambient).length).succ := by
          apply Fin.ext
          rfl
        rw [position]
        exact ih (fun position => values (position + 1)) prior

/-- Filling the finite binder prefix does not skip or replay ambient slots. -/
theorem prefixSub_ambient {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source}
    (bound : List source.Srt) (values : Nat → Tower.Tm m)
    (action : Sub Tower.Head ambient.length m) (index : Fin ambient.length) :
    prefixSub bound values action
      ⟨bound.length + index.val, by simp only [List.length_append]; omega⟩ = action index := by
  induction bound generalizing values with
  | nil =>
      simp only [prefixSub]
      apply congrArg action
      apply Fin.ext
      simp only [List.length_nil, Nat.zero_add]
  | cons sort rest ih =>
      have position :
          (⟨(sort :: rest).length + index.val, by simp only [List.length_append]; omega⟩ :
            Fin ((sort :: rest) ++ ambient).length) =
          (⟨rest.length + index.val, by simp only [List.length_append]; omega⟩ :
            Fin (rest ++ ambient).length).succ := by
        apply Fin.ext
        simp only [List.length_cons, Fin.val_succ]
        omega
      rw [position]
      exact ih (fun position => values (position + 1))

theorem prefixSub_substitute {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source}
    (bound : List source.Srt) (values : Nat → Tower.Tm m)
    (action : Sub Tower.Head ambient.length m) (later : Sub Tower.Head m k) :
    (fun index => Presentation.subst later (prefixSub bound values action index)) =
      prefixSub bound (fun position => Presentation.subst later (values position))
        (fun position => Presentation.subst later (action position)) := by
  induction bound generalizing values with
  | nil => rfl
  | cons sort rest ih =>
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · exact congrFun (ih (fun position => values (position + 1))) prior

/-- The existing telescope uses each supplied position once, in lexical
application order. No default argument or unbounded lookup is introduced. -/
theorem applyClosed_arguments (context : Tower.Ctx n) (values : Sub Tower.Head n m)
    (function : Tower.Tm m) :
    TelescopeAbstraction.applyClosed context values function =
      ((List.finRange n).reverse.map values).foldl Tm.app function := by
  induction context with
  | nil => rfl
  | snoc prior domain ih =>
      simp only [TelescopeAbstraction.applyClosed, ih, List.finRange_succ,
        List.reverse_cons, ← List.map_reverse, List.map_append, List.map_singleton,
        List.map_map, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Function.comp_def]

/-- The existing telescope application exposes exactly its finite list of
selected arguments. This uses its original application function. -/
theorem applyClosed_values (context : Tower.Ctx n) (values : Nat → Tower.Tm m)
    (function : Tower.Tm m) :
    TelescopeAbstraction.applyClosed context (fun index => values index.val) function =
      ((List.range n).reverse.map values).foldl Tm.app function := by
  induction context generalizing values function with
  | nil => rfl
  | snoc prior domain ih =>
      simp only [TelescopeAbstraction.applyClosed, Fin.val_succ]
      rw [ih (fun index => values (index + 1)) function]
      simp only [List.range_succ_eq_map, List.reverse_cons,
        ← List.map_reverse, List.map_append, List.map_singleton,
        List.map_map, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Function.comp_def]
      rfl

/-- Applying the existing abstraction to its selected values computes the
actual simultaneous substitution, including an arbitrary ambient action. -/
theorem abstract_prefix_beta {source : Mettapedia.OSLF.Binding.Signature}
    (types : ClosedOperators.Types source Tower.Head)
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (values : Nat → Tower.Tm m)
    (action : Sub Tower.Head ambient.length m) :
    TelescopeAbstraction.BetaSteps
      (TelescopeAbstraction.applyClosed (ClosedOperators.typeContext types bound)
        (fun index => values index.val) (Presentation.subst action (abstract bound body)))
      (Presentation.subst (prefixSub bound values action) body) := by
  induction bound generalizing values with
  | nil => exact .refl
  | cons sort rest ih =>
      have earlier := ih (.lam body) (fun index => values (index + 1))
      have applied := earlier.lift
        (fun function : Tower.Tm m => Tm.app function (values 0))
        (fun _ _ step => StepCore.congAppFun step)
      refine Relation.ReflTransGen.tail applied ?_
      change StepCore (RootComputation.empty : RootComputation Tower.Head) (fun _ _ => False)
        (.app (.lam (Presentation.subst
          (liftSub (prefixSub rest (fun index => values (index + 1)) action)) body)) (values 0))
        (Presentation.subst (consSub (values 0)
          (prefixSub rest (fun index => values (index + 1)) action)) body)
      rw [subst_consSub]
      exact StepCore.betaPi _ _

/-- The multiple-binder program feeds position zero to the innermost
binder and preserves every ambient variable. No closure image restriction
is needed for the body computation. -/
theorem applyPrefix_abstract {source : Mettapedia.OSLF.Binding.Signature}
    (types : ClosedOperators.Types source Tower.Head)
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (sequence : Tower.Tm ambient.length) :
    TelescopeAbstraction.BetaSteps
      (applyPrefix bound.length (abstract bound body) sequence)
      (Presentation.subst (prefixSub bound
        (fun index => Tm.app sequence (numeral index)) ids) body) := by
  have actual := abstract_prefix_beta types bound body
    (fun index => Tm.app sequence (numeral index)) ids
  rw [applyClosed_values _ (fun index => Tm.app sequence (numeral index))] at actual
  simpa only [subst_ids, applyPrefix_spine] using actual

/-- This closed native program takes a body closure and an unbounded
sequence. Its finite code contains the declared binder count. -/
def introduction (count : Nat) : Tower.Tm 0 :=
  .lam (.lam (applyPrefix count (.var (0 : Fin 1).succ) (.var 0)))

def introductionType (count : Nat) (domain codomain : Tower.Tm 0) : Tower.Tm 0 :=
  closedArrow (curriedType count domain codomain) (closedArrow (sequenceType domain) codomain)

/-- The complete closed prefix program is formed from the actual Nat
lookups and the two supplied formed carrier types. -/
theorem introduction_typed {signature : Signature Tower.Head}
    (lookups : NaturalLookups signature) (count : Nat) {domain codomain : Tower.Tm 0}
    (domainFormed : Typing signature .nil domain (sortTm Tower.zero))
    (codomainFormed : Typing signature .nil codomain (sortTm Tower.zero)) :
    Typing signature .nil (introduction count) (introductionType count domain codomain) := by
  let closure := curriedType count domain codomain
  let sequence := sequenceType domain
  let inner := closedArrow sequence codomain
  let first : Tower.Ctx 1 := .snoc .nil closure
  let second : Tower.Ctx 2 := .snoc first (liftClosed sequence)
  have closureFormed := curriedType_formed count domainFormed codomainFormed
  have sequenceFormed := sequenceType_formed lookups domainFormed
  have innerFormed := closedArrow_formed sequenceFormed codomainFormed
  have programFormed := closedArrow_formed closureFormed innerFormed
  have innerAtFirst := FormationCheckedTelescopePrograms.liftClosed_typing innerFormed first
  change Typing signature first (liftClosed inner) (sortTm Tower.zero) at innerAtFirst
  have closureVariable : Typing signature second (.var (0 : Fin 1).succ) (liftClosed closure) := by
    have actual := FormationSensitive.Typing.var (R := rules signature)
      (Γ := second) (0 : Fin 1).succ
    change Typing signature second (.var (0 : Fin 1).succ)
      (Presentation.rename wk (Presentation.rename wk closure)) at actual
    rw [rename_comp] at actual
    have same : Presentation.rename (fun index => wk (wk index)) closure = (liftClosed closure : Tower.Tm 2) :=
      rename_ext (fun index => Fin.elim0 index) closure
    exact same ▸ actual
  have sequenceVariable : Typing signature second (.var 0) (liftClosed sequence) := by
    have actual := FormationSensitive.Typing.var (R := rules signature) (Γ := second) (0 : Fin 2)
    change Typing signature second (.var 0)
      (Presentation.rename wk (liftClosed sequence)) at actual
    simpa only [rename_liftClosed] using actual
  have body := applyPrefix_typed lookups count closureVariable sequenceVariable
  have innerTyped : Typing signature first
      (.lam (applyPrefix count (.var (0 : Fin 1).succ) (.var 0))) (liftClosed inner) := by
    change Typing signature first _ (liftClosed (closedArrow sequence codomain))
    rw [liftClosed_closedArrow]
    dsimp only [inner] at innerAtFirst
    rw [liftClosed_closedArrow] at innerAtFirst
    exact .lamIntro innerAtFirst (.sort Tower.zero) body
  exact .lamIntro programFormed (.sort Tower.zero) innerTyped

@[simp] theorem lift_introduction (count : Nat) :
    (liftClosed (introduction count) : Tower.Tm n) =
      .lam (.lam (applyPrefix count (.var (0 : Fin (n + 1)).succ) (.var 0))) := by
  simp only [introduction, liftClosed, Presentation.rename, applyPrefix_rename,
    liftRen, Fin.cases_succ, Fin.cases_zero]

private theorem introduce_first (count : Nat) (body : Tower.Tm n) :
    inst0 body (.lam (applyPrefix count (.var (0 : Fin (n + 1)).succ) (.var 0))) =
      .lam (applyPrefix count (Presentation.rename wk body) (.var 0)) := by
  simp only [inst0, Presentation.subst, applyPrefix_substitute,
    liftSub, subst0, Fin.cases_succ, Fin.cases_zero]

private theorem introduce_second (count : Nat) (body sequence : Tower.Tm n) :
    inst0 sequence (applyPrefix count (Presentation.rename wk body) (.var 0)) =
      applyPrefix count body sequence := by
  simp only [inst0, applyPrefix_substitute, Presentation.subst, subst0,
    Fin.cases_zero]
  rw [← inst0, inst0_rename_wk]

open StructuralConversionCode

/-- Explicit beta replay for the original partial binding abstraction.
The ambient context is substituted, while only the declared prefix is closed. -/
def abstractPrefixCode {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source} :
    (bound : List source.Srt) → Tower.Tm (bound ++ ambient).length →
    (Nat → Tower.Tm m) → Sub Tower.Head ambient.length m →
    Code Tower.Head (fun _ => Empty) m
  | [], body, _, action => .refl (Presentation.subst action body)
  | _ :: rest, body, values, action =>
      .trans
        (Code.mapContext (fun function => .app function (values 0))
          (fun step => .congAppFun step (values 0))
          (abstractPrefixCode rest (.lam body) (fun index => values (index + 1)) action))
        (.single (.betaPi
          (Presentation.subst (liftSub (prefixSub rest (fun index => values (index + 1)) action)) body)
          (values 0)))

theorem abstractPrefixCode_checked {source : Mettapedia.OSLF.Binding.Signature}
    (types : ClosedOperators.Types source Tower.Head)
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (values : Nat → Tower.Tm m)
    (action : Sub Tower.Head ambient.length m) :
    (abstractPrefixCode bound body values action).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (TelescopeAbstraction.applyClosed (ClosedOperators.typeContext types bound)
        (fun index => values index.val) (Presentation.subst action (abstract bound body)))
      (Presentation.subst (prefixSub bound values action) body) = true := by
  induction bound generalizing values with
  | nil => exact Code.check_refl _ _ _
  | cons sort rest ih =>
      have earlier := ih (.lam body) (fun index => values (index + 1))
      have applied := Code.check_mapContext (fun _ _ : Tower.Head => False)
        FormationCheckedTelescopePrograms.noRoot
        (fun function => .app function (values 0)) (fun step => .congAppFun step (values 0))
        (fun _ => rfl) earlier
      have beta : Code.check (fun _ _ : Tower.Head => False)
          FormationCheckedTelescopePrograms.noRoot
          (.single (.betaPi (Presentation.subst
            (liftSub (prefixSub rest (fun index => values (index + 1)) action)) body) (values 0)))
          (.app (.lam (Presentation.subst
            (liftSub (prefixSub rest (fun index => values (index + 1)) action)) body)) (values 0))
          (Presentation.subst (prefixSub (sort :: rest) values action) body) = true := by
        change Code.check _ _ _ _ (Presentation.subst
          (consSub (values 0) (prefixSub rest (fun index => values (index + 1)) action)) body) = true
        rw [subst_consSub]
        simp only [Code.check, Code.decode, StepCode.decode, decide_true]
      simpa only [abstractPrefixCode, abstract, ClosedOperators.typeContext,
        TelescopeAbstraction.applyClosed, Presentation.subst, Fin.val_succ, Fin.val_zero] using
        Code.check_trans (fun _ _ : Tower.Head => False)
          FormationCheckedTelescopePrograms.noRoot applied beta

/-- Selected beta occurrences only; payload copying and replay comparisons
are deliberately outside this count. -/
theorem abstractPrefixCode_steps {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (values : Nat → Tower.Tm m)
    (action : Sub Tower.Head ambient.length m) :
    (abstractPrefixCode bound body values action).stepCount = bound.length := by
  induction bound generalizing values with
  | nil => rfl
  | cons sort rest ih =>
      simp only [abstractPrefixCode, Code.stepCount, Code.stepCount_mapContext,
        ih, List.length_cons]

/-- Both administrative beta steps and their literal intermediate are retained. -/
def introductionCode (count : Nat) (body sequence : Tower.Tm n) :
    Code Tower.Head (fun _ => Empty) n :=
  .trans
    (.single (.congAppFun (.betaPi (.lam (applyPrefix count (.var (0 : Fin (n + 1)).succ) (.var 0))) body) sequence))
    (.single (.betaPi (applyPrefix count (Presentation.rename wk body) (.var 0)) sequence))

theorem introductionCode_checked (count : Nat) (body sequence : Tower.Tm n) :
    (introductionCode count body sequence).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (.app (.app (liftClosed (introduction count)) body) sequence)
      (applyPrefix count body sequence) = true := by
  simp only [introductionCode, Code.check, Code.decode, StepCode.decode,
    lift_introduction, introduce_first, introduce_second, mapEndpoints,
    Option.map_some, joinEndpoints, ↓reduceIte]
  trivial

theorem introduction_steps (count : Nat) (body sequence : Tower.Tm n) :
    TelescopeAbstraction.BetaSteps
      (.app (.app (liftClosed (introduction count)) body) sequence)
      (applyPrefix count body sequence) := by
  rw [lift_introduction]
  have first := StepCore.congAppFun (a := sequence)
    (StepCore.betaPi (root := (RootComputation.empty : RootComputation Tower.Head))
      (headEq := fun _ _ => False) (.lam (applyPrefix count (.var (0 : Fin (n + 1)).succ) (.var 0))) body)
  rw [introduce_first] at first
  have second := StepCore.betaPi
    (root := (RootComputation.empty : RootComputation Tower.Head))
    (headEq := fun _ _ => False)
    (applyPrefix count (Presentation.rename wk body) (.var 0)) sequence
  rw [introduce_second] at second
  exact (Relation.ReflTransGen.single first).tail second

/-- Both the administrative program and all body-prefix beta occurrences
are retained in one explicit certificate. -/
def introductionAbstractCode {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (sequence : Tower.Tm ambient.length) :
    Code Tower.Head (fun _ => Empty) ambient.length :=
  .trans (introductionCode bound.length (abstract bound body) sequence)
    (abstractPrefixCode bound body (fun index => Tm.app sequence (numeral index)) ids)

theorem introductionAbstractCode_checked {source : Mettapedia.OSLF.Binding.Signature}
    (types : ClosedOperators.Types source Tower.Head)
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (sequence : Tower.Tm ambient.length) :
    (introductionAbstractCode bound body sequence).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (.app (.app (liftClosed (introduction bound.length)) (abstract bound body)) sequence)
      (Presentation.subst (prefixSub bound
        (fun index => Tm.app sequence (numeral index)) ids) body) = true := by
  have administrative := introductionCode_checked bound.length (abstract bound body) sequence
  have bodySteps := abstractPrefixCode_checked types bound body
    (fun index => Tm.app sequence (numeral index)) ids
  rw [applyClosed_values _ (fun index => Tm.app sequence (numeral index))] at bodySteps
  simp only [subst_ids, ← applyPrefix_spine] at bodySteps
  exact Code.check_trans (fun _ _ : Tower.Head => False)
    FormationCheckedTelescopePrograms.noRoot administrative bodySteps

/-- These are the selected beta occurrences, not a machine or byte bound. -/
theorem introductionAbstractCode_steps {source : Mettapedia.OSLF.Binding.Signature}
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (sequence : Tower.Tm ambient.length) :
    (introductionAbstractCode bound body sequence).stepCount = bound.length + 2 := by
  simp only [introductionAbstractCode, Code.stepCount, introductionCode,
    abstractPrefixCode_steps]
  omega

/-- The full closed program followed by body beta computation produces
exactly the original finite-prefix simultaneous substitution. -/
theorem introduction_abstract_steps {source : Mettapedia.OSLF.Binding.Signature}
    (types : ClosedOperators.Types source Tower.Head)
    {ambient : Mettapedia.OSLF.Binding.Ctx source} (bound : List source.Srt)
    (body : Tower.Tm (bound ++ ambient).length) (sequence : Tower.Tm ambient.length) :
    TelescopeAbstraction.BetaSteps
      (.app (.app (liftClosed (introduction bound.length)) (abstract bound body)) sequence)
      (Presentation.subst (prefixSub bound
        (fun index => Tm.app sequence (numeral index)) ids) body) :=
  (introduction_steps bound.length (abstract bound body) sequence).trans
    (applyPrefix_abstract types bound body sequence)

theorem introductionCode_steps (count : Nat) (body sequence : Tower.Tm n) :
    (introductionCode count body sequence).stepCount = 2 := rfl

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeSequenceBindings
