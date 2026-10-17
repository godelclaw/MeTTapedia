import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices
import Mettapedia.Languages.MeTTa.Experimental.StagedReflective.Presentation
import Mettapedia.OSLF.Syntax.RhoSubstitutionEncoding
import Mettapedia.OSLF.Syntax.VariablePosition
import Mettapedia.OSLF.Syntax.RhoIntrinsicReadback
import Mettapedia.OSLF.Syntax.BindingEqualityCertificates
import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree
import Mettapedia.OSLF.Syntax.RhoScopedInstanceReadout
import Mettapedia.OSLF.Syntax.RhoIntrinsicCanonicalBag
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Optional declared-calculus representation of scoped rho syntax

This is a structural encoding of the complete intrinsic rho binding syntax.
Source variables become native variables and the input continuation becomes a
native lambda. The six rho constructors have distinct declared constant names
and explicit application spines. Object-level rho quotation is one of those
constructors, not the native interpreter-staging quotation operation.

The raw staged comparison preserves renaming and substitution and admits
sorted readback. A separate concrete declaration package installs the source
sorts and constructor types in the cumulative native calculus. Directed parallel execution and the declared structural observer are compared
independently with the original scoped source judgments on the full image.
They do not change an ambient native kernel's conversion policy.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedRepresentation

open Mettapedia.OSLF.Binding
open RhoSchema
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices

def zeroName : Lean.Name := `rho.nil
def parallelName : Lean.Name := `rho.par
def outputName : Lean.Name := `rho.out
def inputName : Lean.Name := `rho.inp
def quoteName : Lean.Name := `rho.quote
def dropName : Lean.Name := `rho.drop

/-- No source variable or input binder is hidden inside an opaque pattern. -/
def encode (stage : Nat) : {Γ : Ctx sig} → {s : Srt} → Term sig Γ s →
    StagedReflectiveTm stage Γ.length
  | _, _, .var v => .var (varIdx (S := sig) v)
  | _, _, .op .nil .nil => .const zeroName
  | _, _, .op .par (.cons p (.cons q .nil)) =>
      .app (.app (.const parallelName) (encode stage p)) (encode stage q)
  | _, _, .op .out (.cons n (.cons p .nil)) =>
      .app (.app (.const outputName) (encode stage n)) (encode stage p)
  | _, _, .op .inp (.cons n (.cons p .nil)) =>
      .app (.app (.const inputName) (encode stage n)) (.lam (encode stage p))
  | _, _, .op .quo (.cons p .nil) => .app (.const quoteName) (encode stage p)
  | _, _, .op .drp (.cons n .nil) => .app (.const dropName) (encode stage n)

/-- Erase the sorts in a source renaming while retaining its actual variable
positions. Peeling the context avoids a cast or variable-recovery oracle. -/
def encodeRen : {Γ Δ : Ctx sig} → Ren sig Γ Δ → NativeRen Γ.length Δ.length
  | [], _, _, index => Fin.elim0 index
  | s :: _, _, action, index =>
      Fin.cases (varIdx (S := sig) (action s .zero))
        (encodeRen (fun t v => action t (.succ v))) index

theorem encodeRen_at_variable : ∀ {Γ Δ : Ctx sig} (action : Ren sig Γ Δ)
    {s : Srt} (v : Var Γ s), encodeRen action (varIdx (S := sig) v) = varIdx (S := sig) (action s v)
  | _, _, _, _, .zero => rfl
  | _, _, action, _, .succ v =>
      encodeRen_at_variable (fun t w => action t (.succ w)) v

theorem encodeRen_weaken {Γ : Ctx sig} {s : Srt} :
    encodeRen (fun _ v => Var.succ v : Ren sig Γ (s :: Γ)) = nativeWk := by
  funext index
  have positionLaw := encodeRen_at_variable
    (fun _ v => Var.succ v : Ren sig Γ (s :: Γ)) (varOfIdx (S := sig) Γ index)
  simpa only [varIdx, varIdx_varOfIdx, nativeWk] using positionLaw

theorem encodeRen_lift {Γ Δ : Ctx sig} (action : Ren sig Γ Δ) (bound : Srt) :
    encodeRen (liftRen action [bound]) = nativeLiftRen (encodeRen action) := by
  funext index
  have positionLaw : ∀ {s : Srt} (v : Var (bound :: Γ) s),
      encodeRen (liftRen action [bound]) (varIdx (S := sig) v) =
        nativeLiftRen (encodeRen action) (varIdx (S := sig) v) := by
    intro s v
    cases v with
    | zero => rfl
    | succ v =>
        rw [encodeRen_at_variable (liftRen action [bound]) (Var.succ v)]
        simp only [liftRen, varIdx, nativeLiftRen, Fin.cases_succ, encodeRen_at_variable]
  have result := positionLaw (varOfIdx (S := sig) (bound :: Γ) index)
  rw [varIdx_varOfIdx (S := sig) (bound :: Γ) index] at result
  exact result

/-- The complete source renaming commutes with the native action, including
the binder extension on every input continuation. -/
theorem encode_rename : ∀ {Γ Δ : Ctx sig} {s : Srt} (action : Ren sig Γ Δ)
    (term : Term sig Γ s) (stage : Nat),
    nativeRename (encodeRen action) (encode stage term) =
      encode stage (rename action term)
  | _, _, _, action, .var v, _ => by
      simp only [encode, nativeRename, rename, encodeRen_at_variable]
  | _, _, _, _, .op .nil .nil, _ => rfl
  | _, _, _, action, .op .par (.cons p (.cons q .nil)), stage => by
      simp only [encode, nativeRename, rename, renameArgs,
        encode_rename action p stage, encode_rename action q stage, liftRen]
  | _, _, _, action, .op .out (.cons n (.cons p .nil)), stage => by
      simp only [encode, nativeRename, rename, renameArgs,
        encode_rename action n stage, encode_rename action p stage, liftRen]
  | _, _, _, action, .op .inp (.cons n (.cons p .nil)), stage => by
      simp only [encode, nativeRename, rename, renameArgs, liftRen]
      rw [encode_rename action n stage, ← encodeRen_lift action Srt.nm,
        encode_rename (liftRen action [Srt.nm]) p stage]
  | _, _, _, action, .op .quo (.cons p .nil), stage => by
      simp only [encode, nativeRename, rename, renameArgs,
        encode_rename action p stage, liftRen]
  | _, _, _, action, .op .drp (.cons n .nil), stage => by
      simp only [encode, nativeRename, rename, renameArgs,
        encode_rename action n stage, liftRen]

/-- Encode every source substitution image at its actual native stage. -/
def encodeSub : {Γ Δ : Ctx sig} → Sub sig Γ Δ → NativeSub Γ.length Δ.length
  | [], _, _, _, index => Fin.elim0 index
  | s :: _, _, action, stage, index =>
      Fin.cases (encode stage (action s .zero))
        (encodeSub (fun t v => action t (.succ v)) stage) index

theorem encodeSub_at_variable : ∀ {Γ Δ : Ctx sig} (action : Sub sig Γ Δ)
    (stage : Nat) {s : Srt} (v : Var Γ s),
    encodeSub action stage (varIdx (S := sig) v) = encode stage (action s v)
  | _, _, _, _, _, .zero => rfl
  | _, _, action, stage, _, .succ v =>
      encodeSub_at_variable (fun t w => action t (.succ w)) stage v

theorem encodeSub_lift {Γ Δ : Ctx sig} (action : Sub sig Γ Δ) (bound : Srt) :
    encodeSub (liftSub action [bound]) = nativeLiftSub (encodeSub action) := by
  funext stage index
  have positionLaw : ∀ {s : Srt} (v : Var (bound :: Γ) s),
      encodeSub (liftSub action [bound]) stage (varIdx (S := sig) v) =
        nativeLiftSub (encodeSub action) stage (varIdx (S := sig) v) := by
    intro s v
    cases v with
    | zero => rfl
    | succ v =>
        rw [encodeSub_at_variable (liftSub action [bound]) stage (Var.succ v)]
        change encode stage (weaken (t := bound) (action s v)) =
          nativeRename nativeWk (encodeSub action stage (varIdx (S := sig) v))
        rw [encodeSub_at_variable]
        have renamed := encode_rename
          (fun _ w => Var.succ w : Ren sig Δ (bound :: Δ)) (action s v) stage
        simpa only [encodeRen_weaken, weaken] using renamed.symm
  have result := positionLaw (varOfIdx (S := sig) (bound :: Γ) index)
  rw [varIdx_varOfIdx (S := sig) (bound :: Γ) index] at result
  exact result

/-- Simultaneous source substitution and native substitution agree on every
sorted term and every context change, without sealing object quotation. -/
theorem encode_substitution : ∀ {Γ Δ : Ctx sig} {s : Srt} (action : Sub sig Γ Δ)
    (term : Term sig Γ s) (stage : Nat),
    nativeSubst (encodeSub action) (encode stage term) =
      encode stage (bind action term)
  | _, _, _, action, .var v, stage => by
      simp only [encode, nativeSubst, Mettapedia.OSLF.Binding.bind, encodeSub_at_variable]
  | _, _, _, _, .op .nil .nil, _ => rfl
  | _, _, _, action, .op .par (.cons p (.cons q .nil)), stage => by
      simp only [encode, nativeSubst, Mettapedia.OSLF.Binding.bind, bindArgs,
        encode_substitution action p stage, encode_substitution action q stage, liftSub]
  | _, _, _, action, .op .out (.cons n (.cons p .nil)), stage => by
      simp only [encode, nativeSubst, Mettapedia.OSLF.Binding.bind, bindArgs,
        encode_substitution action n stage, encode_substitution action p stage, liftSub]
  | _, _, _, action, .op .inp (.cons n (.cons p .nil)), stage => by
      simp only [encode, nativeSubst, Mettapedia.OSLF.Binding.bind, bindArgs, liftSub]
      rw [encode_substitution action n stage, ← encodeSub_lift action Srt.nm,
        encode_substitution (liftSub action [Srt.nm]) p stage]
  | _, _, _, action, .op .quo (.cons p .nil), stage => by
      simp only [encode, nativeSubst, Mettapedia.OSLF.Binding.bind, bindArgs,
        encode_substitution action p stage, liftSub]
  | _, _, _, action, .op .drp (.cons n .nil), stage => by
      simp only [encode, nativeSubst, Mettapedia.OSLF.Binding.bind, bindArgs,
        encode_substitution action n stage, liftSub]


/-- Decode only the declared rho application spines, checking each variable's
actual source sort and opening the input body under a name variable. -/
def decode (context : Ctx sig) (sort : Srt) {stage binders : Nat}
    (term : StagedReflectiveTm stage binders) : Option (Term sig context sort) :=
  match sort, term with
  | .nm, .var index =>
      (Mettapedia.OSLF.Binding.RhoIntrinsicReadback.variableAt context .nm index.val).map Term.var
  | .nm, .app (.const name) process =>
      if name = quoteName then
        (decode context .pr process).map (fun p => .op .quo (.cons p .nil))
      else none
  | .pr, .var index =>
      (Mettapedia.OSLF.Binding.RhoIntrinsicReadback.variableAt context .pr index.val).map Term.var
  | .pr, .const name => if name = zeroName then some (.op .nil .nil) else none
  | .pr, .app (.app (.const name) first) second =>
      if name = parallelName then do
        let p ← decode context .pr first
        let q ← decode context .pr second
        return .op .par (.cons p (.cons q .nil))
      else if name = outputName then do
        let n ← decode context .nm first
        let p ← decode context .pr second
        return .op .out (.cons n (.cons p .nil))
      else if name = inputName then
        match second with
        | .lam body => do
            let n ← decode context .nm first
            let p ← decode (Srt.nm :: context) .pr body
            return .op .inp (.cons n (.cons p .nil))
        | _ => none
      else none
  | .pr, .app (.const name) value =>
      if name = dropName then
        (decode context .nm value).map (fun n => .op .drp (.cons n .nil))
      else none
  | _, _ => none
termination_by structural term

/-- Readback recovers literal source syntax, including variables occurring
under object quotation and arbitrary input nesting. -/
theorem decode_encode : ∀ {context : Ctx sig} {sort : Srt}
    (term : Term sig context sort) (stage : Nat),
    decode context sort (encode stage term) = some term
  | _, sort, .var position, _ => by
      cases sort <;> simp only [decode, encode,
        Mettapedia.OSLF.Binding.RhoIntrinsicReadback.variableAt_index, Option.map_some]
  | _, _, .op .nil .nil, _ => by simp [decode, encode]
  | context, _, .op .par (.cons p (.cons q .nil)), stage => by
      have first := decode_encode p stage
      have second := decode_encode q stage
      simp only [List.nil_append] at first second
      rw [encode, decode.eq_def]
      simp only [↓reduceIte, first, second]
      rfl
  | context, _, .op .out (.cons n (.cons p .nil)), stage => by
      have first := decode_encode n stage
      have second := decode_encode p stage
      simp only [List.nil_append] at first second
      rw [encode, decode.eq_def]
      simp only [↓reduceIte, first, second]
      rfl
  | context, _, .op .inp (.cons n (.cons p .nil)), stage => by
      have first := decode_encode n stage
      have second := decode_encode p stage
      simp only [List.nil_append, List.cons_append] at first second
      rw [encode, decode.eq_def]
      simp only [↓reduceIte, first, second]
      rfl
  | context, _, .op .quo (.cons p .nil), stage => by
      have child := decode_encode p stage
      simp only [List.nil_append] at child
      rw [encode, decode.eq_def]
      simp only [↓reduceIte, child, Option.map_some]
  | context, _, .op .drp (.cons n .nil), stage => by
      have child := decode_encode n stage
      simp only [List.nil_append] at child
      rw [encode, decode.eq_def]
      simp only [↓reduceIte, child, Option.map_some]

/-- The scoped native encoding retains every source constructor and binder,
not just the source equation class. -/
theorem encode_injective {context : Ctx sig} {sort : Srt} (stage : Nat) :
    Function.Injective (encode stage : Term sig context sort → _) := by
  intro first second same
  have decoded := congrArg (decode context sort) same
  simpa only [decode_encode, Option.some.injEq] using decoded

/-- The six source operators do not collide as native declaration names. -/
theorem constructor_names_distinct :
    [zeroName, parallelName, outputName, inputName, quoteName, dropName].Nodup := by decide

namespace Controls

open RhoSchema.IntrinsicEncoding

/-- The source term excluded by sealed-code admission is a genuine scoped
native term here, and sorted readback recovers it unchanged. -/
theorem crossing_quote_roundtrip :
    decode [] .pr (encode 0 crossingQuote) = some crossingQuote :=
  decode_encode crossingQuote 0

/-- All closing action is performed by native substitution, not by editing
an inert runtime payload. -/
theorem native_closes_ambient_without_capture :
    nativeSubst (encodeSub closeInputAmbient) (encode 0 openInputDropsAmbient) =
      encode 0 (bind closeInputAmbient openInputDropsAmbient) :=
  encode_substitution closeInputAmbient openInputDropsAmbient 0

/-- A variable declared to be a name does not become a process variable just
because it has the same numerical de Bruijn position. -/
theorem wrong_variable_sort_refused :
    decode [Srt.nm] .pr (.var 0 : StagedReflectiveTm 0 1) = none := by decide

/-- The input constructor requires an actual native binder in its body slot. -/
theorem input_without_binder_refused :
    decode [] .pr
      (.app (.app (.const inputName) (encode 0 chan)) (.const zeroName) :
        StagedReflectiveTm 0 0) = none := by decide

/-- Object quotation is not recognized by substituting the staging syntax
or an undeclared constant for its declared operator spine. -/
theorem unknown_constructor_refused :
    decode [] .nm
      (.app (.const `rho.unknown) (.const zeroName) : StagedReflectiveTm 0 0) = none := by decide

end Controls


/-! ## The concrete declaration-backed native realization

The staged comparison above preserves raw syntax but its minimal typing core
has no rule for global declarations. The cumulative native declaration owner
provides that actual rule. This finite signature installs both source sorts
and every source constructor using the generic binding-signature interpreter;
formation is then earned from literal lookups and the existing cumulative
universe rules. The directed operations and structural observer below remain
separate from this declaration package's ambient conversion field.
-/

namespace DeclarationProfile

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration
open Mettapedia.TypeTheory.UniverseLevel

/-- One declaration naming map is shared by both rho source sorts and all
six constructors, including the input's declared binding spine. -/
def names : BindingSignatureEmbedding.Names sig where
  sort := fun sort => match sort with
    | .nm => `rho.Name
    | .pr => `rho.Process
  operator := fun {sort} operator => match sort, operator with
    | _, .nil => zeroName
    | _, .par => parallelName
    | _, .out => outputName
    | _, .inp => inputName
    | _, .quo => quoteName
    | _, .drp => dropName

def typeUniverse : Tower.Head := .sort Tower.zero
def above : Tower.Head := .sort (.succ Tower.zero)
def joined : Tower.Head := .sort (.max Tower.zero Tower.zero)

/-- These are actual opaque declaration entries, not a callback supplying
the typing of arbitrary source terms. -/
def declarations : List (DeclName × Entry Tower.Head) :=
  [(`rho.Name, { type := .head typeUniverse }),
   (`rho.Process, { type := .head typeUniverse }),
   (zeroName, { type := BindingSignatureEmbedding.operatorType names Op.nil }),
   (parallelName, { type := BindingSignatureEmbedding.operatorType names Op.par }),
   (outputName, { type := BindingSignatureEmbedding.operatorType names Op.out }),
   (inputName, { type := BindingSignatureEmbedding.operatorType names Op.inp }),
   (quoteName, { type := BindingSignatureEmbedding.operatorType names Op.quo }),
   (dropName, { type := BindingSignatureEmbedding.operatorType names Op.drp })]

def signature : Signature Tower.Head := Signature.ofList declarations

def rules : Rules Tower.Head := extendRules Tower.rules signature

theorem declaration_names_distinct : (declarations.map Prod.fst).Nodup := by decide

/-- The actual max universe is retained and then cumulatively compared
with level zero; no literal `max u u = u` universe equation is assumed. -/
def realization : BindingSignatureEmbedding.Realization names rules where
  typeUniverse := typeUniverse
  above := above
  joined := joined
  universeTyped := LevelTower.HeadTyping.sort Tower.zero
  universeIs := .sort Tower.zero
  aboveIs := .sort (.succ Tower.zero)
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    change LevelTower.Cumulative joined typeUniverse
    intro valuation
    simp [LevelExpr.eval]
  sortLookup := by intro sort; cases sort <;> decide
  operatorLookup := by intro sort operator; cases operator <;> decide

/-- Every complete intrinsic source term has a formed native judgment in
the concrete declaration history, including open terms and input binders. -/
theorem source_judgment {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (term : Mettapedia.OSLF.Binding.Term sig context sort) :
    FormationSensitive.Judgment rules (BindingSignatureEmbedding.context names context)
      (BindingSignatureEmbedding.encode names term)
      (BindingSignatureEmbedding.sortType names sort) :=
  realization.encode_judgment term

theorem crossing_quote_has_judgment :
    FormationSensitive.Judgment rules .nil
      (BindingSignatureEmbedding.encode names RhoSchema.IntrinsicEncoding.crossingQuote)
      (BindingSignatureEmbedding.sortType names Srt.pr) :=
  source_judgment RhoSchema.IntrinsicEncoding.crossingQuote

theorem unknown_declaration_refused :
    signature.typeOf? `rho.unknown = none := by decide

theorem output_does_not_have_parallel_declaration :
    signature.typeOf? outputName ≠
      some (BindingSignatureEmbedding.operatorType names Op.par) := by decide


def readback (context : Ctx sig) (sort : Srt) {binders : Nat}
    (term : Presentation.Tm Tower.Head binders) : Option (Term sig context sort) :=
  match sort, term with
  | .nm, .var index =>
      (Mettapedia.OSLF.Binding.RhoIntrinsicReadback.variableAt context .nm index.val).map Term.var
  | .nm, .app (.const name) process =>
      if name = quoteName then
        (readback context .pr process).map (fun p => .op .quo (.cons p .nil))
      else none
  | .pr, .var index =>
      (Mettapedia.OSLF.Binding.RhoIntrinsicReadback.variableAt context .pr index.val).map Term.var
  | .pr, .const name => if name = zeroName then some (.op .nil .nil) else none
  | .pr, .app (.app (.const name) first) second =>
      if name = parallelName then do
        let p ← readback context .pr first
        let q ← readback context .pr second
        return .op .par (.cons p (.cons q .nil))
      else if name = outputName then do
        let n ← readback context .nm first
        let p ← readback context .pr second
        return .op .out (.cons n (.cons p .nil))
      else if name = inputName then
        match second with
        | .lam body => do
            let n ← readback context .nm first
            let p ← readback (Srt.nm :: context) .pr body
            return .op .inp (.cons n (.cons p .nil))
        | _ => none
      else none
  | .pr, .app (.const name) value =>
      if name = dropName then
        (readback context .nm value).map (fun n => .op .drp (.cons n .nil))
      else none
  | _, _ => none
termination_by structural term

/-- Readback recovers literal source syntax, including variables occurring
under object quotation and arbitrary input nesting. -/
theorem readback_encode : ∀ {context : Ctx sig} {sort : Srt}
    (term : Term sig context sort),
    readback context sort (BindingSignatureEmbedding.encode names term) = some term
  | _, sort, .var position => by
      cases sort <;> simp only [readback, BindingSignatureEmbedding.encode,
        Mettapedia.OSLF.Binding.RhoIntrinsicReadback.variableAt_index, Option.map_some]
  | _, _, .op .nil .nil => by simp [readback, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments, names]
  | context, _, .op .par (.cons p (.cons q .nil)) => by
      have first := readback_encode p
      have second := readback_encode q
      simp only [List.nil_append] at first second
      simp only [BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names] at *
      rw [readback.eq_def]
      simp only [↓reduceIte, first, second]
      rfl
  | context, _, .op .out (.cons n (.cons p .nil)) => by
      have first := readback_encode n
      have second := readback_encode p
      simp only [List.nil_append] at first second
      simp only [BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names] at *
      rw [readback.eq_def]
      simp only [↓reduceIte, first, second]
      rfl
  | context, _, .op .inp (.cons n (.cons p .nil)) => by
      have first := readback_encode n
      have second := readback_encode p
      simp only [List.nil_append, List.cons_append] at first second
      simp only [BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names] at *
      rw [readback.eq_def]
      simp only [↓reduceIte, first, second]
      rfl
  | context, _, .op .quo (.cons p .nil) => by
      have child := readback_encode p
      simp only [List.nil_append] at child
      simp only [BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names] at *
      rw [readback.eq_def]
      simp only [↓reduceIte, child, Option.map_some]
  | context, _, .op .drp (.cons n .nil) => by
      have child := readback_encode n
      simp only [List.nil_append] at child
      simp only [BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names] at *
      rw [readback.eq_def]
      simp only [↓reduceIte, child, Option.map_some]

/-- The scoped native encoding retains every source constructor and binder,
not just the source equation class. -/
theorem declared_encode_injective {context : Ctx sig} {sort : Srt} :
    Function.Injective (BindingSignatureEmbedding.encode (Head := Tower.Head) names : Term sig context sort → _) := by
  intro first second same
  have decoded := congrArg (readback context sort) same
  simpa only [readback_encode, Option.some.injEq] using decoded


/-- Conversion evidence is the existing binding-signature equation
certificate, with finite bodies and substitution vectors. -/
abbrev EquationEvidence (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :=
  Mettapedia.OSLF.Binding.EqualityCertificates.Certificate sig metas rhoSourceE context sort

/-- Check the declared source equations on native constructor syntax. This
is a proof service; it does not make directed COMM into kernel equality. -/
def checkNativeEquation {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (proof : EquationEvidence context sort)
    (first second : Presentation.Tm Tower.Head context.length) : Bool :=
  match readback context sort first, readback context sort second with
  | some sourceFirst, some sourceSecond =>
      Mettapedia.OSLF.Binding.EqualityCertificates.check proof sourceFirst sourceSecond
  | _, _ => false

theorem checkNativeEquation_on_source {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (proof : EquationEvidence context sort)
    (first second : Mettapedia.OSLF.Binding.Term sig context sort) :
    checkNativeEquation proof (BindingSignatureEmbedding.encode names first)
      (BindingSignatureEmbedding.encode names second) =
      Mettapedia.OSLF.Binding.EqualityCertificates.check proof first second := by
  simp only [checkNativeEquation, readback_encode]

/-- The complete authored scoped equation relation is preserved and
reflected by this explicit native evidence boundary, on its full image. -/
theorem source_equation_iff_native_evidence
    {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (first second : Mettapedia.OSLF.Binding.Term sig context sort) :
    EqClosure rhoSourceE first second ↔
      ∃ proof : EquationEvidence context sort,
        checkNativeEquation proof (BindingSignatureEmbedding.encode names first)
          (BindingSignatureEmbedding.encode names second) = true := by
  simp only [checkNativeEquation_on_source]
  exact Mettapedia.OSLF.Binding.EqualityCertificates.check_complete first second

/-- Malformed native syntax cannot be rescued by an otherwise valid
source reflexivity certificate. -/
theorem unrecognized_equation_endpoint_refused :
    checkNativeEquation
      (.refl (.op Op.nil .nil) : EquationEvidence [] Srt.pr)
      (.const `rho.unknown) (.const zeroName) = false := by decide

end DeclarationProfile


/-! ## Native constructor inversion and directed rho execution -/

namespace Inversion
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation DeclarationProfile
open Mettapedia.OSLF.Binding RhoSchema
abbrev E {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (term : Mettapedia.OSLF.Binding.Term sig context sort) : Presentation.Tm Tower.Head context.length :=
  BindingSignatureEmbedding.encode names term

theorem parallel_shape {context : Mettapedia.OSLF.Binding.Ctx sig}
    (left right : Presentation.Tm Tower.Head context.length) :
    (term : Mettapedia.OSLF.Binding.Term sig context Srt.pr) →
      E term = .app (.app (.const parallelName) left) right →
      ∃ first second, term = .op Op.par (.cons first (.cons second .nil)) ∧
        E first = left ∧ E second = right
  | .var _, same => by cases same
  | .op .nil .nil, same => by cases same
  | .op .par (.cons first (.cons second .nil)), same => by
      refine ⟨first, second, rfl, ?_⟩
      simpa only [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names, Presentation.Tm.app.injEq, true_and] using same
  | .op .out (.cons _ (.cons _ .nil)), same => by
      simp [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names, parallelName, outputName] at same
  | .op .inp (.cons _ (.cons _ .nil)), same => by
      simp [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names, parallelName, inputName] at same
  | .op .drp (.cons _ .nil), same => by cases same
theorem output_shape {context : Mettapedia.OSLF.Binding.Ctx sig}
    (channel payload : Presentation.Tm Tower.Head context.length) :
    (term : Mettapedia.OSLF.Binding.Term sig context Srt.pr) →
      E term = .app (.app (.const outputName) channel) payload →
      ∃ name body, term = .op Op.out (.cons name (.cons body .nil)) ∧ E name = channel ∧ E body = payload
  | .var _, same => by
      cases same
  | .op .nil .nil, same => by
      cases same
  | .op .par (.cons first (.cons second .nil)), same => by
      simp [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments, BindingSignatureEmbedding.abstract, names, parallelName, outputName, inputName, dropName, zeroName, quoteName] at same
  | .op .out (.cons channel (.cons payload .nil)), same => by
      refine ⟨channel, payload, rfl, ?_⟩
      simpa only [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names, Presentation.Tm.app.injEq, true_and] using same
  | .op .inp (.cons channel (.cons body .nil)), same => by
      simp [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments, BindingSignatureEmbedding.abstract, names, parallelName, outputName, inputName, dropName, zeroName, quoteName] at same
  | .op .drp (.cons name .nil), same => by
      cases same

theorem input_shape {context : Mettapedia.OSLF.Binding.Ctx sig}
    (channel : Presentation.Tm Tower.Head context.length) (body : Presentation.Tm Tower.Head (context.length+1)) :
    (term : Mettapedia.OSLF.Binding.Term sig context Srt.pr) →
      E term = .app (.app (.const inputName) channel) (.lam body) →
      ∃ name continuation, term = .op Op.inp (.cons name (.cons continuation .nil)) ∧ E name = channel ∧ E continuation = body
  | .var _, same => by
      cases same
  | .op .nil .nil, same => by
      cases same
  | .op .par (.cons first (.cons second .nil)), same => by
      simp [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments, BindingSignatureEmbedding.abstract, names, parallelName, outputName, inputName, dropName, zeroName, quoteName] at same
  | .op .out (.cons channel (.cons payload .nil)), same => by
      simp [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments, BindingSignatureEmbedding.abstract, names, parallelName, outputName, inputName, dropName, zeroName, quoteName] at same
  | .op .inp (.cons channel (.cons body .nil)), same => by
      refine ⟨channel, body, rfl, ?_⟩
      simpa only [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names, Presentation.Tm.app.injEq, Presentation.Tm.lam.injEq, true_and] using same
  | .op .drp (.cons name .nil), same => by
      cases same

theorem drop_shape {context : Mettapedia.OSLF.Binding.Ctx sig}
    (name : Presentation.Tm Tower.Head context.length) :
    (term : Mettapedia.OSLF.Binding.Term sig context Srt.pr) →
      E term = .app (.const dropName) name →
      ∃ sourceName, term = .op Op.drp (.cons sourceName .nil) ∧ E sourceName = name
  | .var _, same => by
      cases same
  | .op .nil .nil, same => by
      cases same
  | .op .par (.cons first (.cons second .nil)), same => by
      cases same
  | .op .out (.cons channel (.cons payload .nil)), same => by
      cases same
  | .op .inp (.cons channel (.cons body .nil)), same => by
      cases same
  | .op .drp (.cons name .nil), same => by
      refine ⟨name, rfl, ?_⟩
      simpa only [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names, Presentation.Tm.app.injEq, true_and] using same

theorem quote_shape {context : Mettapedia.OSLF.Binding.Ctx sig}
    (payload : Presentation.Tm Tower.Head context.length) :
    (term : Mettapedia.OSLF.Binding.Term sig context Srt.nm) →
      E term = .app (.const quoteName) payload →
      ∃ sourcePayload, term = .op Op.quo (.cons sourcePayload .nil) ∧ E sourcePayload = payload
  | .var _, same => by cases same
  | .op .quo (.cons body .nil), same => by
      refine ⟨body, rfl, ?_⟩
      simpa only [E, BindingSignatureEmbedding.encode, BindingSignatureEmbedding.applyArguments,
        BindingSignatureEmbedding.abstract, names, Presentation.Tm.app.injEq, true_and] using same

end Inversion
namespace Operations
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration
open DeclarationProfile

abbrev NativeTerm (n : Nat) := Presentation.Tm Tower.Head n

def parallel {n : Nat} (first second : NativeTerm n) : NativeTerm n :=
  .app (.app (.const parallelName) first) second

def output {n : Nat} (channel payload : NativeTerm n) : NativeTerm n :=
  .app (.app (.const outputName) channel) payload

def input {n : Nat} (channel : NativeTerm n) (body : NativeTerm (n+1)) : NativeTerm n :=
  .app (.app (.const inputName) channel) (.lam body)

def quote {n : Nat} (payload : NativeTerm n) : NativeTerm n :=
  .app (.const quoteName) payload

def drop {n : Nat} (name : NativeTerm n) : NativeTerm n :=
  .app (.const dropName) name

/-- The native rule patterns compute their endpoints using native binder
instantiation. No source proof or semantic callback is a rule premise. -/
inductive Root {n : Nat} : NativeTerm n → NativeTerm n → Prop where
  | communication (channel payload : NativeTerm n) (body : NativeTerm (n+1)) :
      Root (parallel (output channel payload) (input channel body))
        (inst0 (quote payload) body)
  | reflection (payload : NativeTerm n) : Root (drop (quote payload)) payload

def directedComputation : RootComputation Tower.Head where
  step := Root
  rename := by
    intro n m action first second step
    cases step with
    | communication channel payload body =>
        simpa only [parallel, output, input, quote, Presentation.rename, rename_inst0] using
          Root.communication (Presentation.rename action channel)
            (Presentation.rename action payload) (Presentation.rename (liftRen action) body)
    | reflection _ =>
        exact Root.reflection _
  substitute := by
    intro n m action first second step
    cases step with
    | communication channel payload body =>
        simpa only [parallel, output, input, quote, subst, subst_inst0] using
          Root.communication (subst action channel) (subst action payload)
            (subst (liftSub action) body)
    | reflection _ => exact Root.reflection _

/-- Declared root codes contain only finite native arguments. -/
inductive RootCode (n : Nat) where
  | communication (channel payload : NativeTerm n) (body : NativeTerm (n+1))
  | reflection (payload : NativeTerm n)

def decodeRoot {n : Nat} : RootCode n → Option (NativeTerm n × NativeTerm n)
  | .communication channel payload body =>
      some (parallel (output channel payload) (input channel body), inst0 (quote payload) body)
  | .reflection payload => some (drop (quote payload), payload)

def decoder : StructuralConversionCode.RootDecoder directedComputation where
  Code := RootCode
  decode := decodeRoot
  sound := by
    intro n code first second decoded
    cases code with
    | communication channel payload body =>
        cases decoded
        exact Root.communication channel payload body
    | reflection payload =>
        cases decoded
        exact Root.reflection _
  complete := by
    intro n first second step
    cases step with
    | communication channel payload body =>
        exact ⟨.communication channel payload body, rfl⟩
    | reflection _ => exact ⟨.reflection _, rfl⟩



/-- Source execution permits only the displayed parallel frames. Native
lambda and object-quotation congruence are not evaluation contexts here. -/
inductive ParallelStep {n : Nat} : NativeTerm n → NativeTerm n → Prop where
  | root {first second} : Root first second → ParallelStep first second
  | left {first second} (other : NativeTerm n) : ParallelStep first second →
      ParallelStep (parallel first other) (parallel second other)
  | right {first second} (other : NativeTerm n) : ParallelStep first second →
      ParallelStep (parallel other first) (parallel other second)

inductive StepCode (n : Nat) where
  | root (code : RootCode n)
  | left (other : NativeTerm n) (code : StepCode n)
  | right (other : NativeTerm n) (code : StepCode n)

def decodeStep {n : Nat} : StepCode n → NativeTerm n × NativeTerm n
  | .root (.communication channel payload body) =>
      (parallel (output channel payload) (input channel body), inst0 (quote payload) body)
  | .root (.reflection payload) => (drop (quote payload), payload)
  | .left other code =>
      let endpoints := decodeStep code
      (parallel endpoints.1 other, parallel endpoints.2 other)
  | .right other code =>
      let endpoints := decodeStep code
      (parallel other endpoints.1, parallel other endpoints.2)

theorem decodeStep_sound {n : Nat} (code : StepCode n) :
    ParallelStep (decodeStep code).1 (decodeStep code).2 := by
  induction code with
  | root code => cases code with
    | communication channel payload body => exact .root (.communication channel payload body)
    | reflection payload => exact .root (.reflection payload)
  | left other code ih => exact .left other ih
  | right other code ih => exact .right other ih

theorem decodeStep_complete {n : Nat} {first second : NativeTerm n}
    (step : ParallelStep first second) : ∃ code, decodeStep code = (first, second) := by
  induction step with
  | root step => cases step with
    | communication channel payload body => exact ⟨.root (.communication channel payload body), rfl⟩
    | reflection _ => exact ⟨.root (.reflection _), rfl⟩
  | left other step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.left other code, by simp only [decodeStep, decoded]⟩
  | right other step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.right other code, by simp only [decodeStep, decoded]⟩

def checkStep {n : Nat} (code : StepCode n) (first second : NativeTerm n) : Bool :=
  decide (decodeStep code = (first, second))

theorem checkStep_sound {n : Nat} (code : StepCode n) (first second : NativeTerm n)
    (accepted : checkStep code first second = true) : ParallelStep first second := by
  have same := of_decide_eq_true accepted
  have step := decodeStep_sound code
  simpa only [same] using step

theorem checkStep_complete {n : Nat} (first second : NativeTerm n) :
    ParallelStep first second ↔ ∃ code, checkStep code first second = true := by
  constructor
  · intro step
    obtain ⟨code, decoded⟩ := decodeStep_complete step
    exact ⟨code, by simp only [checkStep, decoded, decide_true]⟩
  · rintro ⟨code, accepted⟩
    exact checkStep_sound code first second accepted

def permittedHead {n : Nat} : NativeTerm n → Bool
  | .app (.app (.const name) _) _ => name == parallelName
  | .app (.const name) _ => name == dropName
  | _ => false

theorem parallelStep_permitted_head {n : Nat} {first second : NativeTerm n}
    (step : ParallelStep first second) : permittedHead first = true := by
  induction step with
  | root step => cases step <;> simp [permittedHead, parallel, drop]
  | left => simp [permittedHead, parallel]
  | right => simp [permittedHead, parallel]

/-- A redex inside quotation is not an authorized evaluation position. -/
theorem quoted_redex_cannot_step {n : Nat} (first second : NativeTerm n) :
    ¬ ParallelStep (quote first) second := by
  intro step
  have head := parallelStep_permitted_head step
  simp [permittedHead, quote, quoteName, dropName] at head

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoScopedInstanceReadout

private theorem encode_receive_environment
    {context : Mettapedia.OSLF.Binding.Ctx sig}
    (name : Mettapedia.OSLF.Binding.Term sig context Srt.nm) :
    BindingSignatureEmbedding.encodeSub (Head := Tower.Head) names (receiveRaw name) =
      subst0 (BindingSignatureEmbedding.encode names name) := by
  funext index
  refine Fin.cases ?_ (fun previous => ?_) index
  · rfl
  · let position := Mettapedia.OSLF.Binding.varOfIdx (S := sig) context previous
    have law := BindingSignatureEmbedding.encodeSub_variable (Head := Tower.Head) names
      (receiveRaw name) (Mettapedia.OSLF.Binding.Var.succ position)
    simpa only [position, Mettapedia.OSLF.Binding.varIdx,
      Mettapedia.OSLF.Binding.varIdx_varOfIdx, receiveRaw,
      BindingSignatureEmbedding.encode, subst0, Fin.cases_succ] using law

theorem encode_receive {context : Mettapedia.OSLF.Binding.Ctx sig}
    (name : Mettapedia.OSLF.Binding.Term sig context Srt.nm)
    (body : Mettapedia.OSLF.Binding.Term sig (Srt.nm :: context) Srt.pr) :
    inst0 (BindingSignatureEmbedding.encode names name)
      (BindingSignatureEmbedding.encode names body) =
      BindingSignatureEmbedding.encode (Head := Tower.Head) names
        (Mettapedia.OSLF.Binding.bind (receiveRaw name) body) := by
  rw [inst0, ← encode_receive_environment]
  exact BindingSignatureEmbedding.encode_substitution names (receiveRaw name) body

/-- Every original scoped communication instance executes through the native
rule, including its actual open continuation and quotation/substitution. -/
theorem communication_preserved {context : Mettapedia.OSLF.Binding.Ctx sig}
    (root : Communication context) :
    Root (BindingSignatureEmbedding.encode names root.source)
      (BindingSignatureEmbedding.encode names root.target) := by
  change Root
    (BindingSignatureEmbedding.encode (sort := Srt.pr) names (root.source : Mettapedia.OSLF.Binding.Term sig context Srt.pr))
    (BindingSignatureEmbedding.encode (sort := Srt.pr) names (root.target : Mettapedia.OSLF.Binding.Term sig context Srt.pr))
  rw [root.source_readout, root.target_readout]
  rw [← encode_receive]
  exact Root.communication (BindingSignatureEmbedding.encode names root.channel)
    (BindingSignatureEmbedding.encode names root.payload)
    (BindingSignatureEmbedding.encode names root.continuation)

theorem reflection_preserved {context : Mettapedia.OSLF.Binding.Ctx sig}
    (root : Reflection context) :
    Root (BindingSignatureEmbedding.encode names root.source)
      (BindingSignatureEmbedding.encode names root.target) := by
  rw [root.source_readout, root.target_readout]
  exact Root.reflection (BindingSignatureEmbedding.encode names root.payload)

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation DeclarationProfile
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoScopedInstanceReadout
open Mettapedia.OSLF.Binding.RhoQuotationClassFibres
open Mettapedia.OSLF.Binding.RhoScopedParallelPathReadout

/-- An actual target root on an encoded source is an original source root;
its target remains in the same sorted image. -/
theorem root_reflects {context : Mettapedia.OSLF.Binding.Ctx sig}
    (source : Mettapedia.OSLF.Binding.Term sig context Srt.pr)
    {first second : NativeTerm context.length} (root : Root first second)
    (same : Inversion.E source = first) :
    ∃ target : Mettapedia.OSLF.Binding.Term sig context Srt.pr,
      second = Inversion.E target ∧ SourceStep source target := by
  cases root with
  | communication channel payload body =>
      obtain ⟨left, right, rfl, leftRead, rightRead⟩ :=
        Inversion.parallel_shape (output channel payload) (input channel body) source same
      obtain ⟨sourceChannel, sourcePayload, rfl, channelRead, payloadRead⟩ :=
        Inversion.output_shape channel payload left leftRead
      obtain ⟨inputChannel, sourceBody, rfl, inputChannelRead, bodyRead⟩ :=
        Inversion.input_shape channel body right rightRead
      have sameChannel : sourceChannel = inputChannel :=
        DeclarationProfile.declared_encode_injective (channelRead.trans inputChannelRead.symm)
      subst inputChannel
      refine ⟨Mettapedia.OSLF.Binding.bind (receiveRaw (quoteRaw sourcePayload)) sourceBody, ?_,
        communication_source_step sourceChannel sourcePayload sourceBody⟩
      rw [← payloadRead, ← bodyRead]
      exact encode_receive (quoteRaw sourcePayload) sourceBody
  | reflection _ =>
      obtain ⟨sourceName, rfl, nameRead⟩ := Inversion.drop_shape (quote second) source same
      obtain ⟨sourcePayload, rfl, payloadRead⟩ := Inversion.quote_shape second sourceName nameRead
      exact ⟨sourcePayload, payloadRead.symm, reflection_source_step sourcePayload⟩


/-- Native parallel execution from a sorted source cannot escape its image
and reflects an actual original source event, at every ambient scope. -/
theorem parallel_reflects {context : Mettapedia.OSLF.Binding.Ctx sig}
    (source : Mettapedia.OSLF.Binding.Term sig context Srt.pr)
    {first second : NativeTerm context.length} (step : ParallelStep first second)
    (same : Inversion.E source = first) :
    ∃ target : Mettapedia.OSLF.Binding.Term sig context Srt.pr,
      second = Inversion.E target ∧ SourceStep source target := by
  induction step generalizing source with
  | root step => exact root_reflects source step same
  | @left first second other step ih =>
      obtain ⟨sourceFirst, sourceOther, rfl, firstRead, otherRead⟩ :=
        Inversion.parallel_shape first other source same
      obtain ⟨target, targetRead, sourceStep⟩ := ih sourceFirst firstRead
      refine ⟨.op .par (.cons target (.cons sourceOther .nil)), ?_, source_parallel_left sourceStep sourceOther⟩
      rw [targetRead, ← otherRead]
      rfl
  | @right first second other step ih =>
      obtain ⟨sourceOther, sourceFirst, rfl, otherRead, firstRead⟩ :=
        Inversion.parallel_shape other first source same
      obtain ⟨target, targetRead, sourceStep⟩ := ih sourceFirst firstRead
      refine ⟨.op .par (.cons sourceOther (.cons target .nil)), ?_, source_parallel_right sourceStep sourceOther⟩
      rw [targetRead, ← otherRead]
      rfl

theorem parallel_reflects_on_image {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Mettapedia.OSLF.Binding.Term sig context Srt.pr)
    (step : ParallelStep (Inversion.E first) (Inversion.E second)) :
    SourceStep first second := by
  obtain ⟨target, same, original⟩ := parallel_reflects first step rfl
  have equal : second = target := DeclarationProfile.declared_encode_injective same
  exact equal.symm ▸ original


theorem scoped_roots_preserved {context : Mettapedia.OSLF.Binding.Ctx sig}
    (root : Mettapedia.OSLF.Binding.RhoScopedParallelEvents.Root
      Mettapedia.OSLF.Binding.RhoScopedParallelEvents.sourceRules
      Mettapedia.OSLF.Binding.RhoScopedParallelEvents.withReflection context) :
    Root (Inversion.E root.2.source) (Inversion.E root.2.target) := by
  rcases root with ⟨⟨index, admitted⟩, firing⟩
  cases index with
  | communication => exact communication_preserved firing
  | reflection => exact reflection_preserved firing

/-- The original quotient event relation is exactly native directed
parallel execution surrounded by the original authored source equations.
The equations are not inferred from ambient native conversion. -/
theorem source_step_iff_native_modulo {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Mettapedia.OSLF.Binding.Term sig context Srt.pr) :
    SourceStep first second ↔
      ∃ before after : Mettapedia.OSLF.Binding.Term sig context Srt.pr,
        Mettapedia.OSLF.Binding.EqClosure rhoSourceE first before ∧
        ParallelStep (Inversion.E before) (Inversion.E after) ∧
        Mettapedia.OSLF.Binding.EqClosure rhoSourceE after second := by
  constructor
  · intro step
    obtain ⟨root, surrounding, sourceRead, targetRead⟩ :=
      (Mettapedia.OSLF.Binding.RhoScopedParallelEvents.step_iff_root_surrounding _ _).mp step
    induction surrounding using Quotient.inductionOn with
    | _ remainder =>
        refine ⟨.op .par (.cons root.2.source (.cons remainder .nil)),
          .op .par (.cons root.2.target (.cons remainder .nil)),
          Quotient.exact sourceRead, ?_, Quotient.exact targetRead.symm⟩
        exact .left (Inversion.E remainder) (.root (scoped_roots_preserved root))
  · rintro ⟨before, after, beforeEq, executing, afterEq⟩
    have step := parallel_reflects_on_image before after executing
    have sourceRead : Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project first =
        Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project before := Quotient.sound beforeEq
    have targetRead : Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project after =
        Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project second := Quotient.sound afterEq
    unfold SourceStep at step ⊢
    rw [sourceRead, ← targetRead]
    exact step

/-- Finite equation and directed-step evidence suffices for every original
scoped source event, and accepted evidence reflects it. -/
theorem source_step_iff_native_evidence {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Mettapedia.OSLF.Binding.Term sig context Srt.pr) :
    SourceStep first second ↔
      ∃ before after : Mettapedia.OSLF.Binding.Term sig context Srt.pr,
        ∃ prior : EquationEvidence context Srt.pr,
        ∃ operation : StepCode context.length,
        ∃ later : EquationEvidence context Srt.pr,
          checkNativeEquation prior (Inversion.E first) (Inversion.E before) = true ∧
          checkStep operation (Inversion.E before) (Inversion.E after) = true ∧
          checkNativeEquation later (Inversion.E after) (Inversion.E second) = true := by
  rw [source_step_iff_native_modulo]
  simp_rw [source_equation_iff_native_evidence,
    checkStep_complete]
  constructor
  · rintro ⟨before, after, ⟨prior, priorChecked⟩, ⟨operation, operationChecked⟩,
      ⟨later, laterChecked⟩⟩
    exact ⟨before, after, prior, operation, later, priorChecked, operationChecked, laterChecked⟩
  · rintro ⟨before, after, prior, operation, later, priorChecked, operationChecked, laterChecked⟩
    exact ⟨before, after, ⟨prior, priorChecked⟩, ⟨operation, operationChecked⟩, ⟨later, laterChecked⟩⟩


/-- The exact source evaluation-context policy is stable under renaming. -/
theorem parallel_rename {n m : Nat} (action : Presentation.Ren n m)
    {first second : NativeTerm n} (step : ParallelStep first second) :
    ParallelStep (Presentation.rename action first) (Presentation.rename action second) := by
  induction step with
  | root step => exact .root (directedComputation.rename action step)
  | left other step ih => exact .left (Presentation.rename action other) ih
  | right other step ih => exact .right (Presentation.rename action other) ih

theorem parallel_substitution {n m : Nat} (action : Presentation.Sub Tower.Head n m)
    {first second : NativeTerm n} (step : ParallelStep first second) :
    ParallelStep (Presentation.subst action first) (Presentation.subst action second) := by
  induction step with
  | root step => exact .root (directedComputation.substitute action step)
  | left other step ih => exact .left (Presentation.subst action other) ih
  | right other step ih => exact .right (Presentation.subst action other) ih

/-- Source-image execution produces an actually formed judgment in the
same native source-sort type, not merely an untyped decoded term. -/
theorem parallel_preserves_source_judgment
    {context : Mettapedia.OSLF.Binding.Ctx sig}
    (source : Mettapedia.OSLF.Binding.Term sig context Srt.pr)
    {target : NativeTerm context.length} (step : ParallelStep (Inversion.E source) target) :
    FormationSensitive.Judgment DeclarationProfile.rules
      (BindingSignatureEmbedding.context names context) target
      (BindingSignatureEmbedding.sortType names Srt.pr) := by
  obtain ⟨sourceTarget, same, _⟩ := parallel_reflects source step rfl
  rw [same]
  exact source_judgment sourceTarget

theorem input_body_cannot_step {n : Nat} (channel : NativeTerm n)
    (body : NativeTerm (n+1)) (target : NativeTerm n) :
    ¬ ParallelStep (input channel body) target := by
  intro step
  have head := parallelStep_permitted_head step
  simp [permittedHead, input, inputName, parallelName] at head

theorem output_payload_cannot_step {n : Nat} (channel payload target : NativeTerm n) :
    ¬ ParallelStep (output channel payload) target := by
  intro step
  have head := parallelStep_permitted_head step
  simp [permittedHead, output, outputName, parallelName] at head
end Operations


/-! ## The independently declared scoped structural observer -/

namespace Conversion
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation DeclarationProfile
open Mettapedia.OSLF.Binding.RhoSchema
open Operations (NativeTerm parallel output input quote drop)

/-- The declared structural observer uses rho sorts and constructor
contexts on actual native terms. It contains neither beta nor COMM. -/
inductive Structural : (context : Mettapedia.OSLF.Binding.Ctx sig) → Srt →
    NativeTerm context.length → NativeTerm context.length → Prop where
  | refl {context sort} (term : NativeTerm context.length) : Structural context sort term term
  | symm {context sort} {first second : NativeTerm context.length} :
      Structural context sort first second → Structural context sort second first
  | trans {context sort} {first middle last : NativeTerm context.length} :
      Structural context sort first middle → Structural context sort middle last →
        Structural context sort first last
  | parallelComm {context} (first second : NativeTerm context.length) :
      Structural context .pr (parallel first second) (parallel second first)
  | parallelAssoc {context} (first second third : NativeTerm context.length) :
      Structural context .pr (parallel (parallel first second) third)
        (parallel first (parallel second third))
  | parallelUnit {context} (term : NativeTerm context.length) :
      Structural context .pr (parallel term (.const zeroName)) term
  | nameEta {context} (term : NativeTerm context.length) :
      Structural context .nm (quote (drop term)) term
  | parallelCong {context} {first first' second second' : NativeTerm context.length} :
      Structural context .pr first first' → Structural context .pr second second' →
        Structural context .pr (parallel first second) (parallel first' second')
  | outputCong {context} {name name' payload payload' : NativeTerm context.length} :
      Structural context .nm name name' → Structural context .pr payload payload' →
        Structural context .pr (output name payload) (output name' payload')
  | inputCong {context} {name name' : NativeTerm context.length}
      {body body' : NativeTerm (context.length+1)} :
      Structural context .nm name name' → Structural (.nm :: context) .pr body body' →
        Structural context .pr (input name body) (input name' body')
  | quoteCong {context} {first second : NativeTerm context.length} :
      Structural context .pr first second → Structural context .nm (quote first) (quote second)
  | dropCong {context} {first second : NativeTerm context.length} :
      Structural context .nm first second → Structural context .pr (drop first) (drop second)

open Mettapedia.OSLF.Binding

private theorem axiom_preserved :
    (index : Fin rhoSourceE.length) → {ambient context : Ctx sig} →
    (bodies : ContextualAssignment sig metas ambient) →
    (environment : Sub sig ambient context) →
    (ordinary : Sub sig (rhoSourceE.get index).ctx context) →
      Structural context (rhoSourceE.get index).sort
        (Inversion.E (ContextualAssignment.instantiate bodies environment ordinary (rhoSourceE.get index).lhs))
        (Inversion.E (ContextualAssignment.instantiate bodies environment ordinary (rhoSourceE.get index).rhs))
  | ⟨0, _⟩, _, _, _, _, ordinary => by
      change Structural _ .pr
        (parallel (Inversion.E (ordinary _ .zero)) (Inversion.E (ordinary _ (.succ .zero))))
        (parallel (Inversion.E (ordinary _ (.succ .zero))) (Inversion.E (ordinary _ .zero)))
      exact .parallelComm _ _
  | ⟨1, _⟩, _, _, _, _, ordinary => by
      change Structural _ .pr
        (parallel (parallel (Inversion.E (ordinary _ .zero)) (Inversion.E (ordinary _ (.succ .zero))))
          (Inversion.E (ordinary _ (.succ (.succ .zero)))))
        (parallel (Inversion.E (ordinary _ .zero))
          (parallel (Inversion.E (ordinary _ (.succ .zero))) (Inversion.E (ordinary _ (.succ (.succ .zero))))))
      exact .parallelAssoc _ _ _
  | ⟨2, _⟩, _, _, _, _, ordinary => by
      change Structural _ .pr (parallel (Inversion.E (ordinary _ .zero)) (.const zeroName))
        (Inversion.E (ordinary _ .zero))
      exact .parallelUnit _
  | ⟨3, _⟩, _, _, _, _, ordinary => by
      change Structural _ .nm (quote (drop (Inversion.E (ordinary _ .zero))))
        (Inversion.E (ordinary _ .zero))
      exact .nameEta _
  | ⟨_ + 4, impossible⟩, _, _, _, _, _ => by simp [rhoSourceE] at impossible

theorem source_equation_preserved :
    {context : Ctx sig} → {sort : Srt} → {first second : Term sig context sort} →
      EqClosure rhoSourceE first second → Structural context sort (Inversion.E first) (Inversion.E second)
  | _, _, _, _, .ax index bodies environment ordinary => axiom_preserved index bodies environment ordinary
  | _, _, _, _, .refl term => .refl (Inversion.E term)
  | _, _, _, _, .symm proof => .symm (source_equation_preserved proof)
  | _, _, _, _, .trans first second =>
      .trans (source_equation_preserved first) (source_equation_preserved second)
  | _, _, _, _, .cong Op.nil .nil => .refl _
  | _, _, _, _, .cong Op.par (.cons first (.cons second .nil)) =>
      .parallelCong (source_equation_preserved first) (source_equation_preserved second)
  | _, _, _, _, .cong Op.out (.cons name (.cons payload .nil)) =>
      .outputCong (source_equation_preserved name) (source_equation_preserved payload)
  | _, _, _, _, .cong Op.inp (.cons name (.cons body .nil)) =>
      .inputCong (source_equation_preserved name) (source_equation_preserved body)
  | _, _, _, _, .cong Op.quo (.cons proof .nil) => .quoteCong (source_equation_preserved proof)
  | _, _, _, _, .cong Op.drp (.cons proof .nil) => .dropCong (source_equation_preserved proof)

private def Reads (context : Ctx sig) (sort : Srt)
    (first second : NativeTerm context.length) : Prop :=
  ∀ source : Term sig context sort, Inversion.E source = first →
    ∃ target : Term sig context sort, Inversion.E target = second ∧
      EqClosure rhoSourceE source target

private theorem reads_trans {context : Ctx sig} {sort : Srt}
    {first middle last : NativeTerm context.length}
    (before : Reads context sort first middle) (after : Reads context sort middle last) :
    Reads context sort first last := by
  intro source same
  obtain ⟨intermediate, intermediateRead, priorEq⟩ := before source same
  obtain ⟨target, targetRead, laterEq⟩ := after intermediate intermediateRead
  exact ⟨target, targetRead, priorEq.trans laterEq⟩

open Mettapedia.OSLF.Binding.RhoQuotationClassFibres
open Mettapedia.OSLF.Binding.RhoEquationConstructorControls (parallel_null_equation)

private theorem reads_comm {context : Ctx sig} (first second : NativeTerm context.length) :
    Reads context .pr (parallel first second) (parallel second first) := by
  intro source same
  obtain ⟨p, q, rfl, firstRead, secondRead⟩ := Inversion.parallel_shape first second source same
  refine ⟨.op Op.par (.cons q (.cons p .nil)), ?_, parallel_commutes p q⟩
  change parallel (Inversion.E q) (Inversion.E p) = parallel second first
  rw [firstRead, secondRead]

private theorem reads_assoc_forward {context : Ctx sig} (first second third : NativeTerm context.length) :
    Reads context .pr (parallel (parallel first second) third) (parallel first (parallel second third)) := by
  intro source same
  obtain ⟨pq, r, rfl, pairRead, thirdRead⟩ := Inversion.parallel_shape (parallel first second) third source same
  obtain ⟨p, q, rfl, firstRead, secondRead⟩ := Inversion.parallel_shape first second pq pairRead
  refine ⟨.op Op.par (.cons p (.cons (.op Op.par (.cons q (.cons r .nil))) .nil)), ?_,
    Mettapedia.OSLF.Binding.RhoIntrinsicReadback.parallel_associates_raw p q r⟩
  change parallel (Inversion.E p) (parallel (Inversion.E q) (Inversion.E r)) = _
  rw [firstRead, secondRead, thirdRead]

private theorem reads_assoc_backward {context : Ctx sig} (first second third : NativeTerm context.length) :
    Reads context .pr (parallel first (parallel second third)) (parallel (parallel first second) third) := by
  intro source same
  obtain ⟨p, qr, rfl, firstRead, pairRead⟩ := Inversion.parallel_shape first (parallel second third) source same
  obtain ⟨q, r, rfl, secondRead, thirdRead⟩ := Inversion.parallel_shape second third qr pairRead
  refine ⟨.op Op.par (.cons (.op Op.par (.cons p (.cons q .nil))) (.cons r .nil)), ?_,
    (Mettapedia.OSLF.Binding.RhoIntrinsicReadback.parallel_associates_raw p q r).symm⟩
  change parallel (parallel (Inversion.E p) (Inversion.E q)) (Inversion.E r) = _
  rw [firstRead, secondRead, thirdRead]

private theorem reads_unit_forward {context : Ctx sig} (term : NativeTerm context.length) :
    Reads context .pr (parallel term (.const zeroName)) term := by
  intro source same
  obtain ⟨p, q, rfl, processRead, zeroRead⟩ := Inversion.parallel_shape term (.const zeroName) source same
  have sourceZero : q = (.op Op.nil .nil : Term sig context Srt.pr) := by
    apply declared_encode_injective
    exact zeroRead
  subst q
  exact ⟨p, processRead, parallel_null_equation p⟩

private theorem reads_unit_backward {context : Ctx sig} (term : NativeTerm context.length) :
    Reads context .pr term (parallel term (.const zeroName)) := by
  intro source same
  refine ⟨.op Op.par (.cons source (.cons (.op Op.nil .nil) .nil)), ?_,
    (parallel_null_equation source).symm⟩
  change parallel (Inversion.E source) (.const zeroName) = _
  rw [same]

private theorem reads_eta_forward {context : Ctx sig} (term : NativeTerm context.length) :
    Reads context .nm (quote (drop term)) term := by
  intro source same
  obtain ⟨p, rfl, dropRead⟩ := Inversion.quote_shape (drop term) source same
  obtain ⟨name, rfl, nameRead⟩ := Inversion.drop_shape term p dropRead
  exact ⟨name, nameRead, quote_drop_raw name⟩

private theorem reads_eta_backward {context : Ctx sig} (term : NativeTerm context.length) :
    Reads context .nm term (quote (drop term)) := by
  intro source same
  refine ⟨.op Op.quo (.cons (.op Op.drp (.cons source .nil)) .nil), ?_, (quote_drop_raw source).symm⟩
  change quote (drop (Inversion.E source)) = _
  rw [same]

private theorem reads_parallel_cong {context : Ctx sig}
    {first first' second second' : NativeTerm context.length}
    (firstReads : Reads context .pr first first') (secondReads : Reads context .pr second second') :
    Reads context .pr (parallel first second) (parallel first' second') := by
  intro source same
  obtain ⟨p, q, rfl, firstRead, secondRead⟩ := Inversion.parallel_shape first second source same
  obtain ⟨p', pRead, pEq⟩ := firstReads p firstRead
  obtain ⟨q', qRead, qEq⟩ := secondReads q secondRead
  refine ⟨.op Op.par (.cons p' (.cons q' .nil)), ?_, EqClosure.cong (S := sig) (E := rhoSourceE) Op.par (.cons pEq (.cons qEq .nil))⟩
  change parallel (Inversion.E p') (Inversion.E q') = _
  rw [pRead, qRead]

private theorem reads_output_cong {context : Ctx sig}
    {name name' payload payload' : NativeTerm context.length}
    (nameReads : Reads context .nm name name') (payloadReads : Reads context .pr payload payload') :
    Reads context .pr (output name payload) (output name' payload') := by
  intro source same
  obtain ⟨n, p, rfl, nameRead, payloadRead⟩ := Inversion.output_shape name payload source same
  obtain ⟨n', nRead, nEq⟩ := nameReads n nameRead
  obtain ⟨p', pRead, pEq⟩ := payloadReads p payloadRead
  refine ⟨.op Op.out (.cons n' (.cons p' .nil)), ?_, EqClosure.cong (S := sig) (E := rhoSourceE) Op.out (.cons nEq (.cons pEq .nil))⟩
  change output (Inversion.E n') (Inversion.E p') = _
  rw [nRead, pRead]

private theorem reads_input_cong {context : Ctx sig}
    {name name' : NativeTerm context.length} {body body' : NativeTerm (context.length+1)}
    (nameReads : Reads context .nm name name') (bodyReads : Reads (.nm :: context) .pr body body') :
    Reads context .pr (input name body) (input name' body') := by
  intro source same
  obtain ⟨n, p, rfl, nameRead, bodyRead⟩ := Inversion.input_shape name body source same
  obtain ⟨n', nRead, nEq⟩ := nameReads n nameRead
  obtain ⟨p', pRead, pEq⟩ := bodyReads p bodyRead
  refine ⟨.op Op.inp (.cons n' (.cons p' .nil)), ?_,
    EqClosure.cong (S := sig) (E := rhoSourceE) Op.inp (.cons (bs := []) nEq
      (EqArgs.cons (S := sig) (E := rhoSourceE) (bs := [Srt.nm]) pEq .nil))⟩
  change input (Inversion.E n') (Inversion.E p') = _
  rw [nRead, pRead]

private theorem reads_quote_cong {context : Ctx sig} {first second : NativeTerm context.length}
    (reads : Reads context .pr first second) : Reads context .nm (quote first) (quote second) := by
  intro source same
  obtain ⟨p, rfl, processRead⟩ := Inversion.quote_shape first source same
  obtain ⟨p', pRead, pEq⟩ := reads p processRead
  refine ⟨.op Op.quo (.cons p' .nil), ?_, EqClosure.cong (S := sig) (E := rhoSourceE) Op.quo (.cons pEq .nil)⟩
  change quote (Inversion.E p') = _
  rw [pRead]

private theorem reads_drop_cong {context : Ctx sig} {first second : NativeTerm context.length}
    (reads : Reads context .nm first second) : Reads context .pr (drop first) (drop second) := by
  intro source same
  obtain ⟨name, rfl, nameRead⟩ := Inversion.drop_shape first source same
  obtain ⟨name', targetRead, nameEq⟩ := reads name nameRead
  refine ⟨.op Op.drp (.cons name' .nil), ?_, EqClosure.cong (S := sig) (E := rhoSourceE) Op.drp (.cons nameEq .nil)⟩
  change drop (Inversion.E name') = _
  rw [targetRead]

/-- Both endpoints of an equation remain in the source image whenever the
other endpoint is in it; every equation reconstructs source evidence. -/
private theorem structural_reads {context : Ctx sig} {sort : Srt}
    {first second : NativeTerm context.length} (equation : Structural context sort first second) :
    Reads context sort first second ∧ Reads context sort second first := by
  induction equation with
  | refl term => exact ⟨fun source same => ⟨source, same, .refl _⟩,
      fun source same => ⟨source, same, .refl _⟩⟩
  | symm proof ih => exact ⟨ih.2, ih.1⟩
  | trans before after ihBefore ihAfter =>
      exact ⟨reads_trans ihBefore.1 ihAfter.1, reads_trans ihAfter.2 ihBefore.2⟩
  | parallelComm first second => exact ⟨reads_comm first second, reads_comm second first⟩
  | parallelAssoc first second third =>
      exact ⟨reads_assoc_forward first second third, reads_assoc_backward first second third⟩
  | parallelUnit term => exact ⟨reads_unit_forward term, reads_unit_backward term⟩
  | nameEta term => exact ⟨reads_eta_forward term, reads_eta_backward term⟩
  | parallelCong first second ihFirst ihSecond =>
      exact ⟨reads_parallel_cong ihFirst.1 ihSecond.1, reads_parallel_cong ihFirst.2 ihSecond.2⟩
  | outputCong name payload ihName ihPayload =>
      exact ⟨reads_output_cong ihName.1 ihPayload.1, reads_output_cong ihName.2 ihPayload.2⟩
  | inputCong name body ihName ihBody =>
      exact ⟨reads_input_cong ihName.1 ihBody.1, reads_input_cong ihName.2 ihBody.2⟩
  | quoteCong proof ih => exact ⟨reads_quote_cong ih.1, reads_quote_cong ih.2⟩
  | dropCong proof ih => exact ⟨reads_drop_cong ih.1, reads_drop_cong ih.2⟩

/-- Actual target structural conversion, not a source-decoder definition,
preserves and reflects the entire authored equation theory on the full image. -/
theorem source_equation_iff_structural {context : Ctx sig} {sort : Srt}
    (first second : Term sig context sort) :
    EqClosure rhoSourceE first second ↔ Structural context sort (Inversion.E first) (Inversion.E second) := by
  constructor
  · exact source_equation_preserved
  · intro equation
    obtain ⟨target, same, original⟩ := (structural_reads equation).1 first rfl
    have identical : target = second := declared_encode_injective same
    exact identical ▸ original


/-- Accepted source-equation certificates now earn independently stated
native structural authority on the complete sorted source image. -/
theorem structural_iff_native_evidence {context : Ctx sig} {sort : Srt}
    (first second : Term sig context sort) :
    Structural context sort (Inversion.E first) (Inversion.E second) ↔
      ∃ proof : EquationEvidence context sort,
        checkNativeEquation proof (Inversion.E first) (Inversion.E second) = true :=
  (source_equation_iff_structural first second).symm.trans
    (source_equation_iff_native_evidence first second)

theorem structural_preserves_source_judgment {context : Ctx sig} {sort : Srt}
    (source : Term sig context sort) {target : NativeTerm context.length}
    (equation : Structural context sort (Inversion.E source) target) :
    FormationSensitive.Judgment DeclarationProfile.rules
      (BindingSignatureEmbedding.context names context) target
      (BindingSignatureEmbedding.sortType names sort) := by
  obtain ⟨sourceTarget, same, _⟩ := (structural_reads equation).1 source rfl
  rw [← same]
  exact source_judgment sourceTarget

/-- Both target components are independently stated: sorted structural
conversion and directed parallel evaluation. Their combination reflects
exactly the original equation-quotient source events. -/
theorem source_step_iff_native_structural_execution {context : Ctx sig}
    (first second : Term sig context Srt.pr) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.SourceStep first second ↔
      ∃ before after : Term sig context Srt.pr,
        Structural context .pr (Inversion.E first) (Inversion.E before) ∧
        Operations.ParallelStep (Inversion.E before) (Inversion.E after) ∧
        Structural context .pr (Inversion.E after) (Inversion.E second) := by
  rw [Operations.source_step_iff_native_modulo]
  simp_rw [← source_equation_iff_structural]

theorem process_drop_is_directed :
    Operations.ParallelStep
      (drop (quote (.const zeroName : NativeTerm 0))) (.const zeroName) :=
  .root (.reflection _)

/-- Name eta does not identify a process with its quote-then-drop wrapper.
The same wrapper does execute by the separately declared Drop rule. -/
theorem process_drop_not_structural :
    ¬ Structural [] .pr (drop (quote (.const zeroName))) (.const zeroName) := by
  intro equation
  have original := (source_equation_iff_structural
    (.op Op.drp (.cons (.op Op.quo (.cons (.op Op.nil .nil) .nil)) .nil) : Term sig [] Srt.pr)
    (.op Op.nil .nil)).mpr equation
  have equalClasses :
      Mettapedia.OSLF.Binding.RhoQuotationClassFibres.drop
        (Mettapedia.OSLF.Binding.RhoQuotationClassFibres.quote
          (Mettapedia.OSLF.Binding.RhoQuotationClassFibres.zero [])) =
        Mettapedia.OSLF.Binding.RhoQuotationClassFibres.zero [] := Quotient.sound original
  exact Mettapedia.OSLF.Binding.RhoIntrinsicCanonicalBag.drop_not_zero _ equalClasses


/-- The actual native substitution action preserves the declared structural
observer, including lifting under the input continuation's native binder. -/
theorem structural_substitution {context destination : Ctx sig} {sort : Srt}
    (action : Presentation.Sub Tower.Head context.length destination.length)
    {first second : NativeTerm context.length} (equation : Structural context sort first second) :
    Structural destination sort (Presentation.subst action first) (Presentation.subst action second) := by
  induction equation generalizing destination with
  | refl term => exact .refl _
  | symm proof ih => exact .symm (ih action)
  | trans before after ihBefore ihAfter => exact .trans (ihBefore action) (ihAfter action)
  | parallelComm first second => exact .parallelComm _ _
  | parallelAssoc first second third => exact .parallelAssoc _ _ _
  | parallelUnit term => exact .parallelUnit _
  | nameEta term => exact .nameEta _
  | parallelCong first second ihFirst ihSecond => exact .parallelCong (ihFirst action) (ihSecond action)
  | outputCong name payload ihName ihPayload => exact .outputCong (ihName action) (ihPayload action)
  | inputCong name body ihName ihBody =>
      exact .inputCong (ihName action) (ihBody (destination := Srt.nm :: destination) (liftSub action))
  | quoteCong proof ih => exact .quoteCong (ih action)
  | dropCong proof ih => exact .dropCong (ih action)

def nativeSetoid (context : Ctx sig) (sort : Srt) : Setoid (NativeTerm context.length) where
  r := Structural context sort
  iseqv := ⟨Structural.refl, Structural.symm, Structural.trans⟩

/-- Authored source equation classes embed in the native structural quotient.
The target may contain other native terms; no global surjectivity is asserted. -/
def quotientMap {context : Ctx sig} {sort : Srt} :
    TermQ rhoSourceE context sort → Quotient (nativeSetoid context sort) :=
  Quotient.map Inversion.E (fun _ _ equation => source_equation_preserved equation)

theorem quotientMap_injective {context : Ctx sig} {sort : Srt} :
    Function.Injective (quotientMap (context := context) (sort := sort)) := by
  intro first second same
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
          have equation : Structural context sort (Inversion.E first) (Inversion.E second) :=
            Quotient.exact same
          exact Quotient.sound ((source_equation_iff_structural first second).mpr equation)

def nativeBindQ {context destination : Ctx sig} {sort : Srt}
    (action : Mettapedia.OSLF.Binding.Sub sig context destination) :
    Quotient (nativeSetoid context sort) → Quotient (nativeSetoid destination sort) :=
  Quotient.map (Presentation.subst (BindingSignatureEmbedding.encodeSub names action))
    (fun _ _ equation => structural_substitution _ equation)

/-- The quotient embedding retains the full simultaneous substitution law,
so native equation classes do not erase the source binding algebra. -/
theorem quotientMap_bindQ {context destination : Ctx sig} {sort : Srt}
    (action : Mettapedia.OSLF.Binding.Sub sig context destination)
    (value : TermQ rhoSourceE context sort) :
    quotientMap (Mettapedia.OSLF.Binding.bindQ action value) =
      nativeBindQ action (quotientMap value) := by
  induction value using Quotient.inductionOn with
  | _ term =>
      apply Quotient.sound
      have same := BindingSignatureEmbedding.encode_substitution (Head := Tower.Head) names action term
      exact same.symm ▸ Structural.refl (Inversion.E (bind action term))

/-! ## Explicit finite evidence for the native structural observer -/

namespace Explicit
open Mettapedia.TypeTheory

/-- The request fixes its scope, source sort and both literal native endpoints. -/
structure Claim where
  context : Ctx sig
  sort : Srt
  first : NativeTerm context.length
  second : NativeTerm context.length
  deriving DecidableEq

def Meaning (claim : Claim) : Prop :=
  Structural claim.context claim.sort claim.first claim.second

/-- Each rule stores every endpoint needed to check its premise judgments.
No substitution or evaluation is hidden inside a rule payload. -/
inductive Rule where
  | refl (context : Ctx sig) (sort : Srt) (term : NativeTerm context.length)
  | symm (context : Ctx sig) (sort : Srt) (first second : NativeTerm context.length)
  | trans (context : Ctx sig) (sort : Srt) (first middle last : NativeTerm context.length)
  | parallelComm (context : Ctx sig) (first second : NativeTerm context.length)
  | parallelAssoc (context : Ctx sig) (first second third : NativeTerm context.length)
  | parallelUnit (context : Ctx sig) (term : NativeTerm context.length)
  | nameEta (context : Ctx sig) (term : NativeTerm context.length)
  | parallelCong (context : Ctx sig) (first first' second second' : NativeTerm context.length)
  | outputCong (context : Ctx sig) (name name' payload payload' : NativeTerm context.length)
  | inputCong (context : Ctx sig) (name name' : NativeTerm context.length)
      (body body' : NativeTerm (context.length + 1))
  | quoteCong (context : Ctx sig) (first second : NativeTerm context.length)
  | dropCong (context : Ctx sig) (first second : NativeTerm context.length)

def conclusion : Rule → Claim
  | .refl context sort term => ⟨context, sort, term, term⟩
  | .symm context sort first second => ⟨context, sort, second, first⟩
  | .trans context sort first _ last => ⟨context, sort, first, last⟩
  | .parallelComm context first second =>
      ⟨context, .pr, parallel first second, parallel second first⟩
  | .parallelAssoc context first second third =>
      ⟨context, .pr, parallel (parallel first second) third, parallel first (parallel second third)⟩
  | .parallelUnit context term => ⟨context, .pr, parallel term (.const zeroName), term⟩
  | .nameEta context term => ⟨context, .nm, quote (drop term), term⟩
  | .parallelCong context first first' second second' =>
      ⟨context, .pr, parallel first second, parallel first' second'⟩
  | .outputCong context name name' payload payload' =>
      ⟨context, .pr, output name payload, output name' payload'⟩
  | .inputCong context name name' body body' =>
      ⟨context, .pr, input name body, input name' body'⟩
  | .quoteCong context first second => ⟨context, .nm, quote first, quote second⟩
  | .dropCong context first second => ⟨context, .pr, drop first, drop second⟩

def premises : Rule → List Claim
  | .symm context sort first second => [⟨context, sort, first, second⟩]
  | .trans context sort first middle last =>
      [⟨context, sort, first, middle⟩, ⟨context, sort, middle, last⟩]
  | .parallelCong context first first' second second' =>
      [⟨context, .pr, first, first'⟩, ⟨context, .pr, second, second'⟩]
  | .outputCong context name name' payload payload' =>
      [⟨context, .nm, name, name'⟩, ⟨context, .pr, payload, payload'⟩]
  | .inputCong context name name' body body' =>
      [⟨context, .nm, name, name'⟩, ⟨.nm :: context, .pr, body, body'⟩]
  | .quoteCong context first second => [⟨context, .pr, first, second⟩]
  | .dropCong context first second => [⟨context, .nm, first, second⟩]
  | _ => []

def presentation : Mettapedia.OSLF.NativeTypes.Certificates.Presentation where
  Judgment := Claim
  Rule := Rule
  conclusion := conclusion
  premises := premises

private instance : DecidableEq presentation.Judgment :=
  inferInstanceAs (DecidableEq Claim)

abbrev Certificate := Mettapedia.OSLF.NativeTypes.Certificates.Tree presentation
abbrev Derivation (claim : Claim) := presentation.Derivation claim

def check (claim : Claim) (certificate : Certificate) : Bool :=
  Mettapedia.OSLF.NativeTypes.Certificates.Tree.check certificate claim

theorem rule_sound (rule : Rule)
    (children : ∀ claim ∈ premises rule, Meaning claim) : Meaning (conclusion rule) := by
  cases rule with
  | refl context sort term => exact .refl term
  | symm context sort first second =>
      exact .symm (children ⟨context, sort, first, second⟩ (by simp [premises]))
  | trans context sort first middle last =>
      exact .trans (children ⟨context, sort, first, middle⟩ (by simp [premises]))
        (children ⟨context, sort, middle, last⟩ (by simp [premises]))
  | parallelComm context first second => exact .parallelComm first second
  | parallelAssoc context first second third => exact .parallelAssoc first second third
  | parallelUnit context term => exact .parallelUnit term
  | nameEta context term => exact .nameEta term
  | parallelCong context first first' second second' =>
      exact .parallelCong (children ⟨context, .pr, first, first'⟩ (by simp [premises]))
        (children ⟨context, .pr, second, second'⟩ (by simp [premises]))
  | outputCong context name name' payload payload' =>
      exact .outputCong (children ⟨context, .nm, name, name'⟩ (by simp [premises]))
        (children ⟨context, .pr, payload, payload'⟩ (by simp [premises]))
  | inputCong context name name' body body' =>
      exact .inputCong (children ⟨context, .nm, name, name'⟩ (by simp [premises]))
        (children ⟨.nm :: context, .pr, body, body'⟩ (by simp [premises]))
  | quoteCong context first second =>
      exact .quoteCong (children ⟨context, .pr, first, second⟩ (by simp [premises]))
  | dropCong context first second =>
      exact .dropCong (children ⟨context, .nm, first, second⟩ (by simp [premises]))

theorem derivation_sound {claim : Claim} (derivation : Derivation claim) : Meaning claim := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun claim _ => Meaning claim) (t := derivation)
  intro claim rule children ih
  rcases rule with ⟨rule, same⟩
  cases same
  apply rule_sound rule
  intro child member
  obtain ⟨index, equal⟩ := List.get_of_mem member
  have result : Meaning ((premises rule).get index) := ih ⟨index⟩
  simpa only [equal] using result

private theorem derive (rule : Rule)
    (children : ∀ claim ∈ premises rule, Nonempty (Derivation claim)) :
    Nonempty (Derivation (conclusion rule)) := by
  classical
  exact ⟨.node ⟨rule, rfl⟩ (fun position =>
    Classical.choice (children _ (List.get_mem _ _)))⟩

theorem derivation_complete {context : Ctx sig} {sort : Srt}
    {first second : NativeTerm context.length} (proof : Structural context sort first second) :
    Nonempty (Derivation ⟨context, sort, first, second⟩) := by
  induction proof with
  | refl term => exact derive (.refl _ _ term) (by simp [premises])
  | symm proof ih => exact derive (.symm _ _ _ _) (by simpa [premises] using ih)
  | trans first second ihFirst ihSecond =>
      exact derive (.trans _ _ _ _ _) (by simpa [premises] using And.intro ihFirst ihSecond)
  | parallelComm first second => exact derive (.parallelComm _ first second) (by simp [premises])
  | parallelAssoc first second third =>
      exact derive (.parallelAssoc _ first second third) (by simp [premises])
  | parallelUnit term => exact derive (.parallelUnit _ term) (by simp [premises])
  | nameEta term => exact derive (.nameEta _ term) (by simp [premises])
  | parallelCong first second ihFirst ihSecond =>
      exact derive (.parallelCong _ _ _ _ _) (by simpa [premises] using And.intro ihFirst ihSecond)
  | outputCong name payload ihName ihPayload =>
      exact derive (.outputCong _ _ _ _ _) (by simpa [premises] using And.intro ihName ihPayload)
  | inputCong name body ihName ihBody =>
      exact derive (.inputCong _ _ _ _ _) (by simpa [premises] using And.intro ihName ihBody)
  | quoteCong proof ih => exact derive (.quoteCong _ _ _) (by simpa [premises] using ih)
  | dropCong proof ih => exact derive (.dropCong _ _ _) (by simpa [premises] using ih)

/-- Acceptance reconstructs the original native structural relation. -/
theorem check_sound (claim : Claim) (certificate : Certificate)
    (accepted : check claim certificate = true) : Meaning claim :=
  derivation_sound (Mettapedia.OSLF.NativeTypes.Certificates.Tree.reconstruct certificate claim accepted)

/-- Every independently derivable structural judgment has finite explicit evidence. -/
theorem check_complete (claim : Claim) :
    Meaning claim ↔ ∃ certificate : Certificate, check claim certificate = true := by
  constructor
  · intro proof
    obtain ⟨derivation⟩ := derivation_complete proof
    exact ⟨Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase derivation, Mettapedia.OSLF.NativeTypes.Certificates.Tree.check_erase derivation⟩
  · rintro ⟨certificate, accepted⟩
    exact check_sound claim certificate accepted

/-- Certificate erasure preserves the producer's exact rule payloads and
child occurrences, rather than only its conclusion. -/
theorem check_exact (claim : Claim) (certificate : Certificate) :
    check claim certificate = true ↔
      ∃ derivation : Derivation claim, Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase derivation = certificate :=
  Mettapedia.OSLF.NativeTypes.Certificates.Tree.check_exact certificate claim


private def oneChild {claim : Claim} (proof : Derivation claim) :
    (position : Fin 1) → Derivation (([claim] : List Claim).get position) :=
  Fin.cases proof (fun impossible => Fin.elim0 impossible)

private def twoChildren {first second : Claim}
    (before : Derivation first) (after : Derivation second) :
    (position : Fin 2) → Derivation (([first, second] : List Claim).get position) :=
  Fin.cases before (fun smaller => Fin.cases after (fun impossible => Fin.elim0 impossible) smaller)

/-- Explicit constructor functions retain the exact proof occurrences. -/
def reflexivity {context : Ctx sig} {sort : Srt} (term : NativeTerm context.length) :
    Derivation ⟨context, sort, term, term⟩ := by
  refine .node ⟨.refl context sort term, rfl⟩ ?_
  intro position
  exact Fin.elim0 position.down

def symmetry {context : Ctx sig} {sort : Srt} {first second : NativeTerm context.length}
    (proof : Derivation ⟨context, sort, first, second⟩) :
    Derivation ⟨context, sort, second, first⟩ := by
  refine .node ⟨.symm context sort first second, rfl⟩ ?_
  intro position
  exact oneChild proof position.down

def transitivity {context : Ctx sig} {sort : Srt}
    {first middle last : NativeTerm context.length}
    (before : Derivation ⟨context, sort, first, middle⟩)
    (after : Derivation ⟨context, sort, middle, last⟩) :
    Derivation ⟨context, sort, first, last⟩ := by
  refine .node ⟨.trans context sort first middle last, rfl⟩ ?_
  intro position
  exact twoChildren before after position.down

def commutativity {context : Ctx sig} (first second : NativeTerm context.length) :
    Derivation ⟨context, .pr, parallel first second, parallel second first⟩ := by
  refine .node ⟨.parallelComm context first second, rfl⟩ ?_
  intro position
  exact Fin.elim0 position.down

def associativity {context : Ctx sig} (first second third : NativeTerm context.length) :
    Derivation ⟨context, .pr, parallel (parallel first second) third,
      parallel first (parallel second third)⟩ := by
  refine .node ⟨.parallelAssoc context first second third, rfl⟩ ?_
  intro position
  exact Fin.elim0 position.down

def unit {context : Ctx sig} (term : NativeTerm context.length) :
    Derivation ⟨context, .pr, parallel term (.const zeroName), term⟩ := by
  refine .node ⟨.parallelUnit context term, rfl⟩ ?_
  intro position
  exact Fin.elim0 position.down

def eta {context : Ctx sig} (term : NativeTerm context.length) :
    Derivation ⟨context, .nm, quote (drop term), term⟩ := by
  refine .node ⟨.nameEta context term, rfl⟩ ?_
  intro position
  exact Fin.elim0 position.down

def parallelCongruence {context : Ctx sig}
    {first first' second second' : NativeTerm context.length}
    (before : Derivation ⟨context, .pr, first, first'⟩)
    (after : Derivation ⟨context, .pr, second, second'⟩) :
    Derivation ⟨context, .pr, parallel first second, parallel first' second'⟩ := by
  refine .node ⟨.parallelCong context first first' second second', rfl⟩ ?_
  intro position
  exact twoChildren before after position.down

def outputCongruence {context : Ctx sig}
    {name name' payload payload' : NativeTerm context.length}
    (before : Derivation ⟨context, .nm, name, name'⟩)
    (after : Derivation ⟨context, .pr, payload, payload'⟩) :
    Derivation ⟨context, .pr, output name payload, output name' payload'⟩ := by
  refine .node ⟨.outputCong context name name' payload payload', rfl⟩ ?_
  intro position
  exact twoChildren before after position.down

def inputCongruence {context : Ctx sig}
    {name name' : NativeTerm context.length} {body body' : NativeTerm (context.length + 1)}
    (before : Derivation ⟨context, .nm, name, name'⟩)
    (after : Derivation ⟨.nm :: context, .pr, body, body'⟩) :
    Derivation ⟨context, .pr, input name body, input name' body'⟩ := by
  refine .node ⟨.inputCong context name name' body body', rfl⟩ ?_
  intro position
  exact twoChildren before after position.down

def quoteCongruence {context : Ctx sig} {first second : NativeTerm context.length}
    (proof : Derivation ⟨context, .pr, first, second⟩) :
    Derivation ⟨context, .nm, quote first, quote second⟩ := by
  refine .node ⟨.quoteCong context first second, rfl⟩ ?_
  intro position
  exact oneChild proof position.down

def dropCongruence {context : Ctx sig} {first second : NativeTerm context.length}
    (proof : Derivation ⟨context, .nm, first, second⟩) :
    Derivation ⟨context, .pr, drop first, drop second⟩ := by
  refine .node ⟨.dropCong context first second, rfl⟩ ?_
  intro position
  exact oneChild proof position.down

/-- A substituted derivation is a finite explicit derivation, not a request
that the explicit checker should compute a substitution. -/
def Substituted (claim : Claim) : Type :=
  (destination : Ctx sig) →
  (action : Presentation.Sub Tower.Head claim.context.length destination.length) →
    Derivation ⟨destination, claim.sort,
      Presentation.subst action claim.first, Presentation.subst action claim.second⟩

private def substitutionAlgebra : JudgmentDerivation.Algebra presentation.signature where
  Carrier := Substituted
  conclude := by
    intro claim rule children
    rcases rule with ⟨rule, same⟩
    cases same
    intro destination action
    cases rule with
    | refl context sort term => exact reflexivity _
    | symm context sort first second =>
        exact symmetry (children ⟨⟨0, by simp [presentation, premises]⟩⟩ destination action)
    | trans context sort first middle last =>
        exact transitivity (children ⟨⟨0, by simp [presentation, premises]⟩⟩ destination action)
          (children ⟨⟨1, by simp [presentation, premises]⟩⟩ destination action)
    | parallelComm context first second => exact commutativity _ _
    | parallelAssoc context first second third => exact associativity _ _ _
    | parallelUnit context term => exact unit _
    | nameEta context term => exact eta _
    | parallelCong context first first' second second' =>
        exact parallelCongruence (children ⟨⟨0, by simp [presentation, premises]⟩⟩ destination action)
          (children ⟨⟨1, by simp [presentation, premises]⟩⟩ destination action)
    | outputCong context name name' payload payload' =>
        exact outputCongruence (children ⟨⟨0, by simp [presentation, premises]⟩⟩ destination action)
          (children ⟨⟨1, by simp [presentation, premises]⟩⟩ destination action)
    | inputCong context name name' body body' =>
        exact inputCongruence (children ⟨⟨0, by simp [presentation, premises]⟩⟩ destination action)
          (children ⟨⟨1, by simp [presentation, premises]⟩⟩ (.nm :: destination) (liftSub action))
    | quoteCong context first second =>
        exact quoteCongruence (children ⟨⟨0, by simp [presentation, premises]⟩⟩ destination action)
    | dropCong context first second =>
        exact dropCongruence (children ⟨⟨0, by simp [presentation, premises]⟩⟩ destination action)

/-- Compute all substituted rule payloads, lifting beneath every input binder. -/
def substitute {claim : Claim} (proof : Derivation claim)
    (destination : Ctx sig)
    (action : Presentation.Sub Tower.Head claim.context.length destination.length) :
    Derivation ⟨destination, claim.sort,
      Presentation.subst action claim.first, Presentation.subst action claim.second⟩ :=
  JudgmentDerivation.interpret substitutionAlgebra proof destination action

/-- The computed explicit output needs no substitution primitive at replay. -/
theorem substitute_checked {claim : Claim} (proof : Derivation claim)
    (destination : Ctx sig)
    (action : Presentation.Sub Tower.Head claim.context.length destination.length) :
    check ⟨destination, claim.sort,
      Presentation.subst action claim.first, Presentation.subst action claim.second⟩
      (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute proof destination action)) = true :=
  Mettapedia.OSLF.NativeTypes.Certificates.Tree.check_erase _



/-- Expanding substitution changes payloads but retains every inference
occurrence. This structural count does not bound the changed term payloads. -/
theorem substitute_nodeCount {claim : Claim} (proof : Derivation claim)
    (destination : Ctx sig)
    (action : Presentation.Sub Tower.Head claim.context.length destination.length) :
    (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
      (substitute proof destination action)).nodeCount =
      (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase proof).nodeCount := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun claim proof => ∀ destination action,
      (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute proof destination action)).nodeCount =
        (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase proof).nodeCount)
    (t := proof)
  intro claim rule children ih destination action
  rcases rule with ⟨rule, same⟩
  cases same
  cases rule with
  | refl context sort term => rfl
  | parallelComm context first second => rfl
  | parallelAssoc context first second third => rfl
  | parallelUnit context term => rfl
  | nameEta context term => rfl
  | symm context sort first second =>
      let position := (⟨⟨0, by change 0 < 1; decide⟩⟩ : presentation.signature.Premise ⟨.symm context sort first second, rfl⟩)
      change 1 + (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute (children position) destination action)).nodeCount =
        1 + (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children position)).nodeCount
      rw [ih position destination action]
  | quoteCong context first second =>
      let position := (⟨⟨0, by change 0 < 1; decide⟩⟩ : presentation.signature.Premise ⟨.quoteCong context first second, rfl⟩)
      change 1 + (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute (children position) destination action)).nodeCount =
        1 + (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children position)).nodeCount
      rw [ih position destination action]
  | dropCong context first second =>
      let position := (⟨⟨0, by change 0 < 1; decide⟩⟩ : presentation.signature.Premise ⟨.dropCong context first second, rfl⟩)
      change 1 + (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute (children position) destination action)).nodeCount =
        1 + (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children position)).nodeCount
      rw [ih position destination action]
  | trans context sort first middle last =>
      let before := (⟨⟨0, by change 0 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.trans context sort first middle last, rfl⟩)
      let after := (⟨⟨1, by change 1 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.trans context sort first middle last, rfl⟩)
      change 1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute (children before) destination action)).nodeCount +
        (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
          (substitute (children after) destination action)).nodeCount) =
        1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children before)).nodeCount +
          (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children after)).nodeCount)
      rw [ih before destination action, ih after destination action]
  | parallelCong context first first' second second' =>
      let before := (⟨⟨0, by change 0 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.parallelCong context first first' second second', rfl⟩)
      let after := (⟨⟨1, by change 1 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.parallelCong context first first' second second', rfl⟩)
      change 1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute (children before) destination action)).nodeCount +
        (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
          (substitute (children after) destination action)).nodeCount) =
        1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children before)).nodeCount +
          (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children after)).nodeCount)
      rw [ih before destination action, ih after destination action]
  | outputCong context name name' payload payload' =>
      let before := (⟨⟨0, by change 0 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.outputCong context name name' payload payload', rfl⟩)
      let after := (⟨⟨1, by change 1 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.outputCong context name name' payload payload', rfl⟩)
      change 1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute (children before) destination action)).nodeCount +
        (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
          (substitute (children after) destination action)).nodeCount) =
        1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children before)).nodeCount +
          (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children after)).nodeCount)
      rw [ih before destination action, ih after destination action]
  | inputCong context name name' body body' =>
      let before := (⟨⟨0, by change 0 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.inputCong context name name' body body', rfl⟩)
      let after := (⟨⟨1, by change 1 < 2; decide⟩⟩ : presentation.signature.Premise ⟨.inputCong context name name' body body', rfl⟩)
      change 1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (substitute (children before) destination action)).nodeCount +
        (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
          (substitute (children after) (.nm :: destination) (liftSub action))).nodeCount) =
        1 + ((Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children before)).nodeCount +
          (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase (children after)).nodeCount)
      rw [ih before destination action, ih after (.nm :: destination) (liftSub action)]

/-- The source endpoints remain actual existing sorted terms. -/
def sourceClaim {context : Ctx sig} {sort : Srt}
    (first second : Term sig context sort) : Claim :=
  ⟨context, sort, Inversion.E first, Inversion.E second⟩

private def axiomInstance :
    (index : Fin rhoSourceE.length) → {ambient context : Ctx sig} →
    (bodies : EqualityCertificates.Bodies sig ambient metas) →
    (environment : EqualityCertificates.Substitution sig ambient context) →
    (ordinary : EqualityCertificates.Substitution sig (rhoSourceE.get index).ctx context) →
      Derivation (sourceClaim
        (ContextualAssignment.instantiate bodies.read environment.read ordinary.read
          (rhoSourceE.get index).lhs)
        (ContextualAssignment.instantiate bodies.read environment.read ordinary.read
          (rhoSourceE.get index).rhs))
  | ⟨0, _⟩, _, _, _, _, ordinary =>
      commutativity (Inversion.E (ordinary.read _ .zero))
        (Inversion.E (ordinary.read _ (.succ .zero)))
  | ⟨1, _⟩, _, _, _, _, ordinary =>
      associativity (Inversion.E (ordinary.read _ .zero))
        (Inversion.E (ordinary.read _ (.succ .zero)))
        (Inversion.E (ordinary.read _ (.succ (.succ .zero))))
  | ⟨2, _⟩, _, _, _, _, ordinary => unit (Inversion.E (ordinary.read _ .zero))
  | ⟨3, _⟩, _, _, _, _, ordinary => eta (Inversion.E (ordinary.read _ .zero))
  | ⟨_ + 4, impossible⟩, _, _, _, _, _ => by simp [rhoSourceE] at impossible

/-- A finite product of native derivations for an existing argument spine.
It introduces no equation or syntax constructor. -/
inductive ArgumentDerivations : {arity : List (List Srt × Srt)} →
    {context : Ctx sig} → Args sig arity context → Args sig arity context → Type where
  | nil {context : Ctx sig} : ArgumentDerivations (context := context) .nil .nil
  | cons {arity : List (List Srt × Srt)} {context bound : Ctx sig} {sort : Srt}
      {first second : Term sig (bound ++ context) sort}
      {tail tail' : Args sig arity context}
      (head : Derivation (sourceClaim first second))
      (rest : ArgumentDerivations tail tail') :
      ArgumentDerivations (.cons first tail) (.cons second tail')

private def congruence : {context : Ctx sig} → {sort : Srt} →
    (operator : Op sort) → {first second : Args sig (sig.arity operator) context} →
    ArgumentDerivations first second →
      Derivation (sourceClaim (.op operator first) (.op operator second))
  | _, _, .nil, _, _, .nil => reflexivity _
  | _, _, .par, _, _, .cons first (.cons second .nil) => parallelCongruence first second
  | _, _, .out, _, _, .cons name (.cons payload .nil) => outputCongruence name payload
  | _, _, .inp, _, _, .cons name (.cons body .nil) => inputCongruence name body
  | _, _, .quo, _, _, .cons proof .nil => quoteCongruence proof
  | _, _, .drp, _, _, .cons proof .nil => dropCongruence proof

mutual
/-- Expand the actual compact proof object, reusing the original replay
calculation. The replay equality is computed evidence, not an adequacy callback. -/
def expand : {context : Ctx sig} → {sort : Srt} →
    (certificate : EquationEvidence context sort) →
    (result : EqualityCertificates.Result rhoSourceE context sort) →
    EqualityCertificates.replay certificate = some result →
      Derivation (sourceClaim result.left result.right)
  | _, _, .axiom index bodies environment ordinary, result, success => by
      simp only [EqualityCertificates.replay, Option.some.injEq] at success
      cases success
      exact axiomInstance index bodies environment ordinary
  | _, _, .refl term, result, success => by
      simp only [EqualityCertificates.replay, Option.some.injEq] at success
      cases success
      exact reflexivity _
  | _, _, .symm certificate, result, success => by
      cases outcome : EqualityCertificates.replay certificate with
      | none => simp [EqualityCertificates.replay, outcome] at success
      | some before =>
          simp [EqualityCertificates.replay, outcome] at success
          cases success
          exact symmetry (expand certificate before outcome)
  | _, _, .trans first second, result, success => by
      cases beforeRun : EqualityCertificates.replay first with
      | none => simp [EqualityCertificates.replay, beforeRun] at success
      | some before =>
          cases afterRun : EqualityCertificates.replay second with
          | none => simp [EqualityCertificates.replay, beforeRun, afterRun] at success
          | some after =>
              by_cases same : before.right = after.left
              · simp [EqualityCertificates.replay, beforeRun, afterRun, same] at success
                cases success
                exact transitivity (expand first before beforeRun)
                  (by simpa only [sourceClaim, same] using expand second after afterRun)
              · simp [EqualityCertificates.replay, beforeRun, afterRun, same] at success
  | _, _, .cong operator arguments, result, success => by
      cases outcome : EqualityCertificates.replayArguments arguments with
      | none => simp [EqualityCertificates.replay, outcome] at success
      | some before =>
          simp [EqualityCertificates.replay, outcome] at success
          cases success
          exact congruence operator (expandArguments arguments before outcome)
  | _, _, .substitute sigma certificate, result, success => by
      cases outcome : EqualityCertificates.replay certificate with
      | none => simp [EqualityCertificates.replay, outcome] at success
      | some before =>
          simp [EqualityCertificates.replay, outcome] at success
          cases success
          have computed := substitute (expand certificate before outcome) _
            (BindingSignatureEmbedding.encodeSub names sigma.read)
          simpa only [sourceClaim, BindingSignatureEmbedding.encode_substitution] using computed

def expandArguments : {arity : List (List Srt × Srt)} → {context : Ctx sig} →
    (certificates : EqualityCertificates.ArgumentCertificates sig metas rhoSourceE arity context) →
    (result : EqualityCertificates.ArgumentResult rhoSourceE arity context) →
    EqualityCertificates.replayArguments certificates = some result →
      ArgumentDerivations result.left result.right
  | _, _, .nil, result, success => by
      simp only [EqualityCertificates.replayArguments, Option.some.injEq] at success
      cases success
      exact .nil
  | _, _, .cons head tail, result, success => by
      cases headRun : EqualityCertificates.replay head with
      | none => simp [EqualityCertificates.replayArguments, headRun] at success
      | some headResult =>
          cases tailRun : EqualityCertificates.replayArguments tail with
          | none => simp [EqualityCertificates.replayArguments, headRun, tailRun] at success
          | some tailResult =>
              simp [EqualityCertificates.replayArguments, headRun, tailRun] at success
              cases success
              exact .cons (expand head headResult headRun) (expandArguments tail tailResult tailRun)
end

/-- An explicit output is constructed only after the original compact replay
has produced its actual endpoints. No proof search or choice is performed. -/
def expand? {context : Ctx sig} {sort : Srt}
    (certificate : EquationEvidence context sort) : Option Certificate :=
  match outcome : EqualityCertificates.replay certificate with
  | none => none
  | some result => some (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
      (expand certificate result outcome))

theorem expand_replay {context : Ctx sig} {sort : Srt}
    (certificate : EquationEvidence context sort)
    (result : EqualityCertificates.Result rhoSourceE context sort)
    (success : EqualityCertificates.replay certificate = some result) :
    expand? certificate = some (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
      (expand certificate result success)) := by
  unfold expand?
  split
  · rename_i failure
    rw [failure] at success
    contradiction
  · rename_i value equation
    have same : value = result := Option.some.inj (equation.symm.trans success)
    subst value
    rfl

theorem expand_replay_checked {context : Ctx sig} {sort : Srt}
    (certificate : EquationEvidence context sort)
    (result : EqualityCertificates.Result rhoSourceE context sort)
    (success : EqualityCertificates.replay certificate = some result) :
    check (sourceClaim result.left result.right)
      (Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
        (expand certificate result success)) = true :=
  Mettapedia.OSLF.NativeTypes.Certificates.Tree.check_erase _

/-- Every accepted compact packet computes an accepted explicit packet at
its original literal endpoints. The output payload may be much larger. -/
theorem expand_checked {context : Ctx sig} {sort : Srt}
    (certificate : EquationEvidence context sort) (first second : Term sig context sort)
    (accepted : EqualityCertificates.check certificate first second = true) :
    ∃ output : Certificate, expand? certificate = some output ∧
      check (sourceClaim first second) output = true := by
  cases outcome : EqualityCertificates.replay certificate with
  | none => simp [EqualityCertificates.check, outcome] at accepted
  | some result =>
      have endpoints : result.left = first ∧ result.right = second := by
        simpa [EqualityCertificates.check, outcome] using accepted
      refine ⟨_, expand_replay certificate result outcome, ?_⟩
      simpa only [endpoints.1, endpoints.2] using expand_replay_checked certificate result outcome


private theorem checked_claim_unique (certificate : Certificate) (first second : Claim)
    (before : check first certificate = true) (after : check second certificate = true) :
    first = second := by
  cases certificate with
  | node rule children =>
      have beforeRoot : conclusion rule = first :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp before).1
      have afterRoot : conclusion rule = second :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp after).1
      exact beforeRoot.symm.trans afterRoot

/-- Expansion neither repairs a refused compact certificate nor changes its
literal requested endpoints. This is about this compiler's actual output. -/
theorem expand_checked_iff {context : Ctx sig} {sort : Srt}
    (certificate : EquationEvidence context sort) (first second : Term sig context sort) :
    (∃ output : Certificate, expand? certificate = some output ∧
      check (sourceClaim first second) output = true) ↔
      EqualityCertificates.check certificate first second = true := by
  constructor
  · rintro ⟨output, expanded, accepted⟩
    cases outcome : EqualityCertificates.replay certificate with
    | none =>
        unfold expand? at expanded
        split at expanded
        · contradiction
        · rename_i value equation
          rw [outcome] at equation
          contradiction
    | some result =>
        have sameOutput : output = Mettapedia.OSLF.NativeTypes.Certificates.Tree.erase
            (expand certificate result outcome) :=
          Option.some.inj (expanded.symm.trans (expand_replay certificate result outcome))
        subst output
        have sameClaims := checked_claim_unique _ _ _
          (expand_replay_checked certificate result outcome) accepted
        have fields : Inversion.E result.left = Inversion.E first ∧
            Inversion.E result.right = Inversion.E second := by
          simpa [sourceClaim] using sameClaims
        have sameLeft := declared_encode_injective fields.1
        have sameRight := declared_encode_injective fields.2
        simp [EqualityCertificates.check, outcome, sameLeft, sameRight]
  · exact expand_checked certificate first second

/-- Directed process Drop cannot enter the explicit structural proof service. -/
theorem process_drop_refused (certificate : Certificate) :
    check ⟨[], .pr, drop (quote (.const zeroName)), .const zeroName⟩ certificate = false := by
  cases outcome : check ⟨[], .pr, drop (quote (.const zeroName)), .const zeroName⟩ certificate with
  | false => rfl
  | true => exact False.elim (process_drop_not_structural (check_sound _ _ outcome))


namespace ExpansionControls

/-- A concrete open process grows by replacing every occurrence of its
single variable with two copies, using the shipped simultaneous substitution. -/
def doubled : Nat → Term sig [Srt.pr] Srt.pr
  | 0 => .var .zero
  | n + 1 => .op Op.par (.cons (doubled n) (.cons (doubled n) .nil))

def doubling : EqualityCertificates.Substitution sig [Srt.pr] [Srt.pr] :=
  .cons (.op Op.par (.cons (.var .zero) (.cons (.var .zero) .nil))) .nil

theorem bind_doubled (n : Nat) : bind doubling.read (doubled n) = doubled (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (.op Op.par (.cons (bind doubling.read (doubled n))
        (.cons (bind doubling.read (doubled n)) .nil)) : Term sig [Srt.pr] Srt.pr) = _
      rw [ih]
      rfl

/-- This counts literal source syntax nodes. It is not a proof-node count,
a heap-sharing measure, a clock or a packed-byte length. -/
theorem doubled_payload_nodes (n : Nat) : termSize (doubled n) + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (termSize (doubled n) + (termSize (doubled n) + 0) + 1) + 1 = 2 ^ (n + 1 + 1)
      rw [Nat.pow_succ]
      omega

def compact : Nat → EquationEvidence [Srt.pr] Srt.pr
  | 0 => .refl (.var .zero)
  | n + 1 => .substitute doubling (compact n)

/-- The existing compact evaluator really produces the exponentially large
literal endpoints; the size theorem is not an unattached annotation. -/
theorem compact_replay (n : Nat) :
    EqualityCertificates.replay (compact n) =
      some ⟨doubled n, doubled n, EqClosure.refl (doubled n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compact, EqualityCertificates.replay, ih, bind_doubled]

/-- The explicit output is the computed compiler result at those endpoints. -/
theorem compact_expands (n : Nat) :
    ∃ output : Certificate, expand? (compact n) = some output ∧
      check (sourceClaim (doubled n) (doubled n)) output = true := by
  exact ⟨_, expand_replay (compact n) _ (compact_replay n),
    expand_replay_checked (compact n) _ (compact_replay n)⟩

end ExpansionControls

end Explicit

end Conversion
end Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedRepresentation
