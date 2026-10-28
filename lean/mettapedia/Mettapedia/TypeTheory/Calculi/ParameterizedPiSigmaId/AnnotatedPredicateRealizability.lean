import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateContexts
import Mettapedia.Logic.HOL.Syntax.SubstitutionExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.TelescopeAbstractions

/-!
# Retained guarded realizers over represented source contexts

A realizer combines source typing, the exact term/type readings and an actual
HOL membership proof. A represented substitution supplies both source typing
and target guard proofs. Reading a substitution does not supply those proofs.
Root premises remain a separate ordered prefix of each hypothesis context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
open HOL.PredicateContexts
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v w
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
  {Γ Ξ Ω : HOL.Ctx Base}

structure GuardedContext (P : ChurchRules R) (lex : LexicalReading Head Base Const) (Γ : HOL.Ctx Base) where
  source : CCtx Head Γ.length
  telescope : Telescope Const Γ
  formed : CCtxFormed P source
  reading : ContextReads lex source telescope

namespace GuardedContext
variable (context : GuardedContext P lex Γ) (roots : List (HOL.ClosedFormula Const))

def ofAdmitted {source : CCtx Head Γ.length} (accepted : Reader.AdmittedContext P lex Γ source) :
    GuardedContext P lex Γ := ⟨source, accepted.code, accepted.formed, accepted.reading⟩

def hypotheses : List (HOL.Formula Const Γ) := assumptions roots Γ ++ context.telescope.hypotheses

def snoc {carrier : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P context.source A) : GuardedContext P lex (carrier :: Γ) where
  source := .snoc context.source A
  telescope := .snoc context.telescope predicate
  formed := .snoc context.formed formed
  reading := .snoc context.reading reading

def variableProof {carrier : HOL.Ty Base} (index : HOL.Var Γ carrier) :
    HOL.ProofSyntax Const (context.hypotheses roots) (context.telescope.guard index) :=
  (context.telescope.variableProof index).mono
    (HOL.ProofSyntax.OccurrenceMap.appendLeft (assumptions roots Γ) context.telescope.hypotheses)

private def insertAfter {α : Type u} : (front : List α) → (item : α) → (tail : List α) →
    HOL.ProofSyntax.OccurrenceMap (front ++ tail) (front ++ item :: tail)
  | [], item, _ => HOL.ProofSyntax.OccurrenceMap.prepend item
  | head :: front, item, tail => (insertAfter front item tail).lift head

def weakenProof {carrier : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P context.source A) {formula : HOL.Formula Const Γ}
    (proof : HOL.ProofSyntax Const (context.hypotheses roots) formula) :
    HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) (HOL.weaken formula) := by
  have raised : HOL.ProofSyntax Const (assumptions roots (carrier :: Γ) ++ HOL.weakenHyps context.telescope.hypotheses)
      (HOL.weaken formula) := by
    apply HOL.ProofSyntax.castIndices ?_ rfl (proof.rename HOL.Rename.weaken)
    change HOL.weakenHyps (context.hypotheses roots) = _
    simp only [hypotheses, HOL.weakenHyps, List.map_append]
    exact congrArg (fun front => front ++ HOL.weakenHyps context.telescope.hypotheses)
      (assumptions_weaken roots Γ carrier)
  exact raised.mono (insertAfter (assumptions roots (carrier :: Γ)) (.app (HOL.weaken predicate) (.var .vz))
    (HOL.weakenHyps context.telescope.hypotheses))

/-- Closed root formulas substitute to the same root occurrences in the
recipient context; no new background formula is introduced. -/
def rootSubstitution {sourceContext : HOL.Ctx Base} (substitution : HOL.Subst Const sourceContext Γ) :
    HOL.ProofSyntax.HypothesisSubstitution ((assumptions roots sourceContext).map (HOL.subst substitution))
      (context.hypotheses roots) := fun occurrence => by
  let target : Fin (assumptions roots Γ).length := occurrence.cast (by simp [assumptions])
  apply HOL.ProofSyntax.castIndices rfl ?_
    ((HOL.ProofSyntax.hyp (Const := Const) (Δ := assumptions roots Γ) target).mono
      (HOL.ProofSyntax.OccurrenceMap.appendRight _ context.telescope.hypotheses))
  simp [assumptions, List.get_eq_getElem, target, HOL.subst_weakenCtx]

private def moveGuard {context : HOL.Ctx Base} (front : List (HOL.Formula Const context))
    (guard : HOL.Formula Const context) (tail : List (HOL.Formula Const context)) :
    HOL.ProofSyntax.HypothesisSubstitution (front ++ guard :: tail) (guard :: (front ++ tail)) :=
  HOL.ProofSyntax.HypothesisSubstitution.append front (guard :: tail) (guard :: (front ++ tail))
    (fun index => ((HOL.ProofSyntax.hyp (Δ := front) index).mono
      (HOL.ProofSyntax.OccurrenceMap.appendRight front tail)).prepend guard)
    (Fin.cases (.hyp 0) (fun index => ((HOL.ProofSyntax.hyp (Δ := tail) index).mono
      (HOL.ProofSyntax.OccurrenceMap.appendLeft front tail)).prepend guard))

def lambdaMember {domain codomain : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (domain ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P context.source A) (family : HOL.Term Const (domain :: Γ) (codomain ⇒ .prop))
    (body : HOL.Term Const (domain :: Γ) codomain)
    (member : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) (.app family body)) :
    HOL.ProofSyntax Const (context.hypotheses roots) (.app (HOL.PredicateProducts.pi predicate family) (.lam body)) := by
  let guard := HOL.Term.app (HOL.weaken predicate) (.var .vz)
  have aligned : HOL.ProofSyntax Const (guard :: HOL.weakenHyps (context.hypotheses roots)) (.app family body) := by
    apply HOL.ProofSyntax.castIndices ?_ rfl
      (HOL.ProofSyntax.substituteHypotheses
        (moveGuard (assumptions roots (domain :: Γ)) guard (HOL.weakenHyps context.telescope.hypotheses)) member)
    simp only [hypotheses, HOL.weakenHyps, List.map_append]
    rw [← assumptions_weaken roots Γ domain]
    rfl
  have cancels : HOL.instantiate (.var (.vz : HOL.Var (domain :: Γ) domain))
      (HOL.rename (HOL.Rename.lift HOL.Rename.weaken) body) = body := by
    rw [HOL.instantiate, HOL.subst_rename]
    trans HOL.subst HOL.Subst.id body
    · apply HOL.subst_ext
      intro carrier index
      cases index <;> rfl
    · exact HOL.subst_id body
  let computation : HOL.ProofSyntax Const (guard :: HOL.weakenHyps (context.hypotheses roots))
      (.eq (.app (HOL.weaken (.lam body)) (.var .vz)) body) :=
    HOL.ProofSyntax.castIndices rfl
      (congrArg (HOL.Term.eq (.app (HOL.weaken (.lam body)) (.var .vz))) cancels)
      (.beta (.var .vz) (HOL.rename (HOL.Rename.lift HOL.Rename.weaken) body))
  exact HOL.PredicateProducts.introduce predicate family (.lam body)
    (.impE (.eqPropER (.eqAppArg family computation)) aligned)

theorem variableProof_free {carrier : HOL.Ty Base} (index : HOL.Var Γ carrier) :
    (context.variableProof roots index).FunctionExtensionalityFree := by
  simp [variableProof, Telescope.variableProof, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem weakenProof_free {carrier : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P context.source A) {formula : HOL.Formula Const Γ}
    (proof : HOL.ProofSyntax Const (context.hypotheses roots) formula) (free : proof.FunctionExtensionalityFree) :
    (context.weakenProof roots predicate reading formed proof).FunctionExtensionalityFree := by
  simpa only [weakenProof, HOL.ProofSyntax.functionExtensionalityFree_mono,
    HOL.ProofSyntax.functionExtensionalityFree_castIndices, HOL.ProofSyntax.functionExtensionalityFree_rename] using free

theorem rootSubstitution_free {sourceContext : HOL.Ctx Base} (substitution : HOL.Subst Const sourceContext Γ) :
    ∀ occurrence, (context.rootSubstitution roots substitution occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simp [rootSubstitution, HOL.ProofSyntax.FunctionExtensionalityFree]

private theorem moveGuard_free {context : HOL.Ctx Base} (front : List (HOL.Formula Const context))
    (guard : HOL.Formula Const context) (tail : List (HOL.Formula Const context)) :
    ∀ occurrence, (moveGuard front guard tail occurrence).FunctionExtensionalityFree := by
  apply HOL.ProofSyntax.HypothesisSubstitution.append_free
  · intro index
    simp [HOL.ProofSyntax.prepend, HOL.ProofSyntax.FunctionExtensionalityFree]
  · intro index
    refine Fin.cases ?_ ?_ index
    · trivial
    · intro prior
      simp [HOL.ProofSyntax.prepend, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem lambdaMember_free {domain codomain : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (domain ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P context.source A) (family : HOL.Term Const (domain :: Γ) (codomain ⇒ .prop))
    (body : HOL.Term Const (domain :: Γ) codomain)
    (member : HOL.ProofSyntax Const ((context.snoc predicate reading formed).hypotheses roots) (.app family body))
    (free : member.FunctionExtensionalityFree) :
    (context.lambdaMember roots predicate reading formed family body member).FunctionExtensionalityFree := by
  unfold lambdaMember
  apply HOL.PredicateProducts.introduce_free
  simp only [HOL.ProofSyntax.FunctionExtensionalityFree, HOL.ProofSyntax.functionExtensionalityFree_castIndices, true_and]
  exact HOL.ProofSyntax.substituteHypotheses_free _ member free (moveGuard_free _ _ _)

end GuardedContext

structure GuardedRealizer (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    (source type : CTm Head Γ.length) (carrier : HOL.Ty Base) where
  typed : CTyped P context.source source type
  term : HOL.Term Const Γ carrier
  predicate : HOL.Term Const Γ (carrier ⇒ .prop)
  termRead : Reads lex source term
  typeRead : Reads lex type predicate
  member : HOL.ProofSyntax Const (context.hypotheses roots) (.app predicate term)

structure GuardedSubstitution (roots : List (HOL.ClosedFormula Const))
    (source : GuardedContext P lex Γ) (target : GuardedContext P lex Ξ)
    (raw : CSub Head Γ.length Ξ.length) (code : HOL.Subst Const Γ Ξ) where
  typed : CSubstMor P source.source target.source raw
  represented : ∀ {carrier} (index : HOL.Var Γ carrier), Reads lex (raw index.toFin) (code index)
  guards : source.telescope.Realizes code (target.hypotheses roots)

namespace GuardedSubstitution
variable {roots : List (HOL.ClosedFormula Const)}
  {source : GuardedContext P lex Γ} {target : GuardedContext P lex Ξ}
  {raw : CSub Head Γ.length Ξ.length} {code : HOL.Subst Const Γ Ξ}

def transportStored (realizer : GuardedSubstitution roots source target raw code)
    {formula : HOL.Formula Const Γ} (proof : HOL.ProofSyntax Const (source.hypotheses roots) formula) :
    HOL.ProofSyntax Const (target.hypotheses roots) (HOL.subst code formula) := by
  let inputs := HOL.ProofSyntax.HypothesisSubstitution.append
    ((assumptions roots Γ).map (HOL.subst code)) (source.telescope.hypotheses.map (HOL.subst code))
    (target.hypotheses roots) (target.rootSubstitution roots code) (Telescope.Realizes.hypotheses realizer.guards)
  apply HOL.ProofSyntax.substituteHypothesesCached inputs
  apply HOL.ProofSyntax.castIndices ?_ rfl (proof.subst code)
  exact List.map_append

/-- The assignment is shared by proof traversal and hypothesis bookkeeping. -/
def transport (realizer : GuardedSubstitution roots source target raw code)
    {formula : HOL.Formula Const Γ} (proof : HOL.ProofSyntax Const (source.hypotheses roots) formula) :
    HOL.ProofSyntax Const (target.hypotheses roots) (HOL.subst code formula) :=
  let table := HOL.Subst.Table.ofSubst code
  let same := HOL.Subst.Table.lookup_ofSubst code
  let stored := Eq.ndrec (motive := fun (assignment : HOL.Subst Const Γ Ξ) =>
    GuardedSubstitution roots source target raw assignment) realizer same.symm
  Eq.ndrec (motive := fun (assignment : HOL.Subst Const Γ Ξ) =>
    HOL.ProofSyntax Const (target.hypotheses roots) (HOL.subst assignment formula))
    (transportStored (code := table.lookup) stored proof) same

theorem transport_eq (realizer : GuardedSubstitution roots source target raw code)
    {formula : HOL.Formula Const Γ} (proof : HOL.ProofSyntax Const (source.hypotheses roots) formula) :
    realizer.transport proof = realizer.transportStored proof := by
  have coherent : ∀ (assignment : HOL.Subst Const Γ Ξ) (same : @assignment = @code),
      Eq.ndrec (motive := fun (assigned : HOL.Subst Const Γ Ξ) =>
        HOL.ProofSyntax Const (target.hypotheses roots) (HOL.subst assigned formula))
        (transportStored (Eq.ndrec (motive := fun (assigned : HOL.Subst Const Γ Ξ) =>
          GuardedSubstitution roots source target raw assigned) realizer same.symm) proof) same =
        realizer.transportStored proof := by
    intro assignment same
    cases same
    rfl
  exact coherent _ (HOL.Subst.Table.lookup_ofSubst code)

def identity (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ) :
    GuardedSubstitution roots context context CTm.ids HOL.Subst.id where
  typed index := by
    simpa only [CTm.subst_ids, CTm.ids] using (CDerivable.var (P := P) (Γ := context.source) index)
  represented index := .var index
  guards index := HOL.ProofSyntax.castIndices rfl (HOL.subst_id _).symm (context.variableProof roots index)

def comp {destination : GuardedContext P lex Ω} {nextRaw : CSub Head Ξ.length Ω.length}
    {nextCode : HOL.Subst Const Ξ Ω}
    (first : GuardedSubstitution roots source target raw code)
    (second : GuardedSubstitution roots target destination nextRaw nextCode) :
    GuardedSubstitution roots source destination (fun index => (raw index).subst nextRaw)
      (HOL.Subst.comp nextCode code) where
  typed index := by simpa only [CTm.subst_comp] using (first.typed index).substitute second.typed
  represented index := (first.represented index).substitute nextCode nextRaw second.represented
  guards index := HOL.ProofSyntax.castIndices rfl (HOL.subst_comp nextCode code _)
    (second.transport (first.guards index))

def ofRenaming [DecidableEq Base] (roots : List (HOL.ClosedFormula Const))
    (source : GuardedContext P lex Γ) (target : GuardedContext P lex Ξ)
    (rawRen : Ren Γ.length Ξ.length) (codeRen : HOL.Rename Base Γ Ξ)
    (compatible : ∀ {type} (index : HOL.Var Γ type), (codeRen index).toFin = rawRen index.toFin)
    (placement : CCtxRen source.source target.source rawRen) :
    GuardedSubstitution roots source target (fun index => CTm.var (rawRen index)) (HOL.Subst.ofRename codeRen) where
  typed index := by
    have typeEq : (source.source.lookup index).rename rawRen =
        (source.source.lookup index).subst (fun index => CTm.var (rawRen index)) := by
      simpa only [CTm.subst_ids, CTm.ids, CTm.rename] using CTm.rename_subst rawRen CTm.ids (source.source.lookup index)
    rw [← typeEq]
    exact CTyped.rename (ρ := rawRen) (CDerivable.var (P := P) (Γ := source.source) index) placement
  represented index := by
    change Reads lex (.var (rawRen index.toFin)) (.var (codeRen index))
    rw [← compatible index]
    exact .var _
  guards index :=
    ((ContextReads.renamingRealizer source.reading target.reading codeRen rawRen compatible placement) index).mono
      (HOL.ProofSyntax.OccurrenceMap.appendLeft (assumptions roots Ξ) target.telescope.hypotheses)

def weakening [DecidableEq Base] (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    {carrier : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P context.source A) :
    GuardedSubstitution roots context (context.snoc predicate reading formed)
      (fun index => CTm.var (wk index)) (HOL.Subst.ofRename HOL.Rename.weaken) :=
  ofRenaming roots context (context.snoc predicate reading formed) wk HOL.Rename.weaken (fun _ => rfl)
    (CCtxRen.wk context.source A)

theorem typeFormed (substitution : GuardedSubstitution roots source target raw code)
    {A : CTm Head Γ.length} (formed : CIsType P source.source A) :
    CIsType P target.source (A.subst raw) := by
  obtain ⟨level, allowed, typed⟩ := formed
  exact ⟨level, allowed, typed.substitute substitution.typed⟩

def lift (substitution : GuardedSubstitution roots source target raw code)
    {carrier : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P source.source A) :
    GuardedSubstitution roots (source.snoc predicate reading formed)
      (target.snoc (HOL.subst code predicate) (reading.substitute code raw substitution.represented)
        (substitution.typeFormed formed)) (CTm.liftSub raw) (HOL.Subst.lift code) where
  typed := substitution.typed.lift A
  represented := by
    intro type index
    cases index with
    | vz => exact .var .vz
    | vs prior =>
        simpa only [HOL.Var.toFin, CTm.liftSub_succ, HOL.Subst.lift, HOL.weaken] using
          (substitution.represented prior).rename HOL.Rename.weaken wk (fun _ => rfl)
  guards := fun index => match index with
    | .vz => by
        apply HOL.ProofSyntax.castIndices rfl ?_
          ((target.snoc (HOL.subst code predicate) (reading.substitute code raw substitution.represented)
            (substitution.typeFormed formed)).variableProof roots HOL.Var.vz)
        simp [GuardedContext.snoc, Telescope.guard, Telescope.domain, HOL.subst, HOL.subst_weaken, HOL.Subst.lift]
    | .vs prior => by
        apply HOL.ProofSyntax.castIndices rfl ?_
          (target.weakenProof roots (HOL.subst code predicate) (reading.substitute code raw substitution.represented)
            (substitution.typeFormed formed) (substitution.guards prior))
        simp only [GuardedContext.snoc, Telescope.guard, Telescope.domain, HOL.subst, HOL.subst_weaken,
          HOL.Subst.lift]
        rfl

private theorem subst_cons_weaken {domain result : HOL.Ty Base}
    (argument : HOL.Term Const Ξ domain) (substitution : HOL.Subst Const Γ Ξ) (term : HOL.Term Const Γ result) :
    HOL.subst (HOL.Subst.cons argument substitution) (HOL.weaken term) = HOL.subst substitution term := by
  rw [HOL.weaken, HOL.subst_rename]
  rfl

def cons [DecidableEq Base] (substitution : GuardedSubstitution roots source target raw code)
    {carrier : HOL.Ty Base} {A : CTm Head Γ.length} {argument : CTm Head Ξ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P source.source A)
    (value : GuardedRealizer roots target argument (A.subst raw) carrier) :
    GuardedSubstitution roots (source.snoc predicate reading formed) target
      (CTm.consSub argument raw) (HOL.Subst.cons value.term code) where
  typed := substitution.typed.cons value.typed
  represented := fun index => match index with
    | .vz => value.termRead
    | .vs prior => substitution.represented prior
  guards := fun index => match index with
    | .vz => by
        have same := Reader.term_unique value.typeRead (reading.substitute code raw substitution.represented)
        have member := HOL.ProofSyntax.castIndices rfl
          (congrArg (fun predicate => HOL.Term.app predicate value.term) same) value.member
        apply HOL.ProofSyntax.castIndices rfl ?_ member
        simp only [GuardedContext.snoc, Telescope.guard, Telescope.domain, HOL.subst, HOL.Subst.cons,
          subst_cons_weaken]
    | .vs prior => by
        apply HOL.ProofSyntax.castIndices rfl ?_ (substitution.guards prior)
        simp only [GuardedContext.snoc, Telescope.guard, Telescope.domain, HOL.subst, HOL.Subst.cons,
          subst_cons_weaken]

def Free (substitution : GuardedSubstitution roots source target raw code) : Prop :=
  ∀ {carrier} (index : HOL.Var Γ carrier), (substitution.guards index).FunctionExtensionalityFree

theorem transport_free (realizer : GuardedSubstitution roots source target raw code)
    {formula : HOL.Formula Const Γ} (proof : HOL.ProofSyntax Const (source.hypotheses roots) formula)
    (realizerFree : realizer.Free) (free : proof.FunctionExtensionalityFree) :
    (realizer.transport proof).FunctionExtensionalityFree := by
  rw [transport_eq]
  unfold transportStored
  rw [HOL.ProofSyntax.substituteHypothesesCached_eq]
  apply HOL.ProofSyntax.substituteHypotheses_free
  · simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices,
      HOL.ProofSyntax.functionExtensionalityFree_subst] using free
  · exact HOL.ProofSyntax.HypothesisSubstitution.append_free _ _ _ _ _
      (target.rootSubstitution_free roots code) (Telescope.Realizes.hypotheses_free realizer.guards realizerFree)

theorem identity_free (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ) :
    (identity roots context).Free := by
  intro carrier index
  simpa only [identity, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using context.variableProof_free roots index

theorem comp_free {destination : GuardedContext P lex Ω} {nextRaw : CSub Head Ξ.length Ω.length}
    {nextCode : HOL.Subst Const Ξ Ω} (first : GuardedSubstitution roots source target raw code)
    (second : GuardedSubstitution roots target destination nextRaw nextCode) (firstFree : first.Free) (secondFree : second.Free) :
    (first.comp second).Free := by
  intro carrier index
  simpa only [comp, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
    transport_free second (first.guards index) secondFree (firstFree index)

theorem ofRenaming_free [DecidableEq Base] (roots : List (HOL.ClosedFormula Const))
    (source : GuardedContext P lex Γ) (target : GuardedContext P lex Ξ)
    (rawRen : Ren Γ.length Ξ.length) (codeRen : HOL.Rename Base Γ Ξ)
    (compatible : ∀ {type} (index : HOL.Var Γ type), (codeRen index).toFin = rawRen index.toFin)
    (placement : CCtxRen source.source target.source rawRen) :
    (ofRenaming roots source target rawRen codeRen compatible placement).Free := by
  intro carrier index
  simp [ofRenaming, ContextReads.renamingRealizer, Telescope.variableProof, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem lift_free (substitution : GuardedSubstitution roots source target raw code)
    {carrier : HOL.Ty Base} {A : CTm Head Γ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P source.source A) (free : substitution.Free) :
    (substitution.lift predicate reading formed).Free := by
  intro type index
  cases index with
  | vz =>
      simpa only [lift, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
        (target.snoc (HOL.subst code predicate) (reading.substitute code raw substitution.represented)
          (substitution.typeFormed formed)).variableProof_free roots HOL.Var.vz
  | vs prior =>
      simpa only [lift, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
        target.weakenProof_free roots (HOL.subst code predicate) (reading.substitute code raw substitution.represented)
          (substitution.typeFormed formed) (substitution.guards prior) (free prior)

theorem cons_free [DecidableEq Base] (substitution : GuardedSubstitution roots source target raw code)
    {carrier : HOL.Ty Base} {A : CTm Head Γ.length} {argument : CTm Head Ξ.length}
    (predicate : HOL.Term Const Γ (carrier ⇒ .prop)) (reading : Reads lex A predicate)
    (formed : CIsType P source.source A)
    (value : GuardedRealizer roots target argument (A.subst raw) carrier)
    (substitutionFree : substitution.Free) (valueFree : value.member.FunctionExtensionalityFree) :
    (substitution.cons predicate reading formed value).Free := by
  intro type index
  cases index with
  | vz => simpa only [cons, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using valueFree
  | vs prior => simpa only [cons, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using substitutionFree prior

/-- A realizing target valuation gives a realizing source valuation after
substitution. Both root premises and variable guards are retained. -/
theorem satisfies (substitution : GuardedSubstitution roots source target raw code)
    (model : HOL.HenkinModel.{u,v,w} Base Const) (respects : model.FunctionsRespectEqv)
    (values : model.Valuation Ξ) (admitted : model.ValuationAdmissible values)
    (holds : HOL.Soundness.SatisfiesHyps model values (target.hypotheses roots)) :
    HOL.Soundness.SatisfiesHyps model (HOL.Soundness.substVal model code values) (source.hypotheses roots) := by
  intro formula present
  obtain ⟨occurrence, rfl⟩ := List.mem_iff_get.mp present
  have transported := HOL.Soundness.extDerivation_sound
    (substitution.transport (HOL.ProofSyntax.hyp occurrence)).erase respects admitted holds
  simpa only [HOL.Soundness.denote_subst] using transported

end GuardedSubstitution

namespace Reader
variable [DecidableEq Base]

def readTyped? (lex : LexicalReading Head Base Const) (context : HOL.Ctx Base)
    (source : CTm Head context.length) (carrier : HOL.Ty Base) :
    Option {code : HOL.Term Const context carrier // Reads lex source code} := do
  let result ← read? lex context source
  if same : result.val.1 = carrier then
    some ⟨same ▸ result.val.2, by cases same; exact result.property⟩
  else none

theorem readTyped?_complete {source : CTm Head Γ.length} {carrier : HOL.Ty Base}
    {code : HOL.Term Const Γ carrier} (reading : Reads lex source code) :
    readTyped? lex Γ source carrier = some ⟨code, reading⟩ := by
  simp [readTyped?, read?_complete reading]

theorem product_family_readable {A : CTm Head Γ.length} {B : CTm Head (Γ.length + 1)}
    {domain codomain : HOL.Ty Base} {predicate : HOL.Term Const Γ ((domain ⇒ codomain) ⇒ .prop)}
    (reading : Reads lex (.pi A B) predicate) :
    (readTyped? lex (domain :: Γ) B (codomain ⇒ .prop)).isSome = true := by
  cases reading with
  | product domainRead familyRead => rw [readTyped?_complete familyRead]; rfl

end Reader

namespace GuardedRealizer
variable {roots : List (HOL.ClosedFormula Const)} {context : GuardedContext P lex Γ}
  {source type : CTm Head Γ.length} {carrier : HOL.Ty Base}

def ofVariable (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    (index : HOL.Var Γ carrier) : GuardedRealizer roots context (.var index.toFin)
      (context.source.lookup index.toFin) carrier where
  typed := .var index.toFin
  term := .var index
  predicate := context.telescope.domain index
  termRead := .var index
  typeRead := context.reading.lookup index
  member := context.variableProof roots index

def substitute {target : GuardedContext P lex Ξ} {raw : CSub Head Γ.length Ξ.length}
    {code : HOL.Subst Const Γ Ξ} (realizer : GuardedRealizer roots context source type carrier)
    (substitution : GuardedSubstitution roots context target raw code) :
    GuardedRealizer roots target (source.subst raw) (type.subst raw) carrier where
  typed := realizer.typed.substitute substitution.typed
  term := HOL.subst code realizer.term
  predicate := HOL.subst code realizer.predicate
  termRead := realizer.termRead.substitute code raw substitution.represented
  typeRead := realizer.typeRead.substitute code raw substitution.represented
  member := substitution.transport realizer.member

def application [DecidableEq Base] {A : CTm Head Γ.length} {B : CTm Head (Γ.length + 1)}
    {function argument : CTm Head Γ.length} {domain codomain : HOL.Ty Base}
    (functionValue : GuardedRealizer roots context function (.pi A B) (domain ⇒ codomain))
    (argumentValue : GuardedRealizer roots context argument A domain) :
    GuardedRealizer roots context (.app function argument) (CTm.inst0 argument B) codomain := by
  let family := (Reader.readTyped? lex (domain :: Γ) B (codomain ⇒ .prop)).get
    (Reader.product_family_readable functionValue.typeRead)
  have productRead := Reads.product argumentValue.typeRead family.property
  have same := Reader.term_unique functionValue.typeRead productRead
  have functionGuard := HOL.ProofSyntax.castIndices rfl
    (congrArg (fun predicate => HOL.Term.app predicate functionValue.term) same) functionValue.member
  exact ⟨.appElim functionValue.typed argumentValue.typed, .app functionValue.term argumentValue.term,
    HOL.instantiate argumentValue.term family.val, .application functionValue.termRead argumentValue.termRead,
    family.property.instantiate argumentValue.termRead,
    HOL.PredicateProducts.eliminate _ _ functionValue.term argumentValue.term functionGuard argumentValue.member⟩

def abstraction {L : Type} [UniverseLevel.LevelOrder L] (levels : TypedEquality.Normalization.LevelModel R L)
    {domain codomain : HOL.Ty Base} {A : CTm Head Γ.length} {body B : CTm Head (Γ.length + 1)}
    (predicate : HOL.Term Const Γ (domain ⇒ .prop)) (domainRead : Reads lex A predicate)
    (domainFormed : CIsType P context.source A)
    (familyFormed : CIsType P (.snoc context.source A) B)
    (bodyValue : GuardedRealizer roots (context.snoc predicate domainRead domainFormed) body B codomain) :
    GuardedRealizer roots context (.lam A body) (.pi A B) (domain ⇒ codomain) where
  typed := CTyped.abstractTerm levels domainFormed familyFormed bodyValue.typed
  term := .lam bodyValue.term
  predicate := HOL.PredicateProducts.pi predicate bodyValue.predicate
  termRead := .abstraction domainRead bodyValue.termRead
  typeRead := .product domainRead bodyValue.typeRead
  member := context.lambdaMember roots predicate domainRead domainFormed bodyValue.predicate bodyValue.term bodyValue.member

def convert [DecidableEq Base] {otherType : CTm Head Γ.length}
    (realizer : GuardedRealizer roots context source type carrier)
    (sourceEquality : CTypeEq P context.source type otherType)
    (equality : EqualityAt lex roots Γ type otherType (carrier ⇒ .prop)) :
    GuardedRealizer roots context source otherType carrier := by
  have same := Reader.term_unique realizer.typeRead equality.leftRead
  have oldGuard := HOL.ProofSyntax.castIndices rfl
    (congrArg (fun predicate => HOL.Term.app predicate realizer.term) same) realizer.member
  have moved := equality.proof.mono
    (HOL.ProofSyntax.OccurrenceMap.appendRight (assumptions roots Γ) context.telescope.hypotheses)
  exact ⟨realizer.typed.convType sourceEquality, realizer.term, equality.right,
    realizer.termRead, equality.rightRead, .impE (.eqPropEL (.eqApp realizer.term moved)) oldGuard⟩

/-- Transport membership along a typed term equality and its retained reading. -/
def rewrite [DecidableEq Base] {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L) {target : CTm Head Γ.length}
    (realizer : GuardedRealizer roots context source type carrier)
    (sourceEquality : CEqual P context.source source target type)
    (equality : EqualityAt lex roots Γ source target carrier) :
    GuardedRealizer roots context target type carrier := by
  have same := Reader.term_unique realizer.termRead equality.leftRead
  have oldGuard := HOL.ProofSyntax.castIndices rfl
    (congrArg (fun term => HOL.Term.app realizer.predicate term) same) realizer.member
  have moved := equality.proof.mono
    (HOL.ProofSyntax.OccurrenceMap.appendRight (assumptions roots Γ) context.telescope.hypotheses)
  exact ⟨(sourceEquality.typed levels context.formed).2, equality.right, realizer.predicate,
    equality.rightRead, realizer.typeRead, .impE (.eqPropEL (.eqAppArg realizer.predicate moved)) oldGuard⟩

def Free (realizer : GuardedRealizer roots context source type carrier) : Prop := realizer.member.FunctionExtensionalityFree

theorem ofVariable_free (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    (index : HOL.Var Γ carrier) : (ofVariable roots context index).Free := context.variableProof_free roots index

theorem substitute_free {target : GuardedContext P lex Ξ} {raw : CSub Head Γ.length Ξ.length}
    {code : HOL.Subst Const Γ Ξ} (realizer : GuardedRealizer roots context source type carrier)
    (substitution : GuardedSubstitution roots context target raw code)
    (realizerFree : realizer.Free) (substitutionFree : substitution.Free) :
    (realizer.substitute substitution).Free := substitution.transport_free realizer.member substitutionFree realizerFree

theorem application_free [DecidableEq Base] {A : CTm Head Γ.length} {B : CTm Head (Γ.length + 1)}
    {function argument : CTm Head Γ.length} {domain codomain : HOL.Ty Base}
    (functionValue : GuardedRealizer roots context function (.pi A B) (domain ⇒ codomain))
    (argumentValue : GuardedRealizer roots context argument A domain)
    (functionFree : functionValue.Free) (argumentFree : argumentValue.Free) :
    (application functionValue argumentValue).Free := by
  unfold Free application
  apply HOL.PredicateProducts.eliminate_free
  · simpa only [Free, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using functionFree
  · exact argumentFree

theorem abstraction_free {L : Type} [UniverseLevel.LevelOrder L] (levels : TypedEquality.Normalization.LevelModel R L)
    {domain codomain : HOL.Ty Base} {A : CTm Head Γ.length} {body B : CTm Head (Γ.length + 1)}
    (predicate : HOL.Term Const Γ (domain ⇒ .prop)) (domainRead : Reads lex A predicate)
    (domainFormed : CIsType P context.source A) (familyFormed : CIsType P (.snoc context.source A) B)
    (bodyValue : GuardedRealizer roots (context.snoc predicate domainRead domainFormed) body B codomain)
    (free : bodyValue.Free) :
    (abstraction levels predicate domainRead domainFormed familyFormed bodyValue).Free :=
  context.lambdaMember_free roots predicate domainRead domainFormed bodyValue.predicate bodyValue.term bodyValue.member free

theorem convert_free [DecidableEq Base] {otherType : CTm Head Γ.length}
    (realizer : GuardedRealizer roots context source type carrier)
    (sourceEquality : CTypeEq P context.source type otherType)
    (equality : EqualityAt lex roots Γ type otherType (carrier ⇒ .prop))
    (realizerFree : realizer.Free) (equalityFree : equality.proof.FunctionExtensionalityFree) :
    (realizer.convert sourceEquality equality).Free := by
  simp only [Free, convert, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.functionExtensionalityFree_mono, HOL.ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨equalityFree, realizerFree⟩

theorem rewrite_free [DecidableEq Base] {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L) {target : CTm Head Γ.length}
    (realizer : GuardedRealizer roots context source type carrier)
    (sourceEquality : CEqual P context.source source target type)
    (equality : EqualityAt lex roots Γ source target carrier)
    (realizerFree : realizer.Free) (equalityFree : equality.proof.FunctionExtensionalityFree) :
    (realizer.rewrite levels sourceEquality equality).Free := by
  simp only [Free, rewrite, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.functionExtensionalityFree_mono, HOL.ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨equalityFree, realizerFree⟩

theorem satisfies (realizer : GuardedRealizer roots context source type carrier)
    (model : HOL.HenkinModel.{u,v,w} Base Const) (respects : model.FunctionsRespectEqv)
    (values : model.Valuation Γ) (admitted : model.ValuationAdmissible values)
    (holds : HOL.Soundness.SatisfiesHyps model values (context.hypotheses roots)) :
    (model.denote realizer.predicate values (model.denote realizer.term values)).down :=
  HOL.Soundness.extDerivation_sound realizer.member.erase respects admitted holds

end GuardedRealizer
#print axioms GuardedContext.weakenProof
#print axioms GuardedContext.rootSubstitution
#print axioms GuardedSubstitution.transport
#print axioms GuardedSubstitution.comp
#print axioms GuardedRealizer.substitute
#print axioms GuardedRealizer.application
#print axioms GuardedRealizer.convert
#print axioms GuardedSubstitution.ofRenaming
#print axioms GuardedSubstitution.lift
#print axioms GuardedRealizer.abstraction
#print axioms GuardedSubstitution.transport_free
#print axioms GuardedSubstitution.lift_free
#print axioms GuardedSubstitution.cons_free
#print axioms GuardedSubstitution.satisfies
#print axioms GuardedRealizer.application_free
#print axioms GuardedRealizer.abstraction_free
#print axioms GuardedRealizer.satisfies
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
