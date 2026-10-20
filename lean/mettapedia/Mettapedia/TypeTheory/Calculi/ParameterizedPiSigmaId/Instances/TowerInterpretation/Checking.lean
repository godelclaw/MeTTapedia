import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCheckingOSLF
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotientSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTypedQuotient

/-!
# Checked cumulative evidence and the existing set-tower interpretation

Accepted finite requests first recover their actual formation-sensitive
judgment. The existing admitted cumulative tower maps it to typed equality
and then to annotated set semantics. Contexts, annotations, declaration rules
and the named inaccessible-cardinal hypothesis are preserved explicitly.
Finite conversion codes preserve actual model values. Independently checked
substitution components supply the contextual arrow used by the existing
semantic substitution theorem.

The model is a semantic interpretation. It is not a native Mathdata checker,
a completeness theorem for all set truth, or authority to add reductions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace Checking

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization
open Presentation.FormationSensitiveRuleSignature
open Presentation.FormationSensitiveContextual
open UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation (interpretHead)
open _root_.CategoryTheory

universe u

abbrev setting : Setting Tower.Head Nat :=
  { TowerModel.setting (fun _ => 0) with R := Tower.rules }

theorem qualification : FormationSensitiveTypedQuotient.Qualification setting :=
  ⟨TowerModel.facts, TowerModel.roots, TowerModel.heads, Normalization.LevelTower.churchRosser⟩

/-- Every checked telescope retains formation when passed to typed equality. -/
theorem contextFormed {n : Nat} {Γ : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation Tower.rules Γ) : CtxFormed Tower.rules Γ :=
  FormationSensitiveTypedQuotient.contextFormed qualification formed

theorem requestTyped {claim : Judgment Tower.Head} (request : Tower.Checking.Request claim)
    (accepted : Tower.Checking.check request = true) :
    Typed Tower.rules claim.context claim.subject claim.type :=
  Tower.formationSensitive_toTyped (request.sound Tower.Checking.decoder accepted).typing
    (contextFormed (request.sound Tower.Checking.decoder accepted).context)

/-- An accepted request reaches the independently proved set interpretation.
The annotated telescope, subject and displayed type erase to the requested
ones. The large-cardinal hypothesis is used only in the semantic edge. -/
theorem request_model_sound (h : CofinalInaccessibles.{u})
    {claim : Judgment Tower.Head} (request : Tower.Checking.Request claim)
    (accepted : Tower.Checking.check request = true) :
    ∃ statement : CStatement Tower.Head,
      statement.CtxFormed (TowerControls.P₀ (L := Nat)) ∧
      CDerivable (TowerControls.P₀ (L := Nat)) statement ∧
      statement.erase = .typing claim.context claim.subject claim.type ∧
      Holds (interpretHead h ∅ ∅ (fun _ => (0 : Nat))) (fun _ => ∅) statement := by
  obtain ⟨statement, formed, derived, erases⟩ := tower_elaborates
    (requestTyped request accepted)
    (contextFormed (request.sound Tower.Checking.decoder accepted).context)
  exact ⟨statement, formed, derived, erases, CDerivable.sound_tower h derived⟩

/-- The model forbids every finite request for a closed inhabitant of the
existing empty type, including arbitrary proposed graph contents. -/
theorem empty_request_refuses (h : CofinalInaccessibles.{u}) (term : Tower.Tm 0)
    (request : Tower.Checking.Request (judgment .nil term emptyType.erase)) :
    Tower.Checking.check request = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact candidate_consistent h term (requestTyped request accepted)

/-- On closed universe membership the comparison is exact in both directions.
The reverse direction constructs the source head and cumulative derivations,
then uses finite-certificate coverage. It is not reflection of all set truth. -/
theorem universe_request_iff_set (h : CofinalInaccessibles.{u}) (lower upper : Nat) :
    (∃ request : Tower.Checking.Request
      (judgment .nil (.head (.sort (.const lower))) (.head (.sort (.const upper)))),
      Tower.Checking.check request = true) ↔
    ZFSetInterpretation.universeSet h ∅ lower ∈ ZFSetInterpretation.universeSet h ∅ upper := by
  constructor
  · rintro ⟨request, accepted⟩
    exact (universeAt_mem_iff_universeSet h ∅ CtxFormed.nil).mp (requestTyped request accepted)
  · intro membership
    have order := (ZFSetInterpretation.universeSet_mem_iff h ∅).mp membership
    apply (Tower.Checking.coverage _).mp
    refine ⟨.nil, .cumul (.headType (.sort (.const lower))) ?_⟩
    intro valuation
    change lower + 1 ≤ upper
    exact Nat.succ_le_of_lt order

/-- The same finite requests characterize membership of these universes
inside the existing well-founded embedding into material hypersets. -/
theorem universe_request_iff_hyperset (h : CofinalInaccessibles.{u}) (lower upper : Nat) :
    (∃ request : Tower.Checking.Request
      (judgment .nil (.head (.sort (.const lower))) (.head (.sort (.const upper)))),
      Tower.Checking.check request = true) ↔
    MaterialSets.Hypersets.HSet.ofZFSet (ZFSetInterpretation.universeSet h ∅ lower) ∈
      MaterialSets.Hypersets.HSet.ofZFSet (ZFSetInterpretation.universeSet h ∅ upper) :=
  (universe_request_iff_set h lower upper).trans
    MaterialSets.Hypersets.HSet.ofZFSet_mem_ofZFSet_iff.symm

/-- Contextual types are earned from an actual checked formation request. -/
def admittedType (source : Context Tower.rules) (type : Tower.Tm source.arity)
    (level : LevelExpr Nat)
    (request : Tower.Checking.Request (judgment source.raw type (.head (.sort level))))
    (accepted : Tower.Checking.check request = true) : TypeOver source where
  code := type
  level := .sort level
  universeWitness := .sort level
  formed := (request.sound Tower.Checking.decoder accepted).typing

/-- The term is the original checked subject, with its original displayed type. -/
def admittedTerm (source : Context Tower.rules) (type : TypeOver source)
    (term : Tower.Tm source.arity)
    (request : Tower.Checking.Request (judgment source.raw term type.code))
    (accepted : Tower.Checking.check request = true) : Term source type where
  code := term
  typed := (request.sound Tower.Checking.decoder accepted).typing

/-- Component certificates authorize the original simultaneous substitution;
no unverified raw contextual map is promoted to a typed arrow. -/
def checkedArrow (source target : Context Tower.rules)
    (substitution : Sub Tower.Head target.arity source.arity)
    (requests : (i : Fin target.arity) → Tower.Checking.Request
      (judgment source.raw (substitution i) (subst substitution (Ctx.lookup target.raw i))))
    (accepted : ∀ i, Tower.Checking.check (requests i) = true) : source ⟶ target where
  substitution := substitution
  typed i := ((requests i).sound Tower.Checking.decoder (accepted i)).typing

section Values

variable (h : CofinalInaccessibles.{u})

noncomputable def heads : Tower.Head → ZFSet.{u} := interpretHead h ∅ ∅ (fun _ => (0 : Nat))
abbrev constants : DeclName → ZFSet.{u} := fun _ => ∅

noncomputable def typeValue {source : Context Tower.rules} {context : CCtx Tower.Head source.arity}
    (formed : CCtxFormed (TowerControls.P₀ (L := Nat)) context) (erases : context.erase = source.raw)
    (type : TypeOver source) :
    ConversionQuotient.Value (heads := heads h) (constants := constants) context :=
  ConversionQuotient.typeValue (S := setting) towerLiftingFacts qualification.forms
    qualification.roots qualification.heads qualification.church formed erases type

noncomputable def termValue {source : Context Tower.rules} {context : CCtx Tower.Head source.arity}
    (formed : CCtxFormed (TowerControls.P₀ (L := Nat)) context) (erases : context.erase = source.raw)
    {type : TypeOver source} (term : Term source type) :
    ConversionQuotient.Value (heads := heads h) (constants := constants) context :=
  ConversionQuotient.termValue (S := setting) towerLiftingFacts qualification.forms
    qualification.roots qualification.heads qualification.church formed erases term

/-- The checked subject denotes a member of its checked displayed type. -/
theorem checked_value_member {source : Context Tower.rules}
    {context : CCtx Tower.Head source.arity}
    (formed : CCtxFormed (TowerControls.P₀ (L := Nat)) context) (erases : context.erase = source.raw)
    (type : TypeOver source) (term : Tower.Tm source.arity)
    (request : Tower.Checking.Request (judgment source.raw term type.code))
    (accepted : Tower.Checking.check request = true)
    (environment : ConversionQuotient.Environment (heads := heads h) (constants := constants) context) :
    termValue h formed erases (admittedTerm source type term request accepted) environment ∈
      typeValue h formed erases type environment :=
  ConversionQuotient.termValue_member (S := setting) towerLiftingFacts (standardTowerModel h)
    qualification.forms qualification.roots qualification.heads qualification.church formed erases _ environment

/-- A successful finite conversion check preserves actual type values. This
uses the two independently formed endpoints, not arbitrary set equality. -/
theorem checked_type_conversion {source : Context Tower.rules}
    {context : CCtx Tower.Head source.arity}
    (formed : CCtxFormed (TowerControls.P₀ (L := Nat)) context) (erases : context.erase = source.raw)
    (first second : TypeOver source)
    (code : StructuralConversionCode.Code Tower.Head Tower.Checking.decoder.Code source.arity)
    (accepted : code.check Tower.rules.headEq Tower.Checking.decoder.decode first.code second.code = true) :
    typeValue h formed erases first = typeValue h formed erases second :=
  ConversionQuotient.typeValue_conversion (S := setting) towerLiftingFacts (standardTowerModel h)
    qualification.forms qualification.roots qualification.heads qualification.church formed erases
    first second (StructuralConversionCode.Code.check_sound Tower.Checking.decoder accepted)

/-- Independently checked subjects at one displayed type preserve actual
values when their supplied conversion evidence checks. -/
theorem checked_term_conversion {source : Context Tower.rules}
    {context : CCtx Tower.Head source.arity}
    (formed : CCtxFormed (TowerControls.P₀ (L := Nat)) context) (erases : context.erase = source.raw)
    (type : TypeOver source) (left right : Tower.Tm source.arity)
    (leftRequest : Tower.Checking.Request (judgment source.raw left type.code))
    (rightRequest : Tower.Checking.Request (judgment source.raw right type.code))
    (leftAccepted : Tower.Checking.check leftRequest = true)
    (rightAccepted : Tower.Checking.check rightRequest = true)
    (code : StructuralConversionCode.Code Tower.Head Tower.Checking.decoder.Code source.arity)
    (accepted : code.check Tower.rules.headEq Tower.Checking.decoder.decode left right = true) :
    termValue h formed erases (admittedTerm source type left leftRequest leftAccepted) =
      termValue h formed erases (admittedTerm source type right rightRequest rightAccepted) :=
  ConversionQuotient.termValue_conversion (S := setting) towerLiftingFacts (standardTowerModel h)
    qualification.forms qualification.roots qualification.heads qualification.church formed erases
    _ _ (.refl _) (StructuralConversionCode.Code.check_sound Tower.Checking.decoder accepted)

/-- The operational-logical conversion observation reaches the same actual
set values once both displayed typing requests and the telescope are checked.
The model hypothesis and typed endpoints remain explicit. -/
theorem oslf_term_conversion {source : Context Tower.rules}
    {context : CCtx Tower.Head source.arity}
    (formed : CCtxFormed (TowerControls.P₀ (L := Nat)) context) (erases : context.erase = source.raw)
    (type : TypeOver source) (left right : Tower.Tm source.arity)
    (leftRequest : Tower.Checking.Request (judgment source.raw left type.code))
    (rightRequest : Tower.Checking.Request (judgment source.raw right type.code))
    (leftAccepted : Tower.Checking.check leftRequest = true)
    (rightAccepted : Tower.Checking.check rightRequest = true)
    (observation : (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (FormationSensitiveCheckingOSLF.theory Tower.rules source.arity)).satisfies (S := ()) left
      (FormationSensitiveCheckingOSLF.conversionNativeType Tower.rules right).pred) :
    termValue h formed erases (admittedTerm source type left leftRequest leftAccepted) =
      termValue h formed erases (admittedTerm source type right rightRequest rightAccepted) := by
  obtain ⟨code, accepted⟩ :=
    (FormationSensitiveCheckingOSLF.satisfies_iff_checked Tower.Checking.decoder left right).mp observation
  exact checked_term_conversion h formed erases type left right leftRequest rightRequest
    leftAccepted rightAccepted code accepted

/-- The actual value of a checked term commutes with the actual substitution
whose components were checked. Annotated components retain their own typing
and erasure obligations at this comparison boundary. -/
theorem checked_value_substitution {first last : Context Tower.rules}
    {sourceContext : CCtx Tower.Head first.arity} {targetContext : CCtx Tower.Head last.arity}
    (sourceFormed : CCtxFormed (TowerControls.P₀ (L := Nat)) sourceContext)
    (sourceErases : sourceContext.erase = first.raw)
    (targetFormed : CCtxFormed (TowerControls.P₀ (L := Nat)) targetContext)
    (targetErases : targetContext.erase = last.raw)
    (substitution : Sub Tower.Head last.arity first.arity)
    (requests : (i : Fin last.arity) → Tower.Checking.Request
      (judgment first.raw (substitution i) (subst substitution (Ctx.lookup last.raw i))))
    (accepted : ∀ i, Tower.Checking.check (requests i) = true)
    {annotated : CSub Tower.Head last.arity first.arity}
    (typed : CSubstMor (TowerControls.P₀ (L := Nat)) targetContext sourceContext annotated)
    (componentsErase : ∀ i, (annotated i).erase = substitution i)
    (type : TypeOver last) (term : Tower.Tm last.arity)
    (request : Tower.Checking.Request (judgment last.raw term type.code))
    (termAccepted : Tower.Checking.check request = true)
    (environment : ConversionQuotient.Environment
      (heads := heads h) (constants := constants) sourceContext) :
    termValue h sourceFormed sourceErases
        ((admittedTerm last type term request termAccepted).reindex
          (checkedArrow first last substitution requests accepted)) environment =
      termValue h targetFormed targetErases (admittedTerm last type term request termAccepted)
        (ConversionQuotient.substitutionEnvironment
          (S := setting)
          (heads := heads h) (constants := constants) (P := TowerControls.P₀ (L := Nat))
          (standardTowerModel (L := Nat) h) typed environment) :=
  ConversionQuotient.termValue_reindex (S := setting) (standardTowerModel h) towerLiftingFacts
    qualification.forms qualification.roots qualification.heads qualification.church
    sourceFormed sourceErases targetFormed targetErases
    (checkedArrow first last substitution requests accepted) typed componentsErase _ environment

end Values
end Checking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
