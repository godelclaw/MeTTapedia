import Mettapedia.GSLT.Dedukti.LeanMinusExplicitExamples

/-!
# Type preservation under steps inside terms

`HasType.beta_root` (`TypingSubstitution`) preserves types under a beta step at
the root.  This module carries type preservation to steps at any position.
Two lemmas are proved for that, for every profile and every theory with closed
definitions and closed declared types, without confluence:

* **Correctness of types** (`HasType.correct`): in a well-formed context, and
  for a theory whose declared types are types, the type of a term is a top
  sort or has a sort.
* **Conversion of a context entry** (`HasType.convertContext`): an entry of the
  context may be replaced by a convertible entry, the old entry being a type.

With them, `typePreservation`: in an orthogonal theory whose declared types are
types (`Theory.FormedSignature`), whose definitions have their declared types
(`Theory.TypedBodies`) and whose rules keep the type of their left sides
(`Theory.RulesPreserveTypes`), every step preserves the type of a term in a
well-formed context.  Confluence is used for the beta step at the root only.

For the theory with explicit level substitution (`leanTheoryExplicit`), the
statement `typePreservation_explicit` has exactly these three hypotheses left,
and the third one fails as transcribed (`punitRec_breaks_preservation`): the
rule `PUnit.rec fr Q h x ↪ h`, rule (β-rec-S) of the paper for a structure with
no field, gives `h : ε β (Q PUnit.unit)` the type `ε β (Q x)`, which needs
`x ≡ PUnit.unit`, the unit eta that Lean⁻ removes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx ctxLookup)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.Logic.Relation (Confluent IsNormal)

variable {profile : Profile} {theory : Theory}

/-- **A well-formed context**: every entry is a type of the entries behind it. -/
inductive WellFormedCtx (profile : Profile) (theory : Theory) : Ctx → Prop where
  | nil : WellFormedCtx profile theory []
  | cons {context : Ctx} {entry : Term} {sort : Srt} :
      WellFormedCtx profile theory context → HasType profile theory context entry (.srt sort) →
        WellFormedCtx profile theory (entry :: context)

/-- Every declared type is a type, in the empty context. -/
def Theory.FormedSignature (profile : Profile) (theory : Theory) : Prop :=
  ∀ name type, theory.constType name = some type → ∃ sort, HasType profile theory [] type (.srt sort)

/-- Every transparent definition has its declared type. -/
def Theory.TypedBodies (profile : Profile) (theory : Theory) : Prop :=
  ∀ name body type, theory.body name = some body → theory.constType name = some type →
    HasType profile theory [] body type

/-- Every instance of a declared rule keeps the type of its left side, in a
well-formed context. -/
def Theory.RulesPreserveTypes (profile : Profile) (theory : Theory) : Prop :=
  ∀ (rule : RewriteRule) (assignment : Nat → Term) (context : Ctx) (type : Term), theory.rule rule →
    WellFormedCtx profile theory context → HasType profile theory context (inst assignment rule.lhs) type →
      HasType profile theory context (inst assignment rule.rhs) type

/-! ## The entries of a well-formed context are types -/

theorem ctxLookup_cons_succ (entry : Term) (context : Ctx) (index : Nat) :
    ctxLookup (entry :: context) (index + 1) = (ctxLookup context index).map (lift 1 0) := by
  rw [ctxLookup_eq_getElem?, ctxLookup_eq_getElem?]
  cases found : context[index]? with
  | none => simp [found]
  | some value =>
      simp only [List.getElem?_cons_succ, found, Option.map_some]
      rw [lift_lift_same]
      congr 2
      omega

/-- **Every entry of a well-formed context is a type.** -/
theorem WellFormedCtx.lookup_formed (closedBodies : theory.ClosedBodies)
    (closedTypes : theory.ClosedTypes) :
    ∀ {context : Ctx}, WellFormedCtx profile theory context →
      ∀ (index : Nat) (type : Term), ctxLookup context index = some type →
        ∃ sort, HasType profile theory context type (.srt sort) := by
  intro context wellFormed
  induction wellFormed with
  | nil => intro index type found; simp [ctxLookup, LFTyping.ctxLookupAux] at found
  | @cons context entry sort _ entryTyped ih =>
      intro index type found
      cases index with
      | zero =>
          have same : type = lift 1 0 entry := by
            simpa [ctxLookup, LFTyping.ctxLookupAux] using found.symm
          subst same
          exact ⟨sort, by simpa [lift] using entryTyped.weaken closedBodies closedTypes entry⟩
      | succ index =>
          rw [ctxLookup_cons_succ] at found
          obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
          obtain ⟨originalSort, originalTyped⟩ := ih index original originalFound
          exact ⟨originalSort, by simpa [lift] using originalTyped.weaken closedBodies closedTypes entry⟩

/-! ## Correctness of types -/

/-- The type of an application is a type. -/
theorem HasType.app_type_formed (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    {context : Ctx} {argument domain body : Term}
    (functionTypeFormed : ∃ sort, HasType profile theory context (.pi domain body) (.srt sort))
    (argumentTyped : HasType profile theory context argument domain) :
    ∃ sort, HasType profile theory context (LFTyping.subst0 argument body) (.srt sort) := by
  obtain ⟨_, productTyped⟩ := functionTypeFormed
  obtain ⟨_, codomainSort, _, _, bodyTyped, _, _⟩ := productTyped.pi_inv
  exact ⟨codomainSort, HasType.subst0 closedBodies closedTypes bodyTyped argumentTyped⟩

/-- **Correctness of types**: in a well-formed context, the type of a term is
a sort without a type, or a term with a sort. -/
theorem HasType.correct (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    (signature : theory.FormedSignature profile) {context : Ctx} {term type : Term}
    (wellFormed : WellFormedCtx profile theory context)
    (typed : HasType profile theory context term type) :
    (∃ sort, type = .srt sort ∧ profile.sortAxiom sort = none) ∨
      ∃ sort, HasType profile theory context type (.srt sort) := by
  induction typed with
  | @sort context source target _ =>
      cases above : profile.sortAxiom target with
      | none => exact Or.inl ⟨target, rfl, above⟩
      | some top => exact Or.inr ⟨top, .sort above⟩
  | @var context index type found =>
      exact Or.inr (wellFormed.lookup_formed closedBodies closedTypes index type found)
  | @con context name type declared =>
      obtain ⟨sort, formed⟩ := signature name type declared
      have weakened := formed.weaken_many closedBodies closedTypes context
      rw [List.append_nil, (closedTypes name type declared).lift] at weakened
      exact Or.inr ⟨sort, by simpa [lift] using weakened⟩
  | @pi context domain body domainSort codomainSort resultSort _ _ _ _ _ =>
      cases above : profile.sortAxiom resultSort with
      | none => exact Or.inl ⟨resultSort, rfl, above⟩
      | some top => exact Or.inr ⟨top, .sort above⟩
  | lam domainTyped bodyTypeTyped rule _ _ _ _ =>
      exact Or.inr ⟨_, .pi domainTyped bodyTypeTyped rule⟩
  | app _ argumentTyped ihFunction _ =>
      rcases ihFunction wellFormed with ⟨sort, same, _⟩ | formed
      · cases same
      · exact Or.inr (HasType.app_type_formed closedBodies closedTypes formed argumentTyped)
  | conv _ _ targetTyped _ _ => exact Or.inr ⟨_, targetTyped⟩

/-- The type of an application is always a type, never a top sort. -/
theorem HasType.app_correct (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    (signature : theory.FormedSignature profile) {context : Ctx}
    (wellFormed : WellFormedCtx profile theory context) :
    ∀ {function argument type : Term},
      HasType profile theory context (.app function argument) type →
        ∃ sort, HasType profile theory context type (.srt sort) := by
  intro function argument type typed
  generalize same : Term.app function argument = term at typed
  induction typed with
  | sort _ => cases same
  | var _ => cases same
  | con _ => cases same
  | pi _ _ _ _ _ => cases same
  | lam _ _ _ _ _ _ _ => cases same
  | app functionTyped argumentTyped _ _ =>
      rcases functionTyped.correct closedBodies closedTypes signature wellFormed with
        ⟨sort, shape, _⟩ | formed
      · cases shape
      · exact HasType.app_type_formed closedBodies closedTypes formed argumentTyped
  | conv _ _ targetTyped _ _ => exact ⟨_, targetTyped⟩

/-- A constant has its declared type, or a type with a sort. -/
theorem HasType.con_cases {context : Ctx} {name : String} :
    ∀ {type : Term}, HasType profile theory context (.con name) type →
      theory.constType name = some type ∨ ∃ sort, HasType profile theory context type (.srt sort) := by
  intro type typed
  generalize same : Term.con name = term at typed
  induction typed with
  | sort _ => cases same
  | var _ => cases same
  | con declared => cases same; exact Or.inl declared
  | pi _ _ _ _ _ => cases same
  | lam _ _ _ _ _ _ _ => cases same
  | app _ _ _ _ => cases same
  | conv _ _ targetTyped _ _ => exact Or.inr ⟨_, targetTyped⟩

/-! ## Conversion of a context entry -/

/-- Replacing an entry of the context does not change the lookup of the other
entries. -/
theorem ctxLookup_replace (front back : Ctx) (entry entry' : Term) {index : Nat}
    (other : index ≠ front.length) :
    ctxLookup (front ++ entry' :: back) index = ctxLookup (front ++ entry :: back) index := by
  rw [ctxLookup_eq_getElem?, ctxLookup_eq_getElem?]
  by_cases below : index < front.length
  · rw [List.getElem?_append_left below, List.getElem?_append_left below]
  · have above : front.length ≤ index := by omega
    rw [List.getElem?_append_right above, List.getElem?_append_right above]
    have position : index - front.length = (index - front.length - 1) + 1 := by omega
    rw [position, List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- **Conversion of a context entry**: an entry may be replaced by a
convertible one, when the replaced entry is a type of the entries behind it. -/
theorem HasType.convertContext (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    {context : Ctx} {term type : Term} (typed : HasType profile theory context term type) :
    ∀ (front back : Ctx) (entry entry' : Term) (sort : Srt), context = front ++ entry :: back →
      Conv theory entry entry' → HasType profile theory back entry (.srt sort) →
        HasType profile theory (front ++ entry' :: back) term type := by
  induction typed with
  | sort axiomHolds => intro _ _ _ _ _ _ _ _; exact .sort axiomHolds
  | @var context index type found =>
      intro front back entry entry' sort same convertible entryTyped
      subst same
      by_cases position : index = front.length
      · subst position
        have declared : ctxLookup (front ++ entry :: back) front.length =
            some (lift (front.length + 1) 0 entry) := ctxLookup_subst_same front back entry
        have isEntry : type = lift (front.length + 1) 0 entry :=
          Option.some.inj (found.symm.trans declared)
        subst isEntry
        have replaced : HasType profile theory (front ++ entry' :: back) (.var front.length)
            (lift (front.length + 1) 0 entry') := .var (ctxLookup_subst_same front back entry')
        have weakened := entryTyped.weaken_many closedBodies closedTypes (front ++ [entry'])
        rw [List.append_assoc, List.singleton_append] at weakened
        simp only [List.length_append, List.length_singleton] at weakened
        exact .conv replaced (Conv.lift closedBodies (.symm _ _ convertible) _ _)
          (by simpa [lift] using weakened)
      · exact .var ((ctxLookup_replace front back entry entry' position).trans found)
  | con declared => intro _ _ _ _ _ _ _ _; exact .con declared
  | pi _ _ rule ihDomain ihBody =>
      intro front back entry entry' sort same convertible entryTyped
      exact .pi (ihDomain front back entry entry' sort same convertible entryTyped)
        (ihBody (_ :: front) back entry entry' sort (by rw [same]; rfl) convertible entryTyped) rule
  | lam _ _ rule _ ihDomain ihBodyType ihBody =>
      intro front back entry entry' sort same convertible entryTyped
      exact .lam (ihDomain front back entry entry' sort same convertible entryTyped)
        (ihBodyType (_ :: front) back entry entry' sort (by rw [same]; rfl) convertible entryTyped) rule
        (ihBody (_ :: front) back entry entry' sort (by rw [same]; rfl) convertible entryTyped)
  | app _ _ ihFunction ihArgument =>
      intro front back entry entry' sort same convertible entryTyped
      exact .app (ihFunction front back entry entry' sort same convertible entryTyped)
        (ihArgument front back entry entry' sort same convertible entryTyped)
  | conv _ convertibleType _ ihTerm ihTarget =>
      intro front back entry entry' sort same convertible entryTyped
      exact .conv (ihTerm front back entry entry' sort same convertible entryTyped) convertibleType
        (ihTarget front back entry entry' sort same convertible entryTyped)

/-- Conversion of the first entry of the context. -/
theorem HasType.convertHead (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    {context : Ctx} {entry entry' term type : Term} {sort : Srt}
    (typed : HasType profile theory (entry :: context) term type) (convertible : Conv theory entry entry')
    (entryTyped : HasType profile theory context entry (.srt sort)) :
    HasType profile theory (entry' :: context) term type :=
  typed.convertContext closedBodies closedTypes [] context entry entry' sort rfl convertible entryTyped

/-! ## Type preservation -/

/-- A step of the value substituted gives a conversion of the result. -/
theorem Conv.subst0_of_step (closedBodies : theory.ClosedBodies) {argument argument' : Term}
    (step : Step theory argument argument') (body : Term) :
    Conv theory (LFTyping.subst0 argument body) (LFTyping.subst0 argument' body) :=
  ((Par.substTerm closedBodies (Par.refl body) step.par 0).reduces closedBodies).conv

/-- **Type preservation at the root, beta and definitions.** -/
theorem rootStep_preserves (confluent : Confluent (Step theory)) (headed : theory.Headed)
    (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    (signature : theory.FormedSignature profile) (bodies : theory.TypedBodies profile)
    (rules : theory.RulesPreserveTypes profile) {context : Ctx} {source target type : Term}
    (wellFormed : WellFormedCtx profile theory context)
    (typed : HasType profile theory context source type) (step : RootStep theory source target) :
    HasType profile theory context target type := by
  cases step with
  | beta domain body argument =>
      obtain ⟨sort, formed⟩ := HasType.app_correct closedBodies closedTypes signature wellFormed typed
      exact HasType.beta_root confluent headed closedBodies closedTypes typed formed
  | delta defined =>
      obtain ⟨declared, declaredFound, declaredConv⟩ := typed.con_inv
      have bodyTyped := bodies _ _ declared defined declaredFound
      have weakened := bodyTyped.weaken_many closedBodies closedTypes context
      rw [List.append_nil, (closedBodies _ _ defined).lift,
        (closedTypes _ declared declaredFound).lift] at weakened
      rcases typed.con_cases with sameType | ⟨sort, formed⟩
      · rw [declaredFound] at sameType
        obtain rfl := Option.some.inj sameType
        exact weakened
      · exact .conv weakened declaredConv formed
  | rule assignment member => exact rules _ assignment context type member wellFormed typed

/-- **Type preservation**: in an orthogonal setting, every step of a term
typed in a well-formed context keeps its type, when declared types are types,
definitions have their types and rules keep the type of their left sides. -/
theorem typePreservation (confluent : Confluent (Step theory)) (headed : theory.Headed)
    (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    (signature : theory.FormedSignature profile) (bodies : theory.TypedBodies profile)
    (rules : theory.RulesPreserveTypes profile) {context : Ctx} {source type : Term}
    (wellFormed : WellFormedCtx profile theory context)
    (typed : HasType profile theory context source type) :
    ∀ {target : Term}, Step theory source target → HasType profile theory context target type := by
  induction typed with
  | sort axiomHolds =>
      intro target step
      exact (RootStep.not_srt headed step.srt_inv).elim
  | var found =>
      intro target step
      exact (RootStep.not_var headed step.var_inv).elim
  | con declared =>
      intro target step
      exact rootStep_preserves confluent headed closedBodies closedTypes signature bodies rules wellFormed
        (.con declared) step.con_inv
  | @pi context domain body domainSort codomainSort resultSort domainTyped bodyTyped rule ihDomain ihBody =>
      intro target step
      rcases step.pi_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact (RootStep.not_pi headed root).elim
      · have domain'Typed := ihDomain wellFormed inner
        exact .pi domain'Typed
          (bodyTyped.convertHead closedBodies closedTypes (.rel _ _ inner) domainTyped) rule
      · exact .pi domainTyped (ihBody (.cons wellFormed domainTyped) inner) rule
  | @lam context domain body bodyType domainSort codomainSort resultSort domainTyped bodyTypeTyped rule
      bodyTyped ihDomain _ ihBody =>
      intro target step
      rcases step.lam_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact (RootStep.not_lam headed root).elim
      · have domain'Typed := ihDomain wellFormed inner
        have moved := HasType.lam domain'Typed
          (bodyTypeTyped.convertHead closedBodies closedTypes (.rel _ _ inner) domainTyped) rule
          (bodyTyped.convertHead closedBodies closedTypes (.rel _ _ inner) domainTyped)
        exact .conv moved (Conv.pi (.symm _ _ (.rel _ _ inner)) (.refl _))
          (.pi domainTyped bodyTypeTyped rule)
      · exact .lam domainTyped bodyTypeTyped rule (ihBody (.cons wellFormed domainTyped) inner)
  | @app context function argument domain bodyType functionTyped argumentTyped ihFunction ihArgument =>
      intro target step
      rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
      · exact rootStep_preserves confluent headed closedBodies closedTypes signature bodies rules
          wellFormed (.app functionTyped argumentTyped) root
      · exact .app (ihFunction wellFormed inner) argumentTyped
      · have moved := HasType.app functionTyped (ihArgument wellFormed inner)
        obtain ⟨sort, formed⟩ :=
          HasType.app_correct closedBodies closedTypes signature wellFormed (.app functionTyped argumentTyped)
        exact .conv moved (.symm _ _ (Conv.subst0_of_step closedBodies inner bodyType)) formed
  | conv _ convertible targetTyped ihTerm _ =>
      intro target step
      exact .conv (ihTerm wellFormed step) convertible targetTyped

/-- Under type preservation, reduction keeps the type. -/
theorem typePreservation_reduces (confluent : Confluent (Step theory)) (headed : theory.Headed)
    (closedBodies : theory.ClosedBodies) (closedTypes : theory.ClosedTypes)
    (signature : theory.FormedSignature profile) (bodies : theory.TypedBodies profile)
    (rules : theory.RulesPreserveTypes profile) {context : Ctx} {source target type : Term}
    (wellFormed : WellFormedCtx profile theory context)
    (typed : HasType profile theory context source type) (reduces : Reduces theory source target) :
    HasType profile theory context target type := by
  induction reduces with
  | refl => exact typed
  | tail _ step ih =>
      exact typePreservation confluent headed closedBodies closedTypes signature bodies rules wellFormed ih step

end Mettapedia.GSLT.Dedukti

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx subst0)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)

/-- **Type preservation for the theory with explicit level substitution**:
what is left are its three obligations, that its declared types are types,
that its definitions have their declared types, and that its rules keep the
type of their left sides. -/
theorem typePreservation_explicit
    (signature : leanTheoryExplicit.FormedSignature LFProfile.basic)
    (bodies : leanTheoryExplicit.TypedBodies LFProfile.basic)
    (rules : leanTheoryExplicit.RulesPreserveTypes LFProfile.basic) {context : Ctx}
    {source target type : Term} (wellFormed : WellFormedCtx LFProfile.basic leanTheoryExplicit context)
    (typed : LambdaPiModulo leanTheoryExplicit context source type)
    (step : Step leanTheoryExplicit source target) :
    LambdaPiModulo leanTheoryExplicit context target type :=
  typePreservation leanTheoryExplicit_confluent leanTheoryExplicit_headed leanTheoryExplicit_closedBodies
    leanTheoryExplicit_closedTypes signature bodies rules wellFormed typed step

/-! ## The rule on `PUnit.rec` does not preserve types -/

theorem levelZero_typed_explicit (context : Ctx) :
    LambdaPiModulo leanTheoryExplicit context levelZero L := by
  have nilTyped : LambdaPiModulo leanTheoryExplicit context (ap "nil" [.con "S_code"])
      (tauSet (.con "S_code")) := app_at (.con rfl) (.con rfl) rfl
  have asE : LambdaPiModulo leanTheoryExplicit context (ap "nil" [.con "S_code"]) E :=
    .conv nilTyped (.symm _ _ (conv_delta rfl)) (.con rfl)
  exact app_at (.con rfl) asE rfl

/-- The type of the motive: `‖PUnit.{1}‖ → Prop`. -/
def punitMotiveType : Term := .pi unitTypeExplicit (U levelZero)

/-- The context `Q : PUnit.{1} → Prop, h : Q PUnit.unit, x : PUnit.{1}`,
innermost first. -/
def punitContext : Ctx :=
  [unitTypeExplicit, eps levelZero (.app (.var 0) unitValueExplicit), punitMotiveType]

/-- `PUnit.rec.{1, 0} Q h x`. -/
def punitRedex : Term := ap "PUnit_rec" [instAt [levelOne, levelZero], .var 2, .var 1, .var 0]

/-- The type of the redex, `ε |0| (Q x)`. -/
def punitRedexType : Term := eps levelZero (.app (.var 2) (.var 0))

theorem punitContext_wellFormed : WellFormedCtx LFProfile.basic leanTheoryExplicit punitContext := by
  have rule : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.basic.products := by decide
  have uZero (context : Ctx) : LambdaPiModulo leanTheoryExplicit context (U levelZero) (.srt .type) :=
    app_at (.con rfl) (levelZero_typed_explicit context) rfl
  have motive : LambdaPiModulo leanTheoryExplicit [] punitMotiveType (.srt .type) :=
    .pi (unitTypeExplicit_formed []) (uZero _) rule
  have applied : LambdaPiModulo leanTheoryExplicit [punitMotiveType] (.app (.var 0) unitValueExplicit)
      (U levelZero) := app_at (.var rfl) (unitValueExplicit_typed _) rfl
  have minor : LambdaPiModulo leanTheoryExplicit [punitMotiveType]
      (eps levelZero (.app (.var 0) unitValueExplicit)) (.srt .type) :=
    app_at (app_at (.con rfl) (levelZero_typed_explicit _) rfl) applied rfl
  exact .cons (.cons (.cons .nil motive) minor) (unitTypeExplicit_formed _)

/-- The declared type of `PUnit.rec` at `inst [|1|, |0|]`, with its levels
computed. -/
def punitRecAt : Term :=
  .pi punitMotiveType (.pi (eps levelZero (.app (.var 0) unitValueExplicit))
    (.pi unitTypeExplicit (eps levelZero (.app (.var 2) (.var 0)))))

theorem punitRedex_typed :
    LambdaPiModulo leanTheoryExplicit punitContext punitRedex punitRedexType := by
  have rule : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.basic.products := by decide
  have levels := instAt_typed_explicit punitContext [levelOne, levelZero] (fun level member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact levelOne_typed_explicit _
    · exact levelZero_typed_explicit _)
  have declared := app_at (context := punitContext) (.con (name := "PUnit_rec") rfl) levels rfl
  have uZero (context : Ctx) : LambdaPiModulo leanTheoryExplicit context (U levelZero) (.srt .type) :=
    app_at (.con rfl) (levelZero_typed_explicit context) rfl
  have motive (context : Ctx) : LambdaPiModulo leanTheoryExplicit context punitMotiveType (.srt .type) :=
    .pi (unitTypeExplicit_formed _) (uZero _) rule
  have minorFormed : LambdaPiModulo leanTheoryExplicit (punitMotiveType :: punitContext)
      (eps levelZero (.app (.var 0) unitValueExplicit)) (.srt .type) :=
    app_at (app_at (.con rfl) (levelZero_typed_explicit _) rfl)
      (app_at (.var rfl) (unitValueExplicit_typed _) rfl) rfl
  have resultFormed : LambdaPiModulo leanTheoryExplicit
      (unitTypeExplicit :: eps levelZero (.app (.var 0) unitValueExplicit) :: punitMotiveType :: punitContext)
      (eps levelZero (.app (.var 2) (.var 0))) (.srt .type) :=
    app_at (app_at (.con rfl) (levelZero_typed_explicit _) rfl) (app_at (.var rfl) (.var rfl) rfl) rfl
  have formed : LambdaPiModulo leanTheoryExplicit punitContext punitRecAt (.srt .type) :=
    .pi (motive _) (.pi minorFormed (.pi (unitTypeExplicit_formed _) resultFormed rule) rule) rule
  have atLevels : LambdaPiModulo leanTheoryExplicit punitContext
      (.app (.con "PUnit_rec") (instAt [levelOne, levelZero])) punitRecAt := by
    refine .conv declared ?_ formed
    exact convExplicit_of_evaluate (fuel := 600) (fuel' := 1) (common := punitRecAt)
      (by decide +kernel) (by decide +kernel)
  exact app_at (app_at (app_at atLevels (.var rfl) rfl) (.var rfl) rfl) (.var rfl) rfl

/-- **The transcribed rule on `PUnit.rec` does not preserve types**, in the
theory with explicit level substitution: its left side `PUnit.rec Q h x` has
the type `ε |0| (Q x)` and its right side `h` has not, since `Q PUnit.unit`
and `Q x` are distinct normal forms. -/
theorem punitRec_breaks_preservation :
    ¬ leanTheoryExplicit.RulesPreserveTypes LFProfile.basic := by
  intro preserving
  have member : leanTheoryExplicit.rule punitRecRuleExplicit := by
    show punitRecRuleExplicit ∈ explicitRules
    decide +kernel
  have rhsTyped := preserving punitRecRuleExplicit
    (assign [instAt [levelOne, levelZero], .var 2, .var 1, .var 0]) punitContext punitRedexType member
    punitContext_wellFormed (by
      have same : inst (assign [instAt [levelOne, levelZero], .var 2, .var 1, .var 0])
          punitRecRuleExplicit.lhs = punitRedex := by decide +kernel
      rw [same]
      exact punitRedex_typed)
  have rhsSame : inst (assign [instAt [levelOne, levelZero], .var 2, .var 1, .var 0])
      punitRecRuleExplicit.rhs = .var 1 := by decide +kernel
  rw [rhsSame] at rhsTyped
  have declared : LambdaPiModulo leanTheoryExplicit punitContext (.var 1)
      (eps levelZero (.app (.var 2) unitValueExplicit)) := .var rfl
  have convertible := HasType.unique Example.basic_functional leanTheoryExplicit_confluent
    leanTheoryExplicit_headed leanTheoryExplicit_closedBodies (.var 1) declared rhsTyped
  exact not_conv_of_normal leanTheoryExplicit_confluent
    (normalExplicit_of_stepOnce (by decide +kernel)) (normalExplicit_of_stepOnce (by decide +kernel))
    (by decide) convertible

#print axioms WellFormedCtx.lookup_formed
#print axioms HasType.correct
#print axioms HasType.convertContext
#print axioms rootStep_preserves
#print axioms typePreservation
#print axioms typePreservation_reduces
#print axioms typePreservation_explicit
#print axioms punitRedex_typed
#print axioms punitRec_breaks_preservation

end Mettapedia.GSLT.Dedukti.LeanMinus
