import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorEmbeddings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution
import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Completeness
import Mettapedia.OSLF.NativeTypes.Runtime.Query

/-!
# The driver-based front door, read in the generated logic

The driver-based front door answers queries about a driver's GSLT: its formulas have tests as atoms,
steps of the GSLT, and splits of its spatial theory. Its answers become statements about closed generated
formulas of a language, read in that language's reference structure, given two things (`Faithful`):

- **a faithful rendering**: a native structure on the driver's terms whose steps are the GSLT's, whose
  splits are the spatial theory's, and which renders into the reference structure by a bounded morphism;
- **tests as formulas**: each test is a closed formula that holds at a term's rendering exactly when the
  test holds at the term, and the formulas that close the atoms are forward.

Then the meaning of a driver formula at a decoded request is the truth of a closed generated formula at
the request (`meaning_iff_sat`): the embedded formula, with each test's formula substituted for its atom,
and the dual of that formula for the atom's negation. So a verdict of either front door about such a
query is a verdict of the other: the generated front door's proofs and refutations of the closed formula
settle the driver formula's meaning (`meaning_of_ask_proved`, `not_meaning_of_ask_refuted`). In an
equation-free language the generated front door decides every driver formula at a request whose closure
is finite (`ask_decides_driver`), since substitution keeps formulas forward (`forward_subst`).

The same holds for queries, through their elaboration (`queryMeaning_iff_sat`): a decided answer of the
driver-based front door is a theorem about the closed formula (`sat_of_session_positive`,
`not_sat_of_session_negative`).

**Without separating conjunctions a step morphism is enough** (`FaithfulSteps`, `meaning_iff_sat_steps`):
the embedded formula then uses only steps, connectives and atoms, and the tests enter through the
environment, not through the morphism. A driver over closed terms, whose parts under binders are not its
own terms, cannot render by a bounded morphism, but it can by a step morphism.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (denotation)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver Meaning meaning_at_decoded)

/-- **Embedded front-door formulas are forward**, at both polarities. -/
theorem forward_ofCore {Leaf : Type} {m : ℕ} (positive negative : Leaf → Fin m) (kindOf : ℕ → CollType) :
    ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf) (polarity : Bool),
      (ofCore positive negative kindOf polarity formula).forward = true
  | .atom _, polarity => by cases polarity <;> rfl
  | .top, polarity => by cases polarity <;> rfl
  | .bottom, polarity => by cases polarity <;> rfl
  | .conj left right, polarity => by
    cases polarity <;> simp [ofCore, Formula.forward, forward_ofCore positive negative kindOf left,
      forward_ofCore positive negative kindOf right]
  | .disj left right, polarity => by
    cases polarity <;> simp [ofCore, Formula.forward, forward_ofCore positive negative kindOf left,
      forward_ofCore positive negative kindOf right]
  | .neg inner, polarity => by
    simp only [ofCore]
    exact forward_ofCore positive negative kindOf inner _
  | .imp premise conclusion, polarity => by
    cases polarity <;> simp [ofCore, Formula.forward, forward_ofCore positive negative kindOf premise,
      forward_ofCore positive negative kindOf conclusion]
  | .possibility inner, polarity => by
    cases polarity <;> simp [ofCore, Formula.forward, forward_ofCore positive negative kindOf inner]
  | .outgoingUniversal inner, polarity => by
    cases polarity <;> simp [ofCore, Formula.forward, forward_ofCore positive negative kindOf inner]
  | .separating _ left right, polarity => by
    cases polarity <;> simp [ofCore, Formula.forward, forward_ofCore positive negative kindOf left,
      forward_ofCore positive negative kindOf right]


/-! ## Substitution keeps formulas forward -/

mutual
theorem forward_rename : ∀ {n m : ℕ} (along : Fin n → Fin m) (formula : Formula n),
    (formula.rename along).forward = formula.forward
  | _, _, along, .top => rfl
  | _, _, along, .bot => rfl
  | _, _, along, .and f0 f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f0, forward_rename along f1]
  | _, _, along, .or f0 f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f0, forward_rename along f1]
  | _, _, along, .var _ => rfl
  | _, _, along, .mu f0 => by simp only [Formula.rename, Formula.forward, forward_rename (liftRenaming along) f0]
  | _, _, along, .nu f0 => by simp only [Formula.rename, Formula.forward, forward_rename (liftRenaming along) f0]
  | _, _, along, .possibly _ f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f1]
  | _, _, along, .necessarily _ f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f1]
  | _, _, along, .sometimeBefore _ f1 => rfl
  | _, _, along, .alwaysBefore _ f1 => rfl
  | _, _, along, .atLeast _ d1 _ f3 => by cases d1 <;> simp only [Formula.rename, Formula.forward, forward_rename along f3]
  | _, _, along, .allButFewer _ d1 _ f3 => by cases d1 <;> simp only [Formula.rename, Formula.forward, forward_rename along f3]
  | _, _, along, .built _ fs1 => by simp only [Formula.rename, Formula.forward, forwardList_rename along fs1]
  | _, _, along, .everyBuilt _ fs1 => by simp only [Formula.rename, Formula.forward, forwardList_rename along fs1]
  | _, _, along, .split _ f1 f2 => by simp only [Formula.rename, Formula.forward, forward_rename along f1, forward_rename along f2]
  | _, _, along, .everySplit _ f1 f2 => by simp only [Formula.rename, Formula.forward, forward_rename along f1, forward_rename along f2]
  | _, _, along, .empty _ => rfl
  | _, _, along, .nonEmpty _ => rfl
  | _, _, along, .single _ f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f1]
  | _, _, along, .everySingle _ f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f1]
  | _, _, along, .body f0 => by simp only [Formula.rename, Formula.forward, forward_rename along f0]
  | _, _, along, .everyBody f0 => by simp only [Formula.rename, Formula.forward, forward_rename along f0]
  | _, _, along, .multiBody _ f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f1]
  | _, _, along, .everyMultiBody _ f1 => by simp only [Formula.rename, Formula.forward, forward_rename along f1]
  | _, _, along, .bound _ => rfl
  | _, _, along, .notBound _ => rfl
  | _, _, along, .typed _ => rfl
  | _, _, along, .untyped _ => rfl
  | _, _, along, .is _ => rfl
  | _, _, along, .isNot _ => rfl
  | _, _, along, .mapsAll f0 f1 => rfl
  | _, _, along, .mapsSome f0 f1 => rfl
  | _, _, along, .someOf _ f1 => rfl
  | _, _, along, .everyOf _ f1 => rfl

theorem forwardList_rename : ∀ {n m : ℕ} (along : Fin n → Fin m) (formulas : Formulas n),
    Formula.forwardList (formulas.rename along) = Formula.forwardList formulas
  | _, _, _, .nil => rfl
  | _, _, along, .cons formula formulas => by
    simp only [Formulas.rename, Formula.forwardList, forward_rename along formula, forwardList_rename along formulas]
end

theorem forward_liftSubstitution {n m : ℕ} {substitution : Fin n → Formula m}
    (forward : ∀ index, (substitution index).forward = true) :
    ∀ index, (liftSubstitution substitution index).forward = true := by
  intro index
  refine Fin.cases rfl (fun index => ?_) index
  show ((substitution index).rename Fin.succ).forward = true
  rw [forward_rename]
  exact forward index

mutual
theorem forward_subst : ∀ {n m : ℕ} (substitution : Fin n → Formula m) (formula : Formula n),
    (∀ index, (substitution index).forward = true) → formula.forward = true → (formula.subst substitution).forward = true
  | _, _, substitution, .top, substituted, holds => holds
  | _, _, substitution, .bot, substituted, holds => holds
  | _, _, substitution, .and f0 f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
    exact ⟨forward_subst substitution f0 substituted holds.1, forward_subst substitution f1 substituted holds.2⟩
  | _, _, substitution, .or f0 f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
    exact ⟨forward_subst substitution f0 substituted holds.1, forward_subst substitution f1 substituted holds.2⟩
  | _, _, substitution, .var index, substituted, holds => substituted index
  | _, _, substitution, .mu f0, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst (liftSubstitution substitution) f0 (forward_liftSubstitution substituted) holds
  | _, _, substitution, .nu f0, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst (liftSubstitution substitution) f0 (forward_liftSubstitution substituted) holds
  | _, _, substitution, .possibly _ f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f1 substituted holds
  | _, _, substitution, .necessarily _ f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f1 substituted holds
  | _, _, substitution, .sometimeBefore _ f1, substituted, holds => by simp [Formula.forward] at holds
  | _, _, substitution, .alwaysBefore _ f1, substituted, holds => by simp [Formula.forward] at holds
  | _, _, substitution, .atLeast _ d1 _ f3, substituted, holds => by
    cases d1
    · simp only [Formula.subst, Formula.forward] at holds ⊢
      exact forward_subst substitution f3 substituted holds
    · simp [Formula.forward] at holds
  | _, _, substitution, .allButFewer _ d1 _ f3, substituted, holds => by
    cases d1
    · simp only [Formula.subst, Formula.forward] at holds ⊢
      exact forward_subst substitution f3 substituted holds
    · simp [Formula.forward] at holds
  | _, _, substitution, .built _ fs1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forwardList_subst substitution fs1 substituted holds
  | _, _, substitution, .everyBuilt _ fs1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forwardList_subst substitution fs1 substituted holds
  | _, _, substitution, .split _ f1 f2, substituted, holds => by
    simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
    exact ⟨forward_subst substitution f1 substituted holds.1, forward_subst substitution f2 substituted holds.2⟩
  | _, _, substitution, .everySplit _ f1 f2, substituted, holds => by
    simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
    exact ⟨forward_subst substitution f1 substituted holds.1, forward_subst substitution f2 substituted holds.2⟩
  | _, _, substitution, .empty _, substituted, holds => holds
  | _, _, substitution, .nonEmpty _, substituted, holds => holds
  | _, _, substitution, .single _ f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f1 substituted holds
  | _, _, substitution, .everySingle _ f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f1 substituted holds
  | _, _, substitution, .body f0, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f0 substituted holds
  | _, _, substitution, .everyBody f0, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f0 substituted holds
  | _, _, substitution, .multiBody _ f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f1 substituted holds
  | _, _, substitution, .everyMultiBody _ f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward] at holds ⊢
    exact forward_subst substitution f1 substituted holds
  | _, _, substitution, .bound _, substituted, holds => holds
  | _, _, substitution, .notBound _, substituted, holds => holds
  | _, _, substitution, .typed _, substituted, holds => holds
  | _, _, substitution, .untyped _, substituted, holds => holds
  | _, _, substitution, .is _, substituted, holds => holds
  | _, _, substitution, .isNot _, substituted, holds => holds
  | _, _, substitution, .mapsAll f0 f1, substituted, holds => by simp [Formula.forward] at holds
  | _, _, substitution, .mapsSome f0 f1, substituted, holds => by simp [Formula.forward] at holds
  | _, _, substitution, .someOf _ f1, substituted, holds => by simp [Formula.forward] at holds
  | _, _, substitution, .everyOf _ f1, substituted, holds => by simp [Formula.forward] at holds

theorem forwardList_subst : ∀ {n m : ℕ} (substitution : Fin n → Formula m) (formulas : Formulas n),
    (∀ index, (substitution index).forward = true) → Formula.forwardList formulas = true →
      Formula.forwardList (formulas.subst substitution) = true
  | _, _, _, .nil, _, _ => rfl
  | _, _, substitution, .cons formula formulas, substituted, holds => by
    simp only [Formulas.subst, Formula.forwardList, Bool.and_eq_true] at holds ⊢
    exact ⟨forward_subst substitution formula substituted holds.1,
      forwardList_subst substitution formulas substituted holds.2⟩
end

variable (driver : Driver) (relEnv : RelationEnv) (language : LanguageDef) {m : ℕ}
  (positive negative : driver.Leaf → Fin m) (kindOf : ℕ → CollType)

/-- **A faithful reading of a driver in a language's reference structure**: a native structure on the
driver's terms with the GSLT's steps, rendered into the reference structure by a bounded morphism, and a
closed formula for each test, together with forward closing formulas for the atom variables. -/
structure Faithful where
  structure_ : NativeStructure driver.system.Term
  steps : ∀ source target, structure_.step source .any target ↔ driver.system.Step source target
  rendering : BoundedMorphism structure_ (referenceStructure relEnv language)
  renders : rendering.map = driver.render
  test : driver.Leaf → Formula 0
  testAgrees : ∀ leaf source, (driver.tests leaf).predicate.1 source ↔
    (referenceStructure relEnv language).sat Env.closed (test leaf) (driver.render source)
  closing : Fin m → Formula 0
  closesPositive : ∀ leaf, closing (positive leaf) = test leaf
  closesNegative : ∀ leaf, closing (negative leaf) = (test leaf).dual
  closingForward : ∀ index, (closing index).forward = true

variable {driver relEnv language positive negative kindOf}

/-- **The meaning of a driver formula at a decoded request is the truth of a closed generated formula
there**, when the rendering is faithful and the formula's splits are the spatial theory's. -/
theorem meaning_iff_sat (faithful : Faithful driver relEnv language positive negative)
    (formula : driver.Formula)
    (realized : SplitsRealized kindOf faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) :
    Meaning driver formula raw ↔
      (referenceStructure relEnv language).sat Env.closed
        ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := by
  let reference := referenceStructure relEnv language
  let targetEnv : Env Pattern m := fun index => {term | reference.sat Env.closed (faithful.closing index) term}
  let sourceEnv : Env driver.system.Term m := fun index => faithful.rendering.map ⁻¹' targetEnv index
  have related : faithful.rendering.EnvPreimage sourceEnv targetEnv := fun _ _ => Iff.rfl
  have onPositive : ∀ leaf term, term ∈ sourceEnv (positive leaf) ↔ (driver.tests leaf).predicate.1 term := by
    intro leaf term
    show reference.sat Env.closed (faithful.closing (positive leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesPositive, faithful.renders, faithful.testAgrees]
  have onNegative : ∀ leaf term, term ∈ sourceEnv (negative leaf) ↔ ¬ (driver.tests leaf).predicate.1 term := by
    intro leaf term
    show reference.sat Env.closed (faithful.closing (negative leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesNegative, reference.sat_dual_closed, faithful.renders, faithful.testAgrees]
  have embedded := sat_ofCore (positive := positive) (negative := negative) (kindOf := kindOf) driver.tests
    driver.backend.spatial.theory faithful.steps onPositive onNegative formula true realized decoded.val
  have transported := faithful.rendering.sat_iff (ofCore positive negative kindOf true formula)
    (forward_ofCore positive negative kindOf formula true) related decoded.val
  have mapped : faithful.rendering.map decoded.val = raw := by
    rw [faithful.renders]
    exact decoded.property.2
  rw [meaning_at_decoded driver formula raw decoded, reference.sat_close]
  refine (embedded.symm.trans transported).trans ?_
  rw [mapped]

variable {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel : ℕ}

/-- **The generated front door proves a driver formula's meaning** when it proves the closed formula. -/
theorem meaning_of_ask_proved (faithful : Faithful driver relEnv language positive negative)
    (formula : driver.Formula)
    (realized : SplitsRealized kindOf faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) {hint : Option CertificateCandidate} {rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} {evidence : Evidence}
    (answered : ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing)
      raw hint rounds forms = .proved evidence) :
    Meaning driver formula raw :=
  (meaning_iff_sat faithful formula realized decoded).mpr (ask_proved answered)

/-- **And refutes it** when it refutes the closed formula. -/
theorem not_meaning_of_ask_refuted (faithful : Faithful driver relEnv language positive negative)
    (formula : driver.Formula)
    (realized : SplitsRealized kindOf faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) {hint : Option CertificateCandidate} {rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} {evidence : Evidence}
    (answered : ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing)
      raw hint rounds forms = .refuted evidence) :
    ¬ Meaning driver formula raw := fun holds =>
  ask_refuted answered ((meaning_iff_sat faithful formula realized decoded).mp holds)

/-- **The generated front door decides every driver formula** at a request whose closure is finite, in an
equation-free language. -/
theorem ask_decides_driver (faithful : Faithful driver relEnv language positive negative)
    (formula : driver.Formula) {raw : Pattern} (free : language.isEquationFree = true) {closure : List Pattern}
    (bounded : Closure relEnv language fuel raw closure) {rounds : ℕ} (enoughRounds : closure.length ≤ rounds)
    (hint : Option CertificateCandidate) :
    ∃ evidence,
      ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing) raw
          hint rounds = .proved evidence ∨
        ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing) raw
          hint rounds = .refuted evidence :=
  ask_decides free bounded
    (forward_subst faithful.closing _ faithful.closingForward (forward_ofCore positive negative kindOf formula true))
    enoughRounds hint

/-! ## Queries -/

open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query elaborate elaborate_exact)
open Mettapedia.OSLF.NativeTypes.Runtime (Engine NamedSession named_positive named_negative)

/-- **The meaning of a query at a decoded request is the truth of its closed formula there**, through its
elaboration. -/
theorem queryMeaning_iff_sat (faithful : Faithful driver relEnv language positive negative) {query : Query}
    {formula : driver.Formula} (elaborated : elaborate driver query = .ok formula)
    (realized : SplitsRealized kindOf faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) :
    Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning driver query raw ↔
      (referenceStructure relEnv language).sat Env.closed
        ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := by
  constructor
  · rintro ⟨resolved, resolves, holds⟩
    have same : resolved = formula := by
      have output := (elaborate_exact driver query resolved).mpr resolves
      rw [elaborated] at output
      cases output
      rfl
    subst same
    exact (meaning_iff_sat faithful resolved realized decoded).mp holds
  · intro holds
    exact ⟨formula, (elaborate_exact driver query formula).mp elaborated,
      (meaning_iff_sat faithful formula realized decoded).mpr holds⟩

/-- **A proved answer of the driver-based front door is a theorem about the closed formula.** -/
theorem sat_of_session_positive (faithful : Faithful driver relEnv language positive negative) {query : Query}
    {formula : driver.Formula} (elaborated : elaborate driver query = .ok formula)
    (realized : SplitsRealized kindOf faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) {runtime : Engine driver}
    (session : NamedSession driver runtime query raw)
    (read : session.readout = .checked (.judgment (.decided true))) :
    (referenceStructure relEnv language).sat Env.closed
      ((ofCore positive negative kindOf true formula).subst faithful.closing) raw :=
  (queryMeaning_iff_sat faithful elaborated realized decoded).mp (named_positive session read)

/-- **And a refuted answer refutes it.** -/
theorem not_sat_of_session_negative (faithful : Faithful driver relEnv language positive negative) {query : Query}
    {formula : driver.Formula} (elaborated : elaborate driver query = .ok formula)
    (realized : SplitsRealized kindOf faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) {runtime : Engine driver}
    (session : NamedSession driver runtime query raw)
    (read : session.readout = .checked (.judgment (.decided false))) :
    ¬ (referenceStructure relEnv language).sat Env.closed
      ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := fun holds =>
  named_negative session read ((queryMeaning_iff_sat faithful elaborated realized decoded).mpr holds)

/-! ## Without separating conjunctions -/

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Formula)

/-- A front-door formula without separating conjunctions. -/
def spatialFree {Leaf : Type} : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf → Bool
  | .atom _ | .top | .bottom => true
  | .conj left right | .disj left right | .imp left right => spatialFree left && spatialFree right
  | .neg inner | .possibility inner | .outgoingUniversal inner => spatialFree inner
  | .separating _ _ _ => false

theorem behavioural_ofCore {Leaf : Type} {m : ℕ} (positive negative : Leaf → Fin m) (kindOf : ℕ → CollType) :
    ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf), spatialFree formula = true →
      ∀ polarity, (ofCore positive negative kindOf polarity formula).behaviouralForward = true
  | .atom _, _, polarity => by cases polarity <;> rfl
  | .top, _, polarity => by cases polarity <;> rfl
  | .bottom, _, polarity => by cases polarity <;> rfl
  | .conj left right, free, polarity => by
    simp only [spatialFree, Bool.and_eq_true] at free
    cases polarity <;> simp [ofCore, GeneratedLogic.Formula.behaviouralForward,
      behavioural_ofCore positive negative kindOf left free.1, behavioural_ofCore positive negative kindOf right free.2]
  | .disj left right, free, polarity => by
    simp only [spatialFree, Bool.and_eq_true] at free
    cases polarity <;> simp [ofCore, GeneratedLogic.Formula.behaviouralForward,
      behavioural_ofCore positive negative kindOf left free.1, behavioural_ofCore positive negative kindOf right free.2]
  | .imp premise conclusion, free, polarity => by
    simp only [spatialFree, Bool.and_eq_true] at free
    cases polarity <;> simp [ofCore, GeneratedLogic.Formula.behaviouralForward,
      behavioural_ofCore positive negative kindOf premise free.1,
      behavioural_ofCore positive negative kindOf conclusion free.2]
  | .neg inner, free, polarity => by
    simp only [ofCore]
    exact behavioural_ofCore positive negative kindOf inner free _
  | .possibility inner, free, polarity => by
    cases polarity <;> simp [ofCore, GeneratedLogic.Formula.behaviouralForward,
      behavioural_ofCore positive negative kindOf inner free]
  | .outgoingUniversal inner, free, polarity => by
    cases polarity <;> simp [ofCore, GeneratedLogic.Formula.behaviouralForward,
      behavioural_ofCore positive negative kindOf inner free]
  | .separating _ _ _, free, _ => by simp [spatialFree] at free

theorem splitsRealized_of_spatialFree {Leaf : Type} {system : Mettapedia.GSLT.GSLT.{0}}
    {S : NativeStructure system.Term} {spatial : Mettapedia.OSLF.NativeTypes.Decision.Spatial.SpatialTheory system}
    (kindOf : ℕ → CollType) :
    ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf), spatialFree formula = true →
      SplitsRealized kindOf S spatial formula
  | .atom _, _ | .top, _ | .bottom, _ => trivial
  | .conj left right, free | .disj left right, free | .imp left right, free => by
    simp only [spatialFree, Bool.and_eq_true] at free
    exact ⟨splitsRealized_of_spatialFree kindOf left free.1, splitsRealized_of_spatialFree kindOf right free.2⟩
  | .neg inner, free | .possibility inner, free | .outgoingUniversal inner, free =>
    splitsRealized_of_spatialFree kindOf inner free
  | .separating _ _ _, free => by simp [spatialFree] at free

variable (driver relEnv language positive negative) in
/-- **A faithful reading by steps**: as `Faithful`, with a step morphism in place of a bounded morphism,
for formulas without separating conjunctions. -/
structure FaithfulSteps where
  structure_ : NativeStructure driver.system.Term
  steps : ∀ source target, structure_.step source .any target ↔ driver.system.Step source target
  rendering : StepMorphism structure_ (referenceStructure relEnv language)
  renders : rendering.map = driver.render
  test : driver.Leaf → Formula 0
  testAgrees : ∀ leaf source, (driver.tests leaf).predicate.1 source ↔
    (referenceStructure relEnv language).sat Env.closed (test leaf) (driver.render source)
  closing : Fin m → Formula 0
  closesPositive : ∀ leaf, closing (positive leaf) = test leaf
  closesNegative : ∀ leaf, closing (negative leaf) = (test leaf).dual
  closingForward : ∀ index, (closing index).forward = true

/-- **The meaning of a formula without separating conjunctions is the truth of its closed formula**, along
a faithful reading by steps. -/
theorem meaning_iff_sat_steps (faithful : FaithfulSteps driver relEnv language positive negative)
    (formula : driver.Formula) (free : spatialFree formula = true) {raw : Pattern} (decoded : driver.Decoded raw) :
    Meaning driver formula raw ↔
      (referenceStructure relEnv language).sat Env.closed
        ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := by
  let reference := referenceStructure relEnv language
  let targetEnv : Env Pattern m := fun index => {term | reference.sat Env.closed (faithful.closing index) term}
  let sourceEnv : Env driver.system.Term m := fun index => faithful.rendering.map ⁻¹' targetEnv index
  have related : faithful.rendering.EnvPreimage sourceEnv targetEnv := fun _ _ => Iff.rfl
  have onPositive : ∀ leaf term, term ∈ sourceEnv (positive leaf) ↔ (driver.tests leaf).predicate.1 term := by
    intro leaf term
    show reference.sat Env.closed (faithful.closing (positive leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesPositive, faithful.renders, faithful.testAgrees]
  have onNegative : ∀ leaf term, term ∈ sourceEnv (negative leaf) ↔ ¬ (driver.tests leaf).predicate.1 term := by
    intro leaf term
    show reference.sat Env.closed (faithful.closing (negative leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesNegative, reference.sat_dual_closed, faithful.renders, faithful.testAgrees]
  have embedded := sat_ofCore (positive := positive) (negative := negative) (kindOf := kindOf) driver.tests
    driver.backend.spatial.theory faithful.steps onPositive onNegative formula true
    (splitsRealized_of_spatialFree kindOf formula free) decoded.val
  have transported := faithful.rendering.sat_iff (ofCore positive negative kindOf true formula)
    (behavioural_ofCore positive negative kindOf formula free true) related decoded.val
  have mapped : faithful.rendering.map decoded.val = raw := by
    rw [faithful.renders]
    exact decoded.property.2
  rw [meaning_at_decoded driver formula raw decoded, reference.sat_close]
  refine (embedded.symm.trans transported).trans ?_
  rw [mapped]

/-- **Along a faithful reading by steps, the generated front door decides every formula without separating
conjunctions** at a request whose closure is finite, in an equation-free language, and its answer is the
formula's meaning. -/
theorem ask_decides_driver_steps (faithful : FaithfulSteps driver relEnv language positive negative)
    (formula : driver.Formula) (free : spatialFree formula = true) {raw : Pattern} (decoded : driver.Decoded raw)
    (equationFree : language.isEquationFree = true) {closure : List Pattern}
    (bounded : Closure relEnv language fuel raw closure) {rounds : ℕ} (enoughRounds : closure.length ≤ rounds)
    (hint : Option CertificateCandidate) :
    ∃ evidence,
      (ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing) raw
          hint rounds = .proved evidence ∧ Meaning driver formula raw) ∨
        (ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing)
          raw hint rounds = .refuted evidence ∧ ¬ Meaning driver formula raw) := by
  obtain ⟨evidence, answered⟩ := ask_decides (signature := signature) equationFree bounded
    (forward_subst faithful.closing _ faithful.closingForward (forward_ofCore positive negative kindOf formula true))
    enoughRounds hint
  refine ⟨evidence, answered.imp (fun proved => ⟨proved, ?_⟩) (fun refuted => ⟨refuted, ?_⟩)⟩
  · exact (meaning_iff_sat_steps faithful formula free decoded).mpr (ask_proved proved)
  · exact fun holds => ask_refuted refuted ((meaning_iff_sat_steps faithful formula free decoded).mp holds)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings
