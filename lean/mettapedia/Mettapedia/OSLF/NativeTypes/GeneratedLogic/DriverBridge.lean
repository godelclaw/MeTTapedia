import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorEmbeddings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SplitMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution
import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Completeness
import Mettapedia.OSLF.NativeTypes.Runtime.Query

/-!
# The driver-based front door, read in the generated logic

The driver-based front door answers queries about a driver's GSLT: its formulas have tests as atoms,
steps of the GSLT, and splits of its spatial theory. Its answers become statements about closed generated
formulas of a language, read in that language's reference structure, given two things (`Faithful`):

- **a faithful rendering on a region**: a native structure on the driver's terms whose steps from a region of them
  are the GSLT's, whose splits there are the spatial theory's, and which renders into the reference structure by a
  split morphism (steps and splits forth and back). The region is closed under the driver's steps; it is where the driver's semantics and the
  reference semantics are proved to agree, for instance the well-sorted closed terms of an aligned language;
- **tests as formulas**: each test is a closed formula that holds at a term's rendering exactly when the
  test holds at the term, in the region, and the formulas that close the atoms are forward.

Then the meaning of a driver formula at a decoded request in the region is the truth of a closed generated formula
at the request (`meaning_iff_sat`): the embedded formula, with each test's formula substituted for its atom,
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
own terms, renders by a step morphism.

**A split morphism asks only for steps and splits** (`pullbackSplit`): a driver whose terms are bags of payloads, the
payloads not being its terms, renders by one along its encoding, when the steps and splits of an encoded term stay
among encoded terms.
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

/-- **Embedded front-door formulas use only steps, splits and the connectives**, at both polarities. -/
theorem splitForward_ofCore {Leaf : Type} {m : ℕ} (positive negative : Leaf → Fin m) (kindOf : ℕ → CollType) :
    ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf) (polarity : Bool),
      (ofCore positive negative kindOf polarity formula).splitForward = true
  | .atom _, polarity => by cases polarity <;> rfl
  | .top, polarity => by cases polarity <;> rfl
  | .bottom, polarity => by cases polarity <;> rfl
  | .conj left right, polarity => by
    cases polarity <;> simp [ofCore, Formula.splitForward, splitForward_ofCore positive negative kindOf left,
      splitForward_ofCore positive negative kindOf right]
  | .disj left right, polarity => by
    cases polarity <;> simp [ofCore, Formula.splitForward, splitForward_ofCore positive negative kindOf left,
      splitForward_ofCore positive negative kindOf right]
  | .neg inner, polarity => by
    simp only [ofCore]
    exact splitForward_ofCore positive negative kindOf inner _
  | .imp premise conclusion, polarity => by
    cases polarity <;> simp [ofCore, Formula.splitForward, splitForward_ofCore positive negative kindOf premise,
      splitForward_ofCore positive negative kindOf conclusion]
  | .possibility inner, polarity => by
    cases polarity <;> simp [ofCore, Formula.splitForward, splitForward_ofCore positive negative kindOf inner]
  | .outgoingUniversal inner, polarity => by
    cases polarity <;> simp [ofCore, Formula.splitForward, splitForward_ofCore positive negative kindOf inner]
  | .separating _ left right, polarity => by
    cases polarity <;> simp [ofCore, Formula.splitForward, splitForward_ofCore positive negative kindOf left,
      splitForward_ofCore positive negative kindOf right]


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
  | _, _, along, .inRelation _ => rfl
  | _, _, along, .notInRelation _ => rfl
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
    simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
    exact ⟨holds.1, forward_subst substitution f1 substituted holds.2⟩
  | _, _, substitution, .necessarily _ f1, substituted, holds => by
    simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
    exact ⟨holds.1, forward_subst substitution f1 substituted holds.2⟩
  | _, _, substitution, .sometimeBefore _ f1, substituted, holds => by simp [Formula.forward] at holds
  | _, _, substitution, .alwaysBefore _ f1, substituted, holds => by simp [Formula.forward] at holds
  | _, _, substitution, .atLeast _ d1 _ f3, substituted, holds => by
    cases d1
    · simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
      exact ⟨holds.1, forward_subst substitution f3 substituted holds.2⟩
    · simp [Formula.forward] at holds
  | _, _, substitution, .allButFewer _ d1 _ f3, substituted, holds => by
    cases d1
    · simp only [Formula.subst, Formula.forward, Bool.and_eq_true] at holds ⊢
      exact ⟨holds.1, forward_subst substitution f3 substituted holds.2⟩
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
  | _, _, substitution, .inRelation _, substituted, holds => holds
  | _, _, substitution, .notInRelation _, substituted, holds => holds
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

/-- **A faithful reading of a driver in a language's reference structure**, on a region of the driver's terms that
its steps do not leave: a native structure on the driver's terms whose steps from the region are the GSLT's, rendered
into the reference structure by a split morphism; a closed formula for each test, agreeing with the test on the
region; and forward closing formulas for the atom variables. -/
structure Faithful (equations : LanguageReading := .syntax) where
  structure_ : NativeStructure driver.system.Term
  region : driver.system.Term → Prop
  steps : ∀ source, region source → ∀ target, (structure_.step source .any target ↔ driver.system.Step source target)
  closed : ∀ source target, region source → driver.system.Step source target → region target
  rendering : SplitMorphism structure_ (referenceStructure relEnv language equations)
  renders : rendering.map = driver.render
  covers : driver.Leaf → Prop
  test : driver.Leaf → Formula 0
  testAgrees : ∀ leaf, covers leaf → ∀ source, region source → ((driver.tests leaf).predicate.1 source ↔
    (referenceStructure relEnv language equations).sat Env.closed (test leaf) (driver.render source))
  closing : Fin m → Formula 0
  closesPositive : ∀ leaf, closing (positive leaf) = test leaf
  closesNegative : ∀ leaf, closing (negative leaf) = (test leaf).dual
  closingForward : ∀ index, (closing index).forward = true

variable {driver relEnv language positive negative kindOf} {equations : LanguageReading}

/-- **The meaning of a driver formula at a decoded request in the region is the truth of a closed generated formula
there**, when the rendering is faithful and the formula's splits are the spatial theory's on the region. -/
theorem meaning_iff_sat (faithful : Faithful driver relEnv language positive negative equations)
    (formula : driver.Formula) (atoms : AtomsCovered faithful.covers formula)
    (realized : SplitsRealizedOn kindOf faithful.region faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) (inside : faithful.region decoded.val) :
    Meaning driver formula raw ↔
      (referenceStructure relEnv language equations).sat Env.closed
        ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := by
  let reference := referenceStructure relEnv language equations
  let targetEnv : Env Pattern m := fun index => {term | reference.sat Env.closed (faithful.closing index) term}
  let sourceEnv : Env driver.system.Term m := fun index => faithful.rendering.map ⁻¹' targetEnv index
  have related : faithful.rendering.EnvPreimage sourceEnv targetEnv := fun _ _ => Iff.rfl
  have onPositive : ∀ leaf, faithful.covers leaf → ∀ term, faithful.region term →
      (term ∈ sourceEnv (positive leaf) ↔ (driver.tests leaf).predicate.1 term) := by
    intro leaf covered term within
    show reference.sat Env.closed (faithful.closing (positive leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesPositive, faithful.renders, faithful.testAgrees leaf covered term within]
  have onNegative : ∀ leaf, faithful.covers leaf → ∀ term, faithful.region term →
      (term ∈ sourceEnv (negative leaf) ↔ ¬ (driver.tests leaf).predicate.1 term) := by
    intro leaf covered term within
    show reference.sat Env.closed (faithful.closing (negative leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesNegative, reference.sat_dual_closed, faithful.renders,
      faithful.testAgrees leaf covered term within]
  have embedded := sat_ofCore_on (positive := positive) (negative := negative) (kindOf := kindOf) driver.tests
    driver.backend.spatial.theory faithful.region faithful.covers faithful.steps faithful.closed onPositive onNegative
    formula true atoms realized decoded.val inside
  have transported := faithful.rendering.sat_iff (ofCore positive negative kindOf true formula)
    (splitForward_ofCore positive negative kindOf formula true) related decoded.val
  have mapped : faithful.rendering.map decoded.val = raw := by
    rw [faithful.renders]
    exact decoded.property.2
  rw [meaning_at_decoded driver formula raw decoded, reference.sat_close]
  refine (embedded.symm.trans transported).trans ?_
  rw [mapped]

variable {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel : ℕ}

/-- **The generated front door proves a driver formula's meaning** when it proves the closed formula. -/
theorem meaning_of_ask_proved (faithful : Faithful driver relEnv language positive negative equations)
    (formula : driver.Formula) (atoms : AtomsCovered faithful.covers formula)
    (realized : SplitsRealizedOn kindOf faithful.region faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) (inside : faithful.region decoded.val)
    {hint : Option CertificateCandidate} {rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} (compatible : FormsFor forms equations) {evidence : Evidence}
    (answered : ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing)
      raw hint rounds forms = .proved evidence) :
    Meaning driver formula raw :=
  (meaning_iff_sat faithful formula atoms realized decoded inside).mpr (ask_proved_in compatible answered)

/-- **And refutes it** when it refutes the closed formula. -/
theorem not_meaning_of_ask_refuted (faithful : Faithful driver relEnv language positive negative equations)
    (formula : driver.Formula) (atoms : AtomsCovered faithful.covers formula)
    (realized : SplitsRealizedOn kindOf faithful.region faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) (inside : faithful.region decoded.val)
    {hint : Option CertificateCandidate} {rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} (compatible : FormsFor forms equations) {evidence : Evidence}
    (answered : ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing)
      raw hint rounds forms = .refuted evidence) :
    ¬ Meaning driver formula raw := fun holds =>
  ask_refuted_in compatible answered ((meaning_iff_sat faithful formula atoms realized decoded inside).mp holds)

/-- **The generated front door decides every driver formula** at a request whose closure is finite, in an
equation-free language. -/
theorem ask_decides_driver (faithful : Faithful driver relEnv language positive negative equations)
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

open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query elaborate elaborate_exact Resolves)
open Mettapedia.OSLF.NativeTypes.Runtime (Engine NamedSession named_positive named_negative)

theorem AtomsCovered.mono {Leaf : Type} {covered wider : Leaf → Prop} (within : ∀ leaf, covered leaf → wider leaf) :
    ∀ {formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf},
      AtomsCovered covered formula → AtomsCovered wider formula
  | .atom leaf, atoms => within leaf atoms
  | .top, _ | .bottom, _ => trivial
  | .conj left right, atoms | .disj left right, atoms | .imp left right, atoms | .separating _ left right, atoms =>
    ⟨AtomsCovered.mono within (formula := left) atoms.1, AtomsCovered.mono within (formula := right) atoms.2⟩
  | .neg inner, atoms | .possibility inner, atoms | .outgoingUniversal inner, atoms =>
    AtomsCovered.mono within (formula := inner) atoms

/-- **A query's atoms are the tests its constructor names look up.** -/
theorem atomsCovered_of_resolves {query : Query} {formula : driver.Formula} (resolved : Resolves driver query formula) :
    AtomsCovered (fun leaf => ∃ name, driver.lookup name = some leaf) formula := by
  induction resolved with
  | constructor lookup => exact ⟨_, lookup⟩
  | top | bottom => trivial
  | conj _ _ first second | disj _ _ first second | imp _ _ first second | separating _ _ _ first second =>
    exact ⟨first, second⟩
  | neg _ inner | possibility _ inner | outgoingUniversal _ inner => exact inner

/-- **The meaning of a query at a decoded request in the region is the truth of its closed formula there**, through
its elaboration. -/
theorem queryMeaning_iff_sat (faithful : Faithful driver relEnv language positive negative equations) {query : Query}
    {formula : driver.Formula} (elaborated : elaborate driver query = .ok formula)
    (atoms : AtomsCovered faithful.covers formula)
    (realized : SplitsRealizedOn kindOf faithful.region faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) (inside : faithful.region decoded.val) :
    Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning driver query raw ↔
      (referenceStructure relEnv language equations).sat Env.closed
        ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := by
  constructor
  · rintro ⟨resolved, resolves, holds⟩
    have same : resolved = formula := by
      have output := (elaborate_exact driver query resolved).mpr resolves
      rw [elaborated] at output
      cases output
      rfl
    subst same
    exact (meaning_iff_sat faithful resolved atoms realized decoded inside).mp holds
  · intro holds
    exact ⟨formula, (elaborate_exact driver query formula).mp elaborated,
      (meaning_iff_sat faithful formula atoms realized decoded inside).mpr holds⟩

/-- **A proved answer of the driver-based front door is a theorem about the closed formula.** -/
theorem sat_of_session_positive (faithful : Faithful driver relEnv language positive negative equations) {query : Query}
    {formula : driver.Formula} (elaborated : elaborate driver query = .ok formula)
    (atoms : AtomsCovered faithful.covers formula)
    (realized : SplitsRealizedOn kindOf faithful.region faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) (inside : faithful.region decoded.val) {runtime : Engine driver}
    (session : NamedSession driver runtime query raw)
    (read : session.readout = .checked (.judgment (.decided true))) :
    (referenceStructure relEnv language equations).sat Env.closed
      ((ofCore positive negative kindOf true formula).subst faithful.closing) raw :=
  (queryMeaning_iff_sat faithful elaborated atoms realized decoded inside).mp (named_positive session read)

/-- **And a refuted answer refutes it.** -/
theorem not_sat_of_session_negative (faithful : Faithful driver relEnv language positive negative equations) {query : Query}
    {formula : driver.Formula} (elaborated : elaborate driver query = .ok formula)
    (atoms : AtomsCovered faithful.covers formula)
    (realized : SplitsRealizedOn kindOf faithful.region faithful.structure_ driver.backend.spatial.theory formula)
    {raw : Pattern} (decoded : driver.Decoded raw) (inside : faithful.region decoded.val) {runtime : Engine driver}
    (session : NamedSession driver runtime query raw)
    (read : session.readout = .checked (.judgment (.decided false))) :
    ¬ (referenceStructure relEnv language equations).sat Env.closed
      ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := fun holds =>
  named_negative session read ((queryMeaning_iff_sat faithful elaborated atoms realized decoded inside).mpr holds)

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

theorem splitsRealizedOn_of_spatialFree {Leaf : Type} {system : Mettapedia.GSLT.GSLT.{0}}
    {S : NativeStructure system.Term} {spatial : Mettapedia.OSLF.NativeTypes.Decision.Spatial.SpatialTheory system}
    (kindOf : ℕ → CollType) (region : system.Term → Prop) :
    ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf), spatialFree formula = true →
      SplitsRealizedOn kindOf region S spatial formula
  | .atom _, _ | .top, _ | .bottom, _ => trivial
  | .conj left right, free | .disj left right, free | .imp left right, free => by
    simp only [spatialFree, Bool.and_eq_true] at free
    exact ⟨splitsRealizedOn_of_spatialFree kindOf region left free.1,
      splitsRealizedOn_of_spatialFree kindOf region right free.2⟩
  | .neg inner, free | .possibility inner, free | .outgoingUniversal inner, free =>
    splitsRealizedOn_of_spatialFree kindOf region inner free
  | .separating _ _ _, free => by simp [spatialFree] at free

/-! ## Pulling a structure back along a rendering -/

/-- **The structure a map pulls back**: a relation holds of elements when it holds of their images. The pulled-back
structure has no application of its own, and keeps the body; a step morphism does not read it. -/
def pullback {Source Target : Type} (T : NativeStructure Target) (map : Source → Target) : NativeStructure Source where
  step source label target := T.step (map source) label (map target)
  built element constructor parts := T.built (map element) constructor (parts.map map)
  split element kind first second := T.split (map element) kind (map first) (map second)
  empty element kind := T.empty (map element) kind
  single element kind member := T.single (map element) kind (map member)
  body element inner := T.body (map element) (map inner)
  multiBody element arity inner := T.multiBody (map element) arity (map inner)
  bound element index := T.bound (map element) index
  typed element type := T.typed (map element) type
  named element term := T.named (map element) term
  same first second := T.same (map first) (map second)
  apply inner _ := inner
  inRelation element relation := T.inRelation (map element) relation

/-- **A map whose image the own steps do not leave is a step morphism** from the structure it pulls back. -/
def pullbackMorphism {Source Target : Type} (T : NativeStructure Target) (map : Source → Target)
    (image : ∀ source label target, label.isContext = false → T.step (map source) label target →
      ∃ other, map other = target) :
    StepMorphism (pullback T map) T where
  map := map
  step _ held := held
  stepBack {source label target} own held := by
    obtain ⟨other, rfl⟩ := image source label target own held
    exact ⟨other, held, rfl⟩
  sameIff _ _ := Iff.rfl
  namedIff _ _ := Iff.rfl

/-- **A map whose image the own steps and splits do not leave is a split morphism** from the structure it pulls back. -/
def pullbackSplit {Source Target : Type} (T : NativeStructure Target) (map : Source → Target)
    (stepImage : ∀ source label target, label.isContext = false → T.step (map source) label target →
      ∃ other, map other = target)
    (splitImage : ∀ element kind first second, T.split (map element) kind first second →
      (∃ other, map other = first) ∧ ∃ other, map other = second) :
    SplitMorphism (pullback T map) T where
  map := map
  step _ held := held
  stepBack {source label target} own held := by
    obtain ⟨other, rfl⟩ := stepImage source label target own held
    exact ⟨other, held, rfl⟩
  split held := held
  splitBack {element kind first second} held := by
    obtain ⟨⟨left, rfl⟩, ⟨right, rfl⟩⟩ := splitImage element kind first second held
    exact ⟨left, right, held, rfl, rfl⟩

variable (driver relEnv language positive negative) in
/-- **A faithful reading by steps**: as `Faithful`, with a step morphism in place of a split morphism, for formulas
without separating conjunctions. -/
structure FaithfulSteps (equations : LanguageReading := .syntax) where
  structure_ : NativeStructure driver.system.Term
  region : driver.system.Term → Prop
  steps : ∀ source, region source → ∀ target, (structure_.step source .any target ↔ driver.system.Step source target)
  closed : ∀ source target, region source → driver.system.Step source target → region target
  rendering : StepMorphism structure_ (referenceStructure relEnv language equations)
  renders : rendering.map = driver.render
  covers : driver.Leaf → Prop
  test : driver.Leaf → Formula 0
  testAgrees : ∀ leaf, covers leaf → ∀ source, region source → ((driver.tests leaf).predicate.1 source ↔
    (referenceStructure relEnv language equations).sat Env.closed (test leaf) (driver.render source))
  closing : Fin m → Formula 0
  closesPositive : ∀ leaf, closing (positive leaf) = test leaf
  closesNegative : ∀ leaf, closing (negative leaf) = (test leaf).dual
  closingForward : ∀ index, (closing index).forward = true

/-- **The meaning of a formula without separating conjunctions is the truth of its closed formula**, along a faithful
reading by steps, at a decoded request in the region. -/
theorem meaning_iff_sat_steps (faithful : FaithfulSteps driver relEnv language positive negative equations)
    (formula : driver.Formula) (atoms : AtomsCovered faithful.covers formula) (free : spatialFree formula = true)
    {raw : Pattern} (decoded : driver.Decoded raw)
    (inside : faithful.region decoded.val) :
    Meaning driver formula raw ↔
      (referenceStructure relEnv language equations).sat Env.closed
        ((ofCore positive negative kindOf true formula).subst faithful.closing) raw := by
  let reference := referenceStructure relEnv language equations
  let targetEnv : Env Pattern m := fun index => {term | reference.sat Env.closed (faithful.closing index) term}
  let sourceEnv : Env driver.system.Term m := fun index => faithful.rendering.map ⁻¹' targetEnv index
  have related : faithful.rendering.EnvPreimage sourceEnv targetEnv := fun _ _ => Iff.rfl
  have onPositive : ∀ leaf, faithful.covers leaf → ∀ term, faithful.region term →
      (term ∈ sourceEnv (positive leaf) ↔ (driver.tests leaf).predicate.1 term) := by
    intro leaf covered term within
    show reference.sat Env.closed (faithful.closing (positive leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesPositive, faithful.renders, faithful.testAgrees leaf covered term within]
  have onNegative : ∀ leaf, faithful.covers leaf → ∀ term, faithful.region term →
      (term ∈ sourceEnv (negative leaf) ↔ ¬ (driver.tests leaf).predicate.1 term) := by
    intro leaf covered term within
    show reference.sat Env.closed (faithful.closing (negative leaf)) (faithful.rendering.map term) ↔ _
    rw [faithful.closesNegative, reference.sat_dual_closed, faithful.renders,
      faithful.testAgrees leaf covered term within]
  have embedded := sat_ofCore_on (positive := positive) (negative := negative) (kindOf := kindOf) driver.tests
    driver.backend.spatial.theory faithful.region faithful.covers faithful.steps faithful.closed onPositive onNegative
    formula true atoms (splitsRealizedOn_of_spatialFree kindOf faithful.region formula free) decoded.val inside
  have transported := faithful.rendering.sat_iff (ofCore positive negative kindOf true formula)
    (behavioural_ofCore positive negative kindOf formula free true) related decoded.val
  have mapped : faithful.rendering.map decoded.val = raw := by
    rw [faithful.renders]
    exact decoded.property.2
  rw [meaning_at_decoded driver formula raw decoded, reference.sat_close]
  refine (embedded.symm.trans transported).trans ?_
  rw [mapped]

/-- **Along a faithful reading by steps, the generated front door decides every formula without separating
conjunctions** at a request in the region whose closure is finite, in an equation-free language, and its answer is
the formula's meaning. -/
theorem ask_decides_driver_steps (faithful : FaithfulSteps driver relEnv language positive negative equations)
    (formula : driver.Formula) (atoms : AtomsCovered faithful.covers formula) (free : spatialFree formula = true)
    {raw : Pattern} (decoded : driver.Decoded raw)
    (inside : faithful.region decoded.val)
    (equationFree : language.isEquationFree = true) {closure : List Pattern}
    (bounded : Closure relEnv language fuel raw closure) {rounds : ℕ} (enoughRounds : closure.length ≤ rounds)
    (hint : Option CertificateCandidate) (reference : equations.rules = .reference := by rfl) :
    ∃ evidence,
      (ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing) raw
          hint rounds = .proved evidence ∧ Meaning driver formula raw) ∨
        (ask relEnv signature language fuel ((ofCore positive negative kindOf true formula).subst faithful.closing)
          raw hint rounds = .refuted evidence ∧ ¬ Meaning driver formula raw) := by
  obtain ⟨evidence, answered⟩ := ask_decides (signature := signature) equationFree bounded
    (forward_subst faithful.closing _ faithful.closingForward (forward_ofCore positive negative kindOf formula true))
    enoughRounds hint
  refine ⟨evidence, answered.imp (fun proved => ⟨proved, ?_⟩) (fun refuted => ⟨refuted, ?_⟩)⟩
  · exact (meaning_iff_sat_steps faithful formula atoms free decoded inside).mpr
      (ask_proved_in (formsFor_none reference) proved)
  · exact fun holds => ask_refuted_in (formsFor_none reference) refuted
      ((meaning_iff_sat_steps faithful formula atoms free decoded inside).mp holds)

/-! ## Readings, and the two front doors -/

variable (driver relEnv language positive negative kindOf) in
/-- **A reading of a driver's formulas**: on a region, the meaning of a formula the reading admits, whose atoms it
covers, is the truth of its closed formula. Faithful readings are readings: by steps, of the formulas without
separating conjunctions (`FaithfulSteps.reading`); by split morphisms, of those as well (`Faithful.reading`), and of
every formula when the structure realizes the spatial theory's splits for every formula (`Faithful.readingAll`). -/
structure Reading (equations : LanguageReading := .syntax) where
  region : driver.system.Term → Prop
  covers : driver.Leaf → Prop
  admits : driver.Formula → Bool
  closing : Fin m → Formula 0
  closingForward : ∀ index, (closing index).forward = true
  meaning : ∀ formula, AtomsCovered covers formula → admits formula = true → ∀ {raw : Pattern}
    (decoded : driver.Decoded raw), region decoded.val →
      (Meaning driver formula raw ↔ (referenceStructure relEnv language equations).sat Env.closed
        ((ofCore positive negative kindOf true formula).subst closing) raw)

/-- A faithful reading is a reading of the formulas without separating conjunctions. -/
def Faithful.reading (faithful : Faithful driver relEnv language positive negative equations) :
    Reading driver relEnv language positive negative kindOf equations where
  region := faithful.region
  covers := faithful.covers
  admits := spatialFree
  closing := faithful.closing
  closingForward := faithful.closingForward
  meaning formula atoms spatial _ decoded inside :=
    meaning_iff_sat faithful formula atoms (splitsRealizedOn_of_spatialFree kindOf _ formula spatial) decoded inside

/-- **A faithful reading whose structure realizes the spatial theory's splits for every formula reads every
formula.** -/
def Faithful.readingAll (faithful : Faithful driver relEnv language positive negative equations)
    (realized : ∀ formula : driver.Formula,
      SplitsRealizedOn kindOf faithful.region faithful.structure_ driver.backend.spatial.theory formula) :
    Reading driver relEnv language positive negative kindOf equations where
  region := faithful.region
  covers := faithful.covers
  admits _ := true
  closing := faithful.closing
  closingForward := faithful.closingForward
  meaning formula atoms _ _ decoded inside := meaning_iff_sat faithful formula atoms (realized formula) decoded inside

/-- A faithful reading by steps is a reading of the formulas without separating conjunctions. -/
def FaithfulSteps.reading (faithful : FaithfulSteps driver relEnv language positive negative equations) :
    Reading driver relEnv language positive negative kindOf equations where
  region := faithful.region
  covers := faithful.covers
  admits := spatialFree
  closing := faithful.closing
  closingForward := faithful.closingForward
  meaning formula atoms spatial _ decoded inside := meaning_iff_sat_steps faithful formula atoms spatial decoded inside

/-- **The closed formula of a query** along a reading: its elaboration, embedded, with each test's formula for its
atom, when the reading admits it. -/
def closedFormula (reading : Reading driver relEnv language positive negative kindOf equations) (query : Query) :
    Option (Formula 0) :=
  match elaborate driver query with
  | .ok formula =>
    if reading.admits formula then some ((ofCore positive negative kindOf true formula).subst reading.closing) else none
  | .error _ => none

theorem closedFormula_some {reading : Reading driver relEnv language positive negative kindOf equations}
    {query : Query}
    {closed : Formula 0} (found : closedFormula reading query = some closed) :
    ∃ formula, elaborate driver query = .ok formula ∧ reading.admits formula = true ∧
      closed = (ofCore positive negative kindOf true formula).subst reading.closing := by
  unfold closedFormula at found
  split at found
  · rename_i formula elaborated
    split_ifs at found with spatial
    exact ⟨formula, elaborated, spatial, (Option.some.inj found).symm⟩
  · cases found

/-- **A query means its closed formula** at a decoded request in the region, when the reading covers every test a
name looks up. -/
theorem queryMeaning_iff (reading : Reading driver relEnv language positive negative kindOf equations)
    (covered : ∀ name leaf, driver.lookup name = some leaf → reading.covers leaf) {query : Query}
    {closed : Formula 0} (found : closedFormula reading query = some closed) {raw : Pattern}
    (decoded : driver.Decoded raw) (inside : reading.region decoded.val) :
    Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning driver query raw ↔
      (referenceStructure relEnv language equations).sat Env.closed closed raw := by
  obtain ⟨formula, elaborated, spatial, rfl⟩ := closedFormula_some found
  have atoms : AtomsCovered reading.covers formula :=
    AtomsCovered.mono (fun leaf ⟨name, lookup⟩ => covered name leaf lookup)
      (atomsCovered_of_resolves ((elaborate_exact driver query formula).mp elaborated))
  rw [← reading.meaning formula atoms spatial decoded inside]
  constructor
  · rintro ⟨resolved, resolves, holds⟩
    have output := (elaborate_exact driver query resolved).mpr resolves
    rw [elaborated] at output
    cases output
    exact holds
  · exact fun holds => ⟨formula, (elaborate_exact driver query formula).mp elaborated, holds⟩

/-- **A decided answer of the driver-based front door is the truth of the query's closed formula.** -/
theorem decided_iff (reading : Reading driver relEnv language positive negative kindOf equations)
    (covered : ∀ name leaf, driver.lookup name = some leaf → reading.covers leaf) {query : Query}
    {closed : Formula 0} (found : closedFormula reading query = some closed) {raw : Pattern}
    (decoded : driver.Decoded raw) (inside : reading.region decoded.val) {runtime : Engine driver}
    (session : NamedSession driver runtime query raw) {answer : Bool}
    (read : session.readout = .checked (.judgment (.decided answer))) :
    (referenceStructure relEnv language equations).sat Env.closed closed raw ↔ answer = true := by
  rw [← queryMeaning_iff reading covered found decoded inside]
  cases answer with
  | true => exact iff_of_true (named_positive session read) rfl
  | false => exact iff_of_false (named_negative session read) Bool.false_ne_true

/-- **The two front doors agree**: when the generated front door proves the query's closed formula, a decided answer
of the driver-based front door is yes. -/
theorem decided_of_ask_proved (reading : Reading driver relEnv language positive negative kindOf equations)
    (covered : ∀ name leaf, driver.lookup name = some leaf → reading.covers leaf) {query : Query}
    {closed : Formula 0} (found : closedFormula reading query = some closed) {raw : Pattern}
    (decoded : driver.Decoded raw) (inside : reading.region decoded.val)
    {hint : Option CertificateCandidate} {rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}
    (compatible : FormsFor forms equations) {evidence : Evidence}
    (answered : ask relEnv signature language fuel closed raw hint rounds forms = .proved evidence)
    {runtime : Engine driver} (session : NamedSession driver runtime query raw) {answer : Bool}
    (read : session.readout = .checked (.judgment (.decided answer))) : answer = true :=
  (decided_iff reading covered found decoded inside session read).mp (ask_proved_in compatible answered)

/-- **And when it refutes the closed formula, a decided answer is no.** -/
theorem decided_of_ask_refuted (reading : Reading driver relEnv language positive negative kindOf equations)
    (covered : ∀ name leaf, driver.lookup name = some leaf → reading.covers leaf) {query : Query}
    {closed : Formula 0} (found : closedFormula reading query = some closed) {raw : Pattern}
    (decoded : driver.Decoded raw) (inside : reading.region decoded.val)
    {hint : Option CertificateCandidate} {rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}
    (compatible : FormsFor forms equations) {evidence : Evidence}
    (answered : ask relEnv signature language fuel closed raw hint rounds forms = .refuted evidence)
    {runtime : Engine driver} (session : NamedSession driver runtime query raw) {answer : Bool}
    (read : session.readout = .checked (.judgment (.decided answer))) : answer = false := by
  cases answer with
  | false => rfl
  | true =>
    exact absurd ((decided_iff reading covered found decoded inside session read).mpr rfl)
      (ask_refuted_in compatible answered)

/-! ## Finitely many tests at a time

A driver may have infinitely many tests, as the answer-bag driver has a singleton test for every payload. A formula
names finitely many of them (`leaves`), and a table of those (`LeafTable`) gives each its positive and negative
variable and closing formulas, with a default variable for every other test. -/

/-- The tests a formula names. -/
def leaves {Leaf : Type} : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf → List Leaf
  | .atom leaf => [leaf]
  | .top | .bottom => []
  | .conj left right | .disj left right | .imp left right | .separating _ left right => leaves left ++ leaves right
  | .neg inner | .possibility inner | .outgoingUniversal inner => leaves inner

/-- **A formula's atoms are covered by any predicate that holds of the tests it names.** -/
theorem atomsCovered_of_leaves {Leaf : Type} {covered : Leaf → Prop} :
    ∀ (formula : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Formula Leaf),
      (∀ leaf ∈ leaves formula, covered leaf) → AtomsCovered covered formula
  | .atom leaf, holds => holds leaf (List.mem_singleton_self leaf)
  | .top, _ | .bottom, _ => trivial
  | .conj left right, holds | .disj left right, holds | .imp left right, holds | .separating _ left right, holds =>
    ⟨atomsCovered_of_leaves left fun leaf member => holds leaf (List.mem_append_left _ member),
      atomsCovered_of_leaves right fun leaf member => holds leaf (List.mem_append_right _ member)⟩
  | .neg inner, holds | .possibility inner, holds | .outgoingUniversal inner, holds =>
    atomsCovered_of_leaves inner holds

namespace LeafTable

variable {Leaf : Type} [DecidableEq Leaf] (used : List Leaf)

/-- The number of variables: a positive and a negative one for each listed test and for a default. -/
def width : ℕ := 2 * (used.length + 1)

/-- A test's positive variable: its place in the list, the default past it for an unlisted test. -/
def positiveIndex (leaf : Leaf) : Fin (width used) :=
  ⟨used.idxOf leaf, by have := List.idxOf_le_length (a := leaf) (l := used); unfold width; omega⟩

/-- A test's negative variable. -/
def negativeIndex (leaf : Leaf) : Fin (width used) :=
  ⟨used.length + 1 + used.idxOf leaf, by have := List.idxOf_le_length (a := leaf) (l := used); unfold width; omega⟩

variable (formulaOf : Leaf → Formula 0)

/-- The formula at a place of the list; `⊤` past it. -/
def formulaAt (place : ℕ) : Formula 0 := if bound : place < used.length then formulaOf used[place] else .top

/-- A test's formula: the formula at its place. -/
def test (leaf : Leaf) : Formula 0 := formulaAt used formulaOf (used.idxOf leaf)

/-- The closing formulas: the formulas at the places, then their duals. -/
def closing (index : Fin (width used)) : Formula 0 :=
  if index.val < used.length + 1 then formulaAt used formulaOf index.val
  else (formulaAt used formulaOf (index.val - (used.length + 1))).dual

theorem closesPositive (leaf : Leaf) : closing used formulaOf (positiveIndex used leaf) = test used formulaOf leaf := by
  have := List.idxOf_le_length (a := leaf) (l := used)
  unfold closing positiveIndex test
  rw [if_pos (by simp only; omega)]

theorem closesNegative (leaf : Leaf) :
    closing used formulaOf (negativeIndex used leaf) = (test used formulaOf leaf).dual := by
  unfold closing negativeIndex test
  rw [if_neg (by simp only; omega)]
  simp only [Nat.add_sub_cancel_left]

omit [DecidableEq Leaf] in
theorem closingForward (forward : ∀ leaf ∈ used, (formulaOf leaf).forward = true) (index : Fin (width used)) :
    (closing used formulaOf index).forward = true := by
  have atForward : ∀ place, (formulaAt used formulaOf place).forward = true := fun place => by
    unfold formulaAt
    split
    · exact forward _ (List.getElem_mem _)
    · rfl
  unfold closing
  split
  · exact atForward _
  · rw [Formula.forward_dual]
    exact atForward _

/-- **A listed test's formula is its own.** -/
theorem test_of_mem {leaf : Leaf} (member : leaf ∈ used) : test used formulaOf leaf = formulaOf leaf := by
  unfold test formulaAt
  rw [dif_pos (List.idxOf_lt_length_of_mem member), List.getElem_idxOf]

end LeafTable

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings
