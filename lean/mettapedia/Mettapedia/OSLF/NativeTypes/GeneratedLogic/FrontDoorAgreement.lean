import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DriverBridge
import Mettapedia.OSLF.NativeTypes.Executable

/-!
# Both front doors, on installed drivers

An installed driver answers a query through the runtime (`Executable.ask`); a reading of the driver turns the query into
a closed generated formula (`Embeddings.closedFormula`), which the generated front door answers (`frontDoor`), with a
certified decider such as a presentation decider when one is given (`frontDoorWith`). The two agree (`Agrees`): every
decided readout of the runtime, at every budget, is the generated front door's answer (`agrees_of_frontDoor`,
`agrees_of_frontDoorWith`), since both are the truth of the closed formula.

**One front door.** Through a reading the runtime is a certified decider of the generated front door: for one query
(`queryDecider`), or for every closed formula that reads back as the closed formula of a query (`runtimeDecider`). The
generated front door with the runtime as its first strategy (`askThrough`) answers as the runtime does wherever the
runtime decides (`askThrough_of_decided`), keeps that answer under more budget (`askThrough_mono`), falls back to its
own strategies elsewhere, and its answers are the query's meaning (`askThrough_proved`, `askThrough_refuted`).

**Driver formulas.** A driver formula asked of the runtime directly has its closed formula along a reading that admits
it (`closedOf`), answered by the generated front door (`frontDoorOn`); the two agree (`agreesOn_of_frontDoorOn`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver)

variable {driver : Driver} {relEnv : RelationEnv} {language : LanguageDef} {m : ℕ}
  {positive negative : driver.Leaf → Fin m} {kindOf : ℕ → CollType} {equations : LanguageReading}

/-- **The generated front door's answer** about a query's closed formula along a reading. -/
def frontDoor (reading : Embeddings.Reading driver relEnv language positive negative kindOf equations)
    (signature : Mettapedia.OSLF.Framework.FiniteModels.Signature) (fuel : ℕ) (query : Query) (raw : Pattern)
    (rounds : ℕ) (forms : Option (CanonicalForms relEnv language fuel) := none) : Option Bool :=
  (Embeddings.closedFormula reading query).bind fun closed =>
    match ask relEnv signature language fuel closed raw none rounds forms with
    | .proved _ => some true
    | .refuted _ => some false
    | .unknown _ => none

theorem frontDoor_sound {reading : Embeddings.Reading driver relEnv language positive negative kindOf equations}
    {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel : ℕ} {query : Query} {raw : Pattern}
    {rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)} (compatible : FormsFor forms equations)
    {answer : Bool} (answered : frontDoor reading signature fuel query raw rounds forms = some answer) :
    ∃ closed, Embeddings.closedFormula reading query = some closed ∧
      ((referenceStructure relEnv language equations).sat Env.closed closed raw ↔ answer = true) := by
  unfold frontDoor at answered
  cases found : Embeddings.closedFormula reading query with
  | none => rw [found] at answered; cases answered
  | some closed =>
    rw [found, Option.bind_some] at answered
    refine ⟨closed, rfl, ?_⟩
    split at answered
    · rename_i evidence proved
      cases answered
      exact iff_of_true (ask_proved_in compatible proved) rfl
    · rename_i evidence refuted
      cases answered
      exact iff_of_false (ask_refuted_in compatible refuted) Bool.false_ne_true
    · cases answered

/-- **The runtime agrees with an answer** about a query at a request: every decided readout, at every budget, is it. -/
def Agrees (installed : Installed) (query : Query) (raw : Pattern) (answer : Bool) : Prop :=
  ∀ budget runtimeAnswer, (Mettapedia.OSLF.NativeTypes.Executable.ask installed query raw budget).readout =
    .checked (.judgment (.decided runtimeAnswer)) → runtimeAnswer = answer

/-- **Along a reading covering the tests names look up, the runtime agrees with the generated front door.** -/
theorem agrees_of_frontDoor (installed : Installed) {m : ℕ} {positive negative : installed.native.Leaf → Fin m}
    (reading : Embeddings.Reading installed.native relEnv language positive negative kindOf equations)
    (covered : ∀ name leaf, installed.native.lookup name = some leaf → reading.covers leaf) {query : Query}
    {raw : Pattern} (decoded : installed.native.Decoded raw) (inside : reading.region decoded.val)
    {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} (compatible : FormsFor forms equations) {answer : Bool}
    (answered : frontDoor reading signature fuel query raw rounds forms = some answer) :
    Agrees installed query raw answer := by
  intro budget runtimeAnswer read
  obtain ⟨closed, found, meaning⟩ := frontDoor_sound compatible answered
  have runtime := Embeddings.decided_iff reading covered found decoded inside
    (Mettapedia.OSLF.NativeTypes.Executable.ask installed query raw budget) read
  cases answer <;> cases runtimeAnswer <;> simp_all

/-! ## With a certified decider -/

/-- **The generated front door with a certified decider**, such as a presentation decider: the decider's answer about
the query's closed formula when it gives one, and otherwise the generated front door's. -/
def frontDoorWith (reading : Embeddings.Reading driver relEnv language positive negative kindOf equations)
    (decider : Decider relEnv language equations) (signature : Mettapedia.OSLF.Framework.FiniteModels.Signature)
    (fuel : ℕ) (query : Query) (raw : Pattern) (rounds : ℕ)
    (forms : Option (CanonicalForms relEnv language fuel) := none) : Option Bool :=
  (Embeddings.closedFormula reading query).bind fun closed =>
    match askWith relEnv signature language fuel closed raw decider none rounds forms with
    | .proved _ => some true
    | .refuted _ => some false
    | .unknown _ => none

theorem frontDoorWith_sound {reading : Embeddings.Reading driver relEnv language positive negative kindOf equations}
    {decider : Decider relEnv language equations} {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature}
    {fuel : ℕ} {query : Query} {raw : Pattern} {rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}
    (compatible : FormsFor forms equations) {answer : Bool}
    (answered : frontDoorWith reading decider signature fuel query raw rounds forms = some answer) :
    ∃ closed, Embeddings.closedFormula reading query = some closed ∧
      ((referenceStructure relEnv language equations).sat Env.closed closed raw ↔ answer = true) := by
  unfold frontDoorWith at answered
  cases found : Embeddings.closedFormula reading query with
  | none => rw [found] at answered; cases answered
  | some closed =>
    rw [found, Option.bind_some] at answered
    refine ⟨closed, rfl, ?_⟩
    split at answered
    · rename_i evidence proved
      cases answered
      exact iff_of_true (askWith_proved compatible proved) rfl
    · rename_i evidence refuted
      cases answered
      exact iff_of_false (askWith_refuted compatible refuted) Bool.false_ne_true
    · cases answered

/-- **Along a reading covering the tests names look up, the runtime agrees with the generated front door and its
certified decider.** -/
theorem agrees_of_frontDoorWith (installed : Installed) {m : ℕ} {positive negative : installed.native.Leaf → Fin m}
    (reading : Embeddings.Reading installed.native relEnv language positive negative kindOf equations)
    (covered : ∀ name leaf, installed.native.lookup name = some leaf → reading.covers leaf)
    (decider : Decider relEnv language equations) {query : Query}
    {raw : Pattern} (decoded : installed.native.Decoded raw) (inside : reading.region decoded.val)
    {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} (compatible : FormsFor forms equations) {answer : Bool}
    (answered : frontDoorWith reading decider signature fuel query raw rounds forms = some answer) :
    Agrees installed query raw answer := by
  intro budget runtimeAnswer read
  obtain ⟨closed, found, meaning⟩ := frontDoorWith_sound compatible answered
  have runtime := Embeddings.decided_iff reading covered found decoded inside
    (Mettapedia.OSLF.NativeTypes.Executable.ask installed query raw budget) read
  cases answer <;> cases runtimeAnswer <;> simp_all

/-! ## Driver formulas

A driver formula is asked of the runtime directly (`Executable.search`). Along a reading that admits it and covers its
tests, its closed formula (`closedOf`) is answered by the generated front door (`frontDoorOn`), and the two agree
(`agreesOn_of_frontDoorOn`). -/

/-- **The closed formula of a driver formula** along a reading. -/
def closedOf (reading : Embeddings.Reading driver relEnv language positive negative kindOf equations)
    (formula : driver.Formula) : Formula 0 :=
  (Embeddings.ofCore positive negative kindOf true formula).subst reading.closing

/-- **The runtime agrees with an answer** about a driver formula at a request: every decided readout of its search, at
every budget, is it. -/
def AgreesOn (installed : Installed) (formula : installed.native.Formula) (raw : Pattern) (answer : Bool) : Prop :=
  ∀ budget runtimeAnswer, (Mettapedia.OSLF.NativeTypes.Executable.search installed formula raw budget).readout =
    .judgment (.decided runtimeAnswer) → runtimeAnswer = answer

/-- **The generated front door with a certified decider**, on a driver formula's closed formula. -/
def frontDoorOn (reading : Embeddings.Reading driver relEnv language positive negative kindOf equations)
    (decider : Decider relEnv language equations) (signature : Mettapedia.OSLF.Framework.FiniteModels.Signature)
    (fuel : ℕ) (formula : driver.Formula) (raw : Pattern) (rounds : ℕ)
    (forms : Option (CanonicalForms relEnv language fuel) := none) : Option Bool :=
  match askWith relEnv signature language fuel (closedOf reading formula) raw decider none rounds forms with
  | .proved _ => some true
  | .refuted _ => some false
  | .unknown _ => none

/-- **Along a reading that admits a driver formula and covers its tests, the runtime agrees with the generated front
door and its certified decider.** -/
theorem agreesOn_of_frontDoorOn (installed : Installed) {m : ℕ} {positive negative : installed.native.Leaf → Fin m}
    (reading : Embeddings.Reading installed.native relEnv language positive negative kindOf equations)
    (decider : Decider relEnv language equations) (formula : installed.native.Formula)
    (atoms : Embeddings.AtomsCovered reading.covers formula) (admitted : reading.admits formula = true)
    {raw : Pattern} (decoded : installed.native.Decoded raw) (inside : reading.region decoded.val)
    {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} (compatible : FormsFor forms equations) {answer : Bool}
    (answered : frontDoorOn reading decider signature fuel formula raw rounds forms = some answer) :
    AgreesOn installed formula raw answer := by
  intro budget runtimeAnswer read
  have meaning := reading.meaning formula atoms admitted decoded inside
  have front : (referenceStructure relEnv language equations).sat Env.closed (closedOf reading formula) raw ↔
      answer = true := by
    unfold frontDoorOn at answered
    split at answered
    · rename_i evidence proved
      cases answered
      exact iff_of_true (askWith_proved compatible proved) rfl
    · rename_i evidence refuted
      cases answered
      exact iff_of_false (askWith_refuted compatible refuted) Bool.false_ne_true
    · cases answered
  cases runtimeAnswer with
  | true =>
    exact (front.mp (meaning.mp (Mettapedia.OSLF.NativeTypes.Executable.search_positive installed formula raw budget
      read))).symm
  | false =>
    cases answer with
    | false => rfl
    | true =>
      exact absurd (meaning.mpr (front.mpr rfl))
        (Mettapedia.OSLF.NativeTypes.Executable.search_negative installed formula raw budget read)

/-! ## The runtime as a strategy of the generated front door -/

/-- A decided judgment of a named session comes from a decoded request. -/
theorem decoded_of_judgment {driver : Driver} {runtime : Mettapedia.OSLF.NativeTypes.Runtime.Engine driver}
    {query : Query} {raw : Pattern} (session : Mettapedia.OSLF.NativeTypes.Runtime.NamedSession driver runtime query raw)
    {judgment : Mettapedia.OSLF.NativeTypes.Generation.CheckResult} (read : session.readout = .checked (.judgment judgment)) :
    Nonempty (driver.Decoded raw) := by
  cases session with
  | unknownConstructor name => cases read
  | checked formula resolved inner =>
    cases inner with
    | refusedSource reason => cases read
    | refusedFormula source _ => exact ⟨source⟩
    | rejectedCube source => exact ⟨source⟩
    | unresolvedCube source => exact ⟨source⟩
    | running source _ => exact ⟨source⟩

/-- The decided answer of a runtime readout. -/
def decidedAnswer : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout → Option Bool
  | .checked (.judgment (.decided answer)) => some answer
  | _ => none

theorem decidedAnswer_eq_some {readout : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout} {answer : Bool}
    (decided : decidedAnswer readout = some answer) : readout = .checked (.judgment (.decided answer)) := by
  unfold decidedAnswer at decided
  split at decided
  · cases decided
    rfl
  · cases decided

variable (installed : Installed) {m : ℕ} {positive negative : installed.native.Leaf → Fin m}
  (reading : Embeddings.Reading installed.native relEnv language positive negative kindOf equations)
  (covered : ∀ name leaf, installed.native.lookup name = some leaf → reading.covers leaf)
  (inside : ∀ {raw : Pattern} (decoded : installed.native.Decoded raw), reading.region decoded.val)

/-- **The runtime, for one query, as a certified decider**: at the query's closed formula it answers what the runtime
decides within the budget. -/
def queryDecider (query : Query) (budget : ℕ) : Decider relEnv language equations where
  decide formula raw :=
    if Embeddings.closedFormula reading query = some formula then
      decidedAnswer (Mettapedia.OSLF.NativeTypes.Executable.ask installed query raw budget).readout
    else none
  exact := by
    intro formula raw answer decided
    split_ifs at decided with found
    have read := decidedAnswer_eq_some decided
    obtain ⟨decoded⟩ := decoded_of_judgment _ read
    exact Embeddings.decided_iff reading covered found decoded (inside decoded) _ read

/-- Read a closed formula back as a query, in negation normal form. -/
def readQuery : {n : ℕ} → Formula n → Option Query
  | _, .top => some .top
  | _, .bot => some .bottom
  | _, .and left right => do some (.conj (← readQuery left) (← readQuery right))
  | _, .or left right => do some (.disj (← readQuery left) (← readQuery right))
  | _, .possibly .any inner => do some (.possibility (← readQuery inner))
  | _, .necessarily .any inner => do some (.outgoingUniversal (← readQuery inner))
  | _, .built label _ => some (.constructor label)
  | _, .everyBuilt label _ => some (.neg (.constructor label))
  | _, _ => none

/-- **The runtime as a certified decider of the generated front door**: a closed formula that reads back as the closed
formula of a query is answered as the runtime answers the query within the budget. -/
def runtimeDecider (budget : ℕ) : Decider relEnv language equations where
  decide formula raw :=
    match readQuery formula with
    | some query => (queryDecider installed reading covered inside query budget).decide formula raw
    | none => none
  exact := by
    intro formula raw answer decided
    split at decided
    · exact (queryDecider installed reading covered inside _ budget).exact decided
    · cases decided

/-- **The generated front door with the runtime as its first strategy.** -/
def askThrough (signature : Mettapedia.OSLF.Framework.FiniteModels.Signature) (fuel : ℕ) (query : Query) (raw : Pattern)
    (budget rounds : ℕ) (forms : Option (CanonicalForms relEnv language fuel) := none) : Answer :=
  match Embeddings.closedFormula reading query with
  | some closed =>
    askWith relEnv signature language fuel closed raw (queryDecider installed reading covered inside query budget) none
      rounds forms
  | none => .unknown rounds

variable {installed reading covered inside}
variable {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {fuel : ℕ} {query : Query} {raw : Pattern}
  {budget rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}

/-- **Where the runtime decides, the one front door answers as it does.** -/
theorem askThrough_of_decided {closed : Formula 0} (found : Embeddings.closedFormula reading query = some closed)
    {answer : Bool} (read : (Mettapedia.OSLF.NativeTypes.Executable.ask installed query raw budget).readout =
      .checked (.judgment (.decided answer))) :
    askThrough installed reading covered inside signature fuel query raw budget rounds forms =
      if answer then .proved .decided else .refuted .decided := by
  unfold askThrough askWith
  rw [found]
  simp only [queryDecider, found, if_true, read, decidedAnswer]
  cases answer <;> rfl

/-- **More budget keeps the runtime's answer.** -/
theorem askThrough_mono {closed : Formula 0} (found : Embeddings.closedFormula reading query = some closed)
    {answer : Bool} (read : (Mettapedia.OSLF.NativeTypes.Executable.ask installed query raw budget).readout =
      .checked (.judgment (.decided answer))) {more : ℕ} (enough : budget ≤ more) :
    askThrough installed reading covered inside signature fuel query raw more rounds forms =
      askThrough installed reading covered inside signature fuel query raw budget rounds forms := by
  rw [askThrough_of_decided found read,
    askThrough_of_decided found (Mettapedia.OSLF.NativeTypes.Executable.ask_conclusive_mono installed query raw answer
      read enough)]

/-- **A proved answer of the one front door is the query's meaning**, at a decoded request. -/
theorem askThrough_proved (compatible : FormsFor forms equations) {evidence : Evidence}
    (answered : askThrough installed reading covered inside signature fuel query raw budget rounds forms =
      .proved evidence)
    (decoded : installed.native.Decoded raw) :
    Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning installed.native query raw := by
  unfold askThrough at answered
  split at answered
  · rename_i closed found
    exact (Embeddings.queryMeaning_iff reading covered found decoded (inside decoded)).mpr
      (askWith_proved compatible answered)
  · cases answered

/-- **And a refuted answer is not.** -/
theorem askThrough_refuted (compatible : FormsFor forms equations) {evidence : Evidence}
    (answered : askThrough installed reading covered inside signature fuel query raw budget rounds forms =
      .refuted evidence)
    (decoded : installed.native.Decoded raw) :
    ¬ Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning installed.native query raw := by
  unfold askThrough at answered
  split at answered
  · rename_i closed found
    exact fun holds => askWith_refuted compatible answered
      ((Embeddings.queryMeaning_iff reading covered found decoded (inside decoded)).mp holds)
  · cases answered

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
