import Mathlib.Init
import Mathlib.Data.Fintype.Card

/-!
# Finite-letter closure interfaces for corridor pumping

The corridor argument reads a literal word from left to right.  Once its
prefix is fixed, deleting a repeated middle block needs only preservation of
the right future language; equality of the complete reachable subsets is
stronger than necessary.  This file proves that one-sided statement and its
standard forward-simulation sufficient condition.

The file also records the other two proof-relevant boundaries of the finite
closure computation:

* a rooted, port-ordered factorization of literal cells through a finite code;
* a sparse CSR replay certificate whose entries are both locally witnessed and
  exhaustive.

No numerical closure table is asserted here.  A source-specific development
must still construct the rooted codes, prove transition invariance, and supply
the replayed rows.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteClosureInterfaces

universe uState uLetter uCarrier uReceipt uCode uWitness

section OneSidedPumping

variable {State : Type uState} {Letter : Type uLetter}

/-- A run of a word in a relational transition system. -/
def Run (transition : Letter → State → State → Prop) :
    List Letter → State → State → Prop
  | [], start, finish => start = finish
  | letter :: suffix, start, finish =>
      ∃ middle, transition letter start middle ∧
        Run transition suffix middle finish

theorem run_append_iff (transition : Letter → State → State → Prop)
    (preword suffix : List Letter) (start finish : State) :
    Run transition (preword ++ suffix) start finish ↔
      ∃ middle, Run transition preword start middle ∧
        Run transition suffix middle finish := by
  induction preword generalizing start with
  | nil =>
      simp [Run]
  | cons letter preword ih =>
      simp only [List.cons_append, Run]
      constructor
      · rintro ⟨next, hstep, hrun⟩
        rcases (ih next).1 hrun with ⟨middle, hprefix, hsuffix⟩
        exact ⟨middle, ⟨next, hstep, hprefix⟩, hsuffix⟩
      · rintro ⟨middle, ⟨next, hstep, hprefix⟩, hsuffix⟩
        exact ⟨next, hstep, (ih next).2 ⟨middle, hprefix, hsuffix⟩⟩

/-- States reachable after one fixed prefix from an initial predicate. -/
def ReachableAfter (transition : Letter → State → State → Prop)
    (initial : State → Prop) (preword : List Letter) (finish : State) : Prop :=
  ∃ start, initial start ∧ Run transition preword start finish

/-- Acceptance of a suffix from a set of possible current states. -/
def Accepts (transition : Letter → State → State → Prop)
    (final : State → Prop) (current : State → Prop)
    (word : List Letter) : Prop :=
  ∃ start, current start ∧ ∃ finish,
    Run transition word start finish ∧ final finish

theorem accepts_append_iff (transition : Letter → State → State → Prop)
    (final initial : State → Prop) (preword suffix : List Letter) :
    Accepts transition final initial (preword ++ suffix) ↔
      Accepts transition final (ReachableAfter transition initial preword) suffix := by
  constructor
  · rintro ⟨start, hstart, finish, hrun, hfinish⟩
    rcases (run_append_iff transition preword suffix start finish).1 hrun with
      ⟨middle, hprefix, hsuffix⟩
    exact ⟨middle, ⟨start, hstart, hprefix⟩, finish, hsuffix, hfinish⟩
  · rintro ⟨middle, ⟨start, hstart, hprefix⟩, finish, hsuffix, hfinish⟩
    exact ⟨start, hstart, finish,
      (run_append_iff transition preword suffix start finish).2
        ⟨middle, hprefix, hsuffix⟩, hfinish⟩

/-- Inclusion of right future languages relative to the accepting predicate. -/
def RightLanguageLE (transition : Letter → State → State → Prop)
    (final : State → Prop) (source target : State → Prop) : Prop :=
  ∀ suffix, Accepts transition final source suffix →
    Accepts transition final target suffix

/-- If the state set before a removable middle block has no more accepting
right futures than the state set after it, every shortened accepting run lifts
to an accepting run of the original word. -/
theorem delete_middle_sound_of_rightLanguageLE
    (transition : Letter → State → State → Prop) (final initial : State → Prop)
    (preword middle suffix : List Letter)
    (hlanguage : RightLanguageLE transition final
      (ReachableAfter transition initial preword)
      (ReachableAfter transition initial (preword ++ middle)))
    (hshort : Accepts transition final initial (preword ++ suffix)) :
    Accepts transition final initial ((preword ++ middle) ++ suffix) := by
  apply (accepts_append_iff transition final initial (preword ++ middle) suffix).2
  apply hlanguage suffix
  exact (accepts_append_iff transition final initial preword suffix).1 hshort

/-- The older equality-based pumping premise is a special case of the
one-sided future-language theorem.  Keeping it as a corollary prevents callers
which already prove exact reachable-set equality from maintaining a second
deletion proof. -/
theorem delete_middle_sound_of_reachableAfter_eq
    (transition : Letter → State → State → Prop) (final initial : State → Prop)
    (preword middle suffix : List Letter)
    (hequal : ReachableAfter transition initial preword =
      ReachableAfter transition initial (preword ++ middle))
    (hshort : Accepts transition final initial (preword ++ suffix)) :
    Accepts transition final initial ((preword ++ middle) ++ suffix) := by
  apply delete_middle_sound_of_rightLanguageLE transition final initial
    preword middle suffix
  · intro rightWord haccepts
    rw [← hequal]
    exact haccepts
  · exact hshort

/-- A pointwise forward simulation preserves accepting states and can match
every literal transition. -/
structure ForwardSimulation (transition : Letter → State → State → Prop)
    (final : State → Prop) (simulates : State → State → Prop) : Prop where
  final_preserved : ∀ ⦃source target⦄,
    simulates source target → final source → final target
  step_preserved : ∀ letter ⦃source target source'⦄,
    simulates source target → transition letter source source' →
      ∃ target', transition letter target target' ∧ simulates source' target'

theorem ForwardSimulation.run_preserved
    {transition : Letter → State → State → Prop} {final : State → Prop}
    {simulates : State → State → Prop}
    (simulation : ForwardSimulation transition final simulates)
    {word : List Letter} {source target source' : State}
    (hsimulates : simulates source target)
    (hrun : Run transition word source source') :
    ∃ target', Run transition word target target' ∧ simulates source' target' := by
  induction word generalizing source target with
  | nil =>
      simp only [Run] at hrun ⊢
      subst source'
      exact ⟨target, rfl, hsimulates⟩
  | cons letter suffix ih =>
      rcases hrun with ⟨middle, hstep, hrun⟩
      rcases simulation.step_preserved letter hsimulates hstep with
        ⟨targetMiddle, htargetStep, hmiddleSimulates⟩
      rcases ih hmiddleSimulates hrun with
        ⟨target', htargetRun, hfinalSimulates⟩
      exact ⟨target', ⟨targetMiddle, htargetStep, htargetRun⟩,
        hfinalSimulates⟩

/-- Pointwise coverage of one state set by another through a simulation. -/
def CoveredBy (simulates : State → State → Prop)
    (source target : State → Prop) : Prop :=
  ∀ ⦃state⦄, source state → ∃ targetState, target targetState ∧
    simulates state targetState

theorem rightLanguageLE_of_forwardSimulation
    {transition : Letter → State → State → Prop} {final : State → Prop}
    {simulates : State → State → Prop}
    (simulation : ForwardSimulation transition final simulates)
    {source target : State → Prop}
    (hcovered : CoveredBy simulates source target) :
    RightLanguageLE transition final source target := by
  intro suffix
  rintro ⟨start, hstart, finish, hrun, hfinish⟩
  rcases hcovered hstart with ⟨targetStart, htargetStart, hsimulates⟩
  rcases simulation.run_preserved hsimulates hrun with
    ⟨targetFinish, htargetRun, hfinishSimulates⟩
  exact ⟨targetStart, htargetStart, targetFinish, htargetRun,
    simulation.final_preserved hfinishSimulates hfinish⟩

end OneSidedPumping

section FiniteImage

variable {Witness : Type uWitness} {Code : Type uCode}
  [Fintype Witness] [DecidableEq Code]

/-- The finite set of codes actually produced by a finite witness type.  This
is the executable boundary used when the ambient code type is finite but far
too large to enumerate: enumerate source witnesses, then quotient by their
codes. -/
def realizedCodeImage (encode : Witness → Code) : Finset Code :=
  Finset.univ.image encode

/-- A code together with evidence that some finite source witness produces
it.  Its inhabitants are exactly the realized image of `encode`, rather than
all inhabitants of the ambient code type. -/
abbrev RealizedCode (encode : Witness → Code) :=
  {code : Code // code ∈ realizedCodeImage encode}

/-- Insert a source witness into its realized finite image. -/
def realizedCodeOf (encode : Witness → Code) (witness : Witness) :
    RealizedCode encode :=
  ⟨encode witness, Finset.mem_image.mpr
    ⟨witness, Finset.mem_univ witness, rfl⟩⟩

/-- Every realized code has a source representative.  The choice is used only
to state the quotient presentation; executable closure works with the finite
image itself. -/
noncomputable def realizedCodeRepresentative (encode : Witness → Code)
    (code : RealizedCode encode) : Witness := by
  classical
  exact (Finset.mem_image.mp code.property).choose

@[simp]
theorem realizedCodeOf_representative (encode : Witness → Code)
    (code : RealizedCode encode) :
    realizedCodeOf encode (realizedCodeRepresentative encode code) = code := by
  classical
  apply Subtype.ext
  exact (Finset.mem_image.mp code.property).choose_spec.2

@[simp]
theorem card_realizedCode (encode : Witness → Code) :
    Fintype.card (RealizedCode encode) = (realizedCodeImage encode).card := by
  classical
  exact Fintype.card_coe _

end FiniteImage

section RootedFactorization

variable {RootedCarrier : Type uCarrier}
  {AttachmentReceipt : RootedCarrier → Type uReceipt}

/-- A finite literal-letter code retains its rooted carrier and the attachment
receipt whose incidences, ports, and cap data are part of the quotient. -/
structure LiteralCellCode where
  rootedCarrier : RootedCarrier
  attachmentReceipt : AttachmentReceipt rootedCarrier

variable {Literal : Type*} {Code : Type uCode} {State : Type uState}
  [Fintype Code]

/-- Data sufficient to factor a raw literal transition relation through a
finite, length-independent rooted alphabet. -/
structure RootedLetterPresentation where
  rawTransition : Literal → State → State → Prop
  code : Literal → Code
  representative : Code → Literal
  representative_code : ∀ codeValue, code (representative codeValue) = codeValue
  transition_invariant : ∀ ⦃left right⦄, code left = code right →
    rawTransition left = rawTransition right
  alphabetBound : Nat
  code_card_le : Fintype.card Code ≤ alphabetBound

namespace RootedLetterPresentation

variable (presentation : RootedLetterPresentation
  (Literal := Literal) (Code := Code) (State := State))

/-- The transition relation of a canonical rooted letter. -/
def codedTransition (codeValue : Code) : State → State → Prop :=
  presentation.rawTransition (presentation.representative codeValue)

/-- Transition invariance under rooted, port-ordered isomorphism makes the
raw literal relation factor through its finite code. -/
theorem rawTransition_eq_codedTransition (literal : Literal) :
    presentation.rawTransition literal =
      presentation.codedTransition (presentation.code literal) := by
  apply presentation.transition_invariant
  exact (presentation.representative_code (presentation.code literal)).symm

theorem codedAlphabet_card_le : Fintype.card Code ≤ presentation.alphabetBound :=
  presentation.code_card_le

/-- Canonical quotient presentation obtained by retaining exactly the finite
image of a source witness code.  Transition invariance is the only semantic
obligation: once it is proved, no enumeration of the ambient code carrier is
needed. -/
noncomputable def ofFiniteImage
    {RawCode : Type uCode} [Fintype Literal] [DecidableEq RawCode]
    (rawTransition : Literal → State → State → Prop)
    (encode : Literal → RawCode)
    (hinvariant : ∀ ⦃left right⦄, encode left = encode right →
      rawTransition left = rawTransition right) :
    RootedLetterPresentation
      (Literal := Literal) (Code := RealizedCode encode) (State := State) where
  rawTransition := rawTransition
  code := realizedCodeOf encode
  representative := realizedCodeRepresentative encode
  representative_code := realizedCodeOf_representative encode
  transition_invariant := by
    intro left right heq
    apply hinvariant
    exact congrArg Subtype.val heq
  alphabetBound := (realizedCodeImage encode).card
  code_card_le := by
    rw [card_realizedCode]

@[simp]
theorem ofFiniteImage_alphabetBound
    {RawCode : Type uCode} [Fintype Literal] [DecidableEq RawCode]
    (rawTransition : Literal → State → State → Prop)
    (encode : Literal → RawCode)
    (hinvariant : ∀ ⦃left right⦄, encode left = encode right →
      rawTransition left = rawTransition right) :
    (ofFiniteImage rawTransition encode hinvariant).alphabetBound =
      (realizedCodeImage encode).card :=
  rfl

end RootedLetterPresentation

end RootedFactorization

section SparseReplay

/-- Sparse row storage.  A row is the half-open interval between consecutive
offsets; targets and witnesses are parallel arrays. -/
structure CSRRows where
  rowCount : Nat
  targetCount : Nat
  witnessCount : Nat
  rowOffset : Array Nat
  targetIndex : Array Nat
  witnessIndex : Array Nat
  offset_size : rowOffset.size = rowCount + 1
  payload_size : targetIndex.size = witnessIndex.size
  first_offset : rowOffset[0]? = some 0
  final_offset : rowOffset[rowCount]? = some targetIndex.size
  offsets_monotone : ∀ ⦃left right leftOffset rightOffset : Nat⦄,
    left ≤ right → rowOffset[left]? = some leftOffset →
      rowOffset[right]? = some rightOffset → leftOffset ≤ rightOffset
  targets_bounded : ∀ ⦃position target : Nat⦄,
    targetIndex[position]? = some target → target < targetCount
  witnesses_bounded : ∀ ⦃position witness : Nat⦄,
    witnessIndex[position]? = some witness → witness < witnessCount

/-- One target/witness entry occurs inside one CSR row. -/
def CSRRows.HasEntry (rows : CSRRows) (row target witness : Nat) : Prop :=
  ∃ start stop position : Nat,
    rows.rowOffset[row]? = some start ∧
    rows.rowOffset[row + 1]? = some stop ∧
    start ≤ position ∧ position < stop ∧
    rows.targetIndex[position]? = some target ∧
    rows.witnessIndex[position]? = some witness

/-- A page-local CSR layout.  Each global row has a canonical page and local
row address.  The page function permits each payload page to be compiled and
replayed independently; an implementation need not materialize one enormous
reducible array term. -/
structure PagedCSRRows where
  totalRowCount : Nat
  targetCount : Nat
  witnessCount : Nat
  pageCount : Nat
  page : Fin pageCount → CSRRows
  pageStart : Fin pageCount → Nat
  rowPage : Fin totalRowCount → Fin pageCount
  rowLocal : (row : Fin totalRowCount) → Fin (page (rowPage row)).rowCount
  row_address : ∀ row,
    pageStart (rowPage row) + (rowLocal row).val = row.val
  page_target_count : ∀ pageIndex,
    (page pageIndex).targetCount = targetCount
  page_witness_count : ∀ pageIndex,
    (page pageIndex).witnessCount = witnessCount

/-- One entry of the canonical page-local row for a global row index. -/
def PagedCSRRows.HasEntry
    (rows : PagedCSRRows) (row target witness : Nat) : Prop :=
  ∃ hrow : row < rows.totalRowCount,
    CSRRows.HasEntry
      (rows.page (rows.rowPage ⟨row, hrow⟩))
      (rows.rowLocal ⟨row, hrow⟩).val target witness

/-- A replayable reachable-closure certificate.  `entry_sound` ties every
sparse entry to one common local witness; `entry_complete` proves that no
legal successor was omitted; `frontier_closed` proves that every legal target
has a canonical listed code.  Transition rows are paged CSR payloads, so each
kernel replay unit remains independently bounded. -/
structure ReachableClosureCertificate
    (StateCode : Type uCode) (LetterCode : Type uLetter)
    (Witness : Type uWitness) where
  states : Array StateCode
  letters : Array LetterCode
  witnesses : Array Witness
  rows : PagedCSRRows
  states_injective : ∀ ⦃left right : Nat⦄ ⦃state : StateCode⦄,
    states[left]? = some state → states[right]? = some state → left = right
  row_count : rows.totalRowCount = states.size * letters.size
  target_count : rows.targetCount = states.size
  witness_count : rows.witnessCount = witnesses.size
  transition : StateCode → LetterCode → StateCode → Prop
  witnessValid : Witness → StateCode → LetterCode → StateCode → Prop
  entry_sound : ∀ ⦃stateIndex letterIndex targetIndex witnessIndex : Nat⦄
      ⦃state : StateCode⦄ ⦃letter : LetterCode⦄ ⦃target : StateCode⦄
      ⦃witness : Witness⦄,
    states[stateIndex]? = some state →
    letters[letterIndex]? = some letter →
    states[targetIndex]? = some target →
    witnesses[witnessIndex]? = some witness →
    PagedCSRRows.HasEntry rows (stateIndex * letters.size + letterIndex)
      targetIndex witnessIndex →
    witnessValid witness state letter target ∧ transition state letter target
  entry_complete : ∀ ⦃stateIndex letterIndex : Nat⦄ ⦃state : StateCode⦄
      ⦃letter : LetterCode⦄ ⦃target : StateCode⦄,
    states[stateIndex]? = some state →
    letters[letterIndex]? = some letter →
    transition state letter target →
    ∃ targetIndex witnessIndex witness,
      states[targetIndex]? = some target ∧
      witnesses[witnessIndex]? = some witness ∧
      PagedCSRRows.HasEntry rows (stateIndex * letters.size + letterIndex)
        targetIndex witnessIndex ∧
      witnessValid witness state letter target
  initialIndex : Array Nat
  realizable : StateCode → Prop
  initial_realizable : ∀ ⦃position stateIndex : Nat⦄ ⦃state : StateCode⦄,
    initialIndex[position]? = some stateIndex →
    states[stateIndex]? = some state → realizable state
  accepting : StateCode → Bool
  necessary : StateCode → Bool
  acceptingSemantic : StateCode → Prop
  necessarySemantic : StateCode → Prop
  accepting_exact : ∀ state, accepting state = true ↔ acceptingSemantic state
  necessary_exact : ∀ state, necessary state = true ↔ necessarySemantic state
  frontier_closed : ∀ ⦃stateIndex letterIndex : Nat⦄ ⦃state : StateCode⦄
      ⦃letter : LetterCode⦄ ⦃target : StateCode⦄,
    states[stateIndex]? = some state →
    letters[letterIndex]? = some letter →
    transition state letter target →
    ∃ targetIndex : Nat, states[targetIndex]? = some target

/-- Semantic reachability from an initial state through realized letters.  This
inductive predicate is deliberately independent of any array representation;
an exact certificate identifies it with the injective state array below. -/
inductive ClosureReachable
    {StateCode : Type uCode} {LetterCode : Type uLetter}
    (transition : StateCode → LetterCode → StateCode → Prop)
    (initial : StateCode → Prop) (allowedLetter : LetterCode → Prop) :
    StateCode → Prop where
  | initial {state} : initial state →
      ClosureReachable transition initial allowedLetter state
  | tail {source letter target} :
      ClosureReachable transition initial allowedLetter source →
      allowedLetter letter → transition source letter target →
      ClosureReachable transition initial allowedLetter target

/-- A reachable-closure certificate with the two exactness clauses that a
reported closure cardinality needs.  The base CSR certificate proves every
listed row sound and exhaustive.  This extension additionally proves that the
letter array is the entire allowed alphabet and that every listed state is
actually reachable; initial completeness and frontier closure then give the
reverse inclusion. -/
structure ExactReachableClosureCertificate
    (StateCode : Type uCode) (LetterCode : Type uLetter)
    (Witness : Type uWitness)
    extends ReachableClosureCertificate StateCode LetterCode Witness where
  allowedLetter : LetterCode → Prop
  letters_exact : ∀ letter,
    allowedLetter letter ↔
      ∃ letterIndex : Nat, letters[letterIndex]? = some letter
  initial_complete : ∀ ⦃state : StateCode⦄, realizable state →
    ∃ position stateIndex : Nat,
      initialIndex[position]? = some stateIndex ∧
      states[stateIndex]? = some state
  states_reachable : ∀ ⦃stateIndex : Nat⦄ ⦃state : StateCode⦄,
    states[stateIndex]? = some state →
      ClosureReachable transition realizable allowedLetter state

namespace ReachableClosureCertificate

variable {StateCode : Type uCode} {LetterCode : Type uLetter}
  {Witness : Type uWitness}

/-- Soundness and row exhaustiveness identify the replayed sparse row exactly
with the semantic literal transition relation. -/
theorem row_entry_iff_transition
    (certificate : ReachableClosureCertificate StateCode LetterCode Witness)
    {stateIndex letterIndex targetIndex : Nat}
    {state : StateCode} {letter : LetterCode} {target : StateCode}
    (hstate : certificate.states[stateIndex]? = some state)
    (hletter : certificate.letters[letterIndex]? = some letter)
    (htarget : certificate.states[targetIndex]? = some target) :
    (∃ witnessIndex witness,
      certificate.witnesses[witnessIndex]? = some witness ∧
      PagedCSRRows.HasEntry certificate.rows
        (stateIndex * certificate.letters.size + letterIndex)
        targetIndex witnessIndex) ↔
      certificate.transition state letter target := by
  constructor
  · rintro ⟨witnessIndex, witness, hwitness, hentry⟩
    exact (certificate.entry_sound hstate hletter htarget hwitness hentry).2
  · intro htransition
    rcases certificate.entry_complete hstate hletter htransition with
      ⟨foundTargetIndex, witnessIndex, witness, hfoundTarget, hwitness,
        hentry, _hwitnessValid⟩
    have htargetIndex : foundTargetIndex = targetIndex :=
      certificate.states_injective hfoundTarget htarget
    subst foundTargetIndex
    exact ⟨witnessIndex, witness, hwitness, hentry⟩

end ReachableClosureCertificate

namespace ExactReachableClosureCertificate

variable {StateCode : Type uCode} {LetterCode : Type uLetter}
  {Witness : Type uWitness}

/-- The initial index array names exactly the semantic initial states. -/
theorem initial_entry_iff_realizable
    (certificate : ExactReachableClosureCertificate StateCode LetterCode Witness)
    (state : StateCode) :
    (∃ position stateIndex : Nat,
      certificate.initialIndex[position]? = some stateIndex ∧
      certificate.states[stateIndex]? = some state) ↔
      certificate.realizable state := by
  constructor
  · rintro ⟨position, stateIndex, hinitial, hstate⟩
    exact certificate.initial_realizable hinitial hstate
  · intro hstate
    exact certificate.initial_complete (state := state) hstate

/-- Exactness of the reported state array.  Its entries are precisely the
states semantically reachable from a realizable initial state through the full
allowed letter alphabet.  Together with `states_injective`, this makes
`states.size` an exact closure count rather than an upper bound. -/
theorem state_entry_iff_reachable
    (certificate : ExactReachableClosureCertificate StateCode LetterCode Witness)
    (state : StateCode) :
    (∃ stateIndex : Nat, certificate.states[stateIndex]? = some state) ↔
      ClosureReachable certificate.transition certificate.realizable
        certificate.allowedLetter state := by
  constructor
  · rintro ⟨stateIndex, hstate⟩
    exact certificate.states_reachable hstate
  · intro hreachable
    induction hreachable with
    | initial hinitial =>
        rcases certificate.initial_complete hinitial with
          ⟨_position, stateIndex, _hinitialIndex, hstate⟩
        exact ⟨stateIndex, hstate⟩
    | tail hsource hletter htransition ih =>
        rcases ih with ⟨sourceIndex, hsourceIndex⟩
        rcases (certificate.letters_exact _).mp hletter with
          ⟨letterIndex, hletterIndex⟩
        rcases certificate.frontier_closed hsourceIndex hletterIndex htransition with
          ⟨targetIndex, htargetIndex⟩
        exact ⟨targetIndex, htargetIndex⟩

end ExactReachableClosureCertificate

end SparseReplay

end GoertzelV24FiniteClosureInterfaces

end Mettapedia.GraphTheory.FourColor
