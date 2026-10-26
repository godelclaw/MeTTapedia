import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedExploration
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.Framework.FiniteModelSearch
import Mettapedia.Machines.LevinSearch

/-!
# Searching for explanations

A verdict's explanation is a certificate, and a certificate has a description: a bit string that
decodes to it. Levin search runs every code in rounds, giving a code of description length `ℓ` the work
`2^(r - ℓ)` in round `r` (`Machines/LevinSearch`).

- **Codes** (`codesUpTo`): a bit string `s` has description length `2|s| + 2`. There are `2^n` strings
  of length `n`, so the lengths satisfy Kraft's inequality (`codes_kraft`).
- **Explanations** (`explanations`, `explain`): a decoder from bit strings to candidates, a declared cost
  of checking a candidate, and the check. Every answer is a checked candidate. If some code of length `ℓ`
  decodes to a candidate that checks at cost `t`, the search finds a checked candidate within the first
  `ℓ + ⌈log₂ t⌉ + 1` rounds, after total work at most `4 · 2^ℓ · t` (`explain_finds`): it minimizes
  Levin's `ℓ + log t`.
- **Graded unknowns** (`exhausted_bound`): when `r` rounds find nothing, every checked candidate has
  `ℓ + ⌈log₂ t⌉ + 1 > r`. The question stays open with a proved lower bound on the complexity of any
  explanation, and more rounds raise it.
- **Certificates as candidates** (`CertificateCandidate`): a carrier size, a junk value and the cells
  of a model, written in unary (`decode_encode`). The certificate's preorder is the one its rules force
  (`Certificate.ofContextualCells`).
- **Asking** (`ask`): a hinted candidate first, such as one the cell finder produced; then the region the
  term reaches, a closed region grown from it, a closed canonical region when canonical forms are given,
  and a proof search and a refutation search over codes, all within the same rounds. The answer is
  proved, refuted, or open with its rounds.
  Proved and refuted answers are sound (`ask_proved`, `ask_refuted`). An open answer bounds every
  explanation (`ask_open`). Every certificate that decides the question is reached by enough rounds
  (`ask_complete`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.FiniteModels (Certificate Cells Signature)
open Mettapedia.Machines.LevinSearch (Searcher Family)

/-! ## Codes -/

namespace Codes

/-- All bit strings of a length. -/
def bitStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | length + 1 => (bitStrings length).flatMap fun rest => [false :: rest, true :: rest]

theorem mem_bitStrings : ∀ {length : ℕ} {bits : List Bool}, bits ∈ bitStrings length ↔ bits.length = length
  | 0, bits => by cases bits <;> simp [bitStrings]
  | _ + 1, [] => by simp [bitStrings]
  | length + 1, first :: rest => by
    simp only [bitStrings, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
      Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨rest', member, same | same⟩ <;>
        · simp only [List.cons.injEq] at same
          obtain ⟨-, rfl⟩ := same
          exact mem_bitStrings.mp member
    · intro length'
      refine ⟨rest, mem_bitStrings.mpr length', ?_⟩
      cases first <;> simp

theorem length_bitStrings : ∀ length, (bitStrings length).length = 2 ^ length
  | 0 => rfl
  | length + 1 => by
    simp only [bitStrings, List.length_flatMap, List.length_cons]
    rw [List.map_const', List.sum_replicate, length_bitStrings length, pow_succ]
    simp [mul_comm]

/-- **The description length of a code.** -/
def codeLength (bits : List Bool) : ℕ := 2 * bits.length + 2

/-- The codes of description length at most a bound. -/
def codesUpTo (bound : ℕ) : List (List Bool) :=
  (List.range (bound + 1)).flatMap fun length => if 2 * length + 2 ≤ bound then bitStrings length else []

theorem mem_codesUpTo (bound : ℕ) (bits : List Bool) : bits ∈ codesUpTo bound ↔ codeLength bits ≤ bound := by
  simp only [codesUpTo, codeLength, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨length, -, member⟩
    split at member
    · rw [mem_bitStrings.mp member]
      assumption
    · cases member
  · intro bounded
    exact ⟨bits.length, by omega, by rw [if_pos bounded]; exact mem_bitStrings.mpr rfl⟩

/-- The geometric sum of powers of two. -/
theorem geometric : ∀ top : ℕ, ((List.range (top + 1)).map fun index => 2 ^ (top - index)).sum + 1 = 2 ^ (top + 1)
  | 0 => rfl
  | top + 1 => by
    have shifted : ((List.range (top + 1)).map fun index => 2 ^ (top + 1 - index)) =
        (List.range (top + 1)).map fun index => 2 * 2 ^ (top - index) := by
      apply List.map_congr_left
      intro index member
      rw [List.mem_range] at member
      rw [show top + 1 - index = (top - index) + 1 by omega, pow_succ, mul_comm]
    rw [List.range_succ, List.map_append, List.sum_append, shifted, List.sum_map_mul_left]
    have previous := geometric top
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.sub_self, pow_zero]
    rw [pow_succ]
    omega

theorem sum_map_flatMap {α β : Type} (f : α → List β) (g : β → ℕ) :
    ∀ list : List α, ((list.flatMap f).map g).sum = (list.map fun entry => ((f entry).map g).sum).sum
  | [] => rfl
  | entry :: list => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap f g list]

/-- **Kraft's inequality for the codes.** -/
theorem codes_kraft (bound : ℕ) :
    ((codesUpTo bound).map fun bits => 2 ^ (bound - codeLength bits)).sum ≤ 2 ^ bound := by
  have perLength : ∀ length, ((if 2 * length + 2 ≤ bound then bitStrings length else []).map
      fun bits => 2 ^ (bound - codeLength bits)).sum =
        if 2 * length + 2 ≤ bound then 2 ^ (bound - 2 - length) else 0 := by
    intro length
    split
    · rename_i fits
      have same : ((bitStrings length).map fun bits => 2 ^ (bound - codeLength bits)) =
          (bitStrings length).map fun _ => 2 ^ (bound - 2 * length - 2) := by
        apply List.map_congr_left
        intro bits member
        rw [codeLength, mem_bitStrings.mp member]
        exact congrArg (2 ^ ·) (by omega)
      rw [same, List.map_const', List.sum_replicate, length_bitStrings, smul_eq_mul, ← pow_add]
      exact congrArg (2 ^ ·) (by omega)
    · rfl
  rw [codesUpTo, sum_map_flatMap]
  simp only [perLength]
  by_cases small : bound < 2
  · have zero : ∀ length ∈ List.range (bound + 1),
        (if 2 * length + 2 ≤ bound then 2 ^ (bound - 2 - length) else 0) = 0 := by
      intro length _
      rw [if_neg (by omega)]
    rw [List.map_congr_left zero, List.map_const', List.sum_replicate, smul_zero]
    exact Nat.zero_le _
  · obtain ⟨top, rfl⟩ : ∃ top, bound = top + 2 := ⟨bound - 2, by omega⟩
    have termwise : ∀ length ∈ List.range (top + 2 + 1),
        (if 2 * length + 2 ≤ top + 2 then 2 ^ (top + 2 - 2 - length) else 0) ≤
          if length ≤ top then 2 ^ (top - length) else 0 := by
      intro length _
      split
      · rw [if_pos (by omega)]
        exact le_of_eq (congrArg (2 ^ ·) (by omega))
      · exact Nat.zero_le _
    calc ((List.range (top + 2 + 1)).map fun length =>
          if 2 * length + 2 ≤ top + 2 then 2 ^ (top + 2 - 2 - length) else 0).sum
        ≤ ((List.range (top + 2 + 1)).map fun length => if length ≤ top then 2 ^ (top - length) else 0).sum :=
          List.sum_le_sum termwise
      _ = ((List.range (top + 1)).map fun length => 2 ^ (top - length)).sum := by
          rw [show top + 2 + 1 = (top + 1) + 2 by omega, List.range_add, List.map_append, List.sum_append]
          have tail : ∀ entry ∈ (List.range 2).map (top + 1 + ·),
              (if entry ≤ top then 2 ^ (top - entry) else 0) = 0 := by
            intro entry member
            simp only [List.mem_map, List.mem_range] at member
            obtain ⟨offset, -, rfl⟩ := member
            rw [if_neg (by omega)]
          rw [List.map_congr_left tail, List.map_const', List.sum_replicate, smul_zero, add_zero]
          apply congrArg List.sum
          apply List.map_congr_left
          intro length member
          rw [List.mem_range] at member
          rw [if_pos (by omega)]
      _ ≤ 2 ^ (top + 2) := by
          have := geometric top
          have growth : 2 ^ (top + 1) ≤ 2 ^ (top + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega

end Codes

/-! ## Levin search over explanations -/

section Explanations

open Codes

variable {Candidate : Type} (decode : List Bool → Option Candidate) (cost : Candidate → ℕ) (check : Candidate → Bool)

/-- What a code's searcher has found after some work: its candidate, once the work covers the
candidate's cost and the candidate checks. -/
def probe (bits : List Bool) (work : ℕ) : Option {candidate // check candidate = true} :=
  match decode bits with
  | some candidate =>
    if checked : check candidate = true then
      if cost candidate ≤ work then some ⟨candidate, checked⟩ else none
    else none
  | none => none

/-- The searcher of one code. -/
def codeSearcher (bits : List Bool) : Searcher {candidate // check candidate = true} where
  result := probe decode cost check bits
  persistent work answer found := by
    unfold probe at found ⊢
    cases decoded : decode bits with
    | none => simp [decoded] at found
    | some candidate =>
      simp only [decoded] at found ⊢
      by_cases checked : check candidate = true
      · rw [dif_pos checked] at found ⊢
        by_cases affordable : cost candidate ≤ work
        · rw [if_pos affordable] at found
          rw [if_pos (by omega)]
          exact found
        · rw [if_neg affordable] at found
          cases found
      · rw [dif_neg checked] at found
        cases found

/-- **The portfolio of explanations**: every code, with its description length. -/
def explanations : Family (List Bool) {candidate // check candidate = true} where
  length := codeLength
  searcher := codeSearcher decode cost check
  upTo := codesUpTo
  upTo_exact := mem_codesUpTo
  kraft := codes_kraft

/-- **Levin search for an explanation**, for some rounds. -/
def explain (rounds : ℕ) : Option {candidate // check candidate = true} :=
  (explanations decode cost check).search rounds

theorem explain_mono : ∀ {rounds more : ℕ}, rounds ≤ more → (explain decode cost check rounds).isSome →
    (explain decode cost check more).isSome := by
  intro rounds more le found
  induction le with
  | refl => exact found
  | step _ previous =>
    unfold explain at previous ⊢
    rw [Family.search]
    cases earlier : (explanations decode cost check).search _ with
    | none => rw [earlier] at previous; cases previous
    | some answer => rfl

/-- **Levin's bound for explanations.** If a code decodes to a candidate that checks at cost `t`, the
search finds a checked candidate within `ℓ + ⌈log₂ t⌉ + 1` rounds, after total work at most
`4 · 2^ℓ · max t 1`. -/
theorem explain_finds {bits : List Bool} {candidate : Candidate} (decoded : decode bits = some candidate)
    (checked : check candidate = true) :
    (explain decode cost check (codeLength bits + Nat.clog 2 (cost candidate) + 1)).isSome ∧
      (explanations decode cost check).cost (codeLength bits + Nat.clog 2 (cost candidate) + 1) ≤
        4 * 2 ^ codeLength bits * max (cost candidate) 1 := by
  have found : (codeSearcher decode cost check bits).result (cost candidate) = some ⟨candidate, checked⟩ := by
    simp only [codeSearcher, probe, decoded, checked, dite_true, le_refl, ite_true]
  exact (explanations decode cost check).search_finds found

/-- **A graded unknown**: when `rounds` rounds find nothing, every checked candidate has
`ℓ + ⌈log₂ t⌉ + 1 > rounds`. -/
theorem exhausted_bound {rounds : ℕ} (nothing : explain decode cost check rounds = none) {bits : List Bool}
    {candidate : Candidate} (decoded : decode bits = some candidate) (checked : check candidate = true) :
    rounds < codeLength bits + Nat.clog 2 (cost candidate) + 1 := by
  by_contra enough
  have found := explain_mono decode cost check (more := rounds) (by omega)
    (explain_finds decode cost check decoded checked).1
  rw [nothing] at found
  cases found

end Explanations

/-! ## Certificates as candidates -/

/-- **A candidate certificate**: a carrier `Fin (size + 1)`, a junk value, and the cells of a model. -/
structure CertificateCandidate where
  size : ℕ
  junk : Fin (size + 1)
  cells : Cells (Fin (size + 1))
  deriving DecidableEq, Repr

namespace CertificateCandidate

/-- The certificate a candidate describes, with the preorder its rules force. -/
def certificate (candidate : CertificateCandidate) (signature : Signature) (language : LanguageDef) :
    Certificate (Fin (candidate.size + 1)) :=
  Certificate.ofContextualCells (List.finRange (candidate.size + 1)) (fun entry => List.mem_finRange entry)
    candidate.junk signature candidate.cells language

/-- A declared bound on the cost of checking a candidate. -/
def cost (candidate : CertificateCandidate) : ℕ := (candidate.size + 1) ^ 4 + candidate.cells.length

/-- A number in unary: that many `true`s, then `false`. -/
def unary (number : ℕ) : List Bool := List.replicate number true ++ [false]

/-- Read a number in unary. -/
def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readUnary rest).map fun read => (read.1 + 1, read.2)

theorem readUnary_replicate (rest : List Bool) :
    ∀ number, readUnary (List.replicate number true ++ false :: rest) = some (number, rest)
  | 0 => rfl
  | number + 1 => by
    simp [List.replicate_succ, readUnary, readUnary_replicate rest number]

theorem readUnary_unary (number : ℕ) (rest : List Bool) : readUnary (unary number ++ rest) = some (number, rest) := by
  rw [unary, List.append_assoc, List.singleton_append]
  exact readUnary_replicate rest number

/-- Read cells: each a slot, an input and a value below the carrier size. -/
def readCells (size : ℕ) : ℕ → List Bool → Option (Cells (Fin (size + 1)) × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
    match readUnary bits with
    | none => none
    | some (slot, bits) =>
      match readUnary bits with
      | none => none
      | some (input, bits) =>
        match readUnary bits with
        | none => none
        | some (value, bits) =>
          if inside : value < size + 1 then
            (readCells size count bits).map fun read => (((slot, input), ⟨value, inside⟩) :: read.1, read.2)
          else none

/-- Write cells. -/
def writeCells {size : ℕ} : Cells (Fin (size + 1)) → List Bool
  | [] => []
  | ((slot, input), value) :: cells => unary slot ++ unary input ++ unary value.val ++ writeCells cells

theorem readCells_writeCells {size : ℕ} : ∀ (cells : Cells (Fin (size + 1))) (rest : List Bool),
    readCells size cells.length (writeCells cells ++ rest) = some (cells, rest)
  | [], rest => rfl
  | ((slot, input), value) :: cells, rest => by
    simp only [writeCells, List.length_cons, List.append_assoc, readCells, readUnary_unary, value.isLt, dite_true,
      readCells_writeCells cells rest, Option.map_some]

/-- **Decode a candidate**: its size, its junk value, its number of cells, and the cells, using every bit. -/
def decode (bits : List Bool) : Option CertificateCandidate :=
  match readUnary bits with
  | none => none
  | some (size, bits) =>
    match readUnary bits with
    | none => none
    | some (junk, bits) =>
      if inside : junk < size + 1 then
        match readUnary bits with
        | none => none
        | some (count, bits) =>
          match readCells size count bits with
          | some (cells, []) => some ⟨size, ⟨junk, inside⟩, cells⟩
          | _ => none
      else none

/-- Encode a candidate. -/
def encode (candidate : CertificateCandidate) : List Bool :=
  unary candidate.size ++ unary candidate.junk.val ++ unary candidate.cells.length ++ writeCells candidate.cells

/-- **Every candidate has a code.** -/
theorem decode_encode (candidate : CertificateCandidate) : decode (encode candidate) = some candidate := by
  obtain ⟨size, junk, cells⟩ := candidate
  have read := readCells_writeCells cells []
  rw [List.append_nil] at read
  simp only [encode, decode, List.append_assoc, readUnary_unary, junk.isLt, dite_true, read]

end CertificateCandidate

/-! ## Asking -/

/-- **Evidence** about a formula at a term: a candidate certificate, which maps the language onto a finite
structure; the region the term reaches in some rounds, which sits inside the language; a closed region
grown in some rounds, which decides forward formulas exactly in an equation-free language; a closed
canonical region, which decides behavioural formulas exactly modulo the equations; or a certified decider the
language provides (`Decider`), exact where it answers. -/
inductive Evidence where
  | certificate (candidate : CertificateCandidate)
  | exploration (rounds : ℕ)
  | closedRegion (rounds : ℕ)
  | canonicalRegion (rounds : ℕ)
  | decided
  deriving DecidableEq, Repr

/-- **An answer**: proved or refuted with its evidence, or open after some rounds. -/
inductive Answer where
  | proved (evidence : Evidence)
  | refuted (evidence : Evidence)
  | unknown (rounds : ℕ)
  deriving DecidableEq, Repr

variable (relEnv : RelationEnv) (signature : Signature) (language : LanguageDef) (fuel : ℕ) (formula : Formula 0)
  (term : Pattern)

/-- A candidate proves the formula at the term. -/
def provesBy (candidate : CertificateCandidate) : Bool :=
  proves (candidate.certificate signature language) language formula term

/-- A candidate refutes the formula at the term. -/
def refutesBy (candidate : CertificateCandidate) : Bool :=
  refutes (candidate.certificate signature language) language formula term

/-- Whether evidence establishes the formula at the term, given canonical forms or none. -/
def Evidence.establishes (forms : Option (CanonicalForms relEnv language fuel)) : Evidence → Bool
  | .certificate candidate => provesBy signature language formula term candidate
  | .exploration rounds => exploresFrom relEnv language fuel formula term rounds
  | .closedRegion rounds => language.isEquationFree && formula.forward &&
      decideFrom relEnv language fuel formula term rounds == some true
  | .canonicalRegion rounds => match forms with
    | some forms => formula.behaviouralIn forms.labels &&
        decideCanonical relEnv language fuel forms.canon forms.domain forms.presentations formula term rounds ==
          some true
    | none => false
  | .decided => false

/-- Whether evidence refutes the formula at the term, given canonical forms or none. -/
def Evidence.refutes (forms : Option (CanonicalForms relEnv language fuel)) : Evidence → Bool
  | .certificate candidate => refutesBy signature language formula term candidate
  | .exploration rounds => exploresAgainstFrom relEnv language fuel formula term rounds
  | .closedRegion rounds => language.isEquationFree && formula.forward &&
      decideFrom relEnv language fuel formula term rounds == some false
  | .canonicalRegion rounds => match forms with
    | some forms => formula.behaviouralIn forms.labels &&
        decideCanonical relEnv language fuel forms.canon forms.domain forms.presentations formula term rounds ==
          some false
    | none => false
  | .decided => false

/-- The evidence `ask` weighs: the hint, the region the term reaches, a closed region grown from the term,
a closed canonical region grown from it, and what Levin search finds for a proof and for a refutation. -/
def gathered (hint : Option CertificateCandidate) (rounds : ℕ) : List Evidence :=
  hint.toList.map .certificate ++ [.exploration rounds, .closedRegion rounds, .canonicalRegion rounds] ++
    (explain CertificateCandidate.decode CertificateCandidate.cost (provesBy signature language formula term)
      rounds).toList.map (.certificate ·.1) ++
    (explain CertificateCandidate.decode CertificateCandidate.cost (refutesBy signature language formula term)
      rounds).toList.map (.certificate ·.1)

/-- **Ask** whether a formula holds at a term: the first gathered evidence that establishes it, or else
the first that refutes it, or an open answer. Canonical forms, when given, read the language modulo its
equations. -/
def ask (hint : Option CertificateCandidate) (rounds : ℕ) (forms : Option (CanonicalForms relEnv language fuel) := none) :
    Answer :=
  match (gathered signature language formula term hint rounds).find?
      (Evidence.establishes relEnv signature language fuel formula term forms) with
  | some evidence => .proved evidence
  | none =>
    match (gathered signature language formula term hint rounds).find?
        (Evidence.refutes relEnv signature language fuel formula term forms) with
    | some evidence => .refuted evidence
    | none => .unknown rounds

variable {relEnv signature language fuel formula term}

/-- **Evidence that establishes holds.** -/
theorem Evidence.establishes_sound {forms : Option (CanonicalForms relEnv language fuel)} {evidence : Evidence}
    (checked : evidence.establishes relEnv signature language fuel formula term forms = true) :
    (referenceStructure relEnv language).sat Env.closed formula term := by
  cases evidence with
  | certificate candidate => exact proves_sound checked
  | exploration rounds => exact exploresFrom_sound checked
  | closedRegion rounds =>
    simp only [Evidence.establishes, Bool.and_eq_true, beq_iff_eq] at checked
    exact (decideFrom_sound checked.1.1 checked.1.2 checked.2).mp rfl
  | canonicalRegion rounds =>
    cases forms with
    | none => cases checked
    | some forms =>
      simp only [Evidence.establishes, Bool.and_eq_true, beq_iff_eq] at checked
      exact (decideCanonical_sound_on forms.canonical forms.coherent checked.1 checked.2).mp rfl
  | decided => cases checked

/-- **Evidence that refutes fails.** -/
theorem Evidence.refutes_sound {forms : Option (CanonicalForms relEnv language fuel)} {evidence : Evidence}
    (checked : evidence.refutes relEnv signature language fuel formula term forms = true) :
    ¬ (referenceStructure relEnv language).sat Env.closed formula term := by
  cases evidence with
  | certificate candidate => exact GeneratedLogic.refutes_sound checked
  | exploration rounds => exact exploresAgainstFrom_sound checked
  | closedRegion rounds =>
    simp only [Evidence.refutes, Bool.and_eq_true, beq_iff_eq] at checked
    exact fun holds => Bool.false_ne_true ((decideFrom_sound checked.1.1 checked.1.2 checked.2).mpr holds)
  | canonicalRegion rounds =>
    cases forms with
    | none => cases checked
    | some forms =>
      simp only [Evidence.refutes, Bool.and_eq_true, beq_iff_eq] at checked
      exact fun holds =>
        Bool.false_ne_true ((decideCanonical_sound_on forms.canonical forms.coherent checked.1 checked.2).mpr holds)
  | decided => cases checked

/-- **A proved answer holds.** -/
theorem ask_proved {hint : Option CertificateCandidate} {rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}
    {evidence : Evidence} (answered : ask relEnv signature language fuel formula term hint rounds forms = .proved evidence) :
    (referenceStructure relEnv language).sat Env.closed formula term := by
  unfold ask at answered
  split at answered
  · rename_i found
    cases answered
    exact Evidence.establishes_sound (List.find?_some found)
  · split at answered <;> cases answered

/-- **A refuted answer fails.** -/
theorem ask_refuted {hint : Option CertificateCandidate} {rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}
    {evidence : Evidence} (answered : ask relEnv signature language fuel formula term hint rounds forms = .refuted evidence) :
    ¬ (referenceStructure relEnv language).sat Env.closed formula term := by
  unfold ask at answered
  split at answered
  · cases answered
  · split at answered
    · rename_i found
      cases answered
      exact Evidence.refutes_sound (List.find?_some found)
    · cases answered

/-- **An open answer bounds every explanation**: every candidate that proves or refutes the formula at the
term has `ℓ + ⌈log₂ t⌉ + 1 > rounds` for its code. -/
theorem ask_open {hint : Option CertificateCandidate} {rounds : ℕ} {forms : Option (CanonicalForms relEnv language fuel)}
    (answered : ask relEnv signature language fuel formula term hint rounds forms = .unknown rounds)
    (candidate : CertificateCandidate)
    (decides : provesBy signature language formula term candidate = true ∨
      refutesBy signature language formula term candidate = true) :
    rounds < Codes.codeLength candidate.encode + Nat.clog 2 candidate.cost + 1 := by
  unfold ask at answered
  split at answered
  · cases answered
  · rename_i noProof
    split at answered
    · cases answered
    · rename_i noRefutation
      have noProofSearch : explain CertificateCandidate.decode CertificateCandidate.cost
          (provesBy signature language formula term) rounds = none := by
        cases found : explain CertificateCandidate.decode CertificateCandidate.cost
            (provesBy signature language formula term) rounds with
        | none => rfl
        | some answer =>
          have member : Evidence.certificate answer.1 ∈ gathered signature language formula term hint rounds := by
            simp [gathered, found]
          have rejected := List.find?_eq_none.mp noProof _ member
          simp [Evidence.establishes, answer.2] at rejected
      have noRefutationSearch : explain CertificateCandidate.decode CertificateCandidate.cost
          (refutesBy signature language formula term) rounds = none := by
        cases found : explain CertificateCandidate.decode CertificateCandidate.cost
            (refutesBy signature language formula term) rounds with
        | none => rfl
        | some answer =>
          have member : Evidence.certificate answer.1 ∈ gathered signature language formula term hint rounds := by
            simp [gathered, found]
          have rejected := List.find?_eq_none.mp noRefutation _ member
          simp [Evidence.refutes, answer.2] at rejected
      rcases decides with proving | refuting
      · exact exhausted_bound _ _ _ noProofSearch (CertificateCandidate.decode_encode candidate) proving
      · exact exhausted_bound _ _ _ noRefutationSearch (CertificateCandidate.decode_encode candidate) refuting

/-- **Asking is complete in the limit** for certificates: if some candidate proves or refutes the formula
at the term, enough rounds answer. -/
theorem ask_complete (hint : Option CertificateCandidate) (forms : Option (CanonicalForms relEnv language fuel))
    {candidate : CertificateCandidate}
    (decides : provesBy signature language formula term candidate = true ∨
      refutesBy signature language formula term candidate = true) :
    ∃ rounds, ∀ more, rounds ≤ more → ask relEnv signature language fuel formula term hint more forms ≠ .unknown more := by
  refine ⟨Codes.codeLength candidate.encode + Nat.clog 2 candidate.cost + 1, fun more enough answered => ?_⟩
  have := ask_open answered candidate decides
  omega

/-! ## Certified deciders -/

/-- **A certified decider** for a language: a decision procedure on some formulas and terms, exact in the
language's reference structure wherever it answers. A language whose canonical regions do not reach a former (the
parts of a set, for splits) can supply one built on its own semantics. -/
structure Decider (relEnv : RelationEnv) (language : LanguageDef) where
  decide : Formula 0 → Pattern → Option Bool
  exact : ∀ {formula : Formula 0} {term : Pattern} {answer : Bool}, decide formula term = some answer →
    ((referenceStructure relEnv language).sat Env.closed formula term ↔ answer = true)

variable (relEnv signature language fuel formula term) in
/-- **Ask, with a certified decider**: the decider's answer when it gives one, and otherwise `ask`. -/
def askWith (decider : Decider relEnv language) (hint : Option CertificateCandidate) (rounds : ℕ)
    (forms : Option (CanonicalForms relEnv language fuel) := none) : Answer :=
  match decider.decide formula term with
  | some true => .proved .decided
  | some false => .refuted .decided
  | none => ask relEnv signature language fuel formula term hint rounds forms

/-- **A proved answer holds**, with a certified decider. -/
theorem askWith_proved {decider : Decider relEnv language} {hint : Option CertificateCandidate} {rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} {evidence : Evidence}
    (answered : askWith relEnv signature language fuel formula term decider hint rounds forms = .proved evidence) :
    (referenceStructure relEnv language).sat Env.closed formula term := by
  unfold askWith at answered
  split at answered
  · rename_i decided
    exact (decider.exact decided).mpr rfl
  · cases answered
  · exact ask_proved answered

/-- **A refuted answer fails**, with a certified decider. -/
theorem askWith_refuted {decider : Decider relEnv language} {hint : Option CertificateCandidate} {rounds : ℕ}
    {forms : Option (CanonicalForms relEnv language fuel)} {evidence : Evidence}
    (answered : askWith relEnv signature language fuel formula term decider hint rounds forms = .refuted evidence) :
    ¬ (referenceStructure relEnv language).sat Env.closed formula term := by
  unfold askWith at answered
  split at answered
  · cases answered
  · rename_i decided
    exact fun holds => Bool.false_ne_true ((decider.exact decided).mp holds)
  · exact ask_refuted answered

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
