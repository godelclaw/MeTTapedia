import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessModulo

/-!
# Resumable work

Asking with more rounds need not repeat the work of fewer. The work of a question is the region the term
reaches, the region grown with parts, the canonical region, and the searches for a proof and for a
refutation.

- **Rounds resume** (`iterate_add`): rounds from a saved list are the later rounds from the start. The
  three regions are such rounds (`reachable_eq_iterate`, `grow_eq_iterate`, `growCanonical_eq_iterate`).
- **Levin search resumes** from what the first rounds found (`search_add`).
- **Progress** (`Progress`) keeps the rounds done, the three regions and the two searches. Resuming it
  reads only what it keeps (`Progress.resume`), and gives the progress of the longer question
  (`resume_at`).
- **Its answer is the front door's** (`answer_at`): the evidence is read from the kept regions and
  searches. So a resumed question answers as asking afresh with all the rounds (`resumed_answer`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.Framework.FiniteModels (Signature)
open Mettapedia.Machines.LevinSearch (Family)

/-! ## Rounds resume -/

/-- **Rounds from a saved list** are the later rounds from the start. -/
theorem iterate_add (next : Pattern → List Pattern) (start : List Pattern) (rounds : ℕ) :
    ∀ extra, iterate next start (rounds + extra) = iterate next (iterate next start rounds) extra
  | 0 => rfl
  | extra + 1 => by
    rw [← Nat.add_assoc, iterate_succ, iterate_add next start rounds extra, ← iterate_succ]

variable {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ}

theorem reachable_eq_iterate (term : Pattern) : ∀ rounds,
    reachable relEnv language fuel term rounds =
      iterate (fun state => (stepsAt relEnv language fuel state).map (·.2)) [term] rounds
  | 0 => rfl
  | rounds + 1 => by
    rw [iterate_succ, ← reachable_eq_iterate term rounds]
    rfl

theorem grow_eq_iterate (term : Pattern) : ∀ rounds,
    grow relEnv language fuel term rounds = iterate (nextTerms relEnv language fuel) [term] rounds
  | 0 => rfl
  | rounds + 1 => by
    rw [iterate_succ, ← grow_eq_iterate term rounds]
    rfl

/-- Levin search continued from what earlier rounds found, starting at a round. -/
def searchFrom {ι α : Type} (family : Family ι α) (found : Option α) (start : ℕ) : ℕ → Option α
  | 0 => found
  | extra + 1 => (searchFrom family found start extra).or (family.phase (start + extra))

/-- **Levin search resumes** from what the first rounds found. -/
theorem search_add {ι α : Type} (family : Family ι α) (rounds : ℕ) :
    ∀ extra, family.search (rounds + extra) = searchFrom family (family.search rounds) rounds extra
  | 0 => rfl
  | extra + 1 => by
    show (family.search (rounds + extra)).or (family.phase (rounds + extra)) = _
    rw [search_add family rounds extra]
    rfl

/-! ## Reading regions -/

/-- A test of a region's first term; false on an empty region. -/
def atFirst (region : List Pattern) (read : Fin region.length → Bool) : Bool :=
  if inside : 0 < region.length then read ⟨0, inside⟩ else false

variable (relEnv language fuel)

/-- An existential formula holds in a region at its first term. -/
def exploresIn (region : List Pattern) (formula : Formula 0) : Bool :=
  atFirst region (explores relEnv language fuel region formula)

/-- The verdict of a closed region at its first term. -/
def decideIn (region : List Pattern) (formula : Formula 0) : Option Bool :=
  if closedRegion relEnv language fuel region then
    if inside : 0 < region.length then some ((exploration relEnv language fuel region).check formula ⟨0, inside⟩)
    else none
  else none

/-- The verdict of a closed canonical region at its first term. -/
def decideCanonicalIn (canon : Pattern → Pattern) (domain : Pattern → Bool) (presentations : Pattern → List Pattern)
    (admitted : Bool) (region : List Pattern) (formula : Formula 0) (rules : RuleReading := .reference) : Option Bool :=
  if admitted && canonicalRegion relEnv language fuel canon domain presentations region rules then
    if inside : 0 < region.length then
      some ((canonicalExploration relEnv language fuel canon domain presentations region rules).check formula
        ⟨0, inside⟩)
    else none
  else none

variable {relEnv language fuel}

theorem exploresFrom_eq (formula : Formula 0) (term : Pattern) (rounds : ℕ) :
    exploresFrom relEnv language fuel formula term rounds =
      exploresIn relEnv language fuel (reachable relEnv language fuel term rounds) formula := by
  unfold exploresFrom exploresIn atFirst
  rw [dif_pos (reachable_length_pos relEnv language fuel term rounds)]

theorem decideFrom_eq (formula : Formula 0) (term : Pattern) (rounds : ℕ) :
    decideFrom relEnv language fuel formula term rounds =
      decideIn relEnv language fuel (grow relEnv language fuel term rounds) formula := by
  unfold decideFrom decideIn
  rw [dif_pos (grow_length_pos relEnv language fuel term rounds)]

theorem decideCanonical_eq (canon : Pattern → Pattern) (domain : Pattern → Bool)
    (presentations : Pattern → List Pattern) (formula : Formula 0) (term : Pattern) (rounds : ℕ)
    (rules : RuleReading := .reference) :
    decideCanonical relEnv language fuel canon domain presentations formula term rounds rules =
      decideCanonicalIn relEnv language fuel canon domain presentations (domain term)
        (growCanonical relEnv language fuel canon presentations term rounds rules)
        formula rules := by
  unfold decideCanonical decideCanonicalIn
  rw [dif_pos (growCanonical_length_pos relEnv language fuel canon presentations term rounds rules)]

/-! ## Progress -/

variable (signature : Signature) (language) (formula : Formula 0) (term : Pattern)

/-- **The work of a question so far**: the rounds done, the region the term reaches, the region grown with
parts, the canonical region, and what the searches for a proof and a refutation found. -/
structure Progress where
  rounds : ℕ
  reached : List Pattern
  grown : List Pattern
  canonical : List Pattern
  proof : Option {candidate : CertificateCandidate // provesBy signature language formula term candidate = true}
  refutation : Option {candidate : CertificateCandidate // refutesBy signature language formula term candidate = true}

variable (relEnv fuel) (canon : Pattern → Pattern) (presentations : Pattern → List Pattern)

/-- The progress of a question after some rounds. -/
def Progress.at (rounds : ℕ) (rules : RuleReading := .reference) : Progress language signature formula term :=
  ⟨rounds, reachable relEnv language fuel term rounds, grow relEnv language fuel term rounds,
    growCanonical relEnv language fuel canon presentations term rounds rules,
    explain CertificateCandidate.decode CertificateCandidate.cost (provesBy signature language formula term) rounds,
    explain CertificateCandidate.decode CertificateCandidate.cost (refutesBy signature language formula term) rounds⟩

variable {signature language formula term}

/-- **Resume** a question for more rounds, from what its progress keeps. -/
def Progress.resume (progress : Progress language signature formula term) (extra : ℕ)
    (rules : RuleReading := .reference) : Progress language signature formula term :=
  ⟨progress.rounds + extra,
    iterate (fun state => (stepsAt relEnv language fuel state).map (·.2)) progress.reached extra,
    iterate (nextTerms relEnv language fuel) progress.grown extra,
    iterate (fun state => nextCanonical relEnv language fuel canon presentations state rules) progress.canonical extra,
    searchFrom (explanations CertificateCandidate.decode CertificateCandidate.cost
      (provesBy signature language formula term)) progress.proof progress.rounds extra,
    searchFrom (explanations CertificateCandidate.decode CertificateCandidate.cost
      (refutesBy signature language formula term)) progress.refutation progress.rounds extra⟩

/-- **Resuming gives the progress of the longer question.** -/
theorem resume_at (rounds extra : ℕ) (rules : RuleReading := .reference) :
    (Progress.at relEnv language fuel signature formula term canon presentations rounds rules).resume relEnv fuel canon
        presentations extra rules =
      Progress.at relEnv language fuel signature formula term canon presentations (rounds + extra) rules := by
  simp only [Progress.at, Progress.resume, reachable_eq_iterate, grow_eq_iterate, growCanonical_eq_iterate _ rules,
    iterate_add, explain, search_add]

/-! ## Answers from progress -/

/-- Whether evidence establishes the formula, read from the progress. -/
def Progress.establishes (forms : Option (CanonicalForms relEnv language fuel))
    (progress : Progress language signature formula term) : Evidence → Bool
  | .certificate candidate => formsReference forms && provesBy signature language formula term candidate
  | .exploration _ => formsReference forms && exploresIn relEnv language fuel progress.reached formula
  | .closedRegion _ => formsReference forms && language.isEquationFree && formula.forward &&
      decideIn relEnv language fuel progress.grown formula == some true
  | .canonicalRegion _ => match forms with
    | some forms => formula.behaviouralIn forms.labels &&
        decideCanonicalIn relEnv language fuel forms.canon forms.domain forms.presentations (forms.domain term)
          progress.canonical formula forms.reading.rules == some true
    | none => false
  | .backward _ => formsReference forms && backwardEstablishes language formula term progress.rounds
  | .decided => false

/-- Whether evidence refutes the formula, read from the progress. -/
def Progress.refutes (forms : Option (CanonicalForms relEnv language fuel))
    (progress : Progress language signature formula term) : Evidence → Bool
  | .certificate candidate => formsReference forms && refutesBy signature language formula term candidate
  | .exploration _ => formsReference forms && exploresIn relEnv language fuel progress.reached formula.dual
  | .closedRegion _ => formsReference forms && language.isEquationFree && formula.forward &&
      decideIn relEnv language fuel progress.grown formula == some false
  | .canonicalRegion _ => match forms with
    | some forms => formula.behaviouralIn forms.labels &&
        decideCanonicalIn relEnv language fuel forms.canon forms.domain forms.presentations (forms.domain term)
          progress.canonical formula forms.reading.rules == some false
    | none => false
  | .backward _ => formsReference forms && backwardRefutes language formula term progress.rounds
  | .decided => false

/-- The evidence the progress holds. -/
def Progress.gathered (hint : Option CertificateCandidate) (progress : Progress language signature formula term) :
    List Evidence :=
  hint.toList.map .certificate ++
    [.exploration progress.rounds, .closedRegion progress.rounds, .canonicalRegion progress.rounds] ++
    progress.proof.toList.map (.certificate ·.1) ++ progress.refutation.toList.map (.certificate ·.1) ++
      [.backward progress.rounds]

/-- **The answer the progress gives.** -/
def Progress.answer (forms : Option (CanonicalForms relEnv language fuel)) (hint : Option CertificateCandidate)
    (progress : Progress language signature formula term) : Answer :=
  match (progress.gathered hint).find? (progress.establishes relEnv fuel forms) with
  | some evidence => .proved evidence
  | none =>
    match (progress.gathered hint).find? (progress.refutes relEnv fuel forms) with
    | some evidence => .refuted evidence
    | none => .unknown progress.rounds

theorem find?_congr {α : Type} {first second : α → Bool} : ∀ {elements : List α},
    (∀ element ∈ elements, first element = second element) → elements.find? first = elements.find? second
  | [], _ => rfl
  | element :: elements, same => by
    rw [List.find?_cons, List.find?_cons, same element List.mem_cons_self,
      find?_congr fun other inside => same other (List.mem_cons_of_mem _ inside)]

/-- The canonical forms' function, or the identity. -/
def canonOf {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ}
    (forms : Option (CanonicalForms relEnv language fuel)) : Pattern → Pattern :=
  match forms with
  | some forms => forms.canon
  | none => id

/-- The canonical forms' presentations, or each term as itself. -/
def presentationsOf {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ}
    (forms : Option (CanonicalForms relEnv language fuel)) : Pattern → List Pattern :=
  match forms with
  | some forms => forms.presentations
  | none => List.singleton

/-- The canonical forms' reading of the rules, or the reference relation. -/
def rulesOf {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ}
    (forms : Option (CanonicalForms relEnv language fuel)) : RuleReading :=
  (formsReading forms).rules

/-- **The progress after some rounds answers as the front door.** -/
theorem answer_at (forms : Option (CanonicalForms relEnv language fuel)) (hint : Option CertificateCandidate)
    (rounds : ℕ) :
    (Progress.at relEnv language fuel signature formula term (canonOf forms) (presentationsOf forms)
        rounds (rulesOf forms)).answer relEnv fuel forms hint =
      ask relEnv signature language fuel formula term hint rounds forms := by
  have sameGathered : (Progress.at relEnv language fuel signature formula term (canonOf forms)
    (presentationsOf forms) rounds (rulesOf forms)).gathered hint =
      gathered signature language formula term hint rounds := rfl
  have members : ∀ evidence ∈ gathered signature language formula term hint rounds,
      evidence = .exploration rounds ∨ evidence = .closedRegion rounds ∨ evidence = .canonicalRegion rounds ∨
        evidence = .backward rounds ∨ ∃ candidate, evidence = .certificate candidate := by
    intro evidence inside
    simp only [gathered, List.mem_append, List.mem_map, Option.mem_toList, List.mem_cons, List.not_mem_nil,
      or_false] at inside
    rcases inside with (((⟨candidate, -, rfl⟩ | rfl | rfl | rfl) | ⟨found, -, rfl⟩) | ⟨found, -, rfl⟩) | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨candidate, rfl⟩)))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨found.1, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨found.1, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have establishes : ∀ evidence ∈ gathered signature language formula term hint rounds,
      (Progress.at relEnv language fuel signature formula term (canonOf forms)
        (presentationsOf forms) rounds (rulesOf forms)).establishes relEnv fuel
          forms evidence =
        evidence.establishes relEnv signature language fuel formula term forms := by
    intro evidence inside
    rcases members evidence inside with rfl | rfl | rfl | rfl | ⟨candidate, rfl⟩
    · simp only [Progress.establishes, Evidence.establishes, Progress.at, exploresFrom_eq]
    · simp only [Progress.establishes, Evidence.establishes, Progress.at, decideFrom_eq]
    · cases forms with
      | none => rfl
      | some forms => simp only [Progress.establishes, Evidence.establishes, Progress.at, canonOf, presentationsOf,
        rulesOf, formsReading, decideCanonical_eq]
    · rfl
    · rfl
  have refutes : ∀ evidence ∈ gathered signature language formula term hint rounds,
      (Progress.at relEnv language fuel signature formula term (canonOf forms)
        (presentationsOf forms) rounds (rulesOf forms)).refutes relEnv fuel
          forms evidence =
        evidence.refutes relEnv signature language fuel formula term forms := by
    intro evidence inside
    rcases members evidence inside with rfl | rfl | rfl | rfl | ⟨candidate, rfl⟩
    · simp only [Progress.refutes, Evidence.refutes, Progress.at, exploresAgainstFrom, exploresFrom_eq]
    · simp only [Progress.refutes, Evidence.refutes, Progress.at, decideFrom_eq]
    · cases forms with
      | none => rfl
      | some forms => simp only [Progress.refutes, Evidence.refutes, Progress.at, canonOf, presentationsOf,
        rulesOf, formsReading, decideCanonical_eq]
    · rfl
    · rfl
  unfold Progress.answer ask
  rw [sameGathered, find?_congr establishes, find?_congr refutes]
  rfl

/-- **A resumed question answers as asking afresh with all the rounds.** -/
theorem resumed_answer (forms : Option (CanonicalForms relEnv language fuel)) (hint : Option CertificateCandidate)
    (rounds extra : ℕ) :
    ((Progress.at relEnv language fuel signature formula term (canonOf forms) (presentationsOf forms)
        rounds (rulesOf forms)).resume relEnv fuel (canonOf forms) (presentationsOf forms) extra (rulesOf forms)).answer
        relEnv fuel forms hint =
      ask relEnv signature language fuel formula term hint (rounds + extra) forms := by
  rw [resume_at (rules := rulesOf forms), answer_at]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
