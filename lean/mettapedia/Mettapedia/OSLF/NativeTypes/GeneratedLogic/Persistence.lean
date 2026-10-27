import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Resumption

/-!
# Decided answers stay decided

More rounds never undo an answer of the front door. A proved question stays proved, and a refuted one
stays refuted (`ask_proved_persists`, `ask_refuted_persists`). Each kind of evidence persists:

- **The region a term reaches** grows by extension. An existential formula that holds at its first term
  holds there in every extension (`appendHom`, `exploresFrom_persists`).
- **A closed region** adds nothing in later rounds, since growing asks no more than closedness
  (`grow_still_of_closed`), so its verdict stays (`decideFrom_persists`). The same holds for **a closed
  canonical region** (`decideCanonical_persists`).
- **Levin search** keeps what it found (`search_persists`).

**The portfolio is fair** (`ask_settled_of_evidence`): when any one kind of evidence decides the question
at some rounds, the front door answers at those rounds and at every later one. Sharing the rounds starves
no strategy: the region a term reaches (`ask_settled_of_explored`), a closed region
(`ask_settled_of_closed`), a closed canonical region (`ask_settled_of_canonical`), a backward search
(`ask_settled_of_backward`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.Framework.FiniteModels (Signature)
open Mettapedia.Machines.LevinSearch (Family)

/-! ## Rounds extend -/

theorem addNew_of_subset : ∀ {seen terms : List Pattern}, (∀ term ∈ terms, term ∈ seen) → addNew seen terms = seen
  | _, [], _ => rfl
  | seen, first :: rest, inside => by
    unfold addNew
    rw [if_pos (inside first List.mem_cons_self)]
    exact addNew_of_subset fun term member => inside term (List.mem_cons_of_mem _ member)

theorem iterate_prefix {next : Pattern → List Pattern} {start : List Pattern} {rounds : ℕ} :
    ∀ {more}, rounds ≤ more → iterate next start rounds <+: iterate next start more := by
  intro more le
  induction le with
  | refl => exact List.prefix_refl _
  | @step later _ previous =>
    rw [iterate_succ]
    obtain ⟨extra, same⟩ := addNew_extends (iterate next start later) ((iterate next start later).flatMap next)
    rw [same]
    exact previous.trans (List.prefix_append _ _)

/-- **Levin search keeps what it found.** -/
theorem search_persists {ι α : Type} (family : Family ι α) {rounds more : ℕ} {found : α}
    (searched : family.search rounds = some found) (le : rounds ≤ more) : family.search more = some found := by
  induction le with
  | refl => exact searched
  | @step later _ previous =>
    show (family.search later).or (family.phase later) = some found
    rw [previous]
    rfl

/-! ## Closed regions stay -/

variable {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ}

/-- **A closed region adds nothing in the next round.** -/
theorem grow_still_of_closed {term : Pattern} {rounds : ℕ}
    (closed : closedRegion relEnv language fuel (grow relEnv language fuel term rounds) = true) :
    grow relEnv language fuel term (rounds + 1) = grow relEnv language fuel term rounds := by
  rw [grow_succ]
  apply addNew_of_subset
  intro other inside
  obtain ⟨state, member, listed⟩ := List.mem_flatMap.mp inside
  simp only [closedRegion, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at closed
  obtain ⟨successors, parts⟩ := closed.2 state member
  rcases List.mem_append.mp listed with listed | listed
  · by_cases isState : isStateBool state = true
    · rw [if_pos isState] at listed
      obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp listed
      rcases successors with notState | ⟨-, all⟩
      · rw [notState] at isState
        cases isState
      · exact all entry entryMember
    · rw [if_neg isState] at listed
      cases listed
  · exact parts other listed

/-- **The verdict of a closed region stays.** -/
theorem decideFrom_persists {formula : Formula 0} {term : Pattern} {rounds more : ℕ} {verdict : Bool}
    (decided : decideFrom relEnv language fuel formula term rounds = some verdict) (le : rounds ≤ more) :
    decideFrom relEnv language fuel formula term more = some verdict := by
  have closed : closedRegion relEnv language fuel (grow relEnv language fuel term rounds) = true := by
    unfold decideFrom at decided
    split at decided
    · assumption
    · cases decided
  have stays := grow_stays (grow_still_of_closed closed) (more - rounds)
  rw [show rounds + (more - rounds) = more by omega] at stays
  rw [decideFrom_eq] at decided ⊢
  rw [stays]
  exact decided

/-- **A closed canonical region adds nothing in the next round.** -/
theorem growCanonical_still_of_closed {canon : Pattern → Pattern} {domain : Pattern → Bool}
    {presentations : Pattern → List Pattern} {term : Pattern}
    {rounds : ℕ} {rules : RuleReading}
    (closed : canonicalRegion relEnv language fuel canon domain presentations
      (growCanonical relEnv language fuel canon presentations term rounds rules) rules =
      true) :
    growCanonical relEnv language fuel canon presentations term (rounds + 1) rules =
      growCanonical relEnv language fuel canon presentations term rounds rules := by
  obtain ⟨-, all⟩ := canonicalRegion_parts closed
  rw [growCanonical_eq_iterate term rules, growCanonical_eq_iterate term rules, iterate_succ]
  rw [growCanonical_eq_iterate term rules] at all
  apply addNew_of_subset
  intro other inside
  obtain ⟨state, member, listed⟩ := List.mem_flatMap.mp inside
  obtain ⟨-, -, listing⟩ := all state member
  by_cases isState : isStateBool state = true
  · rw [nextCanonical, if_pos isState] at listed
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp listed
    exact (listing isState).2.2 entry entryMember
  · rw [nextCanonical, if_neg isState] at listed
    cases listed

/-- **The verdict of a closed canonical region stays.** -/
theorem decideCanonical_persists {canon : Pattern → Pattern} {domain : Pattern → Bool}
    {presentations : Pattern → List Pattern} {formula : Formula 0}
    {term : Pattern} {rounds more : ℕ} {verdict : Bool} {rules : RuleReading}
    (decided : decideCanonical relEnv language fuel canon domain presentations formula term rounds rules = some verdict)
    (le : rounds ≤ more) : decideCanonical relEnv language fuel canon domain presentations formula term more rules =
      some verdict := by
  have closed : canonicalRegion relEnv language fuel canon domain presentations
      (growCanonical relEnv language fuel canon presentations term rounds rules) rules = true := by
    unfold decideCanonical at decided
    split at decided
    · rename_i checked
      exact (Bool.and_eq_true_iff.mp checked).2
    · cases decided
  have still := growCanonical_still_of_closed closed
  rw [growCanonical_eq_iterate term rules, growCanonical_eq_iterate term rules] at still
  have stays := iterate_stays still (more - rounds)
  rw [show rounds + (more - rounds) = more by omega, ← growCanonical_eq_iterate term rules,
    ← growCanonical_eq_iterate term rules] at stays
  rw [decideCanonical_eq (rules := rules)] at decided ⊢
  rw [stays]
  exact decided

/-! ## Explored regions extend -/

variable (relEnv language fuel)

/-- **A region sits inside each extension of it.** -/
def appendHom (region tail : List Pattern) :
    Hom (exploration relEnv language fuel region).native (exploration relEnv language fuel (region ++ tail)).native where
  map index := ⟨index, by rw [List.length_append]; omega⟩
  step := by
    intro source label target _ checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  built := by
    intro element constructor parts checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left, Function.comp_def] using checked
  split := by
    intro element kind first second checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  empty := by
    intro element kind checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  single := by
    intro element kind member checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  body := by
    intro element inner checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  multiBody := by
    intro element arity inner checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  bound := by
    intro element index checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  typed := by
    intro element type checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  named := by
    intro element term checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked
  inRelation := by
    intro element relation checked
    simpa [FiniteStructure.native, exploration, List.getElem_append_left] using checked

variable {relEnv language fuel}

theorem exploresIn_append {region : List Pattern} (tail : List Pattern) {formula : Formula 0}
    (explored : exploresIn relEnv language fuel region formula = true) :
    exploresIn relEnv language fuel (region ++ tail) formula = true := by
  unfold exploresIn atFirst at explored ⊢
  split at explored
  · rename_i inside
    rw [dif_pos (by rw [List.length_append]; omega)]
    simp only [explores, Bool.and_eq_true] at explored ⊢
    refine ⟨explored.1, ?_⟩
    rw [FiniteStructure.check_iff] at explored ⊢
    exact (appendHom relEnv language fuel region tail).sat_of_hom formula explored.1 (sourceEnv := Env.closed)
      (targetEnv := Env.closed) (fun index => index.elim0) _ explored.2
  · cases explored

/-- **What the region a term reaches shows stays shown.** -/
theorem exploresFrom_persists {formula : Formula 0} {term : Pattern} {rounds more : ℕ}
    (explored : exploresFrom relEnv language fuel formula term rounds = true) (le : rounds ≤ more) :
    exploresFrom relEnv language fuel formula term more = true := by
  rw [exploresFrom_eq, reachable_eq_iterate] at explored ⊢
  obtain ⟨tail, same⟩ := iterate_prefix (next := fun state => (stepsAt relEnv language fuel state).map (·.2))
    (start := [term]) le
  rw [← same]
  exact exploresIn_append tail explored

/-! ## Answers stay -/

variable {signature : Signature} {formula : Formula 0} {term : Pattern}

theorem mem_gathered {hint : Option CertificateCandidate} {rounds : ℕ} {evidence : Evidence}
    (member : evidence ∈ gathered signature language formula term hint rounds) :
    (∃ candidate ∈ hint, evidence = .certificate candidate) ∨ evidence = .exploration rounds ∨
      evidence = .closedRegion rounds ∨ evidence = .canonicalRegion rounds ∨
      (∃ found, explain CertificateCandidate.decode CertificateCandidate.cost (provesBy signature language formula term)
        rounds = some found ∧ evidence = .certificate found.1) ∨
      (∃ found, explain CertificateCandidate.decode CertificateCandidate.cost (refutesBy signature language formula term)
        rounds = some found ∧ evidence = .certificate found.1) ∨ evidence = .backward rounds := by
  simp only [gathered, List.mem_append, List.mem_map, Option.mem_toList, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with (((⟨candidate, inHint, rfl⟩ | rfl | rfl | rfl) | ⟨found, inProofs, rfl⟩) |
      ⟨found, inRefutations, rfl⟩) | rfl
  · exact Or.inl ⟨candidate, inHint, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨found, inProofs, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨found, inRefutations, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem certificate_mem_gathered_of_hint {hint : Option CertificateCandidate} {rounds : ℕ} {candidate : CertificateCandidate}
    (inHint : candidate ∈ hint) : Evidence.certificate candidate ∈ gathered signature language formula term hint rounds := by
  simp only [gathered, List.mem_append, List.mem_map, Option.mem_toList]
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨candidate, inHint, rfl⟩)))

/-- **Evidence that establishes the formula at some rounds** has a counterpart that does at more. -/
theorem establishes_persists {forms : Option (CanonicalForms relEnv language fuel)} {hint : Option CertificateCandidate}
    {rounds more : ℕ} (le : rounds ≤ more) {evidence : Evidence}
    (member : evidence ∈ gathered signature language formula term hint rounds)
    (checked : evidence.establishes relEnv signature language fuel formula term forms = true) :
    ∃ later ∈ gathered signature language formula term hint more,
      later.establishes relEnv signature language fuel formula term forms = true := by
  rcases mem_gathered member with ⟨candidate, inHint, rfl⟩ | rfl | rfl | rfl | ⟨found, inProofs, rfl⟩ |
      ⟨found, inRefutations, rfl⟩ | rfl
  · exact ⟨_, certificate_mem_gathered_of_hint inHint, checked⟩
  · refine ⟨.exploration more, by simp [gathered], ?_⟩
    simp only [Evidence.establishes, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, exploresFrom_persists checked.2 le⟩
  · refine ⟨.closedRegion more, by simp [gathered], ?_⟩
    simp only [Evidence.establishes, Bool.and_eq_true, beq_iff_eq] at checked ⊢
    exact ⟨checked.1, decideFrom_persists checked.2 le⟩
  · refine ⟨.canonicalRegion more, by simp [gathered], ?_⟩
    cases forms with
    | none => cases checked
    | some forms =>
      simp only [Evidence.establishes, Bool.and_eq_true, beq_iff_eq] at checked ⊢
      exact ⟨checked.1, decideCanonical_persists checked.2 le⟩
  · have kept := search_persists _ inProofs le
    exact ⟨.certificate found.1, by simp [gathered, explain, kept], checked⟩
  · have kept := search_persists _ inRefutations le
    exact ⟨.certificate found.1, by simp [gathered, explain, kept], checked⟩
  · refine ⟨.backward more, by simp [gathered], ?_⟩
    simp only [Evidence.establishes, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, backwardEstablishes_mono le checked.2⟩

/-- **Evidence that refutes the formula at some rounds** has a counterpart that does at more. -/
theorem refutes_persists {forms : Option (CanonicalForms relEnv language fuel)} {hint : Option CertificateCandidate}
    {rounds more : ℕ} (le : rounds ≤ more) {evidence : Evidence}
    (member : evidence ∈ gathered signature language formula term hint rounds)
    (checked : evidence.refutes relEnv signature language fuel formula term forms = true) :
    ∃ later ∈ gathered signature language formula term hint more,
      later.refutes relEnv signature language fuel formula term forms = true := by
  rcases mem_gathered member with ⟨candidate, inHint, rfl⟩ | rfl | rfl | rfl | ⟨found, inProofs, rfl⟩ |
      ⟨found, inRefutations, rfl⟩ | rfl
  · exact ⟨_, certificate_mem_gathered_of_hint inHint, checked⟩
  · refine ⟨.exploration more, by simp [gathered], ?_⟩
    simp only [Evidence.refutes, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, exploresFrom_persists checked.2 le⟩
  · refine ⟨.closedRegion more, by simp [gathered], ?_⟩
    simp only [Evidence.refutes, Bool.and_eq_true, beq_iff_eq] at checked ⊢
    exact ⟨checked.1, decideFrom_persists checked.2 le⟩
  · refine ⟨.canonicalRegion more, by simp [gathered], ?_⟩
    cases forms with
    | none => cases checked
    | some forms =>
      simp only [Evidence.refutes, Bool.and_eq_true, beq_iff_eq] at checked ⊢
      exact ⟨checked.1, decideCanonical_persists checked.2 le⟩
  · have kept := search_persists _ inProofs le
    exact ⟨.certificate found.1, by simp [gathered, explain, kept], checked⟩
  · have kept := search_persists _ inRefutations le
    exact ⟨.certificate found.1, by simp [gathered, explain, kept], checked⟩
  · refine ⟨.backward more, by simp [gathered], ?_⟩
    simp only [Evidence.refutes, Bool.and_eq_true] at checked ⊢
    exact ⟨checked.1, backwardRefutes_mono le checked.2⟩

/-- **A proved question stays proved** with more rounds. -/
theorem ask_proved_persists {forms : Option (CanonicalForms relEnv language fuel)} {hint : Option CertificateCandidate}
    {rounds more : ℕ} (le : rounds ≤ more) {evidence : Evidence}
    (answered : ask relEnv signature language fuel formula term hint rounds forms = .proved evidence) :
    ∃ later, ask relEnv signature language fuel formula term hint more forms = .proved later := by
  unfold ask at answered
  split at answered
  · rename_i found
    obtain ⟨later, member, checked⟩ :=
      establishes_persists le (List.mem_of_find?_eq_some found) (List.find?_some found)
    unfold ask
    split
    · rename_i laterEvidence _
      exact ⟨laterEvidence, rfl⟩
    · rename_i none
      exact absurd checked (by simpa using List.find?_eq_none.mp none later member)
  · split at answered <;> cases answered

/-- **A refuted question stays refuted** with more rounds. -/
theorem ask_refuted_persists {forms : Option (CanonicalForms relEnv language fuel)} {hint : Option CertificateCandidate}
    {rounds more : ℕ} (le : rounds ≤ more) {evidence : Evidence}
    (answered : ask relEnv signature language fuel formula term hint rounds forms = .refuted evidence) :
    ∃ later, ask relEnv signature language fuel formula term hint more forms = .refuted later := by
  unfold ask at answered
  split at answered
  · cases answered
  · split at answered
    · rename_i found
      obtain ⟨later, member, checked⟩ :=
        refutes_persists le (List.mem_of_find?_eq_some found) (List.find?_some found)
      have fails := Evidence.refutes_sound (formsFor_formsReading forms) checked
      unfold ask
      split
      · rename_i proving
        exact absurd (Evidence.establishes_sound (formsFor_formsReading forms) (List.find?_some proving)) fails
      · split
        · rename_i laterEvidence _
          exact ⟨laterEvidence, rfl⟩
        · rename_i none
          exact absurd checked (by simpa using List.find?_eq_none.mp none later member)
    · cases answered

/-! ## The portfolio is fair -/

/-- The front door answers at the rounds where some gathered evidence decides the question. -/
theorem ask_settled_here {forms : Option (CanonicalForms relEnv language fuel)} {hint : Option CertificateCandidate}
    {rounds : ℕ} {evidence : Evidence} (member : evidence ∈ gathered signature language formula term hint rounds)
    (decides : evidence.establishes relEnv signature language fuel formula term forms = true ∨
      evidence.refutes relEnv signature language fuel formula term forms = true) :
    ∃ answer, ask relEnv signature language fuel formula term hint rounds forms = .proved answer ∨
      ask relEnv signature language fuel formula term hint rounds forms = .refuted answer := by
  unfold ask
  split
  · rename_i found _
    exact ⟨found, Or.inl rfl⟩
  · rename_i none
    split
    · rename_i found _
      exact ⟨found, Or.inr rfl⟩
    · rename_i noRefutation
      exfalso
      rcases decides with proving | refuting
      · exact absurd proving (by simpa using List.find?_eq_none.mp none evidence member)
      · exact absurd refuting (by simpa using List.find?_eq_none.mp noRefutation evidence member)

/-- **When any gathered evidence decides the question, the front door answers then and at every later
round.** -/
theorem ask_settled_of_evidence {forms : Option (CanonicalForms relEnv language fuel)}
    {hint : Option CertificateCandidate} {rounds : ℕ} {evidence : Evidence}
    (member : evidence ∈ gathered signature language formula term hint rounds)
    (decides : evidence.establishes relEnv signature language fuel formula term forms = true ∨
      evidence.refutes relEnv signature language fuel formula term forms = true) {more : ℕ} (le : rounds ≤ more) :
    ∃ answer, ask relEnv signature language fuel formula term hint more forms = .proved answer ∨
      ask relEnv signature language fuel formula term hint more forms = .refuted answer := by
  obtain ⟨answer, settled⟩ := ask_settled_here member decides
  rcases settled with proved | refuted
  · obtain ⟨later, kept⟩ := ask_proved_persists le proved
    exact ⟨later, Or.inl kept⟩
  · obtain ⟨later, kept⟩ := ask_refuted_persists le refuted
    exact ⟨later, Or.inr kept⟩

/-- **The region a term reaches**: when it shows the formula, the front door answers from then on. -/
theorem ask_settled_of_explored {forms : Option (CanonicalForms relEnv language fuel)}
    {hint : Option CertificateCandidate} {rounds : ℕ}
    (explored : exploresFrom relEnv language fuel formula term rounds = true ∨
      exploresAgainstFrom relEnv language fuel formula term rounds = true) {more : ℕ} (le : rounds ≤ more)
    (reference : formsReference forms = true := by rfl) :
    ∃ answer, ask relEnv signature language fuel formula term hint more forms = .proved answer ∨
      ask relEnv signature language fuel formula term hint more forms = .refuted answer :=
  ask_settled_of_evidence (evidence := .exploration rounds) (by simp [gathered])
    (by simpa [Evidence.establishes, Evidence.refutes, reference] using explored) le

/-- **A closed region**: when it closes on an equation-free language, the front door answers every forward
formula from then on. -/
theorem ask_settled_of_closed {forms : Option (CanonicalForms relEnv language fuel)}
    {hint : Option CertificateCandidate} {rounds : ℕ} {verdict : Bool} (free : language.isEquationFree = true)
    (forward : formula.forward = true) (decided : decideFrom relEnv language fuel formula term rounds = some verdict)
    {more : ℕ} (le : rounds ≤ more) (reference : formsReference forms = true := by rfl) :
    ∃ answer, ask relEnv signature language fuel formula term hint more forms = .proved answer ∨
      ask relEnv signature language fuel formula term hint more forms = .refuted answer := by
  refine ask_settled_of_evidence (evidence := .closedRegion rounds) (by simp [gathered]) ?_ le
  cases verdict
  · exact Or.inr (by simp [Evidence.refutes, free, forward, decided, reference])
  · exact Or.inl (by simp [Evidence.establishes, free, forward, decided, reference])

/-- **A closed canonical region**: given canonical forms, when it closes, the front door answers every
behavioural formula from then on. -/
theorem ask_settled_of_canonical (forms : CanonicalForms relEnv language fuel) {hint : Option CertificateCandidate}
    {rounds : ℕ} {verdict : Bool} (behavioural : formula.behaviouralIn forms.labels = true)
    (decided : decideCanonical relEnv language fuel forms.canon forms.domain forms.presentations formula term rounds
      forms.reading.rules = some verdict)
    {more : ℕ} (le : rounds ≤ more) :
    ∃ answer, ask relEnv signature language fuel formula term hint more (some forms) = .proved answer ∨
      ask relEnv signature language fuel formula term hint more (some forms) = .refuted answer := by
  refine ask_settled_of_evidence (evidence := .canonicalRegion rounds) (by simp [gathered]) ?_ le
  cases verdict
  · exact Or.inr (by simp [Evidence.refutes, behavioural, decided])
  · exact Or.inl (by simp [Evidence.establishes, behavioural, decided])

/-- **A backward search**: when it decides reaching named goals, or never reaching them, the front door answers from
then on. -/
theorem ask_settled_of_backward {forms : Option (CanonicalForms relEnv language fuel)} {hint : Option CertificateCandidate}
    {rounds : ℕ}
    (decides : backwardEstablishes language formula term rounds = true ∨ backwardRefutes language formula term rounds = true)
    {more : ℕ} (le : rounds ≤ more) (reference : formsReference forms = true := by rfl) :
    ∃ answer, ask relEnv signature language fuel formula term hint more forms = .proved answer ∨
      ask relEnv signature language fuel formula term hint more forms = .refuted answer :=
  ask_settled_of_evidence (evidence := .backward rounds) (by simp [gathered])
    (by simpa [Evidence.establishes, Evidence.refutes, reference] using decides) le

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
