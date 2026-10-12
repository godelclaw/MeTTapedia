import Mathlib.Computability.Halting

/-!
# Elementary formal systems

An elementary formal system in the sense of Smullyan is a finite list of
rules over strings. A rule has premises and a conclusion, each a word of
constants and variables. An instance replaces every variable by a string,
and an instance whose premises are derivable has a derivable conclusion.

A certificate is a list of lines, each naming a rule and a substitution. The
checker runs through the lines, keeps the strings derived so far, and
refuses a line whose rule is missing or whose premises have not been
derived. `derivable_iff_accepts` proves that a string is derivable exactly
when some certificate is accepted for it. The checker is primitive
recursive (`accepts_primrec`), so the derivable strings form a recursively
enumerable set (`derivable_re`).
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ElementaryFormalSystems

open Encodable

/-- A word of a rule: a variable `inl v` or a constant symbol `inr a`. -/
abbrev Word := List (ℕ ⊕ ℕ)

/-- A rule: its premises and its conclusion. -/
abbrev Rule := List Word × Word

/-- Replace every variable by its string; a variable past the list is empty. -/
def substitute (strings : List (List ℕ)) (word : Word) : List ℕ :=
  word.flatMap fun symbol => Sum.elim (fun index => strings.getD index []) (fun a => [a]) symbol

@[simp] theorem substitute_nil (strings : List (List ℕ)) : substitute strings [] = [] := rfl

@[simp] theorem substitute_cons (strings : List (List ℕ)) (symbol : ℕ ⊕ ℕ) (word : Word) :
    substitute strings (symbol :: word) =
      Sum.elim (fun index => strings.getD index []) (fun a => [a]) symbol ++
        substitute strings word := by
  simp [substitute]

@[simp] theorem substitute_append (strings : List (List ℕ)) (first second : Word) :
    substitute strings (first ++ second) =
      substitute strings first ++ substitute strings second := by
  simp [substitute]

/-- A word of constants is its own instance. -/
@[simp] theorem substitute_constants (strings : List (List ℕ)) (symbols : List ℕ) :
    substitute strings (symbols.map Sum.inr) = symbols := by
  induction symbols with
  | nil => rfl
  | cons a symbols ih => simp [ih]

/-- Derivability in an elementary formal system. -/
inductive Derivable (rules : List Rule) : List ℕ → Prop where
  | rule {rule : Rule} (member : rule ∈ rules) (strings : List (List ℕ)) :
      (∀ premise ∈ rule.1, Derivable rules (substitute strings premise)) →
      Derivable rules (substitute strings rule.2)

/-! ## Certificates -/

/-- A line of a certificate: a rule index and a substitution. -/
abbrev Line := ℕ × List (List ℕ)

/-- Membership, written as a fold. -/
def found (string : List ℕ) (derived : List (List ℕ)) : Bool :=
  derived.foldr (fun other rest => decide (other = string) || rest) false

theorem found_iff (string : List ℕ) (derived : List (List ℕ)) :
    found string derived = true ↔ string ∈ derived := by
  induction derived with
  | nil => simp [found]
  | cons other derived ih =>
      simp only [found, List.foldr_cons, Bool.or_eq_true, decide_eq_true_eq,
        List.mem_cons] at ih ⊢
      rw [ih, eq_comm]

/-- All premises of a rule instance have been derived. -/
def premisesFound (strings : List (List ℕ)) (derived : List (List ℕ)) (premises : List Word) :
    Bool :=
  premises.foldr (fun premise rest => found (substitute strings premise) derived && rest) true

theorem premisesFound_iff (strings : List (List ℕ)) (derived : List (List ℕ))
    (premises : List Word) :
    premisesFound strings derived premises = true ↔
      ∀ premise ∈ premises, substitute strings premise ∈ derived := by
  induction premises with
  | nil => simp [premisesFound]
  | cons premise premises ih =>
      simp only [premisesFound, List.foldr_cons, Bool.and_eq_true, List.mem_cons,
        forall_eq_or_imp] at ih ⊢
      rw [found_iff, ih]

/-- One line: the strings derived so far, and whether every line so far was valid. -/
def step (rules : List Rule) (state : List (List ℕ) × Bool) (line : Line) :
    List (List ℕ) × Bool :=
  match rules[line.1]? with
  | none => (state.1, false)
  | some rule => (state.1 ++ [substitute line.2 rule.2],
      state.2 && premisesFound line.2 state.1 rule.1)

/-- Run a certificate from a state. -/
def run (rules : List Rule) (state : List (List ℕ) × Bool) (certificate : List Line) :
    List (List ℕ) × Bool :=
  certificate.foldl (step rules) state

/-- A certificate is accepted for a string when every line is valid and the
string has been derived. -/
def accepts (rules : List Rule) (certificate : List Line) (goal : List ℕ) : Bool :=
  (run rules ([], true) certificate).2 && found goal (run rules ([], true) certificate).1

theorem run_append (rules : List Rule) (state : List (List ℕ) × Bool)
    (first second : List Line) :
    run rules state (first ++ second) = run rules (run rules state first) second := by
  simp [run, List.foldl_append]

theorem run_cons (rules : List Rule) (state : List (List ℕ) × Bool) (line : Line)
    (certificate : List Line) :
    run rules state (line :: certificate) = run rules (step rules state line) certificate := rfl

/-- A failed line stays failed. -/
theorem run_false (rules : List Rule) (derived : List (List ℕ)) :
    ∀ certificate : List Line, (run rules (derived, false) certificate).2 = false
  | [] => rfl
  | line :: certificate => by
      rw [run_cons]
      cases lookup : rules[line.1]? with
      | none => simpa [step, lookup] using run_false rules derived certificate
      | some rule => simpa [step, lookup] using run_false rules _ certificate

/-- **Soundness of the checker.** -/
theorem run_sound (rules : List Rule) :
    ∀ (certificate : List Line) (state : List (List ℕ) × Bool),
      (∀ string ∈ state.1, Derivable rules string) →
      (run rules state certificate).2 = true →
      ∀ string ∈ (run rules state certificate).1, Derivable rules string
  | [], state, derived, _ => derived
  | line :: certificate, state, derived, valid => by
      rw [run_cons] at valid ⊢
      cases lookup : rules[line.1]? with
      | none =>
          simp only [step, lookup] at valid
          rw [run_false] at valid
          exact absurd valid Bool.false_ne_true
      | some rule =>
          simp only [step, lookup] at valid ⊢
          rcases Bool.eq_false_or_eq_true (state.2 && premisesFound line.2 state.1 rule.1) with
            flag | flag
          · rw [flag] at valid ⊢
            apply run_sound rules certificate _ _ valid
            intro string member
            rcases List.mem_append.mp member with earlier | now
            · exact derived string earlier
            · rw [List.mem_singleton] at now
              subst now
              have premises := (premisesFound_iff _ _ _).mp (Bool.and_eq_true _ _ |>.mp flag).2
              exact Derivable.rule (List.mem_of_getElem? lookup) line.2
                fun premise inPremises => derived _ (premises premise inPremises)
          · rw [flag, run_false] at valid
            exact absurd valid Bool.false_ne_true

theorem append_subset {small large : List (List ℕ)} (included : small ⊆ large)
    (extra : List (List ℕ)) : small ++ extra ⊆ large ++ extra := by
  intro string member
  rcases List.mem_append.mp member with inSmall | inExtra
  · exact List.mem_append_left _ (included inSmall)
  · exact List.mem_append_right _ inExtra

/-- More derived strings at the start keep every valid certificate valid. -/
theorem run_mono (rules : List Rule) :
    ∀ (certificate : List Line) (small large : List (List ℕ)), small ⊆ large →
      (run rules (small, true) certificate).2 = true →
      (run rules (large, true) certificate).2 = true ∧
        (run rules (small, true) certificate).1 ⊆ (run rules (large, true) certificate).1
  | [], small, large, included, _ => ⟨rfl, included⟩
  | line :: certificate, small, large, included, valid => by
      rw [run_cons] at valid ⊢
      rw [run_cons]
      cases lookup : rules[line.1]? with
      | none =>
          simp only [step, lookup, run_false] at valid
          exact absurd valid Bool.false_ne_true
      | some rule =>
          simp only [step, lookup, Bool.true_and] at valid ⊢
          rcases Bool.eq_false_or_eq_true (premisesFound line.2 small rule.1) with flag | flag
          · rw [flag] at valid ⊢
            have larger : premisesFound line.2 large rule.1 = true := by
              rw [premisesFound_iff] at flag ⊢
              exact fun premise inPremises => included (flag premise inPremises)
            rw [larger]
            exact run_mono rules certificate _ _ (append_subset included _) valid
          · rw [flag, run_false] at valid
            exact absurd valid Bool.false_ne_true

/-- **Completeness of the checker.** Every derivable string has a certificate. -/
theorem certificate_exists (rules : List Rule) {string : List ℕ}
    (derivable : Derivable rules string) :
    ∃ certificate, (run rules ([], true) certificate).2 = true ∧
      string ∈ (run rules ([], true) certificate).1 := by
  induction derivable with
  | @rule rule member strings _ ih =>
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
      -- one certificate for all premises at once
      have premises : ∀ premises : List Word, (∀ premise ∈ premises,
          ∃ certificate, (run rules ([], true) certificate).2 = true ∧
            substitute strings premise ∈ (run rules ([], true) certificate).1) →
          ∃ certificate, (run rules ([], true) certificate).2 = true ∧
            ∀ premise ∈ premises,
              substitute strings premise ∈ (run rules ([], true) certificate).1 := by
        intro premises each
        induction premises with
        | nil => exact ⟨[], rfl, by simp⟩
        | cons premise premises ihPremises =>
            obtain ⟨first, firstValid, firstFound⟩ := each premise (by simp)
            obtain ⟨rest, restValid, restFound⟩ :=
              ihPremises fun other inOther => each other (by simp [inOther])
            obtain ⟨combinedValid, kept⟩ := run_mono rules rest []
              (run rules ([], true) first).1 (List.nil_subset _) restValid
            have firstState : run rules ([], true) first =
                ((run rules ([], true) first).1, true) := Prod.ext rfl firstValid
            refine ⟨first ++ rest, ?_, ?_⟩
            · rw [run_append, firstState]
              exact combinedValid
            · rw [run_append, firstState]
              intro other inOther
              rcases List.mem_cons.mp inOther with rfl | later
              · rw [run]
                have prefix_ : ∀ (certificate : List Line) (state : List (List ℕ) × Bool),
                    state.1 ⊆ (run rules state certificate).1 := by
                  intro certificate
                  induction certificate with
                  | nil => intro state; exact List.Subset.refl _
                  | cons line certificate ihLines =>
                      intro state
                      rw [run_cons]
                      refine List.Subset.trans ?_ (ihLines _)
                      cases lookup' : rules[line.1]? with
                      | none => simp [step, lookup']
                      | some rule' => simp [step, lookup']
                exact prefix_ rest _ firstFound
              · exact kept (restFound other later)
      obtain ⟨certificate, valid, allFound⟩ := premises rule.1 ih
      refine ⟨certificate ++ [(index, strings)], ?_, ?_⟩
      · have state : run rules ([], true) certificate =
            ((run rules ([], true) certificate).1, true) := Prod.ext rfl valid
        rw [run_append, state]
        simp only [run, List.foldl_cons, List.foldl_nil, step, lookup, Bool.true_and]
        exact (premisesFound_iff _ _ _).mpr allFound
      · have state : run rules ([], true) certificate =
            ((run rules ([], true) certificate).1, true) := Prod.ext rfl valid
        rw [run_append, state]
        simp [run, step, lookup]

/-- **A string is derivable exactly when some certificate is accepted for it.** -/
theorem derivable_iff_accepts (rules : List Rule) (string : List ℕ) :
    Derivable rules string ↔ ∃ certificate, accepts rules certificate string = true := by
  constructor
  · intro derivable
    obtain ⟨certificate, valid, member⟩ := certificate_exists rules derivable
    exact ⟨certificate, by simp [accepts, valid, (found_iff _ _).mpr member]⟩
  · rintro ⟨certificate, accepted⟩
    simp only [accepts, Bool.and_eq_true] at accepted
    exact run_sound rules certificate ([], true) (by simp) accepted.1 string
      ((found_iff _ _).mp accepted.2)

/-! ## The checker is primitive recursive -/

theorem symbol_primrec : Primrec₂ fun (input : List (List ℕ) × Word) (symbol : ℕ ⊕ ℕ) =>
    Sum.elim (fun index => input.1.getD index []) (fun a => [a]) symbol := by
  have cases : Primrec fun x : (List (List ℕ) × Word) × (ℕ ⊕ ℕ) =>
      Sum.casesOn (motive := fun _ => List ℕ) x.2 (fun index => x.1.1.getD index [])
        (fun a => [a]) :=
    Primrec.sumCasesOn Primrec.snd
      ((Primrec.list_getD ([] : List ℕ)).comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
      (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ))).to₂
  refine cases.of_eq fun x => ?_
  rcases x with ⟨input, symbol⟩
  cases symbol <;> rfl

theorem substitute_primrec : Primrec₂ substitute :=
  Primrec.list_flatMap Primrec.snd symbol_primrec

theorem found_primrec : Primrec₂ found := by
  have step : Primrec₂ fun (input : List ℕ × List (List ℕ)) (entry : List ℕ × Bool) =>
      decide (entry.1 = input.1) || entry.2 :=
    Primrec.or.comp
      (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr (f := fun input : List ℕ × List (List ℕ) => input.2)
    (g := fun _ => false) Primrec.snd (Primrec.const false) step

theorem premisesFound_primrec :
    Primrec fun input : List (List ℕ) × List (List ℕ) × List Word =>
      premisesFound input.1 input.2.1 input.2.2 := by
  have step : Primrec₂ fun (input : List (List ℕ) × List (List ℕ) × List Word)
      (entry : Word × Bool) => found (substitute input.1 entry.1) input.2.1 && entry.2 :=
    Primrec.and.comp
      (found_primrec.comp
        (substitute_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr (f := fun input : List (List ℕ) × List (List ℕ) × List Word =>
    input.2.2) (g := fun _ => true) (Primrec.snd.comp Primrec.snd) (Primrec.const true) step

theorem step_primrec (rules : List Rule) : Primrec₂ (step rules) := by
  have shape : ∀ (state : List (List ℕ) × Bool) (line : Line), step rules state line =
      (rules[line.1]?).casesOn (state.1, false) fun rule =>
        (state.1 ++ [substitute line.2 rule.2],
          state.2 && premisesFound line.2 state.1 rule.1) := by
    intro state line
    cases lookup : rules[line.1]? <;> simp [step, lookup]
  refine Primrec₂.of_eq ?_ (fun state line => (shape state line).symm)
  refine Primrec.option_casesOn
    ((Primrec.list_getElem?₁ rules).comp (Primrec.fst.comp Primrec.snd))
    (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const false)) ?_
  refine Primrec₂.mk ?_
  refine Primrec.pair ?_ ?_
  · exact Primrec.list_concat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (substitute_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
  · exact Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (premisesFound_primrec.comp (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))))

theorem accepts_primrec (rules : List Rule) : Primrec₂ (accepts rules) := by
  have running : Primrec fun certificate : List Line => run rules ([], true) certificate :=
    Primrec.list_foldl Primrec.id (Primrec.const ([], true))
      ((step_primrec rules).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  unfold accepts
  exact Primrec.and.comp (Primrec.snd.comp (running.comp Primrec.fst))
    (found_primrec.comp Primrec.snd (Primrec.fst.comp (running.comp Primrec.fst)))

/-- **The derivable strings of an elementary formal system are recursively
enumerable.** -/
theorem derivable_re (rules : List Rule) : REPred (Derivable rules) := by
  let search : List ℕ → ℕ → Option Unit := fun string index =>
    (decode index : Option (List Line)).bind fun certificate =>
      bif accepts rules certificate string then some () else none
  have computable : Computable₂ search := by
    refine Primrec.to_comp ?_
    exact Primrec.option_bind (Primrec.decode.comp Primrec.snd)
      (Primrec.cond ((accepts_primrec rules).comp Primrec.snd (Primrec.fst.comp Primrec.fst))
        (Primrec.const (some ())) (Primrec.const none)).to₂
  refine (Partrec.rfindOpt computable).dom_re.of_eq fun string => ?_
  rw [Nat.rfindOpt_dom, derivable_iff_accepts]
  constructor
  · rintro ⟨index, _, inSearch⟩
    simp only [search, Option.mem_def, Option.bind_eq_some_iff] at inSearch
    obtain ⟨certificate, -, accepted⟩ := inSearch
    refine ⟨certificate, ?_⟩
    cases verdict : accepts rules certificate string
    · simp [verdict] at accepted
    · rfl
  · rintro ⟨certificate, accepted⟩
    exact ⟨encode certificate, (), by simp [search, accepted]⟩

end Mettapedia.Computability.ElementaryFormalSystems
