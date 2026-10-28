import Mettapedia.OSLF.MeTTaIL.ReferenceStepPresented

/-!
# Executing the reference relation through presentations, by table

Through listed presentations a premise may step a child of the same class as the term it belongs to: the
child `{x, x}` of `{x}`, or the rest of a set written with a copy of a member. Derivations then nest without
bound although each is finite, and no fuel lists them all. A table lists them up to what a step is seen by:
its presentation, its rule and its contractum.

- **One round** (`tableStepsAt`): the steps at a presentation, each step premise read from the table's entries at
  listed presentations of its child (`tableStepper`). The children a presentation's premises ask about
  (`stepRequests`) join the presentations to visit.
- **Tabulating** (`tabulate`): rounds from a presentation, keeping one entry per presentation, rule and
  contractum, until a round adds no presentation and no such entry (`Stable`).
- **Sound** (`tabulate_sound`): every entry is a valid step.
- **Complete** (`table_complete`): once stable, every step at a visited presentation has an entry with its
  presentation, its rule and its contractum, by induction on the size of its witness.
- **Certified** (`TableCertified`): a table given as evidence is checked once: each entry by the witness checker, and
  one round for stability. A certified table is sound (`TableCertified.valid`) and complete up to witnesses
  (`TableCertified.complete`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep ReflectiveCanonical ReflectiveSubstitution

/-- A step at a presentation: the presentation, the witness and the contractum. -/
abbrev Entry := Pattern × Witness × Pattern

/-- The rule a witness fires. -/
def Witness.ruleIndex : Witness → Option ℕ
  | .rule index _ _ => some index
  | _ => none

/-- What a table keeps one entry for: the presentation, the rule and the contractum. -/
def Entry.key (entry : Entry) : Pattern × Option ℕ × Pattern := (entry.1, entry.2.1.ruleIndex, entry.2.2)

variable (relEnv : RelationEnv) (language : LanguageDef) (present : Pattern → List Pattern)

/-! ## One round -/

/-- The steps a table lists at a presentation. -/
def tableStepper (table : List Entry) (redex : Pattern) : List (Witness × Pattern) :=
  (table.filter fun entry => entry.1 == redex).map (·.2)

/-- **The steps at a presentation, with step premises read from a table.** -/
def tableStepsAt (table : List Entry) (redex : Pattern) : List (Witness × Pattern) :=
  (List.range language.rewrites.length).flatMap fun index =>
    match language.rewrites[index]? with
    | none => []
    | some rule =>
        (matchPatternForRule language rule redex).flatMap fun initial =>
          (presentedPremisesAt relEnv language present (tableStepper table) (captureSites rule) initial
            rule.premises).map fun entry =>
              (.rule index initial entry.1, applyBindingsScoped (captureSites rule) entry.2 0 rule.right)

/-- The children a premise asks about: the listed presentations of a step premise's child. -/
def premiseRequests (sites : Pattern) : Bindings → Premise → List Pattern
  | bindings, .forAll collection parameter body =>
      match bindings.lookup collection with
      | some (.collection _ elements none) =>
          elements.flatMap fun element => premiseRequests sites (bindParameter bindings parameter element) body
      | _ => []
  | bindings, premise =>
      if isBase premise = true then []
      else
        match stepEndpoints premise with
        | none => []
        | some (source, _) => present (applyBindingsScoped sites bindings (stepDepth sites premise) source)

/-- The children a list of premises asks about, under every bindings the table's listing reaches. -/
def premisesRequests (table : List Entry) (sites : Pattern) : Bindings → List Premise → List Pattern
  | _, [] => []
  | bindings, premise :: premises =>
      premiseRequests present sites bindings premise ++
        (presentedPremiseAt relEnv language present (tableStepper table) sites bindings premise).flatMap fun entry =>
          premisesRequests table sites entry.2 premises

/-- **The children a presentation's steps ask about.** -/
def stepRequests (table : List Entry) (redex : Pattern) : List Pattern :=
  language.rewrites.flatMap fun rule =>
    (matchPatternForRule language rule redex).flatMap fun initial =>
      premisesRequests relEnv language present table (captureSites rule) initial rule.premises

/-- **One round** over the presentations to visit. -/
def tableRound (table : List Entry) (todo : List Pattern) : List Entry :=
  todo.flatMap fun redex => (tableStepsAt relEnv language present table redex).map fun step => (redex, step.1, step.2)

/-- **A stable table**: its presentations ask about no other, and a round adds no presentation, rule and contractum. -/
def Stable (todo : List Pattern) (table : List Entry) : Bool :=
  (todo.all fun redex => (stepRequests relEnv language present table redex).all fun child => child ∈ todo) &&
    (tableRound relEnv language present table todo).all fun entry => table.any fun kept => kept.key == entry.key

/-! ## Tabulating -/

/-- Add the entries a table has no key for. -/
def addKeyed (table entries : List Entry) : List Entry :=
  entries.foldl (fun accumulated entry =>
    if accumulated.any (fun kept => kept.key == entry.key) then accumulated else accumulated ++ [entry]) table

/-- Add the presentations not yet listed. -/
def addPresentations (todo more : List Pattern) : List Pattern :=
  more.foldl (fun accumulated redex => if redex ∈ accumulated then accumulated else accumulated ++ [redex]) todo

/-- **Tabulate**: rounds until the table is stable, within the fuel. -/
def tabulate : ℕ → List Pattern → List Entry → List Pattern × List Entry
  | 0, todo, table => (todo, table)
  | fuel + 1, todo, table =>
      if Stable relEnv language present todo table then (todo, table)
      else
        let todo' := addPresentations todo (todo.flatMap (stepRequests relEnv language present table))
        tabulate fuel todo' (addKeyed table (tableRound relEnv language present table todo'))

/-- **The steps tabulated at a presentation.** -/
def tabledSteps (fuel : ℕ) (redex : Pattern) : List (Witness × Pattern) :=
  tableStepper (tabulate relEnv language present fuel [redex] []).2 redex

/-- **Whether tabulating from a presentation reached a stable table.** -/
def tabledEnough (fuel : ℕ) (redex : Pattern) : Bool :=
  Stable relEnv language present (tabulate relEnv language present fuel [redex] []).1
    (tabulate relEnv language present fuel [redex] []).2

/-! ## Tabulating a region -/

/-- **What a round asks about**: the children the visited presentations' premises ask about, and the listed
presentations of the classes their steps lead to. -/
def regionRequests (table : List Entry) (todo : List Pattern) (round : List Entry) : List Pattern :=
  todo.flatMap (stepRequests relEnv language present table) ++ round.flatMap fun entry => present entry.2.2

/-- **A stable region**: a round asks about no presentation not visited, and adds no presentation, rule and
contractum. -/
def RegionStable (todo : List Pattern) (table : List Entry) : Bool :=
  (regionRequests relEnv language present table todo (tableRound relEnv language present table todo)).all
      (fun child => child ∈ todo) &&
    (tableRound relEnv language present table todo).all fun entry => table.any fun kept => kept.key == entry.key

/-- The next region from a round and what it asks about, or none when the region is stable. -/
def regionNextFrom (todo : List Pattern) (table : List Entry) (round : List Entry) (requested : List Pattern) :
    Option (List Pattern × List Entry) :=
  if requested.all (fun child => child ∈ todo) && round.all (fun entry => table.any fun kept => kept.key == entry.key)
  then none
  else some (addPresentations todo requested, addKeyed table round)

/-- **The next region**, from a round computed once, or none when the region is stable. -/
def regionNext (todo : List Pattern) (table : List Entry) (round : List Entry) : Option (List Pattern × List Entry) :=
  regionNextFrom todo table round (regionRequests relEnv language present table todo round)

/-- **Tabulate a region**: rounds until the region is stable, within the given number of rounds. -/
def regionTabulate : ℕ → List Pattern → List Entry → List Pattern × List Entry
  | 0, todo, table => (todo, table)
  | rounds + 1, todo, table =>
      match regionNext relEnv language present todo table (tableRound relEnv language present table todo) with
      | none => (todo, table)
      | some next => regionTabulate rounds next.1 next.2

/-! ## Sound -/

variable {relEnv language present}

/-- A table of valid entries. -/
def TableValid (table : List Entry) : Prop :=
  ∀ entry ∈ table, StepValid relEnv language entry.1 entry.2.1 entry.2.2 (.presented present)

theorem tableStepper_sound {table : List Entry} (valid : TableValid (relEnv := relEnv) (language := language)
    (present := present) table) :
    ∀ {source witness target}, (witness, target) ∈ tableStepper table source →
      StepValid relEnv language source witness target (.presented present) := by
  intro source witness target member
  simp only [tableStepper, List.mem_map, List.mem_filter, beq_iff_eq] at member
  obtain ⟨entry, ⟨inside, sameRedex⟩, sameStep⟩ := member
  have := valid entry inside
  rw [sameRedex, sameStep] at this
  exact this

theorem tableStepsAt_sound {table : List Entry}
    (valid : TableValid (relEnv := relEnv) (language := language) (present := present) table) {redex : Pattern}
    {witness : Witness} {target : Pattern} (member : (witness, target) ∈ tableStepsAt relEnv language present table redex) :
    StepValid relEnv language redex witness target (.presented present) := by
  simp only [tableStepsAt, List.mem_flatMap, List.mem_range] at member
  obtain ⟨index, _, rest⟩ := member
  split at rest
  · simp at rest
  · rename_i rule found
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at rest
    obtain ⟨initial, matched, ⟨witnesses, final⟩, premisesMember, rfl, rfl⟩ := rest
    exact .presentedRule found matched (presentedPremisesValid_of_mem (tableStepper_sound valid) premisesMember)

theorem tableRound_sound {table : List Entry}
    (valid : TableValid (relEnv := relEnv) (language := language) (present := present) table) (todo : List Pattern) :
    TableValid (relEnv := relEnv) (language := language) (present := present) (tableRound relEnv language present table todo) := by
  intro entry member
  simp only [tableRound, List.mem_flatMap, List.mem_map] at member
  obtain ⟨redex, _, step, stepMember, rfl⟩ := member
  exact tableStepsAt_sound valid stepMember

theorem addKeyed_sound {table : List Entry} :
    ∀ {entries : List Entry}, TableValid (relEnv := relEnv) (language := language) (present := present) table →
      TableValid (relEnv := relEnv) (language := language) (present := present) entries →
        TableValid (relEnv := relEnv) (language := language) (present := present) (addKeyed table entries)
  | [], valid, _ => valid
  | entry :: entries, valid, more => by
    simp only [addKeyed, List.foldl_cons]
    have head : TableValid (relEnv := relEnv) (language := language) (present := present)
        (if table.any (fun kept => kept.key == entry.key) then table else table ++ [entry]) := by
      split
      · exact valid
      · intro other member
        rcases List.mem_append.mp member with inside | fresh
        · exact valid other inside
        · rw [List.mem_singleton.mp fresh]
          exact more entry List.mem_cons_self
    exact addKeyed_sound (table := _) head fun other member => more other (List.mem_cons_of_mem _ member)

/-- **Every tabulated entry is a valid step.** -/
theorem tabulate_sound : ∀ (fuel : ℕ) (todo : List Pattern) {table : List Entry},
    TableValid (relEnv := relEnv) (language := language) (present := present) table →
      TableValid (relEnv := relEnv) (language := language) (present := present)
        (tabulate relEnv language present fuel todo table).2
  | 0, _, _, valid => valid
  | fuel + 1, todo, table, valid => by
    simp only [tabulate]
    split
    · exact valid
    · exact tabulate_sound fuel _ (addKeyed_sound valid (tableRound_sound valid _))

theorem tabledSteps_sound {fuel : ℕ} {redex target : Pattern} {witness : Witness}
    (member : (witness, target) ∈ tabledSteps relEnv language present fuel redex) :
    StepValid relEnv language redex witness target (.presented present) :=
  tableStepper_sound (tabulate_sound fuel [redex] fun _ member => absurd member List.not_mem_nil) member

theorem addPresentations_mem : ∀ (more : List Pattern) {accumulated : List Pattern} {redex : Pattern},
    redex ∈ accumulated → redex ∈ addPresentations accumulated more
  | [], _, _, inside => inside
  | head :: tail, accumulated, redex, inside => by
    simp only [addPresentations, List.foldl_cons]
    apply addPresentations_mem tail
    split
    · exact inside
    · exact List.mem_append_left _ inside

/-- **Every entry of a tabulated region is a valid step.** -/
theorem regionTabulate_sound : ∀ (rounds : ℕ) (todo : List Pattern) {table : List Entry},
    TableValid (relEnv := relEnv) (language := language) (present := present) table →
      TableValid (relEnv := relEnv) (language := language) (present := present)
        (regionTabulate relEnv language present rounds todo table).2
  | 0, _, _, valid => valid
  | rounds + 1, todo, table, valid => by
    simp only [regionTabulate]
    split
    · exact valid
    · rename_i next found
      simp only [regionNext, regionNextFrom] at found
      split at found
      · cases found
      · cases found
        exact regionTabulate_sound rounds _ (addKeyed_sound valid (tableRound_sound valid _))

theorem regionTabulate_first : ∀ (rounds : ℕ) {todo : List Pattern} {table : List Entry} {redex : Pattern},
    redex ∈ todo → redex ∈ (regionTabulate relEnv language present rounds todo table).1
  | 0, _, _, _, inside => inside
  | rounds + 1, todo, table, redex, inside => by
    simp only [regionTabulate]
    split
    · exact inside
    · rename_i next found
      simp only [regionNext, regionNextFrom] at found
      split at found
      · cases found
      · cases found
        exact regionTabulate_first rounds (addPresentations_mem _ inside)

/-- **A stable region is stable**: what its premises ask about is among its presentations. -/
theorem stable_of_regionStable {todo : List Pattern} {table : List Entry}
    (stable : RegionStable relEnv language present todo table = true) : Stable relEnv language present todo table = true := by
  simp only [RegionStable, regionRequests, Stable, Bool.and_eq_true, List.all_eq_true, List.mem_append,
    List.mem_flatMap, decide_eq_true_eq] at stable ⊢
  exact ⟨fun redex visited child asked => stable.1 child (Or.inl ⟨redex, visited, asked⟩), stable.2⟩

/-- **A stable region holds the classes its steps lead to.** -/
theorem successors_visited {todo : List Pattern} {table : List Entry}
    (stable : RegionStable relEnv language present todo table = true) {entry : Entry}
    (member : entry ∈ tableRound relEnv language present table todo) : ∀ shown ∈ present entry.2.2, shown ∈ todo := by
  simp only [RegionStable, regionRequests, Bool.and_eq_true, List.all_eq_true, List.mem_append, List.mem_flatMap,
    decide_eq_true_eq] at stable
  exact fun shown inside => stable.1 shown (Or.inr ⟨entry, member, inside⟩)

/-! ## Complete once stable -/

/-- **A stable table lists, up to its witness, every step whose children it lists.** -/
theorem premise_tabled {table : List Entry} {todo : List Pattern} {size : ℕ}
    (children : ∀ (witness : Witness), sizeOf witness < size → ∀ {redex target : Pattern}, redex ∈ todo →
      StepValid relEnv language redex witness target (.presented present) →
        ∃ witness', (witness', target) ∈ tableStepper table redex) :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      PremiseValid relEnv language sites bindings premise witness result (.presented present) → sizeOf witness < size →
        (∀ child ∈ premiseRequests present sites bindings premise, child ∈ todo) →
          ∃ witness', (witness', result) ∈ presentedPremiseAt relEnv language present (tableStepper table) sites bindings
            premise
  | .forAll collection parameter body, sites, bindings, result, witness, valid, small, asked => by
    cases valid with
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
    | @presentedForAll _ _ _ _ _ _ kind elements bodies found bodiesValid =>
      simp only [premiseRequests, found, List.mem_flatMap] at asked
      have each : ∀ {elements' : List Pattern} {bodies' : List Witness},
          ForAllValid relEnv language sites bindings parameter body elements' bodies' (.presented present) →
          (∀ witness ∈ bodies', sizeOf witness < size) → (∀ element ∈ elements', element ∈ elements) →
          ∃ chosen, List.Forall₂ (fun element choice => ∃ other, (choice, other) ∈
            presentedPremiseAt relEnv language present (tableStepper table) sites (bindParameter bindings parameter element)
              body) elements' chosen := by
        intro elements' bodies' bodiesValid' small' inside
        induction elements' generalizing bodies' with
        | nil => exact ⟨[], .nil⟩
        | cons element rest ih =>
          cases bodiesValid' with
          | presentedCons head tail =>
            obtain ⟨headWitness, headMember⟩ := premise_tabled children body head
              (small' _ List.mem_cons_self) fun child member =>
                asked child ⟨element, inside element List.mem_cons_self, member⟩
            obtain ⟨chosen, chosenRelated⟩ := ih tail (fun other member => small' other (List.mem_cons_of_mem _ member))
              fun other member => inside other (List.mem_cons_of_mem _ member)
            exact ⟨headWitness :: chosen, .cons ⟨_, headMember⟩ chosenRelated⟩
      have bodiesSmall : ∀ other ∈ bodies, sizeOf other < size := by
        intro other member
        have := List.sizeOf_lt_of_mem member
        simp only [Witness.forAll.sizeOf_spec] at small
        omega
      obtain ⟨chosen, related⟩ := each bodiesValid bodiesSmall fun _ member => member
      refine ⟨.forAll chosen, ?_⟩
      simp only [presentedPremiseAt, found]
      exact List.mem_map.mpr ⟨chosen, (mem_foldr_choices_iff _ elements chosen).mpr related, rfl⟩
  | .freshness condition, sites, bindings, result, witness, valid, _, _ => by
    cases valid with
    | presentedFreshness member =>
      refine ⟨.base result, ?_⟩
      simp only [presentedPremiseAt, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq]
      exact ⟨_, member, rfl, rfl⟩
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
  | .relationQuery relation arguments, sites, bindings, result, witness, valid, _, _ => by
    cases valid with
    | presentedQuery member =>
      refine ⟨.base result, ?_⟩
      simp only [presentedPremiseAt, isBase, ↓reduceIte, List.mem_map, Prod.mk.injEq]
      exact ⟨_, member, rfl, rfl⟩
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
  | .congruence source target, sites, bindings, result, witness, valid, small, asked => by
    cases valid with
    | @presentedStep _ _ _ matched _ _ _ _ _ _ candidate step endpoints redexMember stepped candidateMember matchedMember
        merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [premiseRequests, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints] at asked
      have stepSmall : sizeOf step < size := by
        simp only [Witness.premiseStep.sizeOf_spec] at small
        omega
      obtain ⟨witness', listed⟩ := children _ stepSmall (asked _ redexMember) stepped
      refine ⟨.premiseStep witness' candidate matched result, ?_⟩
      simp only [presentedPremiseAt, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
        List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
      exact ⟨_, redexMember, _, listed, _, candidateMember, _, matchedMember, _, merged, rfl, rfl⟩
  | .scopedStep premise, sites, bindings, result, witness, valid, small, asked => by
    cases valid with
    | @presentedStep _ _ _ matched _ _ _ _ _ _ candidate step endpoints redexMember stepped candidateMember matchedMember
        merged =>
      simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
      obtain ⟨rfl, rfl⟩ := endpoints
      simp only [premiseRequests, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints] at asked
      have stepSmall : sizeOf step < size := by
        simp only [Witness.premiseStep.sizeOf_spec] at small
        omega
      obtain ⟨witness', listed⟩ := children _ stepSmall (asked _ redexMember) stepped
      refine ⟨.premiseStep witness' candidate matched result, ?_⟩
      simp only [presentedPremiseAt, isBase, Bool.false_eq_true, ↓reduceIte, stepEndpoints, List.mem_flatMap,
        List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
      exact ⟨_, redexMember, _, listed, _, candidateMember, _, matchedMember, _, merged, rfl, rfl⟩

theorem premises_tabled {table : List Entry} {todo : List Pattern} {size : ℕ}
    (children : ∀ (witness : Witness), sizeOf witness < size → ∀ {redex target : Pattern}, redex ∈ todo →
      StepValid relEnv language redex witness target (.presented present) →
        ∃ witness', (witness', target) ∈ tableStepper table redex) {sites : Pattern} :
    ∀ {premises : List Premise} {bindings final : Bindings} {witnesses : List Witness},
      PremisesValid relEnv language sites bindings premises witnesses final (.presented present) →
      (∀ witness ∈ witnesses, sizeOf witness < size) →
      (∀ child ∈ premisesRequests relEnv language present table sites bindings premises, child ∈ todo) →
        ∃ witnesses', (witnesses', final) ∈
          presentedPremisesAt relEnv language present (tableStepper table) sites bindings premises
  | [], _, _, _, valid, _, _ => by
    cases valid
    exact ⟨[], by simp [presentedPremisesAt]⟩
  | premise :: premises, bindings, final, _, valid, small, asked => by
    cases valid with
    | @presentedCons _ _ _ middle _ _ _ witness witnesses first rest =>
      simp only [premisesRequests, List.mem_append, List.mem_flatMap] at asked
      obtain ⟨witness', headMember⟩ := premise_tabled children premise first (small _ List.mem_cons_self)
        fun child member => asked child (Or.inl member)
      obtain ⟨witnesses', tailMember⟩ := premises_tabled children rest
        (fun other member => small other (List.mem_cons_of_mem _ member))
        fun child member => asked child (Or.inr ⟨_, headMember, member⟩)
      refine ⟨witness' :: witnesses', ?_⟩
      simp only [presentedPremisesAt, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨_, headMember, _, tailMember, rfl, rfl⟩

theorem mem_tableRound {table : List Entry} {todo : List Pattern} {redex : Pattern} {step : Witness × Pattern}
    (visited : redex ∈ todo) (member : step ∈ tableStepsAt relEnv language present table redex) :
    (redex, step.1, step.2) ∈ tableRound relEnv language present table todo :=
  List.mem_flatMap.mpr ⟨redex, visited, List.mem_map.mpr ⟨step, member, rfl⟩⟩

/-- **A stable table is complete up to witnesses**: every step at a visited presentation has an entry with the same
presentation, rule and contractum. -/
theorem table_complete {table : List Entry} {todo : List Pattern}
    (stable : Stable relEnv language present todo table = true) :
    ∀ (size : ℕ) (witness : Witness), sizeOf witness < size → ∀ {redex target : Pattern}, redex ∈ todo →
      StepValid relEnv language redex witness target (.presented present) →
        ∃ entry ∈ table, entry.1 = redex ∧ entry.2.1.ruleIndex = witness.ruleIndex ∧ entry.2.2 = target
  | 0, _, small, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, witness, small, redex, target, visited, valid => by
    simp only [Stable, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at stable
    obtain ⟨closed, kept⟩ := stable
    cases valid with
    | @presentedRule _ _ index rule initial final witnesses found matched premises =>
      have children : ∀ (witness : Witness), sizeOf witness < size → ∀ {redex target : Pattern}, redex ∈ todo →
          StepValid relEnv language redex witness target (.presented present) →
            ∃ witness', (witness', target) ∈ tableStepper table redex := by
        intro child childSmall childRedex childTarget childVisited childValid
        obtain ⟨entry, inside, sameRedex, -, sameTarget⟩ :=
          table_complete (by simpa [Stable] using And.intro closed kept) size child childSmall childVisited childValid
        refine ⟨entry.2.1, ?_⟩
        simp only [tableStepper, List.mem_map, List.mem_filter, beq_iff_eq]
        exact ⟨entry, ⟨inside, sameRedex⟩, by rw [← sameTarget]⟩
      have premisesSmall : ∀ other ∈ witnesses, sizeOf other < size := by
        intro other member
        have := List.sizeOf_lt_of_mem member
        simp only [Witness.rule.sizeOf_spec] at small
        omega
      have asked : ∀ child ∈ premisesRequests relEnv language present table (captureSites rule) initial rule.premises,
          child ∈ todo := by
        intro child member
        refine closed redex visited child ?_
        simp only [stepRequests, List.mem_flatMap]
        exact ⟨rule, List.mem_of_getElem? found, initial, matched, member⟩
      obtain ⟨witnesses', listed⟩ := premises_tabled children premises premisesSmall asked
      have indexBound : index < language.rewrites.length := by
        by_contra outside
        rw [List.getElem?_eq_none (by omega)] at found
        cases found
      have stepMember : (Witness.rule index initial witnesses', applyBindingsScoped (captureSites rule) final 0 rule.right) ∈
          tableStepsAt relEnv language present table redex := by
        simp only [tableStepsAt, List.mem_flatMap, List.mem_range]
        refine ⟨index, indexBound, ?_⟩
        simp only [found, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
        exact ⟨initial, matched, (witnesses', final), listed, rfl, rfl⟩
      obtain ⟨entry, inside, sameKey⟩ := List.any_eq_true.mp (kept _ (mem_tableRound visited stepMember))
      simp only [Entry.key, beq_iff_eq, Prod.mk.injEq] at sameKey
      obtain ⟨sameRedex, sameRule, sameTarget⟩ := sameKey
      exact ⟨entry, inside, sameRedex, by rw [sameRule]; rfl, sameTarget⟩

theorem mem_tabulate_first : ∀ (fuel : ℕ) {todo : List Pattern} {table : List Entry} {redex : Pattern},
    redex ∈ todo → redex ∈ (tabulate relEnv language present fuel todo table).1
  | 0, _, _, _, member => member
  | fuel + 1, todo, table, redex, member => by
    simp only [tabulate]
    split
    · exact member
    · refine mem_tabulate_first fuel ?_
      have keeps : ∀ (more : List Pattern) {accumulated : List Pattern}, redex ∈ accumulated →
          redex ∈ more.foldl (fun accumulated redex => if redex ∈ accumulated then accumulated else accumulated ++ [redex])
            accumulated := by
        intro more
        induction more with
        | nil => exact fun inside => inside
        | cons head tail ih =>
          intro accumulated inside
          simp only [List.foldl_cons]
          apply ih
          split
          · exact inside
          · exact List.mem_append_left _ inside
      exact keeps _ member

/-- **When tabulating is stable, the tabulated steps at a presentation are all its steps up to witnesses.** -/
theorem tabledSteps_complete {fuel : ℕ} {redex target : Pattern} {witness : Witness}
    (enough : tabledEnough relEnv language present fuel redex = true)
    (valid : StepValid relEnv language redex witness target (.presented present)) :
    ∃ witness', (witness', target) ∈ tabledSteps relEnv language present fuel redex ∧
      witness'.ruleIndex = witness.ruleIndex := by
  obtain ⟨entry, inside, sameRedex, sameRule, sameTarget⟩ :=
    table_complete enough _ witness (Nat.lt_succ_self _) (mem_tabulate_first fuel List.mem_cons_self) valid
  refine ⟨entry.2.1, ?_, sameRule⟩
  simp only [tabledSteps, tableStepper, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨entry, ⟨inside, sameRedex⟩, by rw [← sameTarget]⟩

/-! ## Certified tables -/

variable (relEnv language present) in
/-- **A certified table**: every entry checks, and a round over the visited presentations asks about none not visited
and adds no presentation, rule and contractum. -/
def TableCertified (todo : List Pattern) (table : List Entry) : Bool :=
  (table.all fun entry => checkPresentedStep relEnv language present entry.1 entry.2.1 == some entry.2.2) &&
    RegionStable relEnv language present todo table

/-- **A certified table's entries are valid steps.** -/
theorem TableCertified.valid {todo : List Pattern} {table : List Entry}
    (certified : TableCertified relEnv language present todo table = true) :
    TableValid (relEnv := relEnv) (language := language) (present := present) table := by
  intro entry member
  simp only [TableCertified, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at certified
  exact stepValid_of_checkPresentedStep _ (certified.1 entry member)

/-- **A certified table is complete up to witnesses** at the presentations it visits. -/
theorem TableCertified.complete {todo : List Pattern} {table : List Entry}
    (certified : TableCertified relEnv language present todo table = true) {redex target : Pattern} {witness : Witness}
    (visited : redex ∈ todo) (valid : StepValid relEnv language redex witness target (.presented present)) :
    ∃ entry ∈ table, entry.1 = redex ∧ entry.2.1.ruleIndex = witness.ruleIndex ∧ entry.2.2 = target := by
  simp only [TableCertified, Bool.and_eq_true] at certified
  exact table_complete (stable_of_regionStable certified.2) _ witness (Nat.lt_succ_self _) visited valid

end Mettapedia.OSLF.MeTTaIL.ReferenceStep
