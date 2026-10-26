import Mettapedia.Languages.MM0.HOLKernelProofReadbackRenaming
import Mettapedia.Languages.MM0.HOLKernelProofReadback
import Mettapedia.Languages.MM0.HOLKernelStructuralRules
import Mettapedia.Languages.MM0.HOLKernelAssumptions

/-!
# Admission of the maintained HOL structural proof constructions

Identity, composition, pairing and both projections construct independently
admitted proof trees from the actual native witnesses. Their local source
arguments are read from the supplied mixed judgments, and the selected native
rule indices retain their exact declarations. Different child recursion
budgets are joined by the common admission weakening operation.

The resulting weakening law covers formation projections and every ordered
hypothesis occurrence over an arbitrary list of native/source entries. These
are the context constructions used by the complete HOL compiler; its logical,
binding and conversion cases have their separate admission obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelStructuralReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelProofReadback
universe u v
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

theorem read_entails
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (faithful : Function.Injective references) (distinct : references .im ≠ abbreviation.reference)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma) (first second : Preterm) :
    readFormulaIn abbreviation reader parameters names (entails references first second) =
      ((readFormulaIn abbreviation reader parameters names first).bind fun left =>
        (readFormulaIn abbreviation reader parameters names second).map fun right => .imp left right) := by
  simp only [readFormulaIn, entails, applySymbol, Preterm.applyArgs, expandEquivalence, if_neg distinct,
    readJudgmentWith, readHead_reference references faithful, Option.bind_eq_bind]
  cases readJudgmentWith reader references names (expandEquivalence references abbreviation.reference first) <;>
    cases readJudgmentWith reader references names (expandEquivalence references abbreviation.reference second) <;> rfl

theorem read_conjunction
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (faithful : Function.Injective references) (distinct : references .an ≠ abbreviation.reference)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma) (first second : Preterm) :
    readFormulaIn abbreviation reader parameters names (conjunction references first second) =
      ((readFormulaIn abbreviation reader parameters names first).bind fun left =>
        (readFormulaIn abbreviation reader parameters names second).map fun right => .and left right) := by
  simp only [readFormulaIn, conjunction, applySymbol, Preterm.applyArgs, expandEquivalence, if_neg distinct,
    readJudgmentWith, readHead_reference references faithful, Option.bind_eq_bind]
  cases readJudgmentWith reader references names (expandEquivalence references abbreviation.reference first) <;>
    cases readJudgmentWith reader references names (expandEquivalence references abbreviation.reference second) <;> rfl

theorem identity_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : signature.symbol .im ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .id) = some (.structural .id))
    (proposition : Preterm) (sorted : Preterm.HasType terms context proposition [] signature.ids.wff)
    (formula : Formula Const gamma)
    (reading : readFormulaIn abbreviation reader parameters names proposition = some formula) :
    Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt 1 names
      (HOLKernelStructuralRules.identity (definitions := definitions) (hypotheses := [])
        signature rules proposition sorted).val (.imp formula formula)) := by
  let compiled := HOLKernelStructuralRules.identity (definitions := definitions) (hypotheses := [])
    signature rules proposition sorted
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .id) [proposition] []) (entails signature.symbol proposition proposition) :=
    compiled.property
  have instantiated := checked.instantiates (rules.declared .id) .nil
  let admitted : AdmittedApplication abbreviation theorems context reader parameters names
      ruleAt (rules.index .id) [proposition] := {
    rule := .structural .id
    selected := selected
    native := ⟨[], entails signature.symbol proposition proposition⟩
    declared := rules.declared .id
    instantiated := instantiated
    operands := .structural (.id formula)
    operands_read := by
      change ((readFormulaIn abbreviation reader parameters names proposition).bind
        (fun p => some (HOLKernelRuleInstances.StructuralArguments.id p))).map RuleArguments.structural = _
      rw [reading]
      rfl
    premises_read := rfl
    conclusion_read := by
      simp only [read_entails abbreviation signature.symbol_injective distinct, reading,
        Option.bind_some, Option.map_some, RuleArguments.conclusion,
        HOLKernelRuleInstances.StructuralArguments.conclusion] }
  exact ⟨AdmittedStep.application checked.eval admitted rfl .nil⟩


theorem compose_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : signature.symbol .im ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .syl) = some (.structural .syl))
    (first middle last : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (middleSorted : Preterm.HasType terms context middle [] signature.ids.wff)
    (lastSorted : Preterm.HasType terms context last [] signature.ids.wff)
    (one : HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := context) (hypotheses := []) (entails signature.symbol first middle))
    (two : HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := context) (hypotheses := []) (entails signature.symbol middle last))
    (p q r : Formula Const gamma)
    (firstRead : readFormulaIn abbreviation reader parameters names first = some p)
    (middleRead : readFormulaIn abbreviation reader parameters names middle = some q)
    (lastRead : readFormulaIn abbreviation reader parameters names last = some r)
    {fuelOne fuelTwo : Nat}
    (oneAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      fuelOne names one.val (.imp p q))
    (twoAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      fuelTwo names two.val (.imp q r)) :
    Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      (max fuelOne fuelTwo + 1) names
      (HOLKernelStructuralRules.compose signature rules first middle last firstSorted middleSorted lastSorted one two).val
      (.imp p r)) := by
  let compiled := HOLKernelStructuralRules.compose signature rules first middle last firstSorted middleSorted lastSorted one two
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .syl) [first, middle, last] [one.val, two.val]) (entails signature.symbol first last) :=
    compiled.property
  have instantiated := checked.instantiates (rules.declared .syl)
    (.cons one.property (.cons two.property .nil))
  let admitted : AdmittedApplication abbreviation theorems context reader parameters names
      ruleAt (rules.index .syl) [first, middle, last] := {
    rule := .structural .syl
    selected := selected
    native := ⟨[entails signature.symbol first middle, entails signature.symbol middle last],
      entails signature.symbol first last⟩
    declared := rules.declared .syl
    instantiated := instantiated
    operands := .structural (.syl p q r)
    operands_read := by
      change ((readFormulaIn abbreviation reader parameters names first).bind fun p =>
        (readFormulaIn abbreviation reader parameters names middle).bind fun q =>
        (readFormulaIn abbreviation reader parameters names last).bind fun r =>
          some (HOLKernelRuleInstances.StructuralArguments.syl p q r)).map RuleArguments.structural = _
      rw [firstRead, middleRead, lastRead]
      rfl
    premises_read := by
      simp [read_entails abbreviation signature.symbol_injective distinct,
        firstRead, middleRead, lastRead, RuleArguments.premises,
        HOLKernelRuleInstances.StructuralArguments.premises]
    conclusion_read := by
      simp only [read_entails abbreviation signature.symbol_injective distinct,
        firstRead, lastRead, Option.bind_some, Option.map_some,
        RuleArguments.conclusion, HOLKernelRuleInstances.StructuralArguments.conclusion] }
  exact ⟨AdmittedStep.application checked.eval admitted rfl
    (.cons (oneAdmitted.weakenFuel (Nat.le_max_left _ _))
      (.cons (twoAdmitted.weakenFuel (Nat.le_max_right _ _)) .nil))⟩


theorem left_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinctIm : signature.symbol .im ≠ abbreviation.reference)
    (distinctAn : signature.symbol .an ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .anl) = some (.structural .anl))
    (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.wff)
    (p q : Formula Const gamma)
    (firstRead : readFormulaIn abbreviation reader parameters names first = some p)
    (secondRead : readFormulaIn abbreviation reader parameters names second = some q) :
    Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt 1 names
      (HOLKernelStructuralRules.left (definitions := definitions) (hypotheses := [])
        signature rules first second firstSorted secondSorted).val (.imp (.and p q) p)) := by
  let compiled := HOLKernelStructuralRules.left (definitions := definitions) (hypotheses := [])
    signature rules first second firstSorted secondSorted
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .anl) [first, second] [])
      (entails signature.symbol (conjunction signature.symbol first second) first) :=
    compiled.property
  have instantiated := checked.instantiates (rules.declared .anl) .nil
  let admitted : AdmittedApplication abbreviation theorems context reader parameters names
      ruleAt (rules.index .anl) [first, second] := {
    rule := .structural .anl
    selected := selected
    native := ⟨[], entails signature.symbol (conjunction signature.symbol first second) first⟩
    declared := rules.declared .anl
    instantiated := instantiated
    operands := .structural (.anl p q)
    operands_read := by
      change ((readFormulaIn abbreviation reader parameters names first).bind fun p =>
        (readFormulaIn abbreviation reader parameters names second).bind fun q =>
          some (HOLKernelRuleInstances.StructuralArguments.anl p q)).map RuleArguments.structural = _
      rw [firstRead, secondRead]
      rfl
    premises_read := rfl
    conclusion_read := by
      simp only [read_entails abbreviation signature.symbol_injective distinctIm,
        read_conjunction abbreviation signature.symbol_injective distinctAn,
        firstRead, secondRead, Option.bind_some, Option.map_some,
        RuleArguments.conclusion, HOLKernelRuleInstances.StructuralArguments.conclusion] }
  exact ⟨AdmittedStep.application checked.eval admitted rfl .nil⟩


theorem right_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinctIm : signature.symbol .im ≠ abbreviation.reference)
    (distinctAn : signature.symbol .an ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .anr) = some (.structural .anr))
    (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.wff)
    (p q : Formula Const gamma)
    (firstRead : readFormulaIn abbreviation reader parameters names first = some p)
    (secondRead : readFormulaIn abbreviation reader parameters names second = some q) :
    Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt 1 names
      (HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
        signature rules first second firstSorted secondSorted).val (.imp (.and p q) q)) := by
  let compiled := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
    signature rules first second firstSorted secondSorted
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .anr) [first, second] [])
      (entails signature.symbol (conjunction signature.symbol first second) second) :=
    compiled.property
  have instantiated := checked.instantiates (rules.declared .anr) .nil
  let admitted : AdmittedApplication abbreviation theorems context reader parameters names
      ruleAt (rules.index .anr) [first, second] := {
    rule := .structural .anr
    selected := selected
    native := ⟨[], entails signature.symbol (conjunction signature.symbol first second) second⟩
    declared := rules.declared .anr
    instantiated := instantiated
    operands := .structural (.anr p q)
    operands_read := by
      change ((readFormulaIn abbreviation reader parameters names first).bind fun p =>
        (readFormulaIn abbreviation reader parameters names second).bind fun q =>
          some (HOLKernelRuleInstances.StructuralArguments.anr p q)).map RuleArguments.structural = _
      rw [firstRead, secondRead]
      rfl
    premises_read := rfl
    conclusion_read := by
      simp only [read_entails abbreviation signature.symbol_injective distinctIm,
        read_conjunction abbreviation signature.symbol_injective distinctAn,
        firstRead, secondRead, Option.bind_some, Option.map_some,
        RuleArguments.conclusion, HOLKernelRuleInstances.StructuralArguments.conclusion] }
  exact ⟨AdmittedStep.application checked.eval admitted rfl .nil⟩


theorem pair_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinctIm : signature.symbol .im ≠ abbreviation.reference)
    (distinctAn : signature.symbol .an ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .ian) = some (.structural .ian))
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.wff)
    (one : HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := context) (hypotheses := []) (entails signature.symbol antecedent first))
    (two : HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := context) (hypotheses := []) (entails signature.symbol antecedent second))
    (g p q : Formula Const gamma)
    (antecedentRead : readFormulaIn abbreviation reader parameters names antecedent = some g)
    (firstRead : readFormulaIn abbreviation reader parameters names first = some p)
    (secondRead : readFormulaIn abbreviation reader parameters names second = some q)
    {fuelOne fuelTwo : Nat}
    (oneAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      fuelOne names one.val (.imp g p))
    (twoAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      fuelTwo names two.val (.imp g q)) :
    Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      (max fuelOne fuelTwo + 1) names
      (HOLKernelStructuralRules.pair signature rules antecedent first second antecedentSorted firstSorted secondSorted one two).val
      (.imp g (.and p q))) := by
  let compiled := HOLKernelStructuralRules.pair signature rules antecedent first second antecedentSorted firstSorted secondSorted one two
  have checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .ian) [antecedent, first, second] [one.val, two.val])
      (entails signature.symbol antecedent (conjunction signature.symbol first second)) := compiled.property
  have instantiated := checked.instantiates (rules.declared .ian)
    (.cons one.property (.cons two.property .nil))
  let admitted : AdmittedApplication abbreviation theorems context reader parameters names
      ruleAt (rules.index .ian) [antecedent, first, second] := {
    rule := .structural .ian
    selected := selected
    native := ⟨[entails signature.symbol antecedent first, entails signature.symbol antecedent second],
      entails signature.symbol antecedent (conjunction signature.symbol first second)⟩
    declared := rules.declared .ian
    instantiated := instantiated
    operands := .structural (.ian g p q)
    operands_read := by
      change ((readFormulaIn abbreviation reader parameters names antecedent).bind fun g =>
        (readFormulaIn abbreviation reader parameters names first).bind fun p =>
        (readFormulaIn abbreviation reader parameters names second).bind fun q =>
          some (HOLKernelRuleInstances.StructuralArguments.ian g p q)).map RuleArguments.structural = _
      rw [antecedentRead, firstRead, secondRead]
      rfl
    premises_read := by
      simp [read_entails abbreviation signature.symbol_injective distinctIm,
        antecedentRead, firstRead, secondRead, RuleArguments.premises,
        HOLKernelRuleInstances.StructuralArguments.premises]
    conclusion_read := by
      simp only [read_entails abbreviation signature.symbol_injective distinctIm,
        read_conjunction abbreviation signature.symbol_injective distinctAn,
        antecedentRead, firstRead, secondRead, Option.bind_some, Option.map_some,
        RuleArguments.conclusion, HOLKernelRuleInstances.StructuralArguments.conclusion] }
  exact ⟨AdmittedStep.application checked.eval admitted rfl
    (.cons (oneAdmitted.weakenFuel (Nat.le_max_left _ _))
      (.cons (twoAdmitted.weakenFuel (Nat.le_max_right _ _)) .nil))⟩

theorem weaken_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinctIm : signature.symbol .im ≠ abbreviation.reference)
    (distinctAn : signature.symbol .an ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.structural rule))
    (antecedent extra conclusion : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (extraSorted : Preterm.HasType terms context extra [] signature.ids.wff)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.wff)
    (source : HOLKernelStructuralRules.CheckedProof (terms := terms) (definitions := definitions)
      (theorems := theorems) (context := context) (hypotheses := []) (entails signature.symbol antecedent conclusion))
    (g p q : Formula Const gamma)
    (antecedentRead : readFormulaIn abbreviation reader parameters names antecedent = some g)
    (extraRead : readFormulaIn abbreviation reader parameters names extra = some p)
    (conclusionRead : readFormulaIn abbreviation reader parameters names conclusion = some q)
    {fuel : Nat}
    (sourceAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      fuel names source.val (.imp g q)) :
    Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt
      (max 1 fuel + 1) names
      (HOLKernelStructuralRules.weaken signature rules antecedent extra conclusion
        antecedentSorted extraSorted conclusionSorted source).val (.imp (.and g p) q)) := by
  obtain ⟨leftAdmitted⟩ := left_admitted signature abbreviation distinctIm distinctAn rules reader parameters names
    ruleAt bindingAt (selected .anl) antecedent extra antecedentSorted extraSorted g p antecedentRead extraRead
  exact compose_admitted signature abbreviation distinctIm rules reader parameters names ruleAt bindingAt
    (selected .syl) (conjunction signature.symbol antecedent extra) antecedent conclusion
    (conjunction_sorted signature context antecedentSorted extraSorted) antecedentSorted conclusionSorted
    (HOLKernelStructuralRules.left signature rules antecedent extra antecedentSorted extraSorted) source
    (.and g p) g q
    (by simp [read_conjunction abbreviation signature.symbol_injective distinctAn, antecedentRead, extraRead])
    antecedentRead conclusionRead leftAdmitted sourceAdmitted


theorem read_antecedent_mapped
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (faithful : Function.Injective references) (distinctAn : references .an ≠ abbreviation.reference)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    {Entry : Type v} (native : Entry → Preterm) (source : Entry → Formula Const gamma)
    (formation : Preterm) (g : Formula Const gamma)
    (baseRead : readFormulaIn abbreviation reader parameters names formation = some g)
    (entries : List Entry)
    (readings : ∀ entry ∈ entries, readFormulaIn abbreviation reader parameters names (native entry) = some (source entry)) :
    readFormulaIn abbreviation reader parameters names
      (HOLKernelAssumptions.antecedent references formation (entries.map native)) =
      some (entries.foldr (fun entry tail => .and tail (source entry)) g) := by
  induction entries with
  | nil => exact baseRead
  | cons entry rest ih =>
      simp only [List.map_cons, HOLKernelAssumptions.antecedent,
        read_conjunction abbreviation faithful distinctAn,
        ih (fun value member => readings value (List.mem_cons_of_mem entry member)),
        readings entry List.mem_cons_self, Option.bind_some, Option.map_some, List.foldr_cons]

theorem hypothesis_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinctIm : signature.symbol .im ≠ abbreviation.reference)
    (distinctAn : signature.symbol .an ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.structural rule))
    {Entry : Type v} (native : Entry → Preterm) (source : Entry → Formula Const gamma)
    (formation : Preterm) (formed : Preterm.HasType terms context formation [] signature.ids.wff)
    (g : Formula Const gamma)
    (baseRead : readFormulaIn abbreviation reader parameters names formation = some g) :
    ∀ (entries : List Entry)
      (sorted : ∀ entry ∈ entries, Preterm.HasType terms context (native entry) [] signature.ids.wff)
      (_readings : ∀ entry ∈ entries, readFormulaIn abbreviation reader parameters names (native entry) = some (source entry))
      (occurrence : Fin entries.length),
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt fuel names
      (HOLKernelAssumptions.hypothesis (definitions := definitions) (hypotheses := []) signature rules formation formed
        (entries.map native)
        (by intro value member; obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp member; exact sorted entry entryMem)
        ⟨occurrence.val, by rw [List.length_map]; exact occurrence.isLt⟩).val
      (.imp (entries.foldr (fun entry tail => .and tail (source entry)) g) (source (entries.get occurrence)))) := by
  intro entries
  induction entries with
  | nil => intro _ _ occurrence; exact Fin.elim0 occurrence
  | cons first rest ih =>
      intro sorted readings occurrence
      have tailSorted : ∀ value ∈ rest.map native, Preterm.HasType terms context value [] signature.ids.wff := by
        intro value member
        obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp member
        exact sorted entry (List.mem_cons_of_mem first mem)
      have tailRead := read_antecedent_mapped abbreviation signature.symbol_injective distinctAn reader parameters names
        native source formation g baseRead rest (fun entry mem => readings entry (List.mem_cons_of_mem first mem))
      have formedTail := HOLKernelAssumptions.antecedent_sorted signature formation formed (rest.map native) tailSorted
      rcases occurrence with ⟨index, smaller⟩
      cases index with
      | zero =>
          refine ⟨1, ?_⟩
          exact right_admitted signature abbreviation distinctIm distinctAn rules reader parameters names ruleAt bindingAt
            (selected .anr) _ _ formedTail (sorted first List.mem_cons_self) _ _ tailRead (readings first List.mem_cons_self)
      | succ index =>
          let position : Fin rest.length := ⟨index, by simpa using smaller⟩
          obtain ⟨fuel, ⟨previous⟩⟩ := ih
            (fun entry mem => sorted entry (List.mem_cons_of_mem first mem))
            (fun entry mem => readings entry (List.mem_cons_of_mem first mem)) position
          refine ⟨max 1 fuel + 1, ?_⟩
          let nativePosition : Fin (rest.map native).length :=
            ⟨position.val, by rw [List.length_map]; exact position.isLt⟩
          let rawTail := HOLKernelAssumptions.hypothesis (definitions := definitions) (hypotheses := [])
            signature rules formation formed (rest.map native) tailSorted nativePosition
          have next := weaken_admitted signature abbreviation distinctIm distinctAn rules reader parameters names
            ruleAt bindingAt selected
            (HOLKernelAssumptions.antecedent signature.symbol formation (rest.map native))
            (native first) ((rest.map native).get nativePosition) formedTail (sorted first List.mem_cons_self)
            (tailSorted _ (List.get_mem _ nativePosition)) rawTail
            _ _ _ tailRead (readings first List.mem_cons_self)
            (by simpa only [List.get_eq_getElem, List.getElem_map] using
              readings (rest.get position) (List.mem_cons_of_mem first (List.get_mem rest position))) previous
          exact next



theorem formationProjection_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinctIm : signature.symbol .im ≠ abbreviation.reference)
    (distinctAn : signature.symbol .an ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.structural rule))
    {Entry : Type v} (native : Entry → Preterm) (source : Entry → Formula Const gamma)
    (formation : Preterm) (formed : Preterm.HasType terms context formation [] signature.ids.wff)
    (g : Formula Const gamma)
    (baseRead : readFormulaIn abbreviation reader parameters names formation = some g) :
    ∀ (entries : List Entry)
      (sorted : ∀ entry ∈ entries, Preterm.HasType terms context (native entry) [] signature.ids.wff)
      (_readings : ∀ entry ∈ entries, readFormulaIn abbreviation reader parameters names (native entry) = some (source entry)),
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt fuel names
      (HOLKernelAssumptions.formationProjection (definitions := definitions) (hypotheses := []) signature rules formation formed
        (entries.map native)
        (by intro value member; obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp member; exact sorted entry entryMem)).val
      (.imp (entries.foldr (fun entry tail => .and tail (source entry)) g) g)) := by
  intro entries
  induction entries with
  | nil =>
      intro _ _
      exact ⟨1, identity_admitted signature abbreviation distinctIm rules reader parameters names ruleAt bindingAt
        (selected .id) formation formed g baseRead⟩
  | cons first rest ih =>
      intro sorted readings
      have tailSorted : ∀ value ∈ rest.map native, Preterm.HasType terms context value [] signature.ids.wff := by
        intro value member
        obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp member
        exact sorted entry (List.mem_cons_of_mem first mem)
      have tailRead := read_antecedent_mapped abbreviation signature.symbol_injective distinctAn reader parameters names
        native source formation g baseRead rest (fun entry mem => readings entry (List.mem_cons_of_mem first mem))
      have formedTail := HOLKernelAssumptions.antecedent_sorted signature formation formed (rest.map native) tailSorted
      obtain ⟨fuel, ⟨previous⟩⟩ := ih
        (fun entry mem => sorted entry (List.mem_cons_of_mem first mem))
        (fun entry mem => readings entry (List.mem_cons_of_mem first mem))
      refine ⟨max 1 fuel + 1, ?_⟩
      exact weaken_admitted signature abbreviation distinctIm distinctAn rules reader parameters names
        ruleAt bindingAt selected _ _ _ formedTail (sorted first List.mem_cons_self) formed
        (HOLKernelAssumptions.formationProjection (definitions := definitions) (hypotheses := [])
          signature rules formation formed (rest.map native) tailSorted)
        _ _ _ tailRead (readings first List.mem_cons_self) baseRead previous

#print axioms formationProjection_admitted

#print axioms hypothesis_admitted

#print axioms compose_admitted
#print axioms pair_admitted
#print axioms left_admitted
#print axioms right_admitted
#print axioms weaken_admitted

#print axioms identity_admitted
section ContextualAdmission
open HOLKernelJudgmentReadback
open HOLKernelStructuralRules (CheckedProof)
theorem right_admission_under_renaming (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    {delta : Ctx Unit} (names : Names delta) (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.wff)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.wff)
    (g p : Judgment Const delta)
    (firstRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference first) = some g)
    (secondRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference second) = some p)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (structural.index .anr) = some (.structural .anr)) :
    AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
      (HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := []) signature structural first second firstSorted secondSorted).val
      (.imp (.and g.formula p.formula) p.formula) := by
  intro target rho future _ _ related
  have firstFuture := logical_judgment_rename_of_read profile dictionary parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference first) g firstRead
  have secondFuture := logical_judgment_rename_of_read profile dictionary parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference second) p secondRead
  refine ⟨1, ?_⟩
  simpa only [Mettapedia.Logic.HOL.rename] using
    HOLKernelStructuralReadback.right_admitted signature abbreviation (distinct .im) (distinct .an) structural
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters future ruleAt bindingAt selected
      first second firstSorted secondSorted (Mettapedia.Logic.HOL.rename rho g.formula) (Mettapedia.Logic.HOL.rename rho p.formula)
      (by simp only [readFormulaIn, firstFuture, Option.map_some, Judgment.rename_formula])
      (by simp only [readFormulaIn, secondFuture, Option.map_some, Judgment.rename_formula])

theorem weaken_admission_under_renaming (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (dictionary : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    {delta : Ctx Unit} (names : Names delta) (antecedent extra conclusion : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (extraSorted : Preterm.HasType terms context extra [] signature.ids.wff)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.wff)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol antecedent conclusion))
    (g p q : Judgment Const delta)
    (antecedentRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference antecedent) = some g)
    (extraRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference extra) = some p)
    (conclusionRead : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) signature.symbol names
      (expandEquivalence signature.symbol abbreviation.reference conclusion) = some q)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (sourceAdmitted : AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names source.val (.imp g.formula q.formula)) :
    AdmissionUnderRenaming (context := context) abbreviation profile dictionary parameters ruleAt bindingAt names
      (HOLKernelStructuralRules.weaken signature structural antecedent extra conclusion antecedentSorted extraSorted conclusionSorted source).val
      (.imp (.and g.formula p.formula) q.formula) := by
  intro target rho future nodup above related
  obtain ⟨fuel, ⟨tree⟩⟩ := sourceAdmitted rho future nodup above related
  have antecedentFuture := logical_judgment_rename_of_read profile dictionary parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference antecedent) g antecedentRead
  have extraFuture := logical_judgment_rename_of_read profile dictionary parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference extra) p extraRead
  have conclusionFuture := logical_judgment_rename_of_read profile dictionary parameters names future rho related
    (expandEquivalence signature.symbol abbreviation.reference conclusion) q conclusionRead
  refine ⟨max 1 fuel + 1, ?_⟩
  simpa only [Mettapedia.Logic.HOL.rename] using
    HOLKernelStructuralReadback.weaken_admitted signature abbreviation (distinct .im) (distinct .an) structural
      (HOLKernelLogicalFunctionReadback.reader profile dictionary parameters) parameters future ruleAt bindingAt selected
      antecedent extra conclusion antecedentSorted extraSorted conclusionSorted source
      (Mettapedia.Logic.HOL.rename rho g.formula) (Mettapedia.Logic.HOL.rename rho p.formula) (Mettapedia.Logic.HOL.rename rho q.formula)
      (by simp only [readFormulaIn, antecedentFuture, Option.map_some, Judgment.rename_formula])
      (by simp only [readFormulaIn, extraFuture, Option.map_some, Judgment.rename_formula])
      (by simp only [readFormulaIn, conclusionFuture, Option.map_some, Judgment.rename_formula]) tree

#print axioms right_admission_under_renaming
#print axioms weaken_admission_under_renaming
end ContextualAdmission

section ContextPromotion
open HOLKernelStructuralRules (CheckedProof ProofContext)
/-- Formation-to-logical promotion preserves admission of the actual composed receipt. -/
theorem promote_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinct : signature.symbol .im ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .syl) = some (.structural .syl))
    (scope : ProofContext terms definitions theorems context [] signature.symbol signature.ids.wff)
    (conclusion : Preterm) (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.wff)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol scope.formation conclusion))
    (logical formation result : Formula Const gamma)
    (logicalRead : readFormulaIn abbreviation reader parameters names scope.logical = some logical)
    (formationRead : readFormulaIn abbreviation reader parameters names scope.formation = some formation)
    (resultRead : readFormulaIn abbreviation reader parameters names conclusion = some result)
    {projectionFuel sourceFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt projectionFuel names
      scope.projection.val (.imp logical formation))
    (sourceAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt sourceFuel names
      source.val (.imp formation result)) :
    Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt (max projectionFuel sourceFuel + 1) names
      (scope.promote signature rules conclusion conclusionSorted source).val (.imp logical result)) :=
  compose_admitted signature abbreviation distinct rules reader parameters names ruleAt bindingAt selected
    scope.logical scope.formation conclusion scope.logicalSorted scope.formationSorted conclusionSorted scope.projection source
    logical formation result logicalRead formationRead resultRead projectionAdmitted sourceAdmitted

/-- Promotion beneath an extra assumption retains the extended projection and source receipt. -/
theorem promoteUnder_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (distinctIm : signature.symbol .im ≠ abbreviation.reference)
    (distinctAn : signature.symbol .an ≠ abbreviation.reference)
    (rules : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.structural rule))
    (scope : ProofContext terms definitions theorems context [] signature.symbol signature.ids.wff)
    (assumption conclusion : Preterm)
    (assumptionSorted : Preterm.HasType terms context assumption [] signature.ids.wff)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.wff)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := [])
      (entails signature.symbol (conjunction signature.symbol scope.formation assumption) conclusion))
    (logical formation extra result : Formula Const gamma)
    (logicalRead : readFormulaIn abbreviation reader parameters names scope.logical = some logical)
    (formationRead : readFormulaIn abbreviation reader parameters names scope.formation = some formation)
    (extraRead : readFormulaIn abbreviation reader parameters names assumption = some extra)
    (resultRead : readFormulaIn abbreviation reader parameters names conclusion = some result)
    {projectionFuel sourceFuel : Nat}
    (projectionAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt projectionFuel names
      scope.projection.val (.imp logical formation))
    (sourceAdmitted : AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt sourceFuel names
      source.val (.imp (.and formation extra) result)) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems context reader parameters ruleAt bindingAt fuel names
      (scope.promoteUnder signature rules assumption conclusion assumptionSorted conclusionSorted source).val
      (.imp (.and logical extra) result)) := by
  let extendedLogical := conjunction signature.symbol scope.logical assumption
  have extendedSorted := conjunction_sorted signature context scope.logicalSorted assumptionSorted
  let formationProjection := HOLKernelStructuralRules.weaken signature rules scope.logical assumption scope.formation
    scope.logicalSorted assumptionSorted scope.formationSorted scope.projection
  let assumptionProjection := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
    signature rules scope.logical assumption scope.logicalSorted assumptionSorted
  have extendedRead : readFormulaIn abbreviation reader parameters names extendedLogical = some (.and logical extra) := by
    rw [read_conjunction abbreviation signature.symbol_injective distinctAn, logicalRead, extraRead]
    rfl
  have extendedFormationRead : readFormulaIn abbreviation reader parameters names (conjunction signature.symbol scope.formation assumption) =
      some (.and formation extra) := by
    rw [read_conjunction abbreviation signature.symbol_injective distinctAn, formationRead, extraRead]
    rfl
  obtain ⟨formationTree⟩ := weaken_admitted signature abbreviation distinctIm distinctAn rules reader parameters names ruleAt bindingAt selected
    scope.logical assumption scope.formation scope.logicalSorted assumptionSorted scope.formationSorted scope.projection
    logical extra formation logicalRead extraRead formationRead projectionAdmitted
  obtain ⟨assumptionTree⟩ := right_admitted signature abbreviation distinctIm distinctAn rules reader parameters names ruleAt bindingAt (selected .anr)
    scope.logical assumption scope.logicalSorted assumptionSorted logical extra logicalRead extraRead
  obtain ⟨projectionTree⟩ := pair_admitted signature abbreviation distinctIm distinctAn rules reader parameters names ruleAt bindingAt (selected .ian)
    extendedLogical scope.formation assumption extendedSorted scope.formationSorted assumptionSorted formationProjection assumptionProjection
    (.and logical extra) formation extra extendedRead formationRead extraRead formationTree assumptionTree
  refine ⟨max (max (max 1 projectionFuel + 1) 1 + 1) sourceFuel + 1, ?_⟩
  exact compose_admitted signature abbreviation distinctIm rules reader parameters names ruleAt bindingAt (selected .syl)
    extendedLogical (conjunction signature.symbol scope.formation assumption) conclusion extendedSorted
    (conjunction_sorted signature context scope.formationSorted assumptionSorted) conclusionSorted
    (HOLKernelStructuralRules.pair signature rules extendedLogical scope.formation assumption extendedSorted scope.formationSorted
      assumptionSorted formationProjection assumptionProjection) source (.and logical extra) (.and formation extra) result
    extendedRead extendedFormationRead resultRead projectionTree sourceAdmitted

#print axioms promote_admitted
#print axioms promoteUnder_admitted

end ContextPromotion
end Mettapedia.Languages.MM0.HOLKernelStructuralReadback

