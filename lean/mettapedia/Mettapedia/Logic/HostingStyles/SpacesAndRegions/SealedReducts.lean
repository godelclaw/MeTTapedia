import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Readings
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedAsWritten

/-!
# The reducts of a sealed program, as terms of the theory

Under the sealing reading the program `((lam x *@(f x)) payload)` reaches
`(f x)`.  This module shows that, at the empty ambient space, it reaches no
term of another class than four, **on terms**: a transition of the theory is
a step up to the static equivalence, so every spelling of a reduct has to be
followed.

* The spellings.  In a pattern in which every dropping drops a quotation, a
  contraction that is an application of a constructor other than quotation
  comes from an application of that constructor (`eq_apply_of_contract`), a
  contraction that is an abstraction from an abstraction
  (`eq_lambda_of_contract`), a contraction that is a quotation from a
  quotation of the atom or of a dropped quotation of it
  (`eq_quoted_of_contract`), and a pattern whose contraction has no quotation
  and no run is its own contraction (`eq_contract_of_quiet`).
* **The four classes are closed under the steps of every spelling**
  (`quotedUseReduct_step`).  The program has more than one spelling: its
  quotation may be the quotation of a dropped quotation, any number of times;
  the release then steps to a term of the same class.
* **So under the sealing reading the program reaches only terms of the four
  classes** (`quotedUseProgram_sealing_reducts_on_terms`), and **not
  `(f payload)`** (`quotedUseProgram_sealing_not_plainResult_on_terms`),
  which the plain reading reaches.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar instantiateBVarAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
  (contract contractList contractRoot contract_apply_of_ne contractRoot_quote_cases quoted
    dropped unitAtom numeral contract_numeral variableAtom emptySpace nameCode)
open Mettapedia.Logic.HostingStyles.AtomsReduce (symbolAtom tokens_numeral)
open Mettapedia.Logic.HostingStyles.AmbientSpace (tokens_apply_eq_zero_iff)
open Mettapedia.Logic.HostingStyles.AmbientRegions (regionEvaluator admittedAnswers_emptySpace)
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## The spellings of a contraction -/

/-- **A pattern in which every dropping drops a quotation, and whose
contraction has no quotation and no run, is its own contraction.** -/
theorem eq_contract_of_quiet {pattern : Pattern} (drops : dropsQuotations pattern = true)
    (quiet : tokens quoteOrRun (contract pattern) = 0) : contract pattern = pattern :=
  contract_of_tokens_eq_zero (counted := quoteOrRun) (by decide) pattern
    (tokens_of_contract_eq_zero pattern drops quiet)

/-- **A contraction that is an application of a constructor other than
quotation comes from an application of that constructor**, where every
dropping drops a quotation. -/
theorem eq_apply_of_contract {pattern : Pattern} {label : String} {arguments : List Pattern}
    (drops : dropsQuotations pattern = true) (other : label ≠ "prime-quote")
    (same : contract pattern = .apply label arguments) :
    ∃ parts, pattern = .apply label parts ∧ parts.map contract = arguments := by
  cases pattern with
  | bvar index => rw [contract] at same; cases same
  | fvar name => rw [contract] at same; cases same
  | apply head parts =>
      rw [contract_apply] at same
      rcases contractRoot_cases head (parts.map contract) with ⟨name, rfl, shape, value⟩ | plain
      · rw [value] at same
        obtain ⟨argument, rfl, contracted⟩ := List.map_eq_singleton_iff.mp shape
        obtain ⟨-, each⟩ := (dropsQuotations_apply "prime-quote" [argument]).mp drops
        obtain ⟨atom, quotation⟩ := (contract_dropping_of_dropsQuotations argument
          (each argument (by simp))).1 name contracted
        rw [quotation] at same
        simp only [quoted, Pattern.apply.injEq] at same
        exact absurd same.1.symm other
      · rw [plain] at same
        simp only [Pattern.apply.injEq] at same
        obtain ⟨rfl, mapped⟩ := same
        exact ⟨parts, rfl, mapped⟩
  | lambda binder body => rw [contract] at same; cases same
  | multiLambda arity binders body => rw [contract] at same; cases same
  | subst body replacement => rw [contract] at same; cases same
  | collection kind elements rest => rw [contract] at same; cases same

/-- **A contraction that is an abstraction comes from an abstraction**, where
every dropping drops a quotation. -/
theorem eq_lambda_of_contract {pattern body : Pattern} {binder : Option String}
    (drops : dropsQuotations pattern = true) (same : contract pattern = .lambda binder body) :
    ∃ inner, pattern = .lambda binder inner ∧ contract inner = body := by
  cases pattern with
  | bvar index => rw [contract] at same; cases same
  | fvar name => rw [contract] at same; cases same
  | apply head parts =>
      rw [contract_apply] at same
      rcases contractRoot_cases head (parts.map contract) with ⟨name, rfl, shape, value⟩ | plain
      · rw [value] at same
        obtain ⟨argument, rfl, contracted⟩ := List.map_eq_singleton_iff.mp shape
        obtain ⟨-, each⟩ := (dropsQuotations_apply "prime-quote" [argument]).mp drops
        obtain ⟨atom, quotation⟩ := (contract_dropping_of_dropsQuotations argument
          (each argument (by simp))).1 name contracted
        rw [quotation] at same
        cases same
      · rw [plain] at same
        cases same
  | lambda other inner =>
      rw [contract] at same
      simp only [Pattern.lambda.injEq] at same
      obtain ⟨rfl, bodySame⟩ := same
      exact ⟨inner, rfl, bodySame⟩
  | multiLambda arity binders inner => rw [contract] at same; cases same
  | subst inner replacement => rw [contract] at same; cases same
  | collection kind elements rest => rw [contract] at same; cases same

/-- **A contraction that is a quotation comes from a quotation**, of a
pattern whose contraction is the atom, or the dropped quotation of the
atom. -/
theorem eq_quoted_of_contract {name atom : Pattern} (same : contract name = quoted atom) :
    ∃ inner, name = quoted inner ∧
      (contract inner = atom ∨ contract inner = dropped (quoted atom)) := by
  cases name with
  | bvar index => rw [contract] at same; cases same
  | fvar other => rw [contract] at same; cases same
  | apply head parts =>
      rw [contract_apply] at same
      rcases contractRoot_cases head (parts.map contract) with ⟨dropped_, rfl, shape, value⟩ | plain
      · rw [value] at same
        obtain ⟨inner, rfl, contracted⟩ := List.map_eq_singleton_iff.mp shape
        exact ⟨inner, rfl, .inr (by rw [contracted, same]; rfl)⟩
      · rw [plain] at same
        simp only [quoted, Pattern.apply.injEq] at same
        obtain ⟨rfl, mapped⟩ := same
        obtain ⟨inner, rfl, contracted⟩ := List.map_eq_singleton_iff.mp mapped
        exact ⟨inner, rfl, .inl contracted⟩
  | lambda binder body => rw [contract] at same; cases same
  | multiLambda arity binders body => rw [contract] at same; cases same
  | subst body replacement => rw [contract] at same; cases same
  | collection kind elements rest => rw [contract] at same; cases same

/-- **A contraction that is a dropped quotation comes from a dropped
quotation**, of a pattern whose contraction is the atom, or the dropped
quotation of the atom again. -/
theorem eq_dropQuote_of_contract {pattern atom : Pattern}
    (drops : dropsQuotations pattern = true)
    (same : contract pattern = dropped (quoted atom)) :
    ∃ inner, pattern = dropped (quoted inner) ∧
      (contract inner = atom ∨ contract inner = dropped (quoted atom)) := by
  obtain ⟨parts, rfl, mapped⟩ := eq_apply_of_contract (label := "prime-drop") drops (by decide) same
  obtain ⟨name, rfl, nameSame⟩ := List.map_eq_singleton_iff.mp mapped
  obtain ⟨inner, rfl, innerSame⟩ := eq_quoted_of_contract nameSame
  exact ⟨inner, rfl, innerSame⟩

/-- The contractions of the two arguments of an application. -/
theorem eq_pair_of_map_contract {parts : List Pattern} {first second : Pattern}
    (mapped : parts.map contract = [first, second]) :
    ∃ left right, parts = [left, right] ∧ contract left = first ∧ contract right = second := by
  obtain ⟨left, rest, rfl, leftSame, restSame⟩ := List.map_eq_cons_iff.mp mapped
  obtain ⟨right, rfl, rightSame⟩ := List.map_eq_singleton_iff.mp restSame
  exact ⟨left, right, rfl, leftSame, rightSame⟩

/-! ## The four classes -/

/-- `(f x)` with `x` the variable atom of the name: what the quotation of the
program holds under the sealing reading. -/
def quotedCode : Pattern :=
  .apply "App" [symbolAtom (nameCode "f"), variableAtom (numeral (nameCode "x"))]

/-- The program with the quotation in its body released:
`((lam x (f x)) payload)`, the `x` of the body the variable atom. -/
def releasedProgram : Pattern :=
  .apply "App" [.apply "Lam" [unitAtom, .lambda none quotedCode], symbolAtom (nameCode "payload")]

/-- **The four classes of the reducts of the program under the sealing
reading**, each by the pattern that contraction fixes: the program; the
program with its quotation released; the dropped quotation `*@(f x)`; and
`(f x)`. -/
def QuotedUseReduct (pattern : Pattern) : Prop :=
  pattern = readSealing [] [] quotedUseProgram ∨ pattern = releasedProgram ∨
    pattern = dropped (quoted quotedCode) ∨ pattern = quotedCode

/-- **Positive**: `(f x)`. -/
theorem quotedUseReduct_quotedCode : QuotedUseReduct quotedCode := .inr (.inr (.inr rfl))

/-- **Negative**: `(f payload)`. -/
theorem not_quotedUseReduct_plainResult :
    ¬ QuotedUseReduct
      (.apply "App" [symbolAtom (nameCode "f"), symbolAtom (nameCode "payload")]) := by
  rintro (same | same | same | same)
  · rw [readSealing_quotedUseProgram] at same
    simp [symbolAtom] at same
  · simp [releasedProgram, symbolAtom] at same
  · simp [dropped] at same
  · simp [quotedCode, symbolAtom, variableAtom] at same

theorem tokens_quoteOrRun_symbolAtom (code : Nat) : tokens quoteOrRun (symbolAtom code) = 0 :=
  tokens_apply_eq_zero_iff.mpr ⟨by decide, fun argument member => by
    rw [List.mem_singleton.mp member]
    exact tokens_numeral (by decide) (by decide) code⟩

theorem tokens_quoteOrRun_quotedCode : tokens quoteOrRun quotedCode = 0 :=
  tokens_apply_eq_zero_iff.mpr ⟨by decide, fun argument member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact tokens_quoteOrRun_symbolAtom _
    · exact tokens_apply_eq_zero_iff.mpr ⟨by decide, fun inner inside => by
        rw [List.mem_singleton.mp inside]
        exact tokens_numeral (by decide) (by decide) _⟩⟩

theorem tokens_quoteOrRun_releasedProgram : tokens quoteOrRun releasedProgram = 0 :=
  tokens_apply_eq_zero_iff.mpr ⟨by decide, fun argument member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine tokens_apply_eq_zero_iff.mpr ⟨by decide, fun inner inside => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · decide +kernel
      · rw [tokens]
        exact tokens_quoteOrRun_quotedCode
    · exact tokens_quoteOrRun_symbolAtom _⟩

/-- Contraction fixes the sealing reading of the program. -/
theorem contract_readSealing_quotedUseProgram :
    contract (readSealing [] [] quotedUseProgram) = readSealing [] [] quotedUseProgram := by
  rw [readSealing_quotedUseProgram]
  simp [contract, contractList, contractRoot, dropped, quoted, symbolAtom, variableAtom, unitAtom,
    contract_numeral]

/-- **Each of the four patterns is sealed with plain runs.** -/
theorem QuotedUseReduct.sealed {pattern : Pattern} (member : QuotedUseReduct pattern) :
    SealedWithPlainRuns 0 pattern := by
  have code : ∀ depth : Nat, SealedWithPlainRuns depth quotedCode := fun depth =>
    (sealedWithPlainRuns_apply_iff (label := "App") (by decide) depth _).mpr fun part inside => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact sealedWithPlainRuns_symbolAtom _ _
      · exact sealedWithPlainRuns_variableAtom _ _
  rcases member with rfl | rfl | rfl | rfl
  · exact readSealing_sealed quotedUseProgram [] []
  · refine (sealedWithPlainRuns_apply_iff (label := "App") (by decide) 0 _).mpr
      fun part inside => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · refine (sealedWithPlainRuns_apply_iff (label := "Lam") (by decide) 0 _).mpr
        fun inner within => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at within
      rcases within with rfl | rfl
      · exact sealedWithPlainRuns_numeral 0 0
      · exact (sealedWithPlainRuns_lambda 0 none quotedCode).mpr (code 1)
    · exact sealedWithPlainRuns_symbolAtom _ _
  · exact sealedWithPlainRuns_dropQuote (code 0) 0
  · exact code 0

/-! ## The four classes are closed under the steps of every spelling -/

/-- **A step from any spelling of a term of the four classes leads to a term
of the four classes**, at the empty ambient space and under every guard.  The
spelling is a pattern in which every dropping drops a quotation and which is
sealed as it is written. -/
theorem quotedUseReduct_step (admits : Pattern → Bool) {redex next : Pattern}
    (drops : dropsQuotations redex = true) (safe : sealedAt 0 redex = true)
    (member : QuotedUseReduct (contract redex))
    (step : Step (regionEvaluator admits emptySpace) spacesAndRegions redex next) :
    QuotedUseReduct (contract next) := by
  have unitNormal : ∀ target, ¬ Step (regionEvaluator admits emptySpace) spacesAndRegions
      unitAtom target := fun target =>
    leaf_normal_at_emptySpace (label := "prime-unit") (arguments := []) (by decide) (by decide)
      (by decide) (by decide) (by decide) target
  have payloadNormal : ∀ target, ¬ Step (regionEvaluator admits emptySpace) spacesAndRegions
      (symbolAtom (nameCode "payload")) target := fun target =>
    leaf_normal_at_emptySpace (label := "prime-symbol") (by decide) (by decide) (by decide)
      (by decide) (by decide) target
  have codeFixed : contract quotedCode = quotedCode :=
    contract_of_tokens_eq_zero (counted := quoteOrRun) (by decide) _ tokens_quoteOrRun_quotedCode
  rcases member with same | same | same | same
  · rw [readSealing_quotedUseProgram] at same
    obtain ⟨parts, rfl, mapped⟩ := eq_apply_of_contract (label := "App") drops (by decide) same
    obtain ⟨function, argument, rfl, functionSame, argumentSame⟩ := eq_pair_of_map_contract mapped
    have partsDrop := ((dropsQuotations_apply "App" _).mp drops).2
    have functionDrops : dropsQuotations function = true := partsDrop function (by simp)
    have argumentFixed : argument = symbolAtom (nameCode "payload") := by
      rw [← argumentSame]
      exact (eq_contract_of_quiet (partsDrop argument (by simp))
        (by rw [argumentSame]; exact tokens_quoteOrRun_symbolAtom _)).symm
    subst argumentFixed
    obtain ⟨inner, rfl, innerMapped⟩ :=
      eq_apply_of_contract (label := "Lam") functionDrops (by decide) functionSame
    obtain ⟨domain, abstraction, rfl, domainSame, abstractionSame⟩ :=
      eq_pair_of_map_contract innerMapped
    have innerDrop := ((dropsQuotations_apply "Lam" _).mp functionDrops).2
    have domainFixed : domain = unitAtom := by
      rw [← domainSame]
      exact (eq_contract_of_quiet (innerDrop domain (by simp))
        (by rw [domainSame]; decide +kernel)).symm
    subst domainFixed
    obtain ⟨body, rfl, bodySame⟩ :=
      eq_lambda_of_contract (innerDrop abstraction (by simp)) abstractionSame
    have bodyDrops : dropsQuotations body = true := by
      have whole := innerDrop (.lambda none body) (by simp)
      rwa [dropsQuotations] at whole
    obtain ⟨code, rfl, codeSame⟩ := eq_dropQuote_of_contract bodyDrops bodySame
    have quotationSafe : sealedAt 1 (quoted code) = true := by
      have parts := (sealedAt_apply_of_ne (label := "App") (by decide) 0 _).mp safe
      have abstractionSafe := (sealedAt_apply_of_ne (label := "Lam") (by decide) 0 _).mp
        (parts _ (List.mem_cons_self ..))
      have bodySafe := abstractionSafe (.lambda none (dropped (quoted code))) (by simp)
      rw [sealedAt_lambda] at bodySafe
      exact (sealedAt_apply_of_ne (label := "prime-drop") (by decide) (0 + 1) _).mp bodySafe
        (quoted code) (List.mem_singleton.mpr rfl)
    rcases spacesAndRegions_app_step_iff.mp step with ⟨otherDomain, binder, otherBody, shape, rfl⟩ |
      ⟨moved, movedStep, rfl⟩ | ⟨moved, movedStep, -⟩ | found
    · simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
        true_and] at shape
      obtain ⟨-, -, rfl⟩ := shape
      have fixedBody : instantiateBVar (symbolAtom (nameCode "payload")) (dropped (quoted code)) =
          dropped (quoted code) := by
        show instantiateBVarAt 0 _ (.apply "prime-drop" [quoted code]) = _
        rw [instantiateBVarAt, List.map_cons, List.map_nil,
          instantiateBVarAt_quoted_of_sealed quotationSafe]
        rfl
      rw [fixedBody, bodySame]
      exact .inr (.inr (.inl rfl))
    · rcases lam_step_at_emptySpace movedStep with ⟨reached, inside, -⟩ | ⟨reached, inside, rfl⟩
      · exact absurd inside (unitNormal reached)
      · rw [dropQuote_step_at_emptySpace inside]
        have computed : contract (.apply "App" [.apply "Lam" [unitAtom, .lambda none code],
            symbolAtom (nameCode "payload")]) =
            .apply "App" [.apply "Lam" [unitAtom, .lambda none (contract code)],
              symbolAtom (nameCode "payload")] := by
          simp [contract, contractList, contractRoot, symbolAtom, unitAtom, contract_numeral]
        rw [computed]
        rcases codeSame with codeSame | codeSame
        · rw [codeSame]
          exact .inr (.inl rfl)
        · rw [codeSame]
          exact .inl (by rw [readSealing_quotedUseProgram])
    · exact absurd movedStep (payloadNormal moved)
    · rw [admittedAnswers_emptySpace] at found
      cases found
  · have fixed : redex = releasedProgram := by
      rw [← same]
      exact (eq_contract_of_quiet drops
        (by rw [same]; exact tokens_quoteOrRun_releasedProgram)).symm
    subst fixed
    rcases spacesAndRegions_app_step_iff.mp step with ⟨otherDomain, binder, otherBody, shape, rfl⟩ |
      ⟨moved, movedStep, -⟩ | ⟨moved, movedStep, -⟩ | found
    · simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
        true_and] at shape
      obtain ⟨-, -, rfl⟩ := shape
      have instance_ :
          instantiateBVar (symbolAtom (nameCode "payload")) quotedCode = quotedCode := by
        simp [instantiateBVar, instantiateBVarAt, quotedCode, instantiateBVarAt_symbolAtom,
          instantiateBVarAt_variableAtom]
      rw [instance_, codeFixed]
      exact .inr (.inr (.inr rfl))
    · rcases lam_step_at_emptySpace movedStep with ⟨reached, inside, -⟩ | ⟨reached, inside, -⟩
      · exact absurd inside (unitNormal reached)
      · exact absurd inside (symbol_of_variable_normal _ _ reached)
    · exact absurd movedStep (payloadNormal moved)
    · rw [admittedAnswers_emptySpace] at found
      cases found
  · obtain ⟨code, rfl, codeSame⟩ := eq_dropQuote_of_contract drops same
    rw [dropQuote_step_at_emptySpace step]
    rcases codeSame with codeSame | codeSame
    · rw [codeSame]
      exact .inr (.inr (.inr rfl))
    · rw [codeSame]
      exact .inr (.inr (.inl rfl))
  · have fixed : redex = quotedCode := by
      rw [← same]
      exact (eq_contract_of_quiet drops (by rw [same]; exact tokens_quoteOrRun_quotedCode)).symm
    subst fixed
    exact absurd step (symbol_of_variable_normal _ _ next)

/-! ## On terms -/

/-- **Under the sealing reading the program reaches only terms of the four
classes**, at the empty ambient space and under every guard: whatever
spelling a transition takes. -/
theorem quotedUseProgram_sealing_reducts_on_terms (admits : Pattern → Bool)
    {target : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩}
    (reached : Relation.ReflTransGen
      (TermStep (regionEvaluator admits emptySpace) spacesAndRegions)
      (sealingTerm [] quotedUseProgram) target) :
    QuotedUseReduct (contract target.1) := by
  induction reached with
  | refl =>
      show QuotedUseReduct (contract (readSealing [] [] quotedUseProgram))
      rw [contract_readSealing_quotedUseProgram]
      exact .inl rfl
  | tail _ step ih =>
      obtain ⟨redex, contractum, before, fired, after⟩ := step
      have member : QuotedUseReduct (contract redex.1) := by
        rw [← spacesAndRegions_quoteDropOnly.contract_eq before]
        exact ih
      have drops : dropsQuotations redex.1 = true :=
        dropsQuotations_of_wellSorted (fun _ inStage => absurd inStage List.not_mem_nil)
          (by decide) redex
      have safe : sealedAt 0 redex.1 = true :=
        ((sealedTerm_iff_sealedAsWritten (fun _ inStage => absurd inStage List.not_mem_nil)
          (by decide) redex).mp member.sealed).1
      rw [← spacesAndRegions_quoteDropOnly.contract_eq after]
      exact quotedUseReduct_step admits drops safe member fired

/-- **Under the sealing reading the program does not reach `(f payload)`**,
as terms of the theory, at the empty ambient space and under every guard.
The plain reading reaches it at every ambient space
(`quotedUseProgram_plain_reaches`). -/
theorem quotedUseProgram_sealing_not_plainResult_on_terms (admits : Pattern → Bool) :
    ¬ Relation.ReflTransGen (TermStep (regionEvaluator admits emptySpace) spacesAndRegions)
      (sealingTerm [] quotedUseProgram) (plainTerm (.app (.name "f") (.name "payload"))) := by
  intro reached
  have member := quotedUseProgram_sealing_reducts_on_terms admits reached
  rw [plainTerm_fpayload] at member
  have fixed : contract (.apply "App" [symbolAtom (nameCode "f"),
      symbolAtom (nameCode "payload")]) =
      .apply "App" [symbolAtom (nameCode "f"), symbolAtom (nameCode "payload")] := by
    simp [contract, contractList, contractRoot, symbolAtom, contract_numeral]
  rw [fixed] at member
  exact not_quotedUseReduct_plainResult member

#print axioms eq_contract_of_quiet
#print axioms eq_apply_of_contract
#print axioms eq_lambda_of_contract
#print axioms eq_quoted_of_contract
#print axioms eq_dropQuote_of_contract
#print axioms not_quotedUseReduct_plainResult
#print axioms QuotedUseReduct.sealed
#print axioms quotedUseReduct_step
#print axioms quotedUseProgram_sealing_reducts_on_terms
#print axioms quotedUseProgram_sealing_not_plainResult_on_terms

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
