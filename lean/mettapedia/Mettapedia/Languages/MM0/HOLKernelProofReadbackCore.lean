import Mettapedia.Languages.MM0.HOLKernelRuleReadback
import Mettapedia.Logic.HOL.ConversionNormalizationRecipes

/-!
# Context-indexed reconstruction of native HOL proof trees

The shared fold checks the actual native witness, reads formation and
nonbinding inference, and substitutes reconstructed child proofs in their
declaration order. A binding handler receives recursive readers at arbitrary
intrinsic variable frames. It must construct a source proof and establish its
exact reading of the native conclusion; supplying only a statement is
insufficient.

Fuel bounds the recursive computation. Native acceptance, intrinsic source
proof syntax and the equality of the read conclusion remain separate data.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofReadback

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelRuleReadback
open NamedElaboration (SomeConst)

universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

structure ProvedFormula (Const : Ty Unit → Type u) (gamma : Ctx Unit) where
  formula : Formula Const gamma
  proof : ProofSyntax Const [] formula

def supplyChildren [∀ type, DecidableEq (Const type)] :
    (expected : List (Formula Const gamma)) → List (ProvedFormula Const gamma) →
    Option (ProofSyntax.HypothesisSubstitution expected [])
  | [], [] => some (fun occurrence => Fin.elim0 occurrence)
  | formula :: rest, child :: children =>
      if same : child.formula = formula then do
        let tail ← supplyChildren rest children
        pure (Fin.cases (same ▸ child.proof) tail)
      else none
  | _, _ => none

variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

structure SourceReading
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (native : Preterm) where
  source : ProvedFormula Const gamma
  reading : readFormulaIn abbreviation reader parameters names native = some source.formula

structure ProofReadback
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) (names : Names gamma)
    (witness : ProofWitness) where
  native : Preterm
  accepted : witness.proof? terms definitions theorems context [] = some native
  source : ProvedFormula Const gamma
  reading : readFormulaIn abbreviation reader parameters names native = some source.formula

abbrev Reader
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) :=
  {gamma : Ctx Unit} → (names : Names gamma) → (witness : ProofWitness) →
    Option (ProofReadback abbreviation theorems context reader parameters names witness)

abbrev BindingHandler
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat) :=
  Reader abbreviation theorems context reader parameters →
    {gamma : Ctx Unit} → (names : Names gamma) → Nat → List Preterm → List ProofWitness →
    (native : Preterm) → Option (SourceReading abbreviation reader parameters names native)

def readProofWith [∀ type, DecidableEq (Const type)]
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat)
    (ruleAt : Nat → Option Rule)
    (binding : BindingHandler abbreviation theorems context reader parameters)
    {gamma : Ctx Unit} (names : Names gamma) : (fuel : Nat) → (witness : ProofWitness) →
    Option (ProofReadback abbreviation theorems context reader parameters names witness)
  | 0, _ => none
  | fuel + 1, witness =>
      match accepted : witness.proof? terms definitions theorems context [] with
      | none => none
      | some native =>
          match formation : HOLKernelJudgmentReadback.readJudgmentWith reader references names
              (expandEquivalence references abbreviation.reference native) with
          | some (.consequence antecedent (.typing _)) =>
              some ⟨native, accepted, ⟨.imp antecedent.formula .top, .impI .topI⟩,
                by simp [readFormulaIn, formation, HOLKernelJudgmentReadback.Judgment.formula]⟩
          | _ =>
              let recurse : Reader abbreviation theorems context reader parameters :=
                fun nextNames child =>
                  readProofWith abbreviation theorems context reader parameters ruleAt binding nextNames fuel child
              match witness with
              | .hyp _ => none
              | .theoremApp index arguments children =>
                  let standard : Option (SourceReading abbreviation reader parameters names native) := do
                    let application ← readApplication abbreviation theorems context reader parameters names
                      ruleAt index arguments
                    if same : application.native.conclusion = native then
                      let reconstructed ← children.mapM fun child => (recurse names child).map ProofReadback.source
                      let supplied ← supplyChildren application.interpretation.source.premises reconstructed
                      pure ⟨⟨application.interpretation.source.conclusion, application.apply supplied⟩,
                        same ▸ application.interpretation.conclusion_read⟩
                    else none
                  match standard with
                  | some source => some ⟨native, accepted, source.source, source.reading⟩
                  | none =>
                      (binding recurse names index arguments children native).map fun source =>
                        ⟨native, accepted, source.source, source.reading⟩
              | .conversion _ child => do
                  let reconstructed ← recurse names child
                  match reading : readFormulaIn abbreviation reader parameters names native with
                  | none => none
                  | some formula =>
                      if same : reconstructed.source.formula = formula then
                        pure ⟨native, accepted, ⟨formula, same ▸ reconstructed.source.proof⟩, reading⟩
                      else
                        (Mettapedia.Logic.HOL.ConversionRecipes.betaConvertProof?
                          formula reconstructed.source.proof).map fun proof =>
                            ⟨native, accepted, ⟨formula, proof⟩, reading⟩

theorem ProofReadback.native_checked
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {witness : ProofWitness}
    (reconstructed : ProofReadback abbreviation theorems context reader parameters names witness) :
    witness.check terms definitions theorems context [] reconstructed.native = true :=
  (ProofWitness.check_iff _ _ _ _ _ _ _).mpr (ProofWitness.proof_sound reconstructed.accepted)

theorem ProofReadback.source_derivation
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {witness : ProofWitness}
    (reconstructed : ProofReadback abbreviation theorems context reader parameters names witness) :
    ExtDerivation Const [] reconstructed.source.formula := reconstructed.source.proof.erase

theorem ProofReadback.formula_eq
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {witness : ProofWitness} {native : Preterm} {formula : Formula Const gamma}
    (reconstructed : ProofReadback abbreviation theorems context reader parameters names witness)
    (accepted : witness.proof? terms definitions theorems context [] = some native)
    (reading : readFormulaIn abbreviation reader parameters names native = some formula) :
    reconstructed.source.formula = formula := by
  have sameNative : reconstructed.native = native :=
    Option.some.inj (reconstructed.accepted.symm.trans accepted)
  cases sameNative
  exact Option.some.inj (reconstructed.reading.symm.trans reading)

/-- Ordered child admission at a fixed variable frame. -/
inductive AdmittedChildren
    (Child : ProofWitness → Formula Const gamma → Type u) :
    List ProofWitness → List (Formula Const gamma) → Type u where
  | nil : AdmittedChildren Child [] []
  | cons {child : ProofWitness} {children : List ProofWitness}
      {formula : Formula Const gamma} {premises : List (Formula Const gamma)}
      (head : Child child formula)
      (tail : AdmittedChildren Child children premises) :
      AdmittedChildren Child (child :: children) (formula :: premises)

def AdmittedChildren.map
    {Child Next : ProofWitness → Formula Const gamma → Type u}
    (transform : ∀ {child formula}, Child child formula → Next child formula)
    {children : List ProofWitness} {premises : List (Formula Const gamma)} :
    AdmittedChildren Child children premises → AdmittedChildren Next children premises
  | .nil => .nil
  | .cons head tail => .cons (transform head) (tail.map transform)

theorem mapM_supplyChildren_of_admitted [∀ type, DecidableEq (Const type)]
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {names : Names gamma}
    {recurse : (witness : ProofWitness) →
      Option (ProofReadback abbreviation theorems context reader parameters names witness)}
    {Child : ProofWitness → Formula Const gamma → Type u}
    (childrenOk : ∀ (child : ProofWitness) (formula : Formula Const gamma),
      Child child formula →
      ∃ out : ProofReadback abbreviation theorems context reader parameters names child,
        recurse child = some out ∧ out.source.formula = formula)
    {children : List ProofWitness} {premises : List (Formula Const gamma)}
    (admitted : AdmittedChildren Child children premises) :
    ∃ (reconstructed : List (ProvedFormula Const gamma))
      (supplied : ProofSyntax.HypothesisSubstitution premises []),
      (children.mapM fun child => (recurse child).map ProofReadback.source) = some reconstructed ∧
      supplyChildren premises reconstructed = some supplied := by
  induction admitted with
  | nil =>
      exact ⟨[], _, rfl, rfl⟩
  | cons head tail ih =>
      obtain ⟨out, hout, hform⟩ := childrenOk _ _ head
      obtain ⟨restReconstructed, restSupplied, hmap, hsupply⟩ := ih
      refine ⟨out.source :: restReconstructed, Fin.cases (hform ▸ out.source.proof) restSupplied, ?_, ?_⟩
      · simp [List.mapM_cons, hout, hmap]
      · simp [supplyChildren, hform, hsupply]

theorem betaConvertProof?_of_joinable [∀ type, DecidableEq (Const type)]
    {assumptions : List (Formula Const gamma)} {source target : Formula Const gamma}
    (proof : ProofSyntax Const assumptions source)
    (joinable : ConversionTiers.Joinable source target) :
    ∃ converted, ConversionRecipes.betaConvertProof? target proof = some converted := by
  have isSome := (ConversionRecipes.betaEquality?_isSome_iff source target).mpr joinable
  obtain ⟨equality, heq⟩ := Option.isSome_iff_exists.mp isSome
  simp only [ConversionRecipes.betaConvertProof?, heq, Option.bind_eq_bind, Option.bind_some]
  exact ⟨_, rfl⟩

/-- Proof-free one-step admission of a native MM0 proof node at an intrinsic
variable frame. No constructor embeds `ProofSyntax` or `ExtDerivation`. -/
inductive AdmittedStep
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (context : Context)
    (reader : TermReader Const) (parameters : Nat)
    (ruleAt : Nat → Option Rule)
    (BindingStep :
      ({delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u) →
      {delta : Ctx Unit} → Names delta → Nat → List Preterm → List ProofWitness →
      Preterm → Formula Const delta → Type u)
    (Child : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u)
    (names : Names gamma) :
    ProofWitness → Formula Const gamma → Type u where
  | formation {witness : ProofWitness} {native : Preterm}
      {antecedent : HOLKernelJudgmentReadback.Judgment Const gamma}
      {type : Ty Unit} {term : Term Const gamma type}
      (accepted : witness.proof? terms definitions theorems context [] = some native)
      (judgment : HOLKernelJudgmentReadback.readJudgmentWith reader references names
        (expandEquivalence references abbreviation.reference native) =
        some (.consequence antecedent (.typing term))) :
      AdmittedStep abbreviation theorems context reader parameters ruleAt BindingStep Child names
        witness (.imp antecedent.formula .top)
  | application {index : Nat} {arguments : List Preterm} {children : List ProofWitness}
      {native : Preterm}
      (accepted : (ProofWitness.theoremApp index arguments children).proof?
        terms definitions theorems context [] = some native)
      (admitted : AdmittedApplication abbreviation theorems context reader parameters names
        ruleAt index arguments)
      (sameConclusion : admitted.native.conclusion = native)
      (childrenAdmitted : AdmittedChildren (Child names) children admitted.operands.premises) :
      AdmittedStep abbreviation theorems context reader parameters ruleAt BindingStep Child names
        (.theoremApp index arguments children) admitted.operands.conclusion
  | binding {index : Nat} {arguments : List Preterm} {children : List ProofWitness}
      {native : Preterm} {formula : Formula Const gamma}
      (accepted : (ProofWitness.theoremApp index arguments children).proof?
        terms definitions theorems context [] = some native)
      (admitted : BindingStep Child names index arguments children native formula) :
      AdmittedStep abbreviation theorems context reader parameters ruleAt BindingStep Child names
        (.theoremApp index arguments children) formula
  | conversion {conv : ConvWitness} {child : ProofWitness}
      {native : Preterm} {sourceFormula formula : Formula Const gamma}
      (accepted : (ProofWitness.conversion conv child).proof?
        terms definitions theorems context [] = some native)
      (reading : readFormulaIn abbreviation reader parameters names native = some formula)
      (childAdmitted : Child names child sourceFormula)
      (joinable : ConversionTiers.Joinable sourceFormula formula) :
      AdmittedStep abbreviation theorems context reader parameters ruleAt BindingStep Child names
        (.conversion conv child) formula

/-- Change the recursive admission relation while retaining every native
node, rule licence, variable frame and decoded formula. -/
def AdmittedStep.mapChildren
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat} {ruleAt : Nat → Option Rule}
    {BindingStep :
      ({delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u) →
      {delta : Ctx Unit} → Names delta → Nat → List Preterm → List ProofWitness →
      Preterm → Formula Const delta → Type u}
    {Child Next : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u}
    (transform : ∀ {delta} {nextNames : Names delta} {child formula},
      Child nextNames child formula → Next nextNames child formula)
    (bindingMap : ∀ {delta} {nextNames : Names delta} {index arguments children native formula},
      BindingStep Child nextNames index arguments children native formula →
      BindingStep Next nextNames index arguments children native formula)
    {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma} :
    AdmittedStep abbreviation theorems context reader parameters ruleAt BindingStep Child names witness formula →
    AdmittedStep abbreviation theorems context reader parameters ruleAt BindingStep Next names witness formula
  | .formation accepted judgment => .formation accepted judgment
  | .application accepted localRule same children =>
      .application accepted localRule same (children.map transform)
  | .binding accepted bindingAdmitted => .binding accepted (bindingMap bindingAdmitted)
  | .conversion accepted reading child joinable =>
      .conversion accepted reading (transform child) joinable

theorem readProofWith_of_admitted [∀ type, DecidableEq (Const type)]
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context}
    {reader : TermReader Const} {parameters : Nat}
    {ruleAt : Nat → Option Rule}
    {binding : BindingHandler abbreviation theorems context reader parameters}
    {BindingStep :
      ({delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u) →
      {delta : Ctx Unit} → Names delta → Nat → List Preterm → List ProofWitness →
      Preterm → Formula Const delta → Type u}
    {Child : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u}
    {fuel : Nat}
    (childrenOk : ∀ {delta} (nextNames : Names delta) (child : ProofWitness) (formula : Formula Const delta),
      Child nextNames child formula →
      ∃ out : ProofReadback abbreviation theorems context reader parameters nextNames child,
        readProofWith abbreviation theorems context reader parameters ruleAt binding nextNames fuel child = some out ∧
        out.source.formula = formula)
    (bindingOk : ∀ {delta} (recurse : Reader abbreviation theorems context reader parameters),
      (∀ {eps} (nextNames : Names eps) (child : ProofWitness) (formula : Formula Const eps),
        Child nextNames child formula →
        ∃ out : ProofReadback abbreviation theorems context reader parameters nextNames child,
          recurse nextNames child = some out ∧ out.source.formula = formula) →
      ∀ (nextNames : Names delta) (index : Nat) (arguments : List Preterm)
        (children : List ProofWitness) (native : Preterm) (formula : Formula Const delta),
        BindingStep Child nextNames index arguments children native formula →
        ∃ source : SourceReading abbreviation reader parameters nextNames native,
          binding recurse nextNames index arguments children native = some source ∧
          source.source.formula = formula)
    {names : Names gamma} {witness : ProofWitness} {formula : Formula Const gamma}
    (step : AdmittedStep abbreviation theorems context reader parameters ruleAt BindingStep Child names witness formula) :
    ∃ out : ProofReadback abbreviation theorems context reader parameters names witness,
      readProofWith abbreviation theorems context reader parameters ruleAt binding names (fuel + 1) witness = some out ∧
      out.source.formula = formula := by
  cases step with
  | @formation witness native antecedent type term accepted judgment =>
      have reading : readFormulaIn abbreviation reader parameters names native =
          some (.imp antecedent.formula .top) := by
        simp [readFormulaIn, judgment, HOLKernelJudgmentReadback.Judgment.formula]
      suffices ∃ out, readProofWith abbreviation theorems context reader parameters ruleAt binding names (fuel + 1) witness = some out by
        obtain ⟨out, hout⟩ := this
        exact ⟨out, hout, out.formula_eq accepted reading⟩
      unfold readProofWith
      split
      next refused =>
        rw [accepted] at refused
        contradiction
      next native' accepted' =>
        have sameNative : native' = native := Option.some.inj (accepted'.symm.trans accepted)
        subst sameNative
        split
        · exact ⟨_, rfl⟩
        next _ hnot =>
          exact False.elim (hnot antecedent type term judgment)
  | @application index arguments children native accepted admitted sameConclusion childrenAdmitted =>
      have reading : readFormulaIn abbreviation reader parameters names native =
          some admitted.operands.conclusion :=
        sameConclusion ▸ admitted.conclusion_read
      suffices ∃ out, readProofWith abbreviation theorems context reader parameters ruleAt binding names (fuel + 1)
          (.theoremApp index arguments children) = some out by
        obtain ⟨out, hout⟩ := this
        exact ⟨out, hout, out.formula_eq accepted reading⟩
      have childrenAdmitted' :
          AdmittedChildren (Child names) children admitted.interpret.interpretation.source.premises :=
        admitted.operands.interpret_premises.symm ▸ childrenAdmitted
      obtain ⟨reconstructed, supplied, hmap, hsupply⟩ :=
        mapM_supplyChildren_of_admitted (childrenOk names) childrenAdmitted'
      have happ := readApplication_eq_of_admitted admitted
      unfold readProofWith
      split
      next refused =>
        rw [accepted] at refused
        contradiction
      next native' accepted' =>
        have sameNative : native' = native := Option.some.inj (accepted'.symm.trans accepted)
        subst sameNative
        split
        · exact ⟨_, rfl⟩
        · dsimp only
          have sameConc : admitted.interpret.native.conclusion = native' := sameConclusion
          simp only [happ, Option.bind_eq_bind, Option.bind_some, sameConc, ↓reduceDIte,
            hmap, hsupply]
          exact ⟨_, rfl⟩
  | @binding index arguments children native formula accepted admitted =>
      obtain ⟨source, hbinding, hform⟩ :=
        bindingOk _ childrenOk names index arguments children native formula admitted
      have reading : readFormulaIn abbreviation reader parameters names native = some formula :=
        hform ▸ source.reading
      suffices ∃ out, readProofWith abbreviation theorems context reader parameters ruleAt binding names (fuel + 1)
          (.theoremApp index arguments children) = some out by
        obtain ⟨out, hout⟩ := this
        exact ⟨out, hout, out.formula_eq accepted reading⟩
      unfold readProofWith
      split
      next refused =>
        rw [accepted] at refused
        contradiction
      next native' accepted' =>
        have sameNative : native' = native := Option.some.inj (accepted'.symm.trans accepted)
        subst sameNative
        split
        · exact ⟨_, rfl⟩
        · dsimp only
          split
          · exact ⟨_, rfl⟩
          · simp only [hbinding, Option.map_some]
            exact ⟨_, rfl⟩
  | @conversion conv child native sourceFormula formula accepted reading childAdmitted joinable =>
      obtain ⟨childOut, hchild, hchildForm⟩ := childrenOk names child sourceFormula childAdmitted
      suffices ∃ out, readProofWith abbreviation theorems context reader parameters ruleAt binding names (fuel + 1)
          (.conversion conv child) = some out by
        obtain ⟨out, hout⟩ := this
        exact ⟨out, hout, out.formula_eq accepted reading⟩
      unfold readProofWith
      split
      next refused =>
        rw [accepted] at refused
        contradiction
      next native' accepted' =>
        have sameNative : native' = native := Option.some.inj (accepted'.symm.trans accepted)
        subst sameNative
        split
        · exact ⟨_, rfl⟩
        · dsimp only
          simp only [hchild, Option.bind_eq_bind, Option.bind_some]
          split
          next refusedRead =>
            rw [reading] at refusedRead
            contradiction
          next decoded reading' =>
            have sameDecoded : decoded = formula := Option.some.inj (reading'.symm.trans reading)
            subst sameDecoded
            split
            · exact ⟨_, rfl⟩
            · have joinable' : ConversionTiers.Joinable childOut.source.formula decoded :=
                hchildForm ▸ joinable
              obtain ⟨converted, hconv⟩ := betaConvertProof?_of_joinable childOut.source.proof joinable'
              simp only [hconv, Option.map_some]
              exact ⟨_, rfl⟩

#print axioms readProofWith
#print axioms ProofReadback.native_checked
#print axioms ProofReadback.source_derivation
#print axioms readProofWith_of_admitted

end Mettapedia.Languages.MM0.HOLKernelProofReadback
