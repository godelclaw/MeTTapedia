import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTree
import Mettapedia.GSLT.LanguageDef.SemanticService
import Mettapedia.OSLF.Syntax.FiniteRuleProofData
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding

/-!
# Native finite evidence for rho structural and operational judgments

The independent source relations remain `StructuralCongruence`, `NameEquiv`,
`Reduction.Reduces` and `ReducesStar`. This presentation supplies executable
finite proof objects for their complete raw `Pattern` scope. It does not turn
raw patterns into admitted rho terms: formation, ambient scope and declaration
admission remain separate checks.

Permutation carries explicit nil/cons/swap/trans evidence. Congruence carries
paired lists, preserving the occurrence of every argument without a hidden
permutation oracle. COMM computes the existing paper-faithful
`semanticCommSubst`; quotation, binders and contextual closure are inherited
from the independent source relations without a closed-quotation restriction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.TypeTheory

inductive Judgment where
  | structural (source target : Pattern)
  | name (source target : Pattern)
  | step (source target : Pattern)
  | steps (source target : Pattern)
  | permutation (source target : List Pattern)
  deriving DecidableEq, Repr

/-- Meaning is given by the existing independent relations. -/
def Meaning : Judgment → Prop
  | .structural p q => StructuralCongruence p q
  | .name p q => NameEquiv p q
  | .step p q => Nonempty (Reduction.Reduces p q)
  | .steps p q => Nonempty (ReducesStar p q)
  | .permutation ps qs => ps.Perm qs

inductive Rule where
  | structuralRefl (p : Pattern)
  | structuralSymm (p q : Pattern)
  | structuralTrans (p q r : Pattern)
  | parSingleton (p : Pattern)
  | parNilLeft (p : Pattern)
  | parNilRight (p : Pattern)
  | parComm (p q : Pattern)
  | parAssoc (p q r : Pattern)
  | parFlatten (ps qs : List Pattern)
  | parPerm (ps qs : List Pattern)
  | setPerm (ps qs : List Pattern)
  | applyCong (f : String) (pairs : List (Pattern × Pattern))
  | collectionCong (ct : CollType) (guard : Option String)
      (pairs : List (Pattern × Pattern))
  | lambdaCong (nm : Option String) (p q : Pattern)
  | multiLambdaCong (n : Nat) (nms : List String) (p q : Pattern)
  | substCong (p q a b : Pattern)
  | quoteDrop (n : Pattern)
  | parEmpty
  | nameRefl (n : Pattern)
  | nameQuoteDrop (n : Pattern)
  | nameStructural (p q : Pattern)
  | nameSymm (p q : Pattern)
  | nameTrans (p q r : Pattern)
  | comm (channel payload body : Pattern) (rest : List Pattern)
  | stepEquiv (p p' q' q : Pattern)
  | stepPar (p q : Pattern) (rest : List Pattern)
  | stepParAny (p q : Pattern) (before after : List Pattern)
  | stepsRefl (p : Pattern)
  | stepsCons (p q r : Pattern)
  | permNil
  | permCons (p : Pattern) (ps qs : List Pattern)
  | permSwap (p q : Pattern) (rest : List Pattern)
  | permTrans (ps qs rs : List Pattern)
  deriving Repr

def lefts (pairs : List (Pattern × Pattern)) : List Pattern := pairs.map Prod.fst
def rights (pairs : List (Pattern × Pattern)) : List Pattern := pairs.map Prod.snd

/-- Assemble the literal rule endpoints with an explicitly supplied COMM
contractum operation. The raw checker specializes this to semanticCommSubst;
explicit evidence checking supplies its already witnessed result. -/
def conclusionWithComm (contractum : Pattern → Pattern → Pattern) : Rule → Judgment
  | .structuralRefl p => .structural p p
  | .structuralSymm p q => .structural q p
  | .structuralTrans p _ r => .structural p r
  | .parSingleton p => .structural (.collection .hashBag [p] none) p
  | .parNilLeft p => .structural (.collection .hashBag [.apply "PZero" [], p] none) p
  | .parNilRight p => .structural (.collection .hashBag [p, .apply "PZero" []] none) p
  | .parComm p q => .structural
      (.collection .hashBag [p, q] none) (.collection .hashBag [q, p] none)
  | .parAssoc p q r => .structural
      (.collection .hashBag [.collection .hashBag [p, q] none, r] none)
      (.collection .hashBag [p, .collection .hashBag [q, r] none] none)
  | .parFlatten ps qs => .structural
      (.collection .hashBag (ps ++ [.collection .hashBag qs none]) none)
      (.collection .hashBag (ps ++ qs) none)
  | .parPerm ps qs => .structural
      (.collection .hashBag ps none) (.collection .hashBag qs none)
  | .setPerm ps qs => .structural
      (.collection .hashSet ps none) (.collection .hashSet qs none)
  | .applyCong f pairs => .structural (.apply f (lefts pairs)) (.apply f (rights pairs))
  | .collectionCong ct g pairs => .structural
      (.collection ct (lefts pairs) g) (.collection ct (rights pairs) g)
  | .lambdaCong nm p q => .structural (.lambda nm p) (.lambda nm q)
  | .multiLambdaCong n nms p q => .structural (.multiLambda n nms p) (.multiLambda n nms q)
  | .substCong p q a b => .structural (.subst p a) (.subst q b)
  | .quoteDrop n => .structural (.apply "NQuote" [.apply "PDrop" [n]]) n
  | .parEmpty => .structural (.collection .hashBag [] none) (.apply "PZero" [])
  | .nameRefl n => .name n n
  | .nameQuoteDrop n => .name (.apply "NQuote" [.apply "PDrop" [n]]) n
  | .nameStructural p q => .name (.apply "NQuote" [p]) (.apply "NQuote" [q])
  | .nameSymm p q => .name q p
  | .nameTrans p _ r => .name p r
  | .comm n q p rest => .step
      (.collection .hashBag ([.apply "POutput" [n, q],
        .apply "PInput" [n, .lambda none p]] ++ rest) none)
      (.collection .hashBag ([contractum p q] ++ rest) none)
  | .stepEquiv p _ _ q => .step p q
  | .stepPar p q rest => .step
      (.collection .hashBag (p :: rest) none) (.collection .hashBag (q :: rest) none)
  | .stepParAny p q before after => .step
      (.collection .hashBag (before ++ [p] ++ after) none)
      (.collection .hashBag (before ++ [q] ++ after) none)
  | .stepsRefl p => .steps p p
  | .stepsCons p _ r => .steps p r
  | .permNil => .permutation [] []
  | .permCons p ps qs => .permutation (p :: ps) (p :: qs)
  | .permSwap p q rest => .permutation (q :: p :: rest) (p :: q :: rest)
  | .permTrans ps _ rs => .permutation ps rs

def conclusion : Rule → Judgment := conclusionWithComm semanticCommSubst

def pairedPremises (pairs : List (Pattern × Pattern)) : List Judgment :=
  pairs.map (fun pair => .structural pair.1 pair.2)

def premises : Rule → List Judgment
  | .structuralSymm p q => [.structural p q]
  | .structuralTrans p q r => [.structural p q, .structural q r]
  | .parPerm ps qs | .setPerm ps qs => [.permutation ps qs]
  | .applyCong _ pairs | .collectionCong _ _ pairs => pairedPremises pairs
  | .lambdaCong _ p q | .multiLambdaCong _ _ p q => [.structural p q]
  | .substCong p q a b => [.structural p q, .structural a b]
  | .nameStructural p q => [.structural p q]
  | .nameSymm p q => [.name p q]
  | .nameTrans p q r => [.name p q, .name q r]
  | .stepEquiv p p' q' q => [.structural p p', .step p' q', .structural q' q]
  | .stepPar p q _ | .stepParAny p q _ _ => [.step p q]
  | .stepsCons p q r => [.step p q, .steps q r]
  | .permCons _ ps qs => [.permutation ps qs]
  | .permTrans ps qs rs => [.permutation ps qs, .permutation qs rs]
  | _ => []

def presentation : Presentation where
  Judgment := Judgment
  Rule := Rule
  conclusion := conclusion
  premises := premises

abbrev Proof := Tree presentation
abbrev Derivation (claim : Judgment) := presentation.Derivation claim

/-- Check all explicit rule payloads and every child occurrence. -/
def check (claim : Judgment) (proof : Proof) : Bool :=
  @Tree.check presentation (inferInstanceAs (DecidableEq Judgment)) proof claim

private theorem paired_sound (pairs : List (Pattern × Pattern))
    (children : ∀ claim ∈ pairedPremises pairs, Meaning claim) :
    ∀ i (h₁ : i < (lefts pairs).length) (h₂ : i < (rights pairs).length),
      StructuralCongruence ((lefts pairs).get ⟨i, h₁⟩) ((rights pairs).get ⟨i, h₂⟩) := by
  intro i h₁ h₂
  have bound : i < pairs.length := by simpa [lefts] using h₁
  have child := children (.structural (pairs.get ⟨i, bound⟩).1
    (pairs.get ⟨i, bound⟩).2) (by
      apply List.mem_map.mpr
      exact ⟨pairs.get ⟨i, bound⟩, List.get_mem _ _, rfl⟩)
  simpa [lefts, rights, Meaning] using child

theorem rule_sound (rule : Rule)
    (children : ∀ claim ∈ premises rule, Meaning claim) : Meaning (conclusion rule) := by
  have first {claim : Judgment} {rest : List Judgment}
      (same : premises rule = claim :: rest) : Meaning claim :=
    children claim (same ▸ List.mem_cons_self)
  cases rule with
  | structuralRefl p => exact .refl p
  | structuralSymm p q => exact .symm p q (first rfl)
  | structuralTrans p q r =>
      exact .trans p q r (children (.structural p q) (by simp [premises]))
        (children (.structural q r) (by simp [premises]))
  | parSingleton p => exact .par_singleton p
  | parNilLeft p => exact .par_nil_left p
  | parNilRight p => exact .par_nil_right p
  | parComm p q => exact .par_comm p q
  | parAssoc p q r => exact .par_assoc p q r
  | parFlatten ps qs => exact .par_flatten ps qs
  | parPerm ps qs => exact .par_perm ps qs (first rfl)
  | setPerm ps qs => exact .set_perm ps qs (first rfl)
  | applyCong f pairs =>
      exact .apply_cong f _ _ (by simp [lefts, rights]) (paired_sound pairs children)
  | collectionCong ct g pairs =>
      exact .collection_general_cong ct _ _ g (by simp [lefts, rights])
        (paired_sound pairs children)
  | lambdaCong nm p q => exact .lambda_cong nm p q (first rfl)
  | multiLambdaCong n nms p q => exact .multiLambda_cong n nms p q (first rfl)
  | substCong p q a b =>
      exact .subst_cong p q a b (children (.structural p q) (by simp [premises]))
        (children (.structural a b) (by simp [premises]))
  | quoteDrop n => exact .quote_drop n
  | parEmpty => exact .par_empty
  | nameRefl n => exact .refl n
  | nameQuoteDrop n => exact .quote_drop n
  | nameStructural p q => exact .struct_equiv p q (first rfl)
  | nameSymm p q => exact .symm p q (first rfl)
  | nameTrans p q r =>
      exact .trans p q r (children (.name p q) (by simp [premises]))
        (children (.name q r) (by simp [premises]))
  | comm n q p rest => exact ⟨.comm⟩
  | stepEquiv p p' q' q =>
      obtain ⟨reduction⟩ := children (.step p' q') (by simp [premises])
      exact ⟨.equiv (children (.structural p p') (by simp [premises])) reduction
        (children (.structural q' q) (by simp [premises]))⟩
  | stepPar p q rest =>
      obtain ⟨reduction⟩ := first rfl
      exact ⟨.par reduction⟩
  | stepParAny p q before after =>
      obtain ⟨reduction⟩ := first rfl
      exact ⟨.par_any reduction⟩
  | stepsRefl p => exact ⟨.refl p⟩
  | stepsCons p q r =>
      obtain ⟨reduction⟩ := children (.step p q) (by simp [premises])
      obtain ⟨tail⟩ := children (.steps q r) (by simp [premises])
      exact ⟨.step reduction tail⟩
  | permNil => exact .nil
  | permCons p ps qs => exact .cons p (first rfl)
  | permSwap p q rest => exact .swap p q rest
  | permTrans ps qs rs =>
      exact .trans (children (.permutation ps qs) (by simp [premises]))
        (children (.permutation qs rs) (by simp [premises]))

theorem derivation_sound {claim : Judgment} (derivation : Derivation claim) :
    Meaning claim := by
  apply JudgmentDerivation.Derivation.rec
    (motive := fun claim _ => Meaning claim) (t := derivation)
  intro claim rule children ih
  rcases rule with ⟨rule, same⟩
  cases same
  apply rule_sound rule
  intro child member
  obtain ⟨index, equal⟩ := List.get_of_mem member
  have result : Meaning ((premises rule).get index) := ih ⟨index⟩
  simpa only [equal] using result


private theorem derive (rule : Rule)
    (children : ∀ claim ∈ premises rule, Nonempty (Derivation claim)) :
    Nonempty (Derivation (conclusion rule)) := by
  classical
  exact ⟨.node ⟨rule, rfl⟩ (fun position =>
    Classical.choice (children _ (List.get_mem _ _)))⟩

private theorem pairList {ps qs : List Pattern} (lengths : ps.length = qs.length)
    (children : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      Nonempty (Derivation (.structural (ps.get ⟨i, h₁⟩) (qs.get ⟨i, h₂⟩)))) :
    ∃ pairs : List (Pattern × Pattern), lefts pairs = ps ∧ rights pairs = qs ∧
      ∀ claim ∈ pairedPremises pairs, Nonempty (Derivation claim) := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => exact ⟨[], rfl, rfl, by simp [pairedPremises]⟩
      | cons q qs => simp at lengths
  | cons p ps ih =>
      cases qs with
      | nil => simp at lengths
      | cons q qs =>
          have tailLengths : ps.length = qs.length := by simpa using lengths
          have tailChildren : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
              Nonempty (Derivation (.structural (ps.get ⟨i, h₁⟩) (qs.get ⟨i, h₂⟩))) := by
            intro i h₁ h₂
            simpa using children (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          obtain ⟨pairs, left, right, tail⟩ := ih tailLengths tailChildren
          refine ⟨(p, q) :: pairs, by simp [lefts, lefts] at left ⊢; exact left,
            by simp [rights, rights] at right ⊢; exact right, ?_⟩
          intro claim member
          simp only [pairedPremises, List.map_cons, List.mem_cons] at member
          rcases member with rfl | member
          · simpa using children 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          · exact tail claim member

theorem permutation_complete {ps qs : List Pattern} (source : ps.Perm qs) :
    Nonempty (Derivation (.permutation ps qs)) := by
  induction source with
  | nil => exact derive .permNil (by simp [premises])
  | cons p _ ih => exact derive (.permCons p _ _) (by simpa [premises] using ih)
  | swap p q rest => exact derive (.permSwap p q rest) (by simp [premises])
  | trans _ _ ih₁ ih₂ =>
      exact derive (.permTrans _ _ _) (by simpa [premises] using And.intro ih₁ ih₂)

theorem structural_complete {p q : Pattern} (source : StructuralCongruence p q) :
    Nonempty (Derivation (.structural p q)) := by
  induction source with
  | alpha p q same => cases same; exact derive (.structuralRefl p) (by simp [premises])
  | refl p => exact derive (.structuralRefl p) (by simp [premises])
  | symm p q _ ih => exact derive (.structuralSymm p q) (by simpa [premises] using ih)
  | trans p q r _ _ ih₁ ih₂ =>
      exact derive (.structuralTrans p q r) (by simpa [premises] using And.intro ih₁ ih₂)
  | par_singleton p => exact derive (.parSingleton p) (by simp [premises])
  | par_nil_left p => exact derive (.parNilLeft p) (by simp [premises])
  | par_nil_right p => exact derive (.parNilRight p) (by simp [premises])
  | par_comm p q => exact derive (.parComm p q) (by simp [premises])
  | par_assoc p q r => exact derive (.parAssoc p q r) (by simp [premises])
  | par_flatten ps qs => exact derive (.parFlatten ps qs) (by simp [premises])
  | par_perm ps qs permutation =>
      exact derive (.parPerm ps qs) (by simpa [premises] using permutation_complete permutation)
  | set_perm ps qs permutation =>
      exact derive (.setPerm ps qs) (by simpa [premises] using permutation_complete permutation)
  | par_cong ps qs lengths _ ih =>
      obtain ⟨pairs, left, right, children⟩ := pairList lengths ih
      simpa only [conclusion, conclusionWithComm, ← left, ← right] using derive (.collectionCong .hashBag none pairs) children
  | set_cong ps qs lengths _ ih =>
      obtain ⟨pairs, left, right, children⟩ := pairList lengths ih
      simpa only [conclusion, conclusionWithComm, ← left, ← right] using derive (.collectionCong .hashSet none pairs) children
  | apply_cong f ps qs lengths _ ih =>
      obtain ⟨pairs, left, right, children⟩ := pairList lengths ih
      simpa only [conclusion, conclusionWithComm, ← left, ← right] using derive (.applyCong f pairs) children
  | collection_general_cong ct ps qs g lengths _ ih =>
      obtain ⟨pairs, left, right, children⟩ := pairList lengths ih
      simpa only [conclusion, conclusionWithComm, ← left, ← right] using derive (.collectionCong ct g pairs) children
  | lambda_cong nm p q _ ih =>
      exact derive (.lambdaCong nm p q) (by simpa [premises] using ih)
  | multiLambda_cong n nms p q _ ih =>
      exact derive (.multiLambdaCong n nms p q) (by simpa [premises] using ih)
  | subst_cong p q a b _ _ ih₁ ih₂ =>
      exact derive (.substCong p q a b) (by simpa [premises] using And.intro ih₁ ih₂)
  | quote_drop n => exact derive (.quoteDrop n) (by simp [premises])
  | par_empty => exact derive .parEmpty (by simp [premises])


theorem name_complete {p q : Pattern} (source : NameEquiv p q) :
    Nonempty (Derivation (.name p q)) := by
  induction source with
  | quote_drop n => exact derive (.nameQuoteDrop n) (by simp [premises])
  | refl n => exact derive (.nameRefl n) (by simp [premises])
  | struct_equiv p q structural =>
      exact derive (.nameStructural p q) (by simpa [premises] using structural_complete structural)
  | symm p q _ ih => exact derive (.nameSymm p q) (by simpa [premises] using ih)
  | trans p q r _ _ ih₁ ih₂ =>
      exact derive (.nameTrans p q r) (by simpa [premises] using And.intro ih₁ ih₂)

theorem reduction_complete {p q : Pattern} (source : Reduction.Reduces p q) :
    Nonempty (Derivation (.step p q)) := by
  induction source with
  | @comm n payload body rest => exact derive (.comm n payload body rest) (by simp [premises])
  | @equiv p p' q q' before _ after ih =>
      apply derive (.stepEquiv p p' q' q)
      simpa [premises] using
        And.intro (structural_complete before) (And.intro ih (structural_complete after))
  | @par p q rest _ ih => exact derive (.stepPar p q rest) (by simpa [premises] using ih)
  | @par_any p q before after _ ih =>
      exact derive (.stepParAny p q before after) (by simpa [premises] using ih)

theorem reductions_complete {p q : Pattern} (source : ReducesStar p q) :
    Nonempty (Derivation (.steps p q)) := by
  induction source with
  | refl p => exact derive (.stepsRefl p) (by simp [premises])
  | @step p q r head _ ih =>
      exact derive (.stepsCons p q r)
        (by simpa [premises] using And.intro (reduction_complete head) ih)

/-- Every independent source derivation has finite native evidence. This
is not a decision procedure for existence of a source derivation. -/
theorem meaning_iff_derivation (claim : Judgment) :
    Meaning claim ↔ Nonempty (Derivation claim) := by
  constructor
  · cases claim with
    | structural p q => exact structural_complete
    | name p q => exact name_complete
    | step p q => rintro ⟨source⟩; exact reduction_complete source
    | steps p q => rintro ⟨source⟩; exact reductions_complete source
    | permutation ps qs => exact permutation_complete
  · rintro ⟨derivation⟩
    exact derivation_sound derivation

/-- Acceptance reconstructs a derivation whose erasure is exactly the input
proof object, retaining every rule and premise occurrence. -/
theorem check_exact (claim : Judgment) (proof : Proof) :
    check claim proof = true ↔
      ∃ derivation : Derivation claim, Tree.erase derivation = proof :=
  @Tree.check_exact presentation (inferInstanceAs (DecidableEq Judgment)) proof claim

theorem check_sound (claim : Judgment) (proof : Proof)
    (accepted : check claim proof = true) : Meaning claim := by
  obtain ⟨derivation, _⟩ := (check_exact claim proof).mp accepted
  exact derivation_sound derivation

/-- Source truth and existence of accepted evidence coincide for each of
structural congruence, name equivalence, one step and finite reachability. -/
theorem check_complete (claim : Judgment) :
    Meaning claim ↔ ∃ proof : Proof, check claim proof = true := by
  rw [meaning_iff_derivation]
  exact @Tree.check_complete presentation (inferInstanceAs (DecidableEq Judgment)) claim


abbrev Wire := Tree.Wire presentation

/-- Decode an untrusted list-shaped proof, including explicit arity checks. -/
def checkWire (claim : Judgment) (wire : Wire) : Bool :=
  @Tree.checkWire presentation (inferInstanceAs (DecidableEq Judgment)) wire claim

theorem checkWire_exact (claim : Judgment) (wire : Wire) :
    checkWire claim wire = true ↔
      ∃ derivation : Derivation claim, Tree.encodeDerivation derivation = wire :=
  @Tree.checkWire_exact presentation (inferInstanceAs (DecidableEq Judgment)) wire claim

theorem checkWire_sound (claim : Judgment) (wire : Wire)
    (accepted : checkWire claim wire = true) : Meaning claim := by
  obtain ⟨derivation, _⟩ := (checkWire_exact claim wire).mp accepted
  exact derivation_sound derivation

theorem checkWire_complete (claim : Judgment) :
    Meaning claim ↔ ∃ wire : Wire, checkWire claim wire = true := by
  rw [meaning_iff_derivation]
  exact @Tree.checkWire_complete presentation (inferInstanceAs (DecidableEq Judgment)) claim

open Mettapedia.GSLT.LanguageDef

/-- The service's target is the independent source relation, not a checker
acceptance predicate or a supplied semantic-correctness callback. -/
def target : SemanticEvidence.AdmissionObject where
  Carrier := Judgment
  Meaning := Meaning

/-- Instantiate the common native proof-kernel generator with the actual
rho rule family and the proved independent-source adequacy theorem. -/
def nativeProofService : SemanticService.Service target :=
  .nativeProof (SemanticEvidence.FiniteRuleKernel.guest presentation)
    (@SemanticEvidence.FiniteRuleKernel.kernel presentation
      (inferInstanceAs (DecidableEq Judgment)))
    (fun claim => (meaning_iff_derivation claim).trans
      (SemanticEvidence.FiniteRuleKernel.proofFibre_iff_derivation presentation claim).symm)

/-- The same meaning has a separately labelled untrusted-wire boundary. -/
def wireService : SemanticService.Service target :=
  .certificateBoundary Wire ⟨checkWire⟩
    { sound := checkWire_sound
      complete := fun claim meaningful => (checkWire_complete claim).mp meaningful }

theorem native_service_has_no_external_boundary :
    SemanticService.Service.hasExternalCertificateBoundary nativeProofService = false := rfl

theorem wire_service_has_external_boundary :
    SemanticService.Service.hasExternalCertificateBoundary wireService = true := rfl

/-- Construct a COMM proof directly from its actual source arguments. -/
def commProof (channel payload body : Pattern) (rest : List Pattern) : Proof :=
  .node (.comm channel payload body rest) Fin.elim0

/-- Native COMM computes the contractum; it does not consume a supplied
transition certificate or a supplied correctness callback. -/
def communicate (channel payload body : Pattern) (rest : List Pattern) : Pattern × Proof :=
  (.collection .hashBag (semanticCommSubst body payload :: rest) none,
    commProof channel payload body rest)

theorem communicate_checked (channel payload body : Pattern) (rest : List Pattern) :
    check (.step
      (.collection .hashBag ([.apply "POutput" [channel, payload],
        .apply "PInput" [channel, .lambda none body]] ++ rest) none)
      (communicate channel payload body rest).1)
      (communicate channel payload body rest).2 = true := by
  simp [check, communicate, commProof, Tree.check, presentation, conclusion, conclusionWithComm, premises]

def communicate_source (channel payload body : Pattern) (rest : List Pattern) :
    Reduction.Reduces
      (.collection .hashBag ([.apply "POutput" [channel, payload],
        .apply "PInput" [channel, .lambda none body]] ++ rest) none)
      (communicate channel payload body rest).1 :=
  .comm


/-! ## Structural storage of all original rule-instance fields -/

namespace Storage

open Mettapedia.OSLF.Binding.WireCodec

private def pattern : Codec Pattern :=
  Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec

private def patterns : Codec (List Pattern) := Codec.list pattern
private def patternPairs : Codec (List (Pattern × Pattern)) := Codec.list (Codec.prod pattern pattern)
private def strings : Codec (List String) := Codec.list Codec.string

private def optionalString : Codec (Option String) where
  put | none => .atom 0 | some text => .pair (.atom 1) (Codec.string.put text)
  get | .atom 0 => some none | .pair (.atom 1) text => (Codec.string.get text).map some | _ => none
  get_put value := by cases value <;> simp only [Codec.get_put, Option.map_some]

private def collection : Codec CollType := Codec.nat.mapped
  (fun kind => match kind with | .vec => 0 | .hashBag => 1 | .hashSet => 2)
  (fun code => match code with | 0 => some .vec | 1 => some .hashBag | 2 => some .hashSet | _ => none)
  (by intro kind; cases kind <;> rfl)

private inductive Kind where
  | structuralRefl
  | structuralSymm
  | structuralTrans
  | parSingleton
  | parNilLeft
  | parNilRight
  | parComm
  | parAssoc
  | parFlatten
  | parPerm
  | setPerm
  | applyCong
  | collectionCong
  | lambdaCong
  | multiLambdaCong
  | substCong
  | quoteDrop
  | parEmpty
  | nameRefl
  | nameQuoteDrop
  | nameStructural
  | nameSymm
  | nameTrans
  | comm
  | stepEquiv
  | stepPar
  | stepParAny
  | stepsRefl
  | stepsCons
  | permNil
  | permCons
  | permSwap
  | permTrans

private def kindNumber : Kind → Nat
  | .structuralRefl => 0
  | .structuralSymm => 1
  | .structuralTrans => 2
  | .parSingleton => 3
  | .parNilLeft => 4
  | .parNilRight => 5
  | .parComm => 6
  | .parAssoc => 7
  | .parFlatten => 8
  | .parPerm => 9
  | .setPerm => 10
  | .applyCong => 11
  | .collectionCong => 12
  | .lambdaCong => 13
  | .multiLambdaCong => 14
  | .substCong => 15
  | .quoteDrop => 16
  | .parEmpty => 17
  | .nameRefl => 18
  | .nameQuoteDrop => 19
  | .nameStructural => 20
  | .nameSymm => 21
  | .nameTrans => 22
  | .comm => 23
  | .stepEquiv => 24
  | .stepPar => 25
  | .stepParAny => 26
  | .stepsRefl => 27
  | .stepsCons => 28
  | .permNil => 29
  | .permCons => 30
  | .permSwap => 31
  | .permTrans => 32

private def getKind : Nat → Option Kind
  | 0 => some .structuralRefl
  | 1 => some .structuralSymm
  | 2 => some .structuralTrans
  | 3 => some .parSingleton
  | 4 => some .parNilLeft
  | 5 => some .parNilRight
  | 6 => some .parComm
  | 7 => some .parAssoc
  | 8 => some .parFlatten
  | 9 => some .parPerm
  | 10 => some .setPerm
  | 11 => some .applyCong
  | 12 => some .collectionCong
  | 13 => some .lambdaCong
  | 14 => some .multiLambdaCong
  | 15 => some .substCong
  | 16 => some .quoteDrop
  | 17 => some .parEmpty
  | 18 => some .nameRefl
  | 19 => some .nameQuoteDrop
  | 20 => some .nameStructural
  | 21 => some .nameSymm
  | 22 => some .nameTrans
  | 23 => some .comm
  | 24 => some .stepEquiv
  | 25 => some .stepPar
  | 26 => some .stepParAny
  | 27 => some .stepsRefl
  | 28 => some .stepsCons
  | 29 => some .permNil
  | 30 => some .permCons
  | 31 => some .permSwap
  | 32 => some .permTrans
  | _ => none

private def kind : Codec Kind := Codec.nat.mapped kindNumber getKind
  (by intro tag; cases tag <;> rfl)

private def unit : Codec Unit where
  put _ := .atom 0
  get | .atom 0 => some () | _ => none
  get_put _ := rfl

private def Fields : Kind → Type
  | .structuralRefl => (Pattern × Unit)
  | .structuralSymm => (Pattern × (Pattern × Unit))
  | .structuralTrans => (Pattern × (Pattern × (Pattern × Unit)))
  | .parSingleton => (Pattern × Unit)
  | .parNilLeft => (Pattern × Unit)
  | .parNilRight => (Pattern × Unit)
  | .parComm => (Pattern × (Pattern × Unit))
  | .parAssoc => (Pattern × (Pattern × (Pattern × Unit)))
  | .parFlatten => (List Pattern × (List Pattern × Unit))
  | .parPerm => (List Pattern × (List Pattern × Unit))
  | .setPerm => (List Pattern × (List Pattern × Unit))
  | .applyCong => (String × (List (Pattern × Pattern) × Unit))
  | .collectionCong => (CollType × (Option String × (List (Pattern × Pattern) × Unit)))
  | .lambdaCong => (Option String × (Pattern × (Pattern × Unit)))
  | .multiLambdaCong => (Nat × (List String × (Pattern × (Pattern × Unit))))
  | .substCong => (Pattern × (Pattern × (Pattern × (Pattern × Unit))))
  | .quoteDrop => (Pattern × Unit)
  | .parEmpty => Unit
  | .nameRefl => (Pattern × Unit)
  | .nameQuoteDrop => (Pattern × Unit)
  | .nameStructural => (Pattern × (Pattern × Unit))
  | .nameSymm => (Pattern × (Pattern × Unit))
  | .nameTrans => (Pattern × (Pattern × (Pattern × Unit)))
  | .comm => (Pattern × (Pattern × (Pattern × (List Pattern × Unit))))
  | .stepEquiv => (Pattern × (Pattern × (Pattern × (Pattern × Unit))))
  | .stepPar => (Pattern × (Pattern × (List Pattern × Unit)))
  | .stepParAny => (Pattern × (Pattern × (List Pattern × (List Pattern × Unit))))
  | .stepsRefl => (Pattern × Unit)
  | .stepsCons => (Pattern × (Pattern × (Pattern × Unit)))
  | .permNil => Unit
  | .permCons => (Pattern × (List Pattern × (List Pattern × Unit)))
  | .permSwap => (Pattern × (Pattern × (List Pattern × Unit)))
  | .permTrans => (List Pattern × (List Pattern × (List Pattern × Unit)))

private def fields : (tag : Kind) → Codec (Fields tag)
  | .structuralRefl => (Codec.prod pattern unit)
  | .structuralSymm => (Codec.prod pattern (Codec.prod pattern unit))
  | .structuralTrans => (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern unit)))
  | .parSingleton => (Codec.prod pattern unit)
  | .parNilLeft => (Codec.prod pattern unit)
  | .parNilRight => (Codec.prod pattern unit)
  | .parComm => (Codec.prod pattern (Codec.prod pattern unit))
  | .parAssoc => (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern unit)))
  | .parFlatten => (Codec.prod patterns (Codec.prod patterns unit))
  | .parPerm => (Codec.prod patterns (Codec.prod patterns unit))
  | .setPerm => (Codec.prod patterns (Codec.prod patterns unit))
  | .applyCong => (Codec.prod Codec.string (Codec.prod patternPairs unit))
  | .collectionCong => (Codec.prod collection (Codec.prod optionalString (Codec.prod patternPairs unit)))
  | .lambdaCong => (Codec.prod optionalString (Codec.prod pattern (Codec.prod pattern unit)))
  | .multiLambdaCong => (Codec.prod Codec.nat (Codec.prod strings (Codec.prod pattern (Codec.prod pattern unit))))
  | .substCong => (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern unit))))
  | .quoteDrop => (Codec.prod pattern unit)
  | .parEmpty => unit
  | .nameRefl => (Codec.prod pattern unit)
  | .nameQuoteDrop => (Codec.prod pattern unit)
  | .nameStructural => (Codec.prod pattern (Codec.prod pattern unit))
  | .nameSymm => (Codec.prod pattern (Codec.prod pattern unit))
  | .nameTrans => (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern unit)))
  | .comm => (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern (Codec.prod patterns unit))))
  | .stepEquiv => (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern unit))))
  | .stepPar => (Codec.prod pattern (Codec.prod pattern (Codec.prod patterns unit)))
  | .stepParAny => (Codec.prod pattern (Codec.prod pattern (Codec.prod patterns (Codec.prod patterns unit))))
  | .stepsRefl => (Codec.prod pattern unit)
  | .stepsCons => (Codec.prod pattern (Codec.prod pattern (Codec.prod pattern unit)))
  | .permNil => unit
  | .permCons => (Codec.prod pattern (Codec.prod patterns (Codec.prod patterns unit)))
  | .permSwap => (Codec.prod pattern (Codec.prod pattern (Codec.prod patterns unit)))
  | .permTrans => (Codec.prod patterns (Codec.prod patterns (Codec.prod patterns unit)))

private def pack : Rule → (Σ tag : Kind, Fields tag)
  | .structuralRefl p => ⟨.structuralRefl, (p, ())⟩
  | .structuralSymm p q => ⟨.structuralSymm, (p, (q, ()))⟩
  | .structuralTrans p q r => ⟨.structuralTrans, (p, (q, (r, ())))⟩
  | .parSingleton p => ⟨.parSingleton, (p, ())⟩
  | .parNilLeft p => ⟨.parNilLeft, (p, ())⟩
  | .parNilRight p => ⟨.parNilRight, (p, ())⟩
  | .parComm p q => ⟨.parComm, (p, (q, ()))⟩
  | .parAssoc p q r => ⟨.parAssoc, (p, (q, (r, ())))⟩
  | .parFlatten ps qs => ⟨.parFlatten, (ps, (qs, ()))⟩
  | .parPerm ps qs => ⟨.parPerm, (ps, (qs, ()))⟩
  | .setPerm ps qs => ⟨.setPerm, (ps, (qs, ()))⟩
  | .applyCong label pairs => ⟨.applyCong, (label, (pairs, ()))⟩
  | .collectionCong kind rest pairs => ⟨.collectionCong, (kind, (rest, (pairs, ())))⟩
  | .lambdaCong name p q => ⟨.lambdaCong, (name, (p, (q, ())))⟩
  | .multiLambdaCong arity names p q => ⟨.multiLambdaCong, (arity, (names, (p, (q, ()))))⟩
  | .substCong p q a b => ⟨.substCong, (p, (q, (a, (b, ()))))⟩
  | .quoteDrop n => ⟨.quoteDrop, (n, ())⟩
  | .parEmpty => ⟨.parEmpty, ()⟩
  | .nameRefl n => ⟨.nameRefl, (n, ())⟩
  | .nameQuoteDrop n => ⟨.nameQuoteDrop, (n, ())⟩
  | .nameStructural p q => ⟨.nameStructural, (p, (q, ()))⟩
  | .nameSymm p q => ⟨.nameSymm, (p, (q, ()))⟩
  | .nameTrans p q r => ⟨.nameTrans, (p, (q, (r, ())))⟩
  | .comm channel payload body rest => ⟨.comm, (channel, (payload, (body, (rest, ()))))⟩
  | .stepEquiv p previous next q => ⟨.stepEquiv, (p, (previous, (next, (q, ()))))⟩
  | .stepPar p q rest => ⟨.stepPar, (p, (q, (rest, ())))⟩
  | .stepParAny p q before after => ⟨.stepParAny, (p, (q, (before, (after, ()))))⟩
  | .stepsRefl p => ⟨.stepsRefl, (p, ())⟩
  | .stepsCons p q r => ⟨.stepsCons, (p, (q, (r, ())))⟩
  | .permNil => ⟨.permNil, ()⟩
  | .permCons p ps qs => ⟨.permCons, (p, (ps, (qs, ())))⟩
  | .permSwap p q rest => ⟨.permSwap, (p, (q, (rest, ())))⟩
  | .permTrans ps qs rs => ⟨.permTrans, (ps, (qs, (rs, ())))⟩

private def unpack : (Σ tag : Kind, Fields tag) → Rule
  | ⟨.structuralRefl, (p, ())⟩ => .structuralRefl p
  | ⟨.structuralSymm, (p, (q, ()))⟩ => .structuralSymm p q
  | ⟨.structuralTrans, (p, (q, (r, ())))⟩ => .structuralTrans p q r
  | ⟨.parSingleton, (p, ())⟩ => .parSingleton p
  | ⟨.parNilLeft, (p, ())⟩ => .parNilLeft p
  | ⟨.parNilRight, (p, ())⟩ => .parNilRight p
  | ⟨.parComm, (p, (q, ()))⟩ => .parComm p q
  | ⟨.parAssoc, (p, (q, (r, ())))⟩ => .parAssoc p q r
  | ⟨.parFlatten, (ps, (qs, ()))⟩ => .parFlatten ps qs
  | ⟨.parPerm, (ps, (qs, ()))⟩ => .parPerm ps qs
  | ⟨.setPerm, (ps, (qs, ()))⟩ => .setPerm ps qs
  | ⟨.applyCong, (label, (pairs, ()))⟩ => .applyCong label pairs
  | ⟨.collectionCong, (kind, (rest, (pairs, ())))⟩ => .collectionCong kind rest pairs
  | ⟨.lambdaCong, (name, (p, (q, ())))⟩ => .lambdaCong name p q
  | ⟨.multiLambdaCong, (arity, (names, (p, (q, ()))))⟩ => .multiLambdaCong arity names p q
  | ⟨.substCong, (p, (q, (a, (b, ()))))⟩ => .substCong p q a b
  | ⟨.quoteDrop, (n, ())⟩ => .quoteDrop n
  | ⟨.parEmpty, ()⟩ => .parEmpty
  | ⟨.nameRefl, (n, ())⟩ => .nameRefl n
  | ⟨.nameQuoteDrop, (n, ())⟩ => .nameQuoteDrop n
  | ⟨.nameStructural, (p, (q, ()))⟩ => .nameStructural p q
  | ⟨.nameSymm, (p, (q, ()))⟩ => .nameSymm p q
  | ⟨.nameTrans, (p, (q, (r, ())))⟩ => .nameTrans p q r
  | ⟨.comm, (channel, (payload, (body, (rest, ()))))⟩ => .comm channel payload body rest
  | ⟨.stepEquiv, (p, (previous, (next, (q, ()))))⟩ => .stepEquiv p previous next q
  | ⟨.stepPar, (p, (q, (rest, ())))⟩ => .stepPar p q rest
  | ⟨.stepParAny, (p, (q, (before, (after, ()))))⟩ => .stepParAny p q before after
  | ⟨.stepsRefl, (p, ())⟩ => .stepsRefl p
  | ⟨.stepsCons, (p, (q, (r, ())))⟩ => .stepsCons p q r
  | ⟨.permNil, ()⟩ => .permNil
  | ⟨.permCons, (p, (ps, (qs, ())))⟩ => .permCons p ps qs
  | ⟨.permSwap, (p, (q, (rest, ())))⟩ => .permSwap p q rest
  | ⟨.permTrans, (ps, (qs, (rs, ())))⟩ => .permTrans ps qs rs

private theorem unpack_pack (code : Rule) : unpack (pack code) = code := by
  cases code <;> rfl

/-- A finite tagged telescope of actual source fields. Each field uses its
existing structural codec, and the final unit rejects extra fields. -/
def rule : Codec Rule := (Codec.sigma kind fields).mapped pack (some ∘ unpack)
  (fun code => congrArg some (unpack_pack code))

def putRule (code : Rule) : Data := rule.put code
def getRule (raw : Data) : Option Rule := rule.get raw

theorem get_putRule (code : Rule) : getRule (putRule code) = some code := rule.get_put code

/-- Reuse the common list-tree serialization and the source-exact checker. -/
def proof : Codec Wire := Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.wireCodec rule

def encode (wire : Wire) : Data := proof.put wire

def check (claim : Judgment) (raw : Data) : Bool :=
  match proof.canonicalGet raw with
  | none => false
  | some wire => checkWire claim wire

theorem check_exact (claim : Judgment) (raw : Data) :
    check claim raw = true ↔
      ∃ derivation : presentation.Derivation claim,
        encode (Tree.encodeDerivation derivation) = raw := by
  cases decoded : proof.canonicalGet raw with
  | none =>
      constructor
      · intro accepted
        simp only [check, decoded, Bool.false_eq_true] at accepted
      · rintro ⟨derivation, exactInput⟩
        have recovered := proof.canonicalGet_put (Tree.encodeDerivation derivation)
        change proof.canonicalGet (encode (Tree.encodeDerivation derivation)) = _ at recovered
        rw [exactInput, decoded] at recovered
        cases recovered
  | some wire =>
      simp only [check, decoded]
      constructor
      · intro accepted
        have valid : checkWire claim wire = true := accepted
        obtain ⟨derivation, sameWire⟩ := (checkWire_exact claim wire).mp valid
        refine ⟨derivation, ?_⟩
        rw [sameWire]
        exact proof.put_of_canonicalGet raw wire decoded
      · rintro ⟨derivation, exactInput⟩
        have recovered := proof.canonicalGet_put (Tree.encodeDerivation derivation)
        change proof.canonicalGet (encode (Tree.encodeDerivation derivation)) = _ at recovered
        rw [exactInput, decoded] at recovered
        have sameWire := Option.some.inj recovered
        change checkWire claim wire = true
        rw [sameWire]
        exact (checkWire_exact claim _).mpr ⟨derivation, rfl⟩

theorem check_sound (claim : Judgment) (raw : Data)
    (accepted : check claim raw = true) : Meaning claim := by
  obtain ⟨derivation, _⟩ := (check_exact claim raw).mp accepted
  exact (meaning_iff_derivation claim).mpr ⟨derivation⟩

theorem check_complete (claim : Judgment) :
    Meaning claim ↔ ∃ raw : Data, check claim raw = true := by
  constructor
  · intro meaningful
    obtain ⟨derivation⟩ := (meaning_iff_derivation claim).mp meaningful
    exact ⟨encode (Tree.encodeDerivation derivation), (check_exact claim _).mpr ⟨derivation, rfl⟩⟩
  · rintro ⟨raw, accepted⟩
    exact check_sound claim raw accepted


/-- Retain the goal's constructor and both full endpoint payloads. -/
private def judgmentFields : Judgment → Nat × (List Pattern × List Pattern)
  | .structural left right => (0, ([left], [right]))
  | .name left right => (1, ([left], [right]))
  | .step left right => (2, ([left], [right]))
  | .steps left right => (3, ([left], [right]))
  | .permutation left right => (4, (left, right))

private def fromJudgmentFields : Nat × (List Pattern × List Pattern) → Option Judgment
  | (0, ([left], [right])) => some (.structural left right)
  | (1, ([left], [right])) => some (.name left right)
  | (2, ([left], [right])) => some (.step left right)
  | (3, ([left], [right])) => some (.steps left right)
  | (4, (left, right)) => some (.permutation left right)
  | _ => none

def judgment : Codec Judgment :=
  (Codec.prod Codec.nat (Codec.prod patterns patterns)).mapped
    judgmentFields fromJudgmentFields (by intro claim; cases claim <;> rfl)

open Mettapedia.OSLF.Binding.WireCodec.Binary

def encodeBinary (wire : Wire) : List Alphabet := encodeWith proof wire

/-- Whole-word checking retains the exact canonical input, including every
field and child occurrence. It rejects ignored suffixes and encoding aliases. -/
def checkBinary (claim : Judgment) (word : List Alphabet) : Bool :=
  match decodeWith proof word with
  | none => false
  | some wire => decide (encodeBinary wire = word) && checkWire claim wire

theorem checkBinary_exact (claim : Judgment) (word : List Alphabet) :
    checkBinary claim word = true ↔
      ∃ derivation : presentation.Derivation claim,
        encodeBinary (Tree.encodeDerivation derivation) = word := by
  cases decoded : decodeWith proof word with
  | none =>
      constructor
      · intro accepted; simp only [checkBinary, decoded, Bool.false_eq_true] at accepted
      · rintro ⟨derivation, exactWord⟩
        have recovered := decodeWith_encodeWith proof (Tree.encodeDerivation derivation)
        change decodeWith proof (encodeBinary (Tree.encodeDerivation derivation)) = _ at recovered
        rw [exactWord, decoded] at recovered
        cases recovered
  | some wire =>
      simp only [checkBinary, decoded, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨exactWord, accepted⟩
        obtain ⟨derivation, sameWire⟩ := (checkWire_exact claim wire).mp accepted
        exact ⟨derivation, sameWire ▸ exactWord⟩
      · rintro ⟨derivation, exactWord⟩
        have recovered := decodeWith_encodeWith proof (Tree.encodeDerivation derivation)
        change decodeWith proof (encodeBinary (Tree.encodeDerivation derivation)) = _ at recovered
        rw [exactWord, decoded] at recovered
        have sameWire := Option.some.inj recovered
        rw [sameWire]
        exact ⟨exactWord, (checkWire_exact claim _).mpr ⟨derivation, rfl⟩⟩

theorem checkBinary_sound (claim : Judgment) (word : List Alphabet)
    (accepted : checkBinary claim word = true) : Meaning claim := by
  obtain ⟨derivation, _⟩ := (checkBinary_exact claim word).mp accepted
  exact (meaning_iff_derivation claim).mpr ⟨derivation⟩

theorem trailing_refused (claim : Judgment) (wire : Wire) (tail : List Alphabet)
    (nonempty : tail.isEmpty = false) :
    checkBinary claim (encodeBinary wire ++ tail) = false := by
  simp only [checkBinary, encodeBinary, decodeWith_trailing_refused proof wire tail nonempty]

/-- The artifact transports the requested judgment together with its evidence;
the checker never replaces the requested goal by the proof's own conclusion. -/
def request : Codec (Judgment × Wire) := Codec.prod judgment proof

def encodeRequest (claim : Judgment) (wire : Wire) : List Alphabet :=
  encodeWith request (claim, wire)

def checkRequest (word : List Alphabet) : Option Judgment := do
  let (claim, wire) ← decodeWith request word
  if encodeRequest claim wire = word ∧ checkWire claim wire = true then some claim else none

theorem checkRequest_exact (claim : Judgment) (word : List Alphabet) :
    checkRequest word = some claim ↔
      ∃ derivation : presentation.Derivation claim,
        encodeRequest claim (Tree.encodeDerivation derivation) = word := by
  cases decoded : decodeWith request word with
  | none =>
      constructor
      · intro accepted; simp only [checkRequest, decoded, Bind.bind, Option.bind] at accepted; cases accepted
      · rintro ⟨derivation, exactWord⟩
        have recovered := decodeWith_encodeWith request (claim, Tree.encodeDerivation derivation)
        change decodeWith request (encodeRequest claim (Tree.encodeDerivation derivation)) = _ at recovered
        rw [exactWord, decoded] at recovered
        cases recovered
  | some packet =>
      rcases packet with ⟨found, wire⟩
      by_cases valid : encodeRequest found wire = word ∧ checkWire found wire = true
      · simp only [checkRequest, decoded, Bind.bind, Option.bind, if_pos valid, Option.some.injEq]
        constructor
        · intro sameClaim
          cases sameClaim
          obtain ⟨derivation, sameWire⟩ := (checkWire_exact claim wire).mp valid.2
          exact ⟨derivation, sameWire ▸ valid.1⟩
        · rintro ⟨derivation, exactWord⟩
          have recovered := decodeWith_encodeWith request (claim, Tree.encodeDerivation derivation)
          change decodeWith request (encodeRequest claim (Tree.encodeDerivation derivation)) = _ at recovered
          rw [exactWord, decoded] at recovered
          exact congrArg Prod.fst (Option.some.inj recovered)
      · simp only [checkRequest, decoded, Bind.bind, Option.bind, if_neg valid]
        constructor
        · intro impossible; cases impossible
        · rintro ⟨derivation, exactWord⟩
          exfalso
          apply valid
          have recovered := decodeWith_encodeWith request (claim, Tree.encodeDerivation derivation)
          change decodeWith request (encodeRequest claim (Tree.encodeDerivation derivation)) = _ at recovered
          rw [exactWord, decoded] at recovered
          have same := Option.some.inj recovered
          cases same
          exact ⟨exactWord, (checkWire_exact claim _).mpr ⟨derivation, rfl⟩⟩

theorem checkRequest_sound (word : List Alphabet) (claim : Judgment)
    (accepted : checkRequest word = some claim) : Meaning claim := by
  obtain ⟨derivation, _⟩ := (checkRequest_exact claim word).mp accepted
  exact (meaning_iff_derivation claim).mpr ⟨derivation⟩

theorem checkRequest_complete (claim : Judgment) :
    Meaning claim ↔ ∃ word, checkRequest word = some claim := by
  constructor
  · intro meaningful
    obtain ⟨derivation⟩ := (meaning_iff_derivation claim).mp meaningful
    exact ⟨encodeRequest claim (Tree.encodeDerivation derivation),
      (checkRequest_exact claim _).mpr ⟨derivation, rfl⟩⟩
  · rintro ⟨word, accepted⟩
    exact checkRequest_sound word claim accepted

end Storage

namespace Controls

abbrev zero : Pattern := .apply "PZero" []
abbrev channel : Pattern := .apply "NQuote" [zero]
abbrev left : Pattern := .fvar "left"
abbrev right : Pattern := .fvar "right"

def singleton (p : Pattern) : Proof := .node (.parSingleton p) Fin.elim0

def binder : Proof :=
  .node (.lambdaCong none (.collection .hashBag [.bvar 0] none) (.bvar 0))
    (fun _ => singleton (.bvar 0))

def multiBinder : Proof :=
  .node (.multiLambdaCong 2 ["x", "y"]
    (.collection .hashBag [.bvar 1] none) (.bvar 1))
    (fun _ => singleton (.bvar 1))

def quote : Proof :=
  .node (.applyCong "NQuote" [(.collection .hashBag [.bvar 0] none, .bvar 0)])
    (fun _ => singleton (.bvar 0))

def explicitSubstitution : Proof :=
  .node (.substCong (.collection .hashBag [.bvar 0] none) (.bvar 0) channel channel)
    (fun position => if position.val = 0 then singleton (.bvar 0)
      else .node (.structuralRefl channel) Fin.elim0)

def swapped : Proof := .node (.permSwap left right []) Fin.elim0

def parallelPermutation : Proof :=
  .node (.parPerm [right, left] [left, right]) (fun _ => swapped)

def wrongPermutation : Proof :=
  .node (.parPerm [right, left] [left, left]) (fun _ => swapped)

def wrongBinderChild : Proof :=
  .node (.lambdaCong none (.collection .hashBag [.bvar 0] none) (.bvar 0))
    (fun _ => singleton (.bvar 1))

def repeatedPremises : Proof :=
  .node (.applyCong "Pair"
    [(.collection .hashBag [left] none, left),
     (.collection .hashBag [left] none, left)])
    (fun _ => singleton left)

/-- Every repeated premise remains a distinct finite position. -/
theorem repeated_premise_count :
    (premises (.applyCong "Pair"
      [(.collection .hashBag [left] none, left),
       (.collection .hashBag [left] none, left)])).length = 2 := by decide

theorem binder_checked :
    check (.structural (.lambda none (.collection .hashBag [.bvar 0] none))
      (.lambda none (.bvar 0))) binder = true := by decide

theorem multiBinder_checked :
    check (.structural (.multiLambda 2 ["x", "y"] (.collection .hashBag [.bvar 1] none))
      (.multiLambda 2 ["x", "y"] (.bvar 1))) multiBinder = true := by decide

/-- Evidence covers quoted open patterns; no quotation-sealing assumption
is inserted into the independent raw structural judgment. -/
theorem open_quote_checked :
    check (.structural (.apply "NQuote" [.collection .hashBag [.bvar 0] none])
      (.apply "NQuote" [.bvar 0])) quote = true := by decide

theorem explicitSubstitution_checked :
    check (.structural (.subst (.collection .hashBag [.bvar 0] none) channel)
      (.subst (.bvar 0) channel)) explicitSubstitution = true := by decide

theorem permutation_checked :
    check (.structural (.collection .hashBag [right, left] none)
      (.collection .hashBag [left, right] none)) parallelPermutation = true := by decide

theorem forged_permutation_refused :
    check (.structural (.collection .hashBag [right, left] none)
      (.collection .hashBag [left, left] none)) wrongPermutation = false := by decide

theorem wrong_binder_child_refused :
    check (.structural (.lambda none (.collection .hashBag [.bvar 0] none))
      (.lambda none (.bvar 0))) wrongBinderChild = false := by decide

theorem changed_binder_metadata_refused :
    check (.structural (.lambda (some "x") (.collection .hashBag [.bvar 0] none))
      (.lambda (some "x") (.bvar 0))) binder = false := by decide

theorem wrong_quote_endpoint_refused :
    check (.structural (.apply "NQuote" [.collection .hashBag [.bvar 0] none])
      (.apply "NQuote" [.bvar 1])) quote = false := by decide

theorem native_communication_checked :
    check (.step
      (.collection .hashBag [.apply "POutput" [channel, zero],
        .apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 0])]] none)
      (.collection .hashBag [zero] none))
      (commProof channel zero (.apply "PDrop" [.bvar 0]) []) = true := by decide

theorem mismatched_channel_refused :
    check (.step
      (.collection .hashBag [.apply "POutput" [channel, zero],
        .apply "PInput" [left, .lambda none (.apply "PDrop" [.bvar 0])]] none)
      (.collection .hashBag [zero] none))
      (commProof channel zero (.apply "PDrop" [.bvar 0]) []) = false := by decide

theorem wrong_contractum_refused :
    check (.step
      (.collection .hashBag [.apply "POutput" [channel, zero],
        .apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 0])]] none)
      (.collection .hashBag [left] none))
      (commProof channel zero (.apply "PDrop" [.bvar 0]) []) = false := by decide


/-- Raw-wire shape checks reject a missing structural premise. -/
theorem missing_wire_child_refused :
    checkWire (.name (.apply "NQuote" [left]) (.apply "NQuote" [right]))
      (.node (.nameStructural left right) []) = false := by decide +kernel

/-- Extra occurrences cannot hide underneath an otherwise valid leaf. -/
theorem extra_wire_child_refused :
    checkWire (.structural left left)
      (.node (.structuralRefl left) [.node (.structuralRefl left) []]) = false := by decide +kernel

/-- A correct child count does not authorize an unrelated child judgment. -/
theorem mismatched_wire_child_refused :
    checkWire (.name (.apply "NQuote" [left]) (.apply "NQuote" [right]))
      (.node (.nameStructural left right) [.node (.structuralRefl left) []]) = false := by decide +kernel

theorem comm_wire_checked :
    checkWire (.step
      (.collection .hashBag [.apply "POutput" [channel, zero],
        .apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 0])]] none)
      (.collection .hashBag [zero] none))
      (.node (.comm channel zero (.apply "PDrop" [.bvar 0]) []) []) = true := by decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeEvidence
