import Mettapedia.Languages.HOLLight.QuantifierExpansion

/-!
# Executed serialization of original HOL universal instantiation

One fixed admitted predicate and incoming theorem compile to a finite indexed
word program. Its three dynamic fields are the complete raw operand, the
original named operand and the origin. The output is exactly the existing
checked SPEC block: eighteen primitive occurrences, their ordered references,
all intermediate claims, and complete hypothesis and axiom dependencies.

The linear execution bound measures the supplied field bytes. Computing those
fields and compiling a changing predicate to finite control are separate
obligations of the complete translator. This typed field-image result does not
claim admission of arbitrary packets, a whole-driver clock, or a uniform bound
on compilation of the fixed theorem and predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.QuantifierEmission
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open GraphExpansion EqualityExpansion PrimitiveTransport QuantifierExpansion
open EqualityExpansion.Emission
open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory.SyntaxEncoding ProofDataEncoding
open Mettapedia.Logic.DerivationGraph
open Turing Polynomial
open ProofExecution (Origin)
open PrimitiveSentences (truthDB identityBool)

abbrev Plan := Indexed.Template Alphabet 3
abbrev PlanNode := Node Plan Plan Plan

/-- The two original BETA/INST occurrences as independently instantiated node fields. -/
def betaNodes (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checked : body.inferType [domain] = some codomain) : List PlanNode :=
  let seed := betaSeed domain body codomain checked
  let raw : Plan := [.inr 0]
  let named : Plan := [.inr 1]
  let origin : Plan := [.inr 2]
  let redex := Templates.application (Templates.literal (putTerm (.abs domain body))) raw
  let reduced := Templates.single 0 (TemplateInstantiationMachine.compile 0 body)
  let conclusion := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality codomain redex reduced))
  let argumentSource := Templates.pair named (Templates.literal (putTy domain))
  let entries := Templates.pair
    (Templates.pair argumentSource
      (Templates.literal (putSourceTerm (.var (betaNeedle domain body).name domain))))
    (Templates.literal (.atom 0))
  let inst := unaryRequest 9 (Templates.pair entries (Templates.literal (theoremCodec.put seed.intermediate)))
  [⟨Templates.literal (theoremCodec.put seed.intermediate),
      Templates.literal (requestCodec.put (.inference (.beta seed.source))), [], origin⟩,
   ⟨conclusion, inst, [0], origin⟩]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem betaNodes_exact (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checked : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) (origin : Origin) :
    (betaNodes domain body codomain checked).map
      (Node.map (fun t => Indexed.instantiate t (betaFields argument origin))
        (fun t => Indexed.instantiate t (betaFields argument origin))
        (fun t => Indexed.instantiate t (betaFields argument origin))) =
    (betaBlock (betaExpansion domain body codomain checked argument argumentType) origin).1.map
      (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  have sourceType : (checkedSource argument).ty = domain :=
    (congrArg CanonicalTerm.ty (checkedSource_exact argument)).trans argumentType
  have sourceSame : (betaExpansion domain body codomain checked argument argumentType).source =
      (betaSeed domain body codomain checked).source := rfl
  have intermediateSame : (betaExpansion domain body codomain checked argument argumentType).intermediate =
      (betaSeed domain body codomain checked).intermediate := rfl
  have reducedSlot : Indexed.instantiate
      (Templates.single 0 (TemplateInstantiationMachine.compile 0 body)) (betaFields argument origin) =
      encodeWith dbTermCodec (DBTerm.instantiateAt argument.term 0 body) := by
    rw [Templates.single_exact]
    exact TemplateInstantiationMachine.compile_exact 0 body argument.term
  simp only [betaNodes, betaBlock, List.map_cons, List.map_nil, Node.map,
    sourceSame, intermediateSame, betaEntries_exact, betaExpansion_conclusion,
    unaryRequest, Templates.theoremTemplate, Templates.canonical, Templates.equality,
    Templates.application, Templates.pair_exact, Templates.literal_exact,
    Indexed.instantiate_hole, Indexed.instantiate_nil, reducedSlot]
  simp [betaFields, requestCodec, putRequest, putInference,
    canonicalCodec, theoremCodec, sequentCodec, termMapletCodec, checkedSourceCodec, sourceTermCodec,
    dbTermCodec, tyCodec, Codec.prod, Codec.mapped, Codec.list, Codec.putList,
    encodeWith, encodeData_pair, Theorem.emptyResult,
    CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, betaRedex, betaReduced,
    putTerm, sourceType, List.append_assoc]


/-- Fixed predicate and universal beta expansion. The argument of SPEC is absent. -/
def predicate (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool) : CanonicalTerm :=
  ⟨.abs domain body, .function domain Ty.bool, DBTerm.inferType_abs_of checked⟩

def universalBeta (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool) : BetaExpansion :=
  betaExpansion (.function domain Ty.bool)
    (CanonicalTerm.equalityDB (.function domain Ty.bool) (.bound 0) (.abs domain truthDB))
    Ty.bool (DBTerm.inferType_equalityDB (by simp [DBTerm.inferType])
      (DBTerm.inferType_abs_of DerivedRules.inferType_truthDB))
    (predicate domain body checked) rfl

def functionProof (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool) : Theorem :=
  eqMpResult (universalBeta domain body checked).conclusion input
    (CanonicalTerm.equalityOfSameType (predicate domain body checked)
      ⟨.abs domain truthDB, .function domain Ty.bool,
        DBTerm.inferType_abs_of DerivedRules.inferType_truthDB⟩ rfl)

def identityTerm : CanonicalTerm :=
  ⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩

/-- Complete original SPEC fields, built once for the input theorem and body.
The operand, its named representative and occurrence origin remain dynamic. -/
def nodes (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool) : List PlanNode :=
  let raw : Plan := [.inr 0]
  let origin : Plan := [.inr 2]
  let canon := Templates.canonical Ty.bool
  let empty := Templates.theoremTemplate ∅ ∅
  let dependent := Templates.theoremTemplate input.axioms input.sequent.hyp
  let truth : Plan := Templates.literal (putTerm truthDB)
  let left := Templates.application (Templates.literal (putTerm (.abs domain body))) raw
  let right := Templates.application (Templates.literal (putTerm (.abs domain truthDB))) raw
  let reduced := Templates.single 0 (TemplateInstantiationMachine.compile 0 body)
  let argCanonical := Templates.canonical domain raw
  let argProof := empty (canon (Templates.equality domain raw raw))
  let function := Templates.literal (theoremCodec.put (functionProof input domain body checked))
  let appProof := dependent (canon (Templates.equality Ty.bool left right))
  let truthBeta := empty (canon (Templates.equality Ty.bool right truth))
  let appTruth := dependent (canon (Templates.equality Ty.bool left truth))
  let reversed := dependent (canon (Templates.equality Ty.bool truth left))
  let truthProof := Templates.literal (theoremCodec.put (reflexivity identityTerm))
  let applied := dependent (canon left)
  let bodyBeta := empty (canon (Templates.equality Ty.bool left reduced))
  let result := dependent (canon reduced)
  let fixed (block : ProofSystem.Certificate) := substituteNodes ![origin] (blockNodes block)
  let primitive (count : Nat) (claim request : Plan) := primitiveNodes count claim request origin
  let universal :=  universalBeta domain body checked
  let functionBlock := primitiveBlock (.inference (.eqMp universal.conclusion input))
    (functionProof input domain body checked) ("", 0)
  (expandBlock [] 1 (fixed (betaBlock universal ("", 0)), 1)).1 ++
  (expandBlock [2, 0] 3 (fixed functionBlock, 2)).1 ++
  (expandBlock [] 4 (primitive 0 argProof (unaryRequest 0 argCanonical), 0)).1 ++
  (expandBlock [3, 4] 5 (primitive 2 appProof (binaryRequest 2 function argProof), 2)).1 ++
  (expandBlock [] 6 (betaNodes domain truthDB Ty.bool DerivedRules.inferType_truthDB, 1)).1 ++
  (expandBlock [5, 7] 8 (primitive 2 appTruth (binaryRequest 1 appProof truthBeta), 2)).1 ++
  (expandBlock [8] 9 (substituteNodes ![appTruth, left, truth, origin]
    (symmetryNodes input.axioms input.sequent.hyp Ty.bool), 5)).1 ++
  (expandBlock [] 14 (fixed (primitiveBlock (.inference (.refl identityTerm)) (reflexivity identityTerm) ("",0)), 0)).1 ++
  (expandBlock [13, 14] 15 (primitive 2 applied (binaryRequest 6 reversed truthProof), 2)).1 ++
  (expandBlock [] 16 (betaNodes domain body Ty.bool checked, 1)).1 ++
  (expandBlock [17, 15] 18 (primitive 2 result (binaryRequest 6 bodyBeta applied), 2)).1

def template (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool) : Plan :=
  certificateTemplate (nodes input domain body checked, 18)

theorem nodes_length (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool) :
    (nodes input domain body checked).length = 18 := by rfl


set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- Every byte field and physical parent address agrees with the original
chronological assembler, before any certificate serialization. -/
theorem expanded_exact (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) :
    (do let (receipts, roots) ← expandFrom [] #[0]
          (specExpansion policy input domain body checked argument argumentType shape origin).requests 1
        let root ← roots[11]?
        pure (receipts.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)), root)) =
      some ((nodes input domain body checked).map
        (Node.map (fun t => Indexed.instantiate t (betaFields argument origin))
          (fun t => Indexed.instantiate t (betaFields argument origin))
          (fun t => Indexed.instantiate t (betaFields argument origin))), 18) := by
  have sourceType : (checkedSource argument).ty = domain :=
    (congrArg CanonicalTerm.ty (checkedSource_exact argument)).trans argumentType
  have reducedSlot : Indexed.instantiate
      (Templates.single 0 (TemplateInstantiationMachine.compile 0 body)) (betaFields argument origin) =
      encodeWith dbTermCodec (DBTerm.instantiateAt argument.term 0 body) := by
    rw [Templates.single_exact]
    exact TemplateInstantiationMachine.compile_exact 0 body argument.term
  have truthSlot : Indexed.instantiate
      (Templates.single 0 (TemplateInstantiationMachine.compile 0 truthDB)) (betaFields argument origin) =
      encodeWith dbTermCodec truthDB := by
    rw [Templates.single_exact]
    simpa only [DerivedRules.instantiateAt_truthDB, TemplateInstantiationMachine.termWire,
      betaFields, Matrix.cons_val_zero, dbTermCodec, encodeWith] using
      TemplateInstantiationMachine.compile_exact 0 truthDB argument.term
  simp only [specExpansion, expandFrom, lookupPremises, RuleRequest.premises, InferenceRequest.premises, betaBlock, primitiveBlock,
    symmetryBlock, expandBlock, address, Node.relocate, nodes, substituteNodes,
    blockNodes, primitiveNodes, betaNodes, symmetryNodes,
    List.map_append, List.map_cons, List.map_nil, List.length_append,
    List.length_cons, List.length_nil, List.nil_append,
    Node.map, Templates.substitute_exact]
  simp only [Templates.theoremTemplate, Templates.canonical, Templates.equality,
    Templates.application, unaryRequest, binaryRequest, Templates.pair_exact,
    Templates.literal_exact, Indexed.instantiate_hole, Indexed.instantiate_nil,
    reducedSlot, truthSlot]
  simp [Node.map,
    Templates.pair_exact, Templates.literal_exact, Indexed.instantiate_hole,
    betaFields, predicate, universalBeta, functionProof, identityTerm, betaSeed,
    betaExpansion_conclusion, betaExpansion_source_exact, betaEntries_exact, betaIntermediate_exact,
    requestCodec, putRequest, putInference, canonicalCodec, theoremCodec,
    sequentCodec, termMapletCodec, checkedSourceCodec, sourceTermCodec,
    dbTermCodec, tyCodec, Codec.prod, Codec.mapped, Codec.list, Codec.putList,
    encodeWith, encodeData_pair, Theorem.emptyResult, Theorem.unionResult,
    Theorem.preserveAxiomsResult, reflexivity, eqMpResult, appResult, transResult,
    symmetryResult, headCongruence, fullCongruence, partialLeft, partialRight,
    equalityConstant, CanonicalTerm.applicationOfFunction, CanonicalTerm.constant,
    CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, betaRedex, betaReduced,
    putTerm, sourceType, argumentType, List.append_assoc,
    DerivedRules.instantiateAt_truthDB, DerivedRules.truthTerm]


/-- Emission agrees with any successful result of the original checked builder. -/
theorem emitted_exact (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) (block : ProofSystem.Certificate)
    (computed : specTypedBlock? policy input domain body checked argument argumentType shape origin = some block) :
    Indexed.instantiate (template input domain body checked) (betaFields argument origin) =
      encodeCertificate block := by
  have expanded := finishPlan_expanded (start_checked policy [input]) computed
  have mapped := congrArg (Option.map (fun (out : ProofSystem.Certificate) =>
    (out.1.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)), out.2))) expanded
  have aligned := expanded_exact policy input domain body checked argument argumentType shape origin
  simp only [start, Array.toList_empty, List.length_cons, List.length_nil, Nat.zero_add,
    Bind.bind, Pure.pure, Option.map_bind, Function.comp_def, Option.map_some] at mapped
  have result : some ((nodes input domain body checked).map
        (Node.map (fun t => Indexed.instantiate t (betaFields argument origin))
          (fun t => Indexed.instantiate t (betaFields argument origin))
          (fun t => Indexed.instantiate t (betaFields argument origin))), 18) =
      some (block.1.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)), block.2) := by
    cases execution : expandFrom [] #[0]
        (specExpansion policy input domain body checked argument argumentType shape origin).requests 1 with
    | none => simp [execution] at mapped
    | some out =>
      rcases out with ⟨receipts, roots⟩
      simp only [execution, Option.bind_some] at mapped
      simp only [execution, Bind.bind, Pure.pure, Option.bind_some] at aligned
      exact aligned.symm.trans mapped
  have parts := Prod.mk.inj (Option.some.inj result)
  have bytes := certificateTemplate_of_nodes (nodes input domain body checked)
    block.1 18 (betaFields argument origin) parts.1
  rw [show (block.1, 18) = block from Prod.ext rfl parts.2] at bytes
  exact bytes

/-- The serializer's exact dynamic input has three independent complete fields. -/
def inputWire (argument : CanonicalTerm) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (betaFields argument origin)

/-- The original builder always returns the typed 18-node SPEC block. -/
theorem built_isSome (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) :
    (specTypedBlock? policy input domain body checked argument argumentType shape origin).isSome = true := by
  obtain ⟨block, computed, _⟩ := specTypedBlock?_checked policy input domain body checked argument argumentType shape origin
  rw [computed]; rfl

def built (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) : ProofSystem.Certificate :=
  (specTypedBlock? policy input domain body checked argument argumentType shape origin).get
    (by rw [built_isSome])

theorem built_computed (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) :
    specTypedBlock? policy input domain body checked argument argumentType shape origin =
      some (built policy input domain body checked argument argumentType shape origin) :=
  (Option.some_get _).symm

theorem built_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) :
    BlockChecked policy [input] (specResult input domain body checked argument argumentType)
      (built policy input domain body checked argument argumentType shape origin) := by
  obtain ⟨block, computed, valid⟩ := specTypedBlock?_checked policy input domain body checked argument argumentType shape origin
  rw [built_computed] at computed
  exact (Option.some.inj computed).symm ▸ valid

/-- This finite machine emits the complete original checked block. Its linear
clock charges every raw operand byte, named operand byte and origin byte. -/
def outputs (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) :
    TM2OutputsInTime (Indexed.machine (template input domain body checked))
      (inputWire argument origin)
      (some (encodeCertificate (built policy input domain body checked argument argumentType shape origin)))
      (4 * ((template input domain body checked).length + 1) * ((inputWire argument origin).length + 1)) := by
  have same := emitted_exact policy input domain body checked argument argumentType shape origin
    _ (built_computed policy input domain body checked argument argumentType shape origin)
  exact same ▸ Indexed.outputs (template input domain body checked) (betaFields argument origin)

/-- The independent original decoder returns the checked original block. -/
theorem emitted_decodes (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) :
    decodeCertificate (Indexed.instantiate (template input domain body checked) (betaFields argument origin)) =
      some (built policy input domain body checked argument argumentType shape origin) := by
  rw [emitted_exact policy input domain body checked argument argumentType shape origin
    _ (built_computed policy input domain body checked argument argumentType shape origin)]
  exact decodeCertificate_encodeCertificate _


/-- A fixed admitted predicate has one machine for all correctly typed operands.
The coefficient accounts for its complete static theorem and template payload.
Computing the named operand and building this fixed control remain separate. -/
noncomputable def realization (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body)) :
    TM2ComputableInPolyTime
      (fun data : {argument : CanonicalTerm // argument.ty = domain} × Origin => inputWire data.1.val data.2)
      encodeCertificate
      (fun data => built policy input domain body checked data.1.val data.1.property shape data.2) where
  tm := Indexed.machine (template input domain body checked)
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := C (4 * ((template input domain body checked).length + 1)) * (X + C 1)
  outputsFun data := by
    change TM2OutputsInTime (Indexed.machine (template input domain body checked))
      ((inputWire data.1.val data.2).map id)
      (some ((encodeCertificate (built policy input domain body checked data.1.val data.1.property shape data.2)).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs policy input domain body checked data.1.val data.1.property shape data.2

/-- Complete byte readout is accepted by the existing relative graph checker. -/
theorem emitted_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (domain : Ty) (body : DBTerm)
    (checked : body.inferType [domain] = some Ty.bool)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB domain (.abs domain body))
    (origin : Origin) :
    ∃ block, decodeCertificate (Indexed.instantiate (template input domain body checked) (betaFields argument origin)) = some block ∧
      BlockChecked policy [input] (specResult input domain body checked argument argumentType) block ∧
      block.1.length = 18 ∧ block.1.map (·.origin) = List.replicate 18 origin := by
  refine ⟨built policy input domain body checked argument argumentType shape origin,
    emitted_decodes policy input domain body checked argument argumentType shape origin,
    built_checked policy input domain body checked argument argumentType shape origin, ?_, ?_⟩
  · exact specTypedBlock?_size policy input domain body checked argument argumentType shape origin
      (built_computed policy input domain body checked argument argumentType shape origin)
  · exact specTypedBlock?_origins policy input domain body checked argument argumentType shape origin
      (built_computed policy input domain body checked argument argumentType shape origin)

end Mettapedia.Languages.HOLLight.QuantifierEmission
