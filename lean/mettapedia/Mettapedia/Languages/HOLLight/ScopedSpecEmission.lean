import Mettapedia.Languages.HOLLight.ScopedBetaEmission

/-!
# Original eighteen-node SPEC fields for changing authored bodies

The fixed descriptor contains an authored typed body and its fixed provenance.
Earlier raw and named operands compute the changing predicate and incoming
universal theorem. Current raw and named operand bytes and the original origin
then generate every claim, primitive request, ordered parent occurrence, and
selected root of the original checked SPEC block.

The complete descriptor is charged by its template length. This is fixed-C
specialization; it does not interpret a calculus specification supplied at run
time. Argument rendering and row-stage admission remain separate joins.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.ScopedSpecEmission
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open PrimitiveTransport EqualityExpansion EqualityExpansion.Emission GraphExpansion
open ProofDataEncoding Mettapedia.Logic.DerivationGraph
open ProofExecution (Origin)
open PrimitiveSentences (truthDB identityBool)
open ScopedBetaEmission (FieldCount Plan fields rawBody rawBody_exact body checkedBody)

/-- The original computed source representative, before any byte emission. -/
theorem checkedSource_named (value : CanonicalTerm) :
    named? value.term [] = some (checkedSource value).source := by
  have computed : checkedSource? value = some (checkedSource value) := (Option.some_get _).symm
  unfold checkedSource? at computed
  cases namedResult : named? value.term [] with
  | none => simp [namedResult] at computed
  | some source =>
      simp only [namedResult,Bind.bind,Pure.pure,Option.bind_some] at computed
      split at computed
      · exact congrArg (fun result : CheckedSourceTerm => some result.source) (Option.some.inj computed)
      · contradiction

/-- The current predicate is computed from the authored body and earlier operands. -/
def predicate (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain) : CanonicalTerm :=
  QuantifierEmission.predicate domain (body previous authored)
    (checkedBody arity domain Ty.bool authored checked previous typed)

def predicateRaw (arity : Nat) (domain : Ty) (authored : DBTerm) : Plan arity :=
  ScopedBetaEmission.abstraction domain (rawBody arity authored)

theorem predicateRaw_exact {arity : Nat} (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (origin : Origin) :
    Indexed.instantiate (predicateRaw arity domain authored) (fields previous argument origin) =
      encodeWith dbTermCodec (predicate arity domain authored checked previous typed).term :=
  ScopedBetaEmission.abstraction_exact domain _ _ _ (rawBody_exact authored previous argument origin)

def predicateNamed (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool) : Plan arity :=
  Templates.substitute
    (ScopedNamedTemplates.plan arity (.abs domain authored) []
      (by simpa only [DBTerm.LooseBelow,List.length_nil,Nat.zero_add,Nat.add_comm] using
        ScopedBetaEmission.body_scope arity domain Ty.bool authored checked))
    (fun index => [.inr (ScopedBetaEmission.namedIndex index)])

theorem predicateNamed_exact {arity : Nat} (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    Indexed.instantiate (predicateNamed arity domain authored checked) (fields previous argument origin) =
      encodeWith sourceTermCodec (checkedSource (predicate arity domain authored checked previous typed)).source := by
  rw [predicateNamed,Templates.substitute_exact]
  have exactResult := ScopedNamedTemplates.compile_exact_values arity previous
    (fun index => (checkedSource (previous index)).source) empty independent 0 (.abs domain authored) []
  have planned := ScopedNamedTemplates.plan_computed arity (.abs domain authored) []
    (by simpa only [DBTerm.LooseBelow,List.length_nil,Nat.zero_add,Nat.add_comm] using
      ScopedBetaEmission.body_scope arity domain Ty.bool authored checked)
  simp only [List.length_nil] at planned
  rw [planned] at exactResult
  have named := checkedSource_named (predicate arity domain authored checked previous typed)
  change named? (.abs domain (body previous authored)) [] = _ at named
  rw [TemplateInstantiationMachine.Indexed.sequence_abs] at exactResult
  rw [show named? (.abs domain (TemplateInstantiationMachine.Indexed.sequence (List.ofFn previous) (0+1) authored)) [] = _ from named] at exactResult
  simpa only [Option.map_some,Option.some.injEq,Indexed.instantiate_hole,Indexed.instantiate_nil,
    List.append_nil,ScopedBetaEmission.named_field] using exactResult

/-- The fixed authored provenance is retained while its universal conclusion changes. -/
def input (seed : Theorem) (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain) : Theorem :=
  Theorem.preserveAxiomsResult seed seed.sequent.hyp
    (betaRedex (.function domain Ty.bool)
      (CanonicalTerm.equalityDB (.function domain Ty.bool) (.bound 0) (.abs domain truthDB)) Ty.bool
      (DBTerm.inferType_equalityDB (by simp [DBTerm.inferType])
        (DBTerm.inferType_abs_of DerivedRules.inferType_truthDB))
      (predicate arity domain authored checked previous typed) rfl)

theorem input_shape (seed : Theorem) (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain) :
    (input seed arity domain authored checked previous typed).sequent.concl.term =
      DerivedRules.forallAppDB domain (.abs domain (body previous authored)) := rfl

def inputTemplate (seed : Theorem) (arity : Nat) (domain : Ty) (authored : DBTerm) : Plan arity :=
  Templates.theoremTemplate seed.axioms seed.sequent.hyp (Templates.canonical Ty.bool
    (Templates.application (Templates.literal (putTerm (ExcludedMiddle.forallDB domain)))
      (predicateRaw arity domain authored)))

theorem inputTemplate_exact (seed : Theorem) {arity : Nat} (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (origin : Origin) :
    Indexed.instantiate (inputTemplate seed arity domain authored) (fields previous argument origin) =
      encodeWith theoremCodec (input seed arity domain authored checked previous typed) := by
  unfold inputTemplate
  apply Templates.theoremTemplate_exact seed.axioms seed.sequent.hyp _ _
    (input seed arity domain authored checked previous typed) rfl rfl
  apply Templates.canonical_exact Ty.bool _ _ (input seed arity domain authored checked previous typed).sequent.concl rfl
  exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _)
    (predicateRaw_exact domain authored checked previous typed argument origin)

/-- Original fixed universal body; only its predicate argument changes. -/
def universalBody (domain : Ty) : DBTerm :=
  CanonicalTerm.equalityDB (.function domain Ty.bool) (.bound 0) (.abs domain truthDB)
theorem universalChecked (domain : Ty) : (universalBody domain).inferType [.function domain Ty.bool] = some Ty.bool :=
  DBTerm.inferType_equalityDB (by simp [DBTerm.inferType])
    (DBTerm.inferType_abs_of DerivedRules.inferType_truthDB)

def universalNodes (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool) : List (Node (Plan arity) (Plan arity) (Plan arity)) :=
  substituteNodes ![predicateRaw arity domain authored,predicateNamed arity domain authored checked,
    [.inr (ScopedBetaEmission.originIndex arity)]]
    (QuantifierEmission.betaNodes (.function domain Ty.bool) (universalBody domain) Ty.bool (universalChecked domain))

theorem universalNodes_exact {arity : Nat} (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    (universalNodes arity domain authored checked).map
      (Node.map (fun template => Indexed.instantiate template (fields previous argument origin))
        (fun template => Indexed.instantiate template (fields previous argument origin))
        (fun template => Indexed.instantiate template (fields previous argument origin))) =
    (betaBlock (QuantifierEmission.universalBeta domain (body previous authored)
      (checkedBody arity domain Ty.bool authored checked previous typed)) origin).1.map
      (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  rw [universalNodes,substituteNodes_exact]
  have aligned : (fun slot => Indexed.instantiate
      (![predicateRaw arity domain authored,predicateNamed arity domain authored checked,
        [.inr (ScopedBetaEmission.originIndex arity)]] slot : Plan arity) (fields previous argument origin)) =
      betaFields (predicate arity domain authored checked previous typed) origin := by
    funext slot
    fin_cases slot
    · exact predicateRaw_exact domain authored checked previous typed argument origin
    · exact predicateNamed_exact domain authored checked previous typed argument origin empty independent
    · simp [Indexed.instantiate,betaFields]
  rw [aligned]
  exact QuantifierEmission.betaNodes_exact _ _ _ _ _ rfl origin


/-- The universal beta conclusion is generated from the same changing predicate. -/
def universalConclusion (arity : Nat) (domain : Ty) (authored : DBTerm) : Plan arity :=
  let functionType := Ty.function domain Ty.bool
  let rawPredicate := predicateRaw arity domain authored
  let universal := Templates.application (Templates.literal (putTerm (ExcludedMiddle.forallDB domain))) rawPredicate
  let equation := Templates.equality functionType rawPredicate (Templates.literal (putTerm (.abs domain truthDB)))
  Templates.theoremTemplate ∅ ∅ (Templates.canonical Ty.bool (Templates.equality Ty.bool universal equation))

/-- Both incoming and intermediate theorems retain the fixed authored provenance. -/
def functionTemplate (seed : Theorem) (arity : Nat) (domain : Ty) (authored : DBTerm) : Plan arity :=
  Templates.theoremTemplate seed.axioms seed.sequent.hyp (Templates.canonical Ty.bool
    (Templates.equality (.function domain Ty.bool) (predicateRaw arity domain authored)
      (Templates.literal (putTerm (.abs domain truthDB)))))

theorem expanded_nodes {J J' W W' O O' : Type}
    (conclusion : J → J') (witness : W → W') (origin : O → O')
    (roots : List Nat) (base : Nat) (nodes : List (Node J W O)) (root : Nat) :
    (expandBlock roots base (nodes,root)).1.map (Node.map conclusion witness origin) =
      (expandBlock roots base (nodes.map (Node.map conclusion witness origin),root)).1 :=
  (congrArg Prod.fst (expandBlock_map conclusion witness origin roots base (nodes,root))).symm

theorem fixedNodes_exact {arity : Nat} (plan : Indexed.Template Alphabet arity)
    (words : Fin arity → List Alphabet) (origin : Origin)
    (exactOrigin : Indexed.instantiate plan words=encodeWith originCodec origin)
    (block : ProofSystem.Certificate) :
    (substituteNodes ![plan] (blockNodes block)).map
      (Node.map (fun template => Indexed.instantiate template words)
        (fun template => Indexed.instantiate template words)
        (fun template => Indexed.instantiate template words)) =
    (stampedBlock origin block).1.map
      (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  rw [substituteNodes_exact]
  have aligned : (fun index => Indexed.instantiate (![plan] index) words) = originFields origin := by
    funext index
    fin_cases index
    exact exactOrigin
  rw [aligned]
  exact blockNodes_exact block origin

/-- The fixed descriptor generates all eighteen original primitive occurrences. -/
def nodes (seed : Theorem) (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool) :
    List (Node (Plan arity) (Plan arity) (Plan arity)) :=
  let raw : Plan arity := [.inr (ScopedBetaEmission.rawOperandIndex arity)]
  let named : Plan arity := [.inr (ScopedBetaEmission.namedOperandIndex arity)]
  let origin : Plan arity := [.inr (ScopedBetaEmission.originIndex arity)]
  let canon := Templates.canonical Ty.bool
  let empty := Templates.theoremTemplate ∅ ∅
  let dependent := Templates.theoremTemplate seed.axioms seed.sequent.hyp
  let truth : Plan arity := Templates.literal (putTerm truthDB)
  let left := Templates.application (predicateRaw arity domain authored) raw
  let right := Templates.application (Templates.literal (putTerm (.abs domain truthDB))) raw
  let reduced := ScopedBetaEmission.reduced arity authored raw
  let argCanonical := Templates.canonical domain raw
  let argProof := empty (canon (Templates.equality domain raw raw))
  let function := functionTemplate seed arity domain authored
  let appProof := dependent (canon (Templates.equality Ty.bool left right))
  let truthBeta := empty (canon (Templates.equality Ty.bool right truth))
  let appTruth := dependent (canon (Templates.equality Ty.bool left truth))
  let reversed := dependent (canon (Templates.equality Ty.bool truth left))
  let truthProof := Templates.literal (theoremCodec.put (reflexivity QuantifierEmission.identityTerm))
  let applied := dependent (canon left)
  let bodyBeta := empty (canon (Templates.equality Ty.bool left reduced))
  let result := dependent (canon reduced)
  let fixed (block : ProofSystem.Certificate) := substituteNodes ![origin] (blockNodes block)
  let primitive (count : Nat) (claim request : Plan arity) := primitiveNodes count claim request origin
  (expandBlock [] 1 (universalNodes arity domain authored checked,1)).1 ++
  (expandBlock [2,0] 3 (primitive 2 function
    (binaryRequest 6 (universalConclusion arity domain authored) (inputTemplate seed arity domain authored)),2)).1 ++
  (expandBlock [] 4 (primitive 0 argProof (unaryRequest 0 argCanonical),0)).1 ++
  (expandBlock [3,4] 5 (primitive 2 appProof (binaryRequest 2 function argProof),2)).1 ++
  (expandBlock [] 6 (substituteNodes ![raw,named,origin]
    (QuantifierEmission.betaNodes domain truthDB Ty.bool DerivedRules.inferType_truthDB),1)).1 ++
  (expandBlock [5,7] 8 (primitive 2 appTruth (binaryRequest 1 appProof truthBeta),2)).1 ++
  (expandBlock [8] 9 (substituteNodes ![appTruth,left,truth,origin]
    (symmetryNodes seed.axioms seed.sequent.hyp Ty.bool),5)).1 ++
  (expandBlock [] 14 (fixed (primitiveBlock (.inference (.refl QuantifierEmission.identityTerm))
    (reflexivity QuantifierEmission.identityTerm) ("",0)),0)).1 ++
  (expandBlock [13,14] 15 (primitive 2 applied (binaryRequest 6 reversed truthProof),2)).1 ++
  (expandBlock [] 16 (ScopedBetaEmission.nodes arity domain Ty.bool authored checked,1)).1 ++
  (expandBlock [17,15] 18 (primitive 2 result (binaryRequest 6 bodyBeta applied),2)).1

theorem nodes_length (seed : Theorem) (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool) :
    (nodes seed arity domain authored checked).length=18 := by
  simp only [nodes,expandBlock,List.length_append,List.length_map,universalNodes,substituteNodes,
    QuantifierEmission.betaNodes,primitiveNodes,symmetryNodes,blockNodes,primitiveBlock,ScopedBetaEmission.nodes,
    List.length_cons,List.length_nil]

/-- Correspondence is checked against the existing original SPEC node plan. -/
theorem nodes_exact (seed : Theorem) {arity : Nat} (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (argumentType : argument.ty=domain) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    (nodes seed arity domain authored checked).map
      (Node.map (fun template => Indexed.instantiate template (fields previous argument origin))
        (fun template => Indexed.instantiate template (fields previous argument origin))
        (fun template => Indexed.instantiate template (fields previous argument origin))) =
    (QuantifierEmission.nodes (input seed arity domain authored checked previous typed) domain (body previous authored)
      (checkedBody arity domain Ty.bool authored checked previous typed)).map
      (Node.map (fun template => Indexed.instantiate template (betaFields argument origin))
        (fun template => Indexed.instantiate template (betaFields argument origin))
        (fun template => Indexed.instantiate template (betaFields argument origin))) := by
  have operandFields : (fun slot => Indexed.instantiate
      (![[.inr (ScopedBetaEmission.rawOperandIndex arity)],
         [.inr (ScopedBetaEmission.namedOperandIndex arity)],
         [.inr (ScopedBetaEmission.originIndex arity)]] slot : Plan arity) (fields previous argument origin)) =
      betaFields argument origin := by
    funext slot
    fin_cases slot <;> simp [Indexed.instantiate,betaFields]
  have upper := universalNodes_exact domain authored checked previous typed argument origin empty independent
  have lower := ScopedBetaEmission.nodes_exact domain Ty.bool authored checked previous typed argument argumentType origin empty independent
  have originalLower := QuantifierEmission.betaNodes_exact domain (body previous authored) Ty.bool
    (checkedBody arity domain Ty.bool authored checked previous typed) argument argumentType origin
  have rawPredicate := predicateRaw_exact domain authored checked previous typed argument origin
  have reduced := ScopedBetaEmission.reduced_exact authored ([.inr (ScopedBetaEmission.rawOperandIndex arity)] : Plan arity)
    previous argument argument origin (by simp)
  have originalReduced : Indexed.instantiate (Templates.single 0
      (TemplateInstantiationMachine.compile 0 (body previous authored))) (betaFields argument origin) =
      encodeWith dbTermCodec (DBTerm.instantiateAt argument.term 0 (body previous authored)) := by
    rw [Templates.single_exact]
    exact TemplateInstantiationMachine.compile_exact 0 (body previous authored) argument.term
  have inputBytes := inputTemplate_exact seed domain authored checked previous typed argument origin
  simp only [nodes,QuantifierEmission.nodes,List.map_append,expanded_nodes]
  rw [upper,lower,← originalLower]
  simp only [expandBlock, betaBlock, List.map_cons, Node.map, List.map_nil, Node.relocate, primitiveNodes,
    binaryRequest, unaryRequest, Templates.pair_exact, Templates.literal_exact, inputBytes, Indexed.instantiate_hole,
    Indexed.instantiate_nil, List.append_nil, Templates.theoremTemplate, Templates.canonical, Templates.equality,
    Templates.application, rawPredicate, substituteNodes, QuantifierEmission.betaNodes, Templates.substitute_exact,
    symmetryNodes, blockNodes, primitiveBlock, originalReduced, reduced]
  simp only [encodeWith, theoremCodec, Codec.mapped, Codec.prod, sequentCodec, canonicalCodec, dbTermCodec,
    tyCodec, Option.pure_def, Option.bind_eq_bind, QuantifierEmission.universalBeta, CanonicalTerm.equalityDB,
    QuantifierEmission.predicate, betaIntermediate_exact, Theorem.emptyResult, CanonicalTerm.equalityOfSameType,
    betaRedex, betaReduced, DBTerm.instantiateAt, DBTerm.instantiateAt_target, zero_add,
    DerivedRules.instantiateAt_truthDB, putTerm, encodeData_pair, Fin.isValue, List.cons_append, List.append_assoc,
    requestCodec, betaExpansion_source_exact, putRequest, putInference, checkedSourceCodec, sourceTermCodec,
    betaExpansion_conclusion, betaEntries_exact, Codec.list, termMapletCodec, Codec.putList, functionTemplate,
    Templates.theoremTemplate, Templates.canonical, Templates.equality, Templates.application, Templates.pair_exact,
    Templates.literal_exact, rawPredicate, predicate, universalConclusion, ExcludedMiddle.forallDB, input,
    Theorem.preserveAxiomsResult, ScopedBetaEmission.origin_field, List.nil_append, ScopedBetaEmission.operand_field,
    List.range_zero, List.map_nil, betaSeed, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_app_two,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil,
    Matrix.cons_val_zero, operandFields, betaFields, ScopedBetaEmission.named_operand_field, Matrix.cons_app_three,
    reflexivity, QuantifierEmission.identityTerm, RuleRequest.premises, InferenceRequest.premises, List.length_nil,
    QuantifierEmission.functionProof, eqMpResult, Theorem.unionResult, Finset.empty_union, List.length_cons]


def template (seed : Theorem) (arity : Nat) (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool) : Plan arity :=
  certificateTemplate (nodes seed arity domain authored checked,18)

/-- The original chronological assembler yields exactly the generated eighteen-node graph. -/
theorem expanded_exact (policy : AxiomPolicy) [DecidablePred policy] (seed : Theorem) {arity : Nat}
    (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (argumentType : argument.ty=domain) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    (do let (receipts,roots) ← expandFrom [] #[0]
          (QuantifierExpansion.specExpansion policy (input seed arity domain authored checked previous typed)
            domain (body previous authored) (checkedBody arity domain Ty.bool authored checked previous typed)
            argument argumentType (input_shape seed arity domain authored checked previous typed) origin).requests 1
        let root ← roots[11]?
        pure (receipts.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)),root)) =
      some ((nodes seed arity domain authored checked).map
        (Node.map (fun t => Indexed.instantiate t (fields previous argument origin))
          (fun t => Indexed.instantiate t (fields previous argument origin))
          (fun t => Indexed.instantiate t (fields previous argument origin))),18) := by
  rw [nodes_exact seed domain authored checked previous typed argument argumentType origin empty independent]
  exact QuantifierEmission.expanded_exact policy _ domain _ _ argument argumentType _ origin

/-- Equality to the original checked builder fixes every serialized byte. -/
theorem emitted_exact (policy : AxiomPolicy) [DecidablePred policy] (seed : Theorem) {arity : Nat}
    (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (argumentType : argument.ty=domain) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source)
    (block : ProofSystem.Certificate)
    (computed : QuantifierExpansion.specTypedBlock? policy (input seed arity domain authored checked previous typed)
      domain (body previous authored) (checkedBody arity domain Ty.bool authored checked previous typed)
      argument argumentType (input_shape seed arity domain authored checked previous typed) origin = some block) :
    Indexed.instantiate (template seed arity domain authored checked) (fields previous argument origin) =
      encodeCertificate block := by
  have expanded := finishPlan_expanded (start_checked policy [input seed arity domain authored checked previous typed]) computed
  have mapped := congrArg (Option.map (fun (out : ProofSystem.Certificate) =>
    (out.1.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)),out.2))) expanded
  have aligned := expanded_exact policy seed domain authored checked previous typed argument argumentType origin empty independent
  simp only [start,Array.toList_empty,List.length_cons,List.length_nil,Nat.zero_add,
    Bind.bind,Pure.pure,Option.map_bind,Function.comp_def,Option.map_some] at mapped
  have result : some ((nodes seed arity domain authored checked).map
      (Node.map (fun t => Indexed.instantiate t (fields previous argument origin))
        (fun t => Indexed.instantiate t (fields previous argument origin))
        (fun t => Indexed.instantiate t (fields previous argument origin))),18) =
      some (block.1.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)),block.2) := by
    cases execution : expandFrom [] #[0]
        (QuantifierExpansion.specExpansion policy (input seed arity domain authored checked previous typed)
          domain (body previous authored) (checkedBody arity domain Ty.bool authored checked previous typed)
          argument argumentType (input_shape seed arity domain authored checked previous typed) origin).requests 1 with
    | none => simp [execution] at mapped
    | some out =>
      rcases out with ⟨receipts,roots⟩
      simp only [execution,Option.bind_some] at mapped
      simp only [execution,Bind.bind,Pure.pure,Option.bind_some] at aligned
      exact aligned.symm.trans mapped
  have parts := Prod.mk.inj (Option.some.inj result)
  have bytes := certificateTemplate_of_nodes (nodes seed arity domain authored checked)
    block.1 18 (fields previous argument origin) parts.1
  rw [show (block.1,18)=block from Prod.ext rfl parts.2] at bytes
  exact bytes

/-- The actual finite copier is fixed by the authored descriptor. Its input
contains only earlier raw/named operands, current raw/named operand, and origin. -/
def outputs (policy : AxiomPolicy) [DecidablePred policy] (seed : Theorem) {arity : Nat}
    (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (argumentType : argument.ty=domain) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source)
    (block : ProofSystem.Certificate)
    (computed : QuantifierExpansion.specTypedBlock? policy (input seed arity domain authored checked previous typed)
      domain (body previous authored) (checkedBody arity domain Ty.bool authored checked previous typed)
      argument argumentType (input_shape seed arity domain authored checked previous typed) origin = some block) :
    Turing.TM2OutputsInTime (Indexed.machine (template seed arity domain authored checked))
      (Indexed.argumentWire (fields previous argument origin)) (some (encodeCertificate block))
      (4*((template seed arity domain authored checked).length+1)*
        ((Indexed.argumentWire (fields previous argument origin)).length+1)) := by
  rw [← emitted_exact policy seed domain authored checked previous typed argument argumentType origin empty independent block computed]
  exact Indexed.outputs _ _

/-- Successful output is authorized solely by the original HOL primitive replay. -/
theorem decodes_checked (policy : AxiomPolicy) [DecidablePred policy] (seed : Theorem) {arity : Nat}
    (domain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some Ty.bool)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (argumentType : argument.ty=domain) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    ∃ block, decodeCertificate (Indexed.instantiate (template seed arity domain authored checked)
      (fields previous argument origin)) = some block ∧
      BlockChecked policy [input seed arity domain authored checked previous typed]
        (QuantifierExpansion.specResult (input seed arity domain authored checked previous typed) domain
          (body previous authored) (checkedBody arity domain Ty.bool authored checked previous typed) argument argumentType) block ∧
      block.1.length=18 ∧ block.1.map (fun node => node.origin)=List.replicate 18 origin := by
  obtain ⟨block,computed,valid⟩ := QuantifierExpansion.specTypedBlock?_checked policy
    (input seed arity domain authored checked previous typed) domain (body previous authored)
    (checkedBody arity domain Ty.bool authored checked previous typed) argument argumentType
    (input_shape seed arity domain authored checked previous typed) origin
  refine ⟨block,?_,valid,?_,?_⟩
  · rw [emitted_exact policy seed domain authored checked previous typed argument argumentType origin empty independent block computed]
    exact decodeCertificate_encodeCertificate block
  · exact QuantifierExpansion.specTypedBlock?_size policy _ _ _ _ _ _ _ _ computed
  · exact QuantifierExpansion.specTypedBlock?_origins policy _ _ _ _ _ _ _ _ computed

end Mettapedia.Languages.HOLLight.ScopedSpecEmission
