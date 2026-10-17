import Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion
import Mettapedia.Languages.HOLLight.DynamicModusPonensTemplates

/-!
# Original MP fields, relocation and chronological insertion

Original request lowering and expansion transport earn every field, parent list
and root of the eleven-field MP descriptor. Original replay earns its finite
compiled topology. The handoff constructs the original checked block internally
and supplies the complete physical relocation, certificate parsing and receipt
append path with its original input clock. Earlier-root authorization belongs
to the chronological driver.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.DynamicModusPonensRelocation
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Logic.DerivationGraph
open ProofDataEncoding PrimitiveTransport EqualityExpansion.Emission
open GraphExpansion ImplicationExpansion ImplicationExpansion.Emission

theorem aligned_of_maps {arity : Nat}
    (nodes : List (Node (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)))
    (receipts : List ProofExecution.Receipt) (root : Nat) (payload : Fin arity → List Alphabet)
    (same : nodes.map (Node.map (fun plan => Indexed.instantiate plan payload)
      (fun plan => Indexed.instantiate plan payload) (fun plan => Indexed.instantiate plan payload)) =
      receipts.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec))) :
    RelocatedCertificateInsertion.Aligned (nodes,root) receipts payload := by
  change List.Forall₂ _ nodes receipts
  induction nodes generalizing receipts with
  | nil =>
      cases receipts with
      | nil => exact .nil
      | cons receipt rest => simp at same
  | cons node rest ih =>
      cases receipts with
      | nil => simp at same
      | cons receipt remaining =>
          simp only [List.map_cons] at same
          obtain ⟨head,tail⟩ := List.cons.inj same
          refine .cons ⟨?_,?_,?_,?_⟩ (ih remaining tail)
          · exact congrArg (fun node => node.conclusion) head
          · exact congrArg (fun node => node.witness) head
          · exact congrArg (fun node => node.origin) head
          · exact congrArg (fun node => node.parents) head

theorem dynamic_mp_aligned (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (inputHyp : input.sequent.hyp = ∅) (premiseHyp : premise.sequent.hyp = ∅)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) (policy : AxiomPolicy) [DecidablePred policy]
    (shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (block : ProofSystem.Certificate)
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    DynamicModusPonensTemplates.assembled.2 = block.2 ∧
      RelocatedCertificateInsertion.Aligned DynamicModusPonensTemplates.assembled block.1
        (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin) := by
  set descriptor := DynamicModusPonensTemplates.assembled with descriptorDef
  clear_value descriptor
  let payload := mpFields input premise left right pairLeftSource pairRightSource origin
  set source := (mpPlan input premise left right leftBool rightBool origin).1 with sourceDef
  clear_value source
  let lower := Node.map (fun plan => Indexed.instantiate plan payload)
    (fun plan => Indexed.instantiate plan payload) (fun plan => Indexed.instantiate plan payload)
  let encode := Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)
  have finished : GraphExpansion.finishPlan policy (GraphExpansion.start [input,premise]) #[0,1] source 21 = some block := by
    simpa only [mpTypedBlock?,mpExpansion_requests,← sourceDef] using computed
  have sourceAssembly := GraphExpansion.finishPlan_expanded (GraphExpansion.start_checked policy [input,premise]) finished
  change (do let (nodes,roots) ← GraphExpansion.expandFrom [] #[0,1] source 2
             let root ← roots[21]?
             pure (nodes,root)) = some block at sourceAssembly
  have sourceTransport := GraphExpansion.expandFrom_selected_bind_map (encodeWith theoremCodec)
    (encodeWith requestCodec) (encodeWith originCodec) #[0,1] source 21 2
  have encodedComputed := congrArg
    (Option.map (fun (localBlock : ProofSystem.Certificate) => (localBlock.1.map encode,localBlock.2))) sourceAssembly
  simp only [Option.map_some] at encodedComputed
  have sourceMapped := sourceTransport.trans encodedComputed
  have requestTransport := mpRequests_lowered input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed
    pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin
  rw [inputHyp,premiseHyp,← sourceDef] at requestTransport
  have mappedAssembly : (DynamicModusPonensTemplates.originalAssembly? input.axioms premise.axioms).map
      (fun assembled => (assembled.1.map lower,assembled.2)) = some (block.1.map encode,block.2) := by
    cases formed : mpRequests? input.axioms premise.axioms ∅ ∅ with
    | none => simp [formed] at requestTransport
    | some requests =>
        simp only [formed,Option.map_some] at requestTransport
        have requestsExact := Option.some.inj requestTransport
        change requests.map (Node.map (fun plan => Indexed.instantiate plan payload)
          (fun (localBlock : List (Node (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9)) × Nat) => (localBlock.1.map lower,localBlock.2))
          (fun plan => Indexed.instantiate plan payload)) =
          source.map (Node.map (encodeWith theoremCodec) (fun (localBlock : ProofSystem.Certificate) => (localBlock.1.map encode,localBlock.2)) (encodeWith originCodec)) at requestsExact
        have transported := GraphExpansion.expandFrom_selected_bind_map_of_eq
          (fun plan => Indexed.instantiate plan payload) (fun plan => Indexed.instantiate plan payload)
          (fun plan => Indexed.instantiate plan payload) #[0,1] requests
          (source.map (Node.map (encodeWith theoremCodec)
            (fun (localBlock : ProofSystem.Certificate) => (localBlock.1.map encode,localBlock.2)) (encodeWith originCodec)))
          21 2 (block.1.map encode,block.2) requestsExact sourceMapped
        unfold DynamicModusPonensTemplates.originalAssembly?
        simp only [formed,Bind.bind,Option.bind_some]
        exact transported
  have assemblyExact := DynamicModusPonensTemplates.assembled_fields input.axioms premise.axioms
  rw [← descriptorDef] at assemblyExact
  rw [assemblyExact,Option.map_some] at mappedAssembly
  have both := Option.some.inj mappedAssembly
  have rootsSame := congrArg Prod.snd both
  have nodesSame := congrArg Prod.fst both
  have lowerSame (node : DynamicModusPonensTemplates.TemplateNode) :
      lower (DynamicModusPonensTemplates.specializeNode input.axioms premise.axioms node) =
      Node.map (fun plan => Indexed.instantiate plan (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin))
        (fun plan => Indexed.instantiate plan (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin))
        (fun plan => Indexed.instantiate plan (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)) node := by
    cases node
    simp only [lower,DynamicModusPonensTemplates.specializeNode,Node.map,Templates.substitute_exact,payload,
      DynamicModusPonensTemplates.fields_aligned]
  refine ⟨rootsSame,aligned_of_maps _ _ _ _ ?_⟩
  simpa only [List.map_map,Function.comp_def,lowerSame,encode] using nodesSame

theorem original_handoff (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (inputHyp : input.sequent.hyp = ∅) (premiseHyp : premise.sequent.hyp = ∅)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) (policy : AxiomPolicy) [DecidablePred policy]
    (shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) :
    ∃ (safe : GraphRelocationEmission.SafeBlock 2 58 DynamicModusPonensTemplates.assembled)
      (block : ProofSystem.Certificate),
      mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block ∧
      BlockChecked policy [input,premise] (mpResult input premise right) block ∧
      block.1.length = 58 ∧
      DynamicModusPonensTemplates.assembled.2 = block.2 ∧
      RelocatedCertificateInsertion.Aligned DynamicModusPonensTemplates.assembled block.1
        (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin) ∧
      (∀ (roots : Fin 2 → Nat) (base : Nat) (earlier : List ProofExecution.Receipt),
        Nonempty (TM2OutputsInTime (RelocatedCertificateInsertion.machine 2 58
          DynamicModusPonensTemplates.assembled safe)
          (RelocatedCertificateInsertion.inputWire
            (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)
            roots base earlier)
          (some (encodeCertificate
            (earlier++(GraphExpansion.expandBlock (List.ofFn roots) base block).1,
              (GraphExpansion.expandBlock (List.ofFn roots) base block).2)))
          (RelocatedCertificateInsertion.coefficient 2 58 DynamicModusPonensTemplates.assembled safe *
            ((RelocatedCertificateInsertion.inputWire
              (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)
              roots base earlier).length+1)))) := by
  obtain ⟨block,computed,checked,size,_,_,_⟩ := DynamicModusPonensTemplates.emitted_original input premise left right
    leftBool rightBool inputHyp premiseHyp leftEmpty rightEmpty leftNamed pairLeftSource pairRightSource
    pairLeftNamed pairRightNamed origin policy shape matching
  obtain ⟨rootSame,aligned⟩ := dynamic_mp_aligned input premise left right leftBool rightBool inputHyp premiseHyp
    leftEmpty rightEmpty leftNamed pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin policy
    shape matching block computed
  have checkedDescriptor : BlockChecked policy [input,premise] (mpResult input premise right)
      (block.1,DynamicModusPonensTemplates.assembled.2) := by
    simpa only [rootSame,Prod.mk.eta] using checked
  have safe : GraphRelocationEmission.SafeBlock 2 DynamicModusPonensTemplates.assembled.1.length
      DynamicModusPonensTemplates.assembled := GraphRelocationEmission.safeBlock_of_checked
    (premiseCount := 2) DynamicModusPonensTemplates.assembled block.1
    (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)
    [input,premise] (mpResult input premise right) rfl aligned checkedDescriptor
  have lengthSame : DynamicModusPonensTemplates.assembled.1.length=58 :=
    (List.Forall₂.length_eq aligned).trans size
  rw [lengthSame] at safe
  refine ⟨safe,block,computed,checked,size,rootSame,aligned,?_⟩
  intro roots base earlier
  have outputs := RelocatedCertificateInsertion.outputs 58 DynamicModusPonensTemplates.assembled safe block.1
    (DynamicModusPonensTemplates.fields input premise left right pairLeftSource pairRightSource origin)
    roots base earlier aligned
  exact ⟨by simpa only [rootSame,Prod.mk.eta] using outputs⟩

end Mettapedia.Languages.HOLLight.DynamicModusPonensRelocation
