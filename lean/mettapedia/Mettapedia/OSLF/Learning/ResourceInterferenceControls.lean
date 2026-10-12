import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion
import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCostImage

open Mettapedia.OSLF.Framework

/-!
# Operational controls for the resource-receipt boundary

The declared compiler profile is the existing typed output-only resource frame.
Name possession is a separate capability inventory. The dormant context also
contains the metabolic name literally in its suspended continuation. This is a
closed-system control with supplied capabilities, not a name-discovery theorem.
The larger resource-protocol compiler is compared separately: it does encode a
bare receiver. No identification with all internalized located-stack contexts
is made.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Learning.ResourceInterferenceControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Canonical CanonicalTyping CanonicalBag CanonicalReaction HeaderInversion
open LanguageDefGSLT LanguageDefRewriteSystem CanonicalStepperCompleteness
open ResourcePredation
open Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTRhoInternalization
open Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCostImage

structure ResourceContext where
  heldChannels : List Nat
  frame : List Pattern

def HasCapability (context : ResourceContext) (channel : Nat) : Prop :=
  channel ∈ context.heldChannels

/-- The source grammar is the existing finite typed credit-channel frame. -/
noncomputable def Image (context : ResourceContext) : Prop :=
  ResourceOnlyImageFrame (Synapse := Unit) (Neuron := Unit)
    (receiptSlots := 1) (signalSlots := 1) (creditBudget := 1) context.frame

noncomputable def frameContext (channels : List (CreditImageChannel Unit Unit 1 1 1))
    (heldChannels : List Nat) : ResourceContext :=
  ⟨heldChannels, channels.map fun channel => resourceToken (imageChannelCode channel)⟩

theorem compiled_frame_in_image
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (heldChannels : List Nat) :
    Image (frameContext channels heldChannels) := ⟨channels, rfl⟩

private def headerPrime (header : Header) (closed : ClosedRhoProcess header.pattern) :
    { pattern : Pattern // IsPrime pattern } :=
  ⟨canonicalize header.pattern,
    (RhoClosedTerm.canonicalize (⟨header.pattern, closed⟩ : RhoProcess)).2,
    canonicalize_isCanonical _, header.canonical_nonunit, fun _ => header.canonical_nonbag _ none⟩

private def tokenPrime (channel : Nat) : { pattern : Pattern // IsPrime pattern } :=
  headerPrime (.output (markerName channel) rhoZero) (resourceToken_closed channel)

private def receiverPrime (channel : Nat) (body : Pattern) (closed : ClosedRhoProcess body) :
    { pattern : Pattern // IsPrime pattern } :=
  headerPrime (.input (markerName channel) body) (awaitResource_closed channel closed)

private theorem tokenPrime_shape (channel : Nat) :
    (tokenPrime channel).1 = output (canonicalize (markerName channel)) rhoZero := by
  simp only [tokenPrime, headerPrime, Header.pattern, canonicalize_output]
  rfl

private theorem receiverPrime_shape (channel : Nat) (body : Pattern)
    (closed : ClosedRhoProcess body) :
    (receiverPrime channel body closed).1 =
      input (canonicalize (markerName channel)) (canonicalize body) := by
  simp only [receiverPrime, headerPrime, Header.pattern, canonicalize_input]
  rfl

private def token (key : Nat) (origin : Origin) (channel : Nat) : Occurrence :=
  ⟨key, origin, tokenPrime channel⟩

private def receiver (key : Nat) (origin : Origin) (channel : Nat)
    (body : Pattern) (closed : ClosedRhoProcess body) : Occurrence :=
  ⟨key, origin, receiverPrime channel body closed⟩

def harvestingContext : ResourceContext := ⟨[0], [predator 0]⟩

def dormantContext : ResourceContext :=
  ⟨[0, 1], [awaitResource 1 (resourceToken 0)]⟩

theorem harvesting_holds_name : HasCapability harvestingContext 0 := by
  simp [HasCapability, harvestingContext]

theorem dormant_holds_name : HasCapability dormantContext 0 := by
  simp [HasCapability, dormantContext]

private theorem input_frame_not_image (heldChannels : List Nat) (channel : Nat)
    (body : Pattern) : ¬ Image ⟨heldChannels, [awaitResource channel body]⟩ := by
  rintro ⟨channels, equal⟩
  have member : awaitResource channel body ∈
      channels.map (fun c => resourceToken (imageChannelCode c)) := by
    rw [← equal]
    simp
  obtain ⟨c, _, impossible⟩ := List.mem_map.mp member
  simp [awaitResource, resourceToken, commIn, commOut] at impossible

theorem harvesting_not_image : ¬ Image harvestingContext :=
  input_frame_not_image [0] 0 rhoZero

theorem dormant_not_image : ¬ Image dormantContext :=
  input_frame_not_image [0, 1] 1 (resourceToken 0)

/-- Key 1 is the protected message; key 0 is the contextual receiver. -/
def harvestingConfiguration : Configuration :=
  Configuration.ofList [receiver 0 .context 0 rhoZero rhoZero_closed, token 1 .computation 0]

def legitimateConfiguration : Configuration :=
  Configuration.ofList [receiver 0 .computation 0 rhoZero rhoZero_closed, token 1 .computation 0]

def dormantConfiguration : Configuration :=
  Configuration.ofList [receiver 0 .context 1 (resourceToken 0) (resourceToken_closed 0),
    token 1 .computation 0]

private def zeroRule : GroundComm where
  inputChannel := canonicalize (markerName 0)
  outputChannel := canonicalize (markerName 0)
  body := rhoZero
  payload := rhoZero
  inputPrime := by
    simpa only [receiverPrime_shape, show canonicalize rhoZero = rhoZero from rfl] using (receiverPrime 0 rhoZero rhoZero_closed).2
  outputPrime := by
    simpa only [tokenPrime_shape] using (tokenPrime 0).2
  channels := rfl

def harvestingFiring : Firing harvestingConfiguration where
  inputIndex := ⟨0, by simp [harvestingConfiguration, Configuration.ofList]⟩
  outputIndex := ⟨0, by simp [harvestingConfiguration, Configuration.ofList]⟩
  rule := zeroRule
  inputAt := receiverPrime_shape 0 rhoZero rhoZero_closed
  outputAt := tokenPrime_shape 0

def legitimateFiring : Firing legitimateConfiguration where
  inputIndex := ⟨0, by simp [legitimateConfiguration, Configuration.ofList]⟩
  outputIndex := ⟨0, by simp [legitimateConfiguration, Configuration.ofList]⟩
  rule := zeroRule
  inputAt := receiverPrime_shape 0 rhoZero rhoZero_closed
  outputAt := tokenPrime_shape 0

/-- The actual public step and its chosen contextual receipt are both supplied. -/
theorem actual_harvesting_communication :
    HarvestAt 1 harvestingFiring ∧
      rhoLanguageDefGSLT.Step (readout harvestingConfiguration)
        (readout harvestingFiring.target) :=
  ⟨⟨rfl, rfl, rfl⟩, harvestingFiring.public_step⟩

theorem harvesting_configuration_distinct : Distinct harvestingConfiguration := by
  simp [Distinct, harvestingConfiguration, Configuration.ofList, receiver, token]

theorem harvested_occurrence_removed :
    ∀ occurrence ∈ harvestingFiring.target.occurrences, occurrence.key ≠ 1 :=
  harvestingFiring.resource_key_removed harvesting_configuration_distinct

theorem legitimate_spending_is_not_harvest :
    rhoLanguageDefGSLT.Step (readout legitimateConfiguration)
      (readout legitimateFiring.target) ∧ ¬ HarvestAt 1 legitimateFiring := by
  refine ⟨legitimateFiring.public_step, ?_⟩
  simp [HarvestAt, Firing.receiver, legitimateFiring, legitimateConfiguration, Configuration.ofList, receiver]

/-- No public scheduling or equation transport enables the suspended receiver. -/
theorem dormant_no_firing (firing : Firing dormantConfiguration) : False := by
  have inputMember := List.getElem_mem firing.inputIndex.isLt
  have outputMember := List.mem_of_mem_eraseIdx (List.getElem_mem firing.outputIndex.isLt)
  have inputShape := firing.inputAt
  have outputShape := firing.outputAt
  rcases List.mem_cons.mp inputMember with first | last
  · rw [first] at inputShape
    have subjects : canonicalize (markerName 1) = firing.rule.inputChannel := by
      have fields : canonicalize (markerName 1) = firing.rule.inputChannel ∧
          canonicalize (resourceToken 0) = firing.rule.body := by
        simpa only [receiver, receiverPrime_shape, input, Pattern.apply.injEq,
          List.cons.injEq, Pattern.lambda.injEq, true_and, and_true] using inputShape
      exact fields.1
    rcases List.mem_cons.mp outputMember with same | rest
    · rw [same] at outputShape
      simp only [receiver, receiverPrime_shape, input, output] at outputShape
      simp at outputShape
    · have resourceEqual :
          (dormantConfiguration.occurrences.eraseIdx firing.inputIndex.val)[firing.outputIndex.val] =
            token 1 .computation 0 := by simpa using rest
      rw [resourceEqual] at outputShape
      have outputs : canonicalize (markerName 0) = firing.rule.outputChannel := by
        have fields : canonicalize (markerName 0) = firing.rule.outputChannel ∧
            rhoZero = firing.rule.payload := by
          simpa only [token, tokenPrime_shape, output, Pattern.apply.injEq,
            List.cons.injEq, true_and, and_true] using outputShape
        exact fields.1
      have channels := firing.rule.channels
      rw [← subjects, ← outputs] at channels
      have unequal : canonicalize (canonicalize (markerName 1)) ≠
          canonicalize (canonicalize (markerName 0)) := by decide
      exact unequal channels
  · have resourceEqual : dormantConfiguration.occurrences[firing.inputIndex.val] =
        token 1 .computation 0 := by simpa using last
    rw [resourceEqual] at inputShape
    simp [token, tokenPrime_shape, input, output] at inputShape

theorem dormant_never_harvests : ¬ CanHarvest 1 dormantConfiguration :=
  never_harvest_of_no_firing dormant_no_firing 1

theorem dormant_every_public_execution_is_quiet {target : RhoProcess}
    (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step
      (readout dormantConfiguration) target) :
    target = readout dormantConfiguration :=
  public_history_quiet_of_no_firing dormant_no_firing history

/-- The unrestricted non-image/name-possession converse fails in this profile. -/
theorem non_image_possession_not_sufficient :
    ¬ Image dormantContext ∧ HasCapability dormantContext 0 ∧
      ¬ CanHarvest 1 dormantConfiguration :=
  ⟨dormant_not_image, dormant_holds_name, dormant_never_harvests⟩

/-- A different existing compiler image does contain the bare receiver. -/
theorem receiver_in_larger_protocol_image (channel : Nat) :
    ∃ protocol : ResourceProtocol, protocol.toRho = predator channel :=
  ⟨.await channel .empty, rfl⟩

/-- Annotate the actual emitted frame, preserving every repeated channel. -/
noncomputable def compiledOccurrences
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat) : Configuration :=
  Configuration.ofList (List.ofFn fun position : Fin channels.length =>
    token (firstKey + position.val) .context (imageChannelCode channels[position.val]))

theorem compiled_occurrences_patterns
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat) :
    patterns (compiledOccurrences channels firstKey) =
      ((frameContext channels []).frame).map canonicalize := by
  simp only [patterns, compiledOccurrences, Configuration.ofList, List.map_ofFn]
  change List.ofFn (fun position : Fin channels.length =>
      canonicalize (resourceToken (imageChannelCode channels[position.val]))) = _
  simpa only [frameContext, List.map_map, Function.comp_def] using
    (List.ofFn_getElem_eq_map channels
      (fun channel => canonicalize (resourceToken (imageChannelCode channel))))

/-- The annotation has the same canonical inventory as the independently
emitted raw compiler frame, including duplicate resources. -/
theorem compiled_occurrences_readout
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat) :
    inventory (compiledOccurrences channels firstKey) =
      fromProcess (ofList (frameContext channels []).frame
        (resourceOnlyImageFrame_closed (compiled_frame_in_image channels []))) := by
  apply Subtype.ext
  rw [fromProcess_ofList_inventory]
  change (patterns (compiledOccurrences channels firstKey) : Multiset Pattern) = _
  rw [compiled_occurrences_patterns]
  have nonzero : ∀ pattern ∈ ((frameContext channels []).frame).map canonicalize,
      pattern ≠ .apply "PZero" [] := by
    intro pattern member
    obtain ⟨original, inFrame, rfl⟩ := List.mem_map.mp member
    obtain ⟨channel, _, rfl⟩ := List.mem_map.mp inFrame
    exact (tokenPrime (imageChannelCode channel)).2.2.2.1
  have nonbag : ∀ pattern ∈ ((frameContext channels []).frame).map canonicalize,
      ∀ elements, pattern ≠ .collection .hashBag elements none := by
    intro pattern member
    obtain ⟨original, inFrame, rfl⟩ := List.mem_map.mp member
    obtain ⟨channel, _, rfl⟩ := List.mem_map.mp inFrame
    exact (tokenPrime (imageChannelCode channel)).2.2.2.2
  rw [bagContents_eq_self nonzero nonbag]

theorem compiled_occurrences_context_outputs
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat) :
    ContextOutputs (compiledOccurrences channels firstKey) := by
  intro occurrence member _
  change occurrence ∈ List.ofFn _ at member
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
  exact ⟨canonicalize (markerName (imageChannelCode channels[position.val])),
    rhoZero, tokenPrime_shape _⟩

/-- Every finite execution in the actual output-only compiler frame is
protected against contextual receipt, while computation receivers may spend. -/
theorem compiled_frame_never_harvests
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat)
    (computation : Configuration)
    (owned : ∀ occurrence ∈ computation.occurrences, occurrence.origin = .computation)
    (resourceKey : Nat) :
    ¬ CanHarvest resourceKey (Configuration.join computation (compiledOccurrences channels firstKey)) := by
  apply contextOutputs_never_harvest
  intro occurrence member context
  change occurrence ∈ computation.occurrences ++
    (compiledOccurrences channels firstKey).occurrences at member
  rcases List.mem_append.mp member with own | frame
  · have impossible := (owned occurrence own).symm.trans context
    cases impossible
  · exact compiled_occurrences_context_outputs channels firstKey occurrence frame context

/-- The dormant executable body literally retains the supplied metabolic name
inside a guarded resource output; possession was not defined by readiness. -/
theorem dormant_suspended_metabolic_name :
    dormantContext.frame = [input (markerName 1) (output (markerName 0) rhoZero)] := rfl

private theorem zeroRule_reactum_empty : zeroRule.reactum = CanonicalBag.empty := by
  apply Subtype.ext
  change (CanonicalBag.fromProcess zeroRule.result).1 = 0
  change (normalizeBagElements [.apply "PZero" []] : Multiset Pattern) = 0
  simp [normalizeBagElements, bagSplice]
  exact (sortPatterns_perm []).symm.eq_nil

private theorem zeroRule_spawned_empty {source : Configuration}
    (firing : Firing source) (rule : firing.rule = zeroRule) : firing.spawned = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp only [Firing.spawned, List.length_ofFn]
  rw [rule, zeroRule_reactum_empty]
  simp [CanonicalBag.empty, ordered]

theorem harvesting_target_empty : harvestingFiring.target.occurrences = [] := by
  change harvestingFiring.spawned ++ harvestingFiring.tail.occurrences = []
  rw [zeroRule_spawned_empty harvestingFiring rfl]
  rfl

theorem legitimate_target_empty : legitimateFiring.target.occurrences = [] := by
  change legitimateFiring.spawned ++ legitimateFiring.tail.occurrences = []
  rw [zeroRule_spawned_empty legitimateFiring rfl]
  rfl

/-- Different receiver origins can have the same endpoint. Endpoint reflection
alone therefore cannot decide whether the resource was harvested. -/
theorem same_endpoint_different_receiver_origins :
    readout harvestingFiring.target = readout legitimateFiring.target ∧
      HarvestAt 1 harvestingFiring ∧ ¬ HarvestAt 1 legitimateFiring := by
  refine ⟨?_, actual_harvesting_communication.1, legitimate_spending_is_not_harvest.2⟩
  apply congrArg toProcess
  apply Subtype.ext
  change (harvestingFiring.target.occurrences.map (fun occurrence => occurrence.term.1) :
    Multiset Pattern) =
      (legitimateFiring.target.occurrences.map (fun occurrence => occurrence.term.1) :
        Multiset Pattern)
  rw [harvesting_target_empty, legitimate_target_empty]

def duplicateConfiguration : Configuration :=
  Configuration.ofList [receiver 0 .context 0 rhoZero rhoZero_closed,
    token 1 .computation 0, token 2 .computation 0]

def duplicateFirstFiring : Firing duplicateConfiguration where
  inputIndex := ⟨0, by simp [duplicateConfiguration, Configuration.ofList]⟩
  outputIndex := ⟨0, by simp [duplicateConfiguration, Configuration.ofList]⟩
  rule := zeroRule
  inputAt := receiverPrime_shape 0 rhoZero rhoZero_closed
  outputAt := tokenPrime_shape 0

def duplicateSecondFiring : Firing duplicateConfiguration where
  inputIndex := ⟨0, by simp [duplicateConfiguration, Configuration.ofList]⟩
  outputIndex := ⟨1, by simp [duplicateConfiguration, Configuration.ofList]⟩
  rule := zeroRule
  inputAt := receiverPrime_shape 0 rhoZero rhoZero_closed
  outputAt := tokenPrime_shape 0

theorem duplicate_occurrences_retained :
    duplicateFirstFiring.target.occurrences = [token 2 .computation 0] ∧
      duplicateSecondFiring.target.occurrences = [token 1 .computation 0] ∧
      HarvestAt 1 duplicateFirstFiring ∧ HarvestAt 2 duplicateSecondFiring := by
  refine ⟨?_, ?_, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · change duplicateFirstFiring.spawned ++ duplicateFirstFiring.tail.occurrences = _
    rw [zeroRule_spawned_empty duplicateFirstFiring rfl]
    rfl
  · change duplicateSecondFiring.spawned ++ duplicateSecondFiring.tail.occurrences = _
    rw [zeroRule_spawned_empty duplicateSecondFiring rfl]
    simp [Firing.tail, duplicateSecondFiring, duplicateConfiguration, Configuration.ofList]

theorem duplicate_endpoints_agree :
    readout duplicateFirstFiring.target = readout duplicateSecondFiring.target := by
  apply congrArg toProcess
  apply Subtype.ext
  change (duplicateFirstFiring.target.occurrences.map (fun occurrence => occurrence.term.1) :
    Multiset Pattern) =
      (duplicateSecondFiring.target.occurrences.map (fun occurrence => occurrence.term.1) :
        Multiset Pattern)
  rw [duplicate_occurrences_retained.1, duplicate_occurrences_retained.2.1]
  rfl

/-- Protection is not preservation of contents: legitimate spending really
consumes the message even though contextual harvesting never occurs. -/
theorem legitimate_spending_removes_resource_without_harvest :
    legitimateFiring.target.occurrences = [] ∧ ¬ CanHarvest 1 legitimateConfiguration := by
  refine ⟨legitimate_target_empty, contextOutputs_never_harvest ?_ 1⟩
  intro occurrence member context
  simp only [legitimateConfiguration, Configuration.ofList, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> cases context

/-- Initial origins are compared separately with the surrounding frame and
protected process, not inferred from the combined terminal observation. -/
def ResourceContext.Realizes (context : ResourceContext) (protectedProcess : RhoProcess)
    (configuration : Configuration) : Prop :=
  ∃ closedFrame : ∀ process ∈ context.frame, ClosedRhoProcess process,
    inventory (configuration.selectOrigin .context) = fromProcess (ofList context.frame closedFrame) ∧
    inventory (configuration.selectOrigin .computation) = fromProcess protectedProcess

def protectedMessage : RhoProcess := ⟨resourceToken 0, resourceToken_closed 0⟩

private theorem singleton_token_inventory :
    inventory (Configuration.ofList [token 1 .computation 0]) =
      fromProcess protectedMessage := by
  apply Subtype.ext
  rw [fromProcess_inventory]
  change ([canonicalize (resourceToken 0)] : Multiset Pattern) =
    (bagContents [canonicalize (resourceToken 0)] : Multiset Pattern)
  rw [bagContents_eq_self
    (by intro pattern member; rcases List.mem_singleton.mp member with rfl; exact (tokenPrime 0).2.2.2.1)
    (by intro pattern member; rcases List.mem_singleton.mp member with rfl; exact (tokenPrime 0).2.2.2.2)]

private theorem singleton_receiver_inventory (channel : Nat) (body : Pattern)
    (closed : ClosedRhoProcess body) :
    inventory (Configuration.ofList [receiver 0 .context channel body closed]) =
      fromProcess (ofList [awaitResource channel body] (by
        intro process member
        have equal : process = awaitResource channel body := by simpa using member
        subst process
        exact awaitResource_closed channel closed)) := by
  apply Subtype.ext
  rw [fromProcess_ofList_inventory]
  change ([canonicalize (awaitResource channel body)] : Multiset Pattern) =
    (bagContents [canonicalize (awaitResource channel body)] : Multiset Pattern)
  rw [bagContents_eq_self
    (by intro pattern member; rcases List.mem_singleton.mp member with rfl; exact (receiverPrime channel body closed).2.2.2.1)
    (by intro pattern member; rcases List.mem_singleton.mp member with rfl; exact (receiverPrime channel body closed).2.2.2.2)]

theorem harvesting_context_realized :
    harvestingContext.Realizes protectedMessage harvestingConfiguration := by
  refine ⟨?_, ?_, ?_⟩
  · intro process member
    have equal : process = predator 0 := by simpa [harvestingContext] using member
    subst process
    exact awaitResource_closed 0 rhoZero_closed
  · exact singleton_receiver_inventory 0 rhoZero rhoZero_closed
  · exact singleton_token_inventory

theorem dormant_context_realized :
    dormantContext.Realizes protectedMessage dormantConfiguration := by
  refine ⟨?_, ?_, ?_⟩
  · intro process member
    have equal : process = awaitResource 1 (resourceToken 0) := by
      simpa [dormantContext] using member
    subst process
    exact awaitResource_closed 1 (resourceToken_closed 0)
  · exact singleton_receiver_inventory 1 (resourceToken 0) (resourceToken_closed 0)
  · exact singleton_token_inventory

theorem dormant_configuration_distinct : Distinct dormantConfiguration := by
  simp [Distinct, dormantConfiguration, Configuration.ofList, receiver, token]

theorem harvesting_initial_resource : ProtectedResource 1 harvestingConfiguration := by
  refine ⟨harvesting_configuration_distinct, token 1 .computation 0, ?_, rfl, rfl,
    canonicalize (markerName 0), rhoZero, tokenPrime_shape 0⟩
  simp [harvestingConfiguration, Configuration.ofList]

theorem dormant_initial_resource : ProtectedResource 1 dormantConfiguration := by
  refine ⟨dormant_configuration_distinct, token 1 .computation 0, ?_, rfl, rfl,
    canonicalize (markerName 0), rhoZero, tokenPrime_shape 0⟩
  simp [dormantConfiguration, Configuration.ofList]

theorem harvesting_possible : CanHarvest 1 harvestingConfiguration :=
  ⟨harvesting_initial_resource, harvestingConfiguration, .refl,
    harvestingFiring, actual_harvesting_communication.1⟩

/-- The counterexample concerns this very context and this very initial
resource; it covers all finite closed executions. -/
theorem operational_possession_separator :
    ¬ Image dormantContext ∧ HasCapability dormantContext 0 ∧
      dormantContext.Realizes protectedMessage dormantConfiguration ∧
      ProtectedResource 1 dormantConfiguration ∧ ¬ CanHarvest 1 dormantConfiguration :=
  ⟨dormant_not_image, dormant_holds_name, dormant_context_realized,
    dormant_initial_resource, dormant_never_harvests⟩

/-- After this receipt, every later firing is unable to select the old key. -/
theorem harvested_key_never_reused {future : Configuration}
    (history : History harvestingFiring.target future) (firing : Firing future) :
    firing.resource.key ≠ 1 :=
  harvestingFiring.consumed_key_never_reappears harvesting_configuration_distinct history
    firing.resource (List.mem_of_mem_eraseIdx (List.getElem_mem firing.outputIndex.isLt))

/-- The independently authored closed parallel plugging operation. -/
def ResourceContext.plug (context : ResourceContext) (protectedProcess : RhoProcess)
    (closedFrame : ∀ process ∈ context.frame, ClosedRhoProcess process) : RhoProcess :=
  ofList (protectedProcess.1 :: context.frame) (by
    intro process member
    rcases List.mem_cons.mp member with rfl | frame
    · exact protectedProcess.2
    · exact closedFrame process frame)

private theorem plug_inventory (context : ResourceContext) (protectedProcess : RhoProcess)
    (closedFrame : ∀ process ∈ context.frame, ClosedRhoProcess process) :
    fromProcess (context.plug protectedProcess closedFrame) =
      append (fromProcess protectedProcess) (fromProcess (ofList context.frame closedFrame)) := by
  apply Subtype.ext
  change (fromProcess (context.plug protectedProcess closedFrame)).1 =
    (fromProcess protectedProcess).1 + (fromProcess (ofList context.frame closedFrame)).1
  rw [ResourceContext.plug, fromProcess_ofList_inventory,
    fromProcess_inventory, fromProcess_ofList_inventory]
  change (bagContents (canonicalize protectedProcess.1 :: context.frame.map canonicalize) :
    Multiset Pattern) =
      (bagContents [canonicalize protectedProcess.1] : Multiset Pattern) +
      (bagContents (context.frame.map canonicalize) : Multiset Pattern)
  have split : bagContents (canonicalize protectedProcess.1 :: context.frame.map canonicalize) =
      bagContents [canonicalize protectedProcess.1] ++
        bagContents (context.frame.map canonicalize) := by
    simp [bagContents, List.filter_append]
  rw [split]
  exact (Multiset.coe_add _ _).symm

/-- The provenance projections assemble to the actual plugged closed process. -/
theorem ResourceContext.Realizes.plug_readout {context : ResourceContext}
    {protectedProcess : RhoProcess} {configuration : Configuration}
    (realizes : context.Realizes protectedProcess configuration) :
    ∃ closedFrame, rhoProcessEquations.r (readout configuration)
      (context.plug protectedProcess closedFrame) := by
  obtain ⟨closedFrame, contextual, computation⟩ := realizes
  refine ⟨closedFrame, (fromProcess_eq_iff _ _).mp ?_⟩
  rw [readout, fromProcess_toProcess, inventory_origin_partition,
    contextual, computation, plug_inventory]

private theorem compiled_occurrences_owned
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat)
    (occurrence : Occurrence)
    (member : occurrence ∈ (compiledOccurrences channels firstKey).occurrences) :
    occurrence.origin = .context := by
  change occurrence ∈ List.ofFn _ at member
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
  rfl

/-- The two actors of the annotated assembly are the independently emitted
compiler frame and the supplied computation, respectively. -/
theorem compiled_frame_realizes
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (heldChannels : List Nat)
    (firstKey : Nat) (computation : Configuration)
    (owned : ∀ occurrence ∈ computation.occurrences, occurrence.origin = .computation) :
    (frameContext channels heldChannels).Realizes (readout computation)
      (Configuration.join computation (compiledOccurrences channels firstKey)) := by
  have ownSelf : computation.occurrences.filter
      (fun occurrence => occurrence.origin == .computation) = computation.occurrences :=
    List.filter_eq_self.mpr (by intro occurrence member; simp [owned occurrence member])
  have ownOther : computation.occurrences.filter
      (fun occurrence => occurrence.origin == .context) = [] :=
    List.filter_eq_nil_iff.mpr (by intro occurrence member; simp [owned occurrence member])
  have frameSelf : (compiledOccurrences channels firstKey).occurrences.filter
      (fun occurrence => occurrence.origin == .context) =
        (compiledOccurrences channels firstKey).occurrences :=
    List.filter_eq_self.mpr (by
      intro occurrence member
      simp [compiled_occurrences_owned channels firstKey occurrence member])
  have frameOther : (compiledOccurrences channels firstKey).occurrences.filter
      (fun occurrence => occurrence.origin == .computation) = [] :=
    List.filter_eq_nil_iff.mpr (by
      intro occurrence member
      simp [compiled_occurrences_owned channels firstKey occurrence member])
  refine ⟨resourceOnlyImageFrame_closed (compiled_frame_in_image channels heldChannels), ?_, ?_⟩
  · unfold inventory patterns Configuration.selectOrigin Configuration.join
    simp only [List.filter_append, ownOther, frameSelf, List.nil_append]
    exact compiled_occurrences_readout channels firstKey
  · unfold inventory patterns Configuration.selectOrigin Configuration.join
    simp only [List.filter_append, ownSelf, frameOther, List.append_nil]
    exact (fromProcess_toProcess (inventory computation)).symm

theorem compiled_occurrences_distinct
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat) :
    Distinct (compiledOccurrences channels firstKey) := by
  simp only [Distinct, compiledOccurrences, Configuration.ofList, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro first second equal
  apply Fin.ext
  change firstKey + first.val = firstKey + second.val at equal
  omega

/-- Fresh frame keys preserve the independently designated computation resource. -/
theorem compiled_frame_retains_resource
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (firstKey : Nat)
    (computation : Configuration) (freshFrame : computation.nextKey ≤ firstKey)
    (resourceKey : Nat) (protectedResource : ProtectedResource resourceKey computation) :
    ProtectedResource resourceKey
      (Configuration.join computation (compiledOccurrences channels firstKey)) := by
  obtain ⟨distinct, occurrence, member, key, origin, channel, payload, shape⟩ := protectedResource
  refine ⟨?_, occurrence, List.mem_append_left _ member, key, origin, channel, payload, shape⟩
  change ((computation.occurrences ++ (compiledOccurrences channels firstKey).occurrences).map
    Occurrence.key).Nodup
  rw [List.map_append, List.nodup_append]
  refine ⟨distinct, compiled_occurrences_distinct channels firstKey, ?_⟩
  intro leftKey left rightKey right equal
  obtain ⟨oldOccurrence, oldMember, oldKey⟩ := List.mem_map.mp left
  obtain ⟨newOccurrence, newMember, newKey⟩ := List.mem_map.mp right
  have upper := computation.reserved oldOccurrence oldMember
  change newOccurrence ∈ List.ofFn _ at newMember
  obtain ⟨position, occurrenceEqual⟩ := List.mem_ofFn.mp newMember
  subst newOccurrence
  change firstKey + position.val = rightKey at newKey
  omega

/-- A scoped protection contract for an actual compiled frame, its separate
actors and a present resource. It does not enlarge the compiler context image. -/
theorem compiled_frame_protection
    (channels : List (CreditImageChannel Unit Unit 1 1 1)) (heldChannels : List Nat)
    (firstKey : Nat) (computation : Configuration)
    (owned : ∀ occurrence ∈ computation.occurrences, occurrence.origin = .computation)
    (freshFrame : computation.nextKey ≤ firstKey)
    (resourceKey : Nat) (protectedResource : ProtectedResource resourceKey computation) :
    Image (frameContext channels heldChannels) ∧
      (frameContext channels heldChannels).Realizes (readout computation)
        (Configuration.join computation (compiledOccurrences channels firstKey)) ∧
      ProtectedResource resourceKey
        (Configuration.join computation (compiledOccurrences channels firstKey)) ∧
      ¬ CanHarvest resourceKey
        (Configuration.join computation (compiledOccurrences channels firstKey)) :=
  ⟨compiled_frame_in_image channels heldChannels,
    compiled_frame_realizes channels heldChannels firstKey computation owned,
    compiled_frame_retains_resource channels firstKey computation freshFrame resourceKey protectedResource,
    compiled_frame_never_harvests channels firstKey computation owned resourceKey⟩

end Mettapedia.OSLF.Learning.ResourceInterferenceControls
