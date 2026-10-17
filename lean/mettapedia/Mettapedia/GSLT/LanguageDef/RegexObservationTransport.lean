import Mettapedia.GSLT.LanguageDef.RegexObservationKernel

/-!
# Transport of full intrinsic regex observations

Pointwise agreement of independently authorized instruction lookups preserves
the complete recursive observation, not merely recognition. Simple-fold
providers may also choose different canonical representatives of the same
equivalence classes: only their induced comparison is observed by backrefs.
Capture contents, branch words and direction remain part of the result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexObservationTransport

open RegexDependentObservation
open RegexObservationKernel

/-- Providers can rename canonical representatives while retaining precisely
the same comparison relation on original input scalars. -/
def ProviderEquivalent (first second : Interpretation) : Prop :=
  ∀ left right, (first.unicodeCanonical left == first.unicodeCanonical right) =
    (second.unicodeCanonical left == second.unicodeCanonical right)

theorem equivalent_congr (first second : Interpretation) (same : ProviderEquivalent first second)
    (mode : Comparison) (left right : Nat) :
    equivalent first mode left right = equivalent second mode left right := by
  cases mode with
  | exact | asciiFold => rfl
  | unicodeFold => exact same left right

theorem pairwiseEquivalent_congr (source target : Interpretation) (same : ProviderEquivalent source target)
    (mode : Comparison) (left right : List Nat) :
    pairwiseEquivalent source mode left right = pairwiseEquivalent target mode left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head tail ih =>
      cases right with
      | nil => rfl
      | cons other rest =>
          simp only [pairwiseEquivalent, List.all₂]
          rw [equivalent_congr source target same]
          simpa only [pairwiseEquivalent] using
            congrArg (fun rest => if equivalent target mode head other = true then rest else false) (ih rest)

theorem backreference_congr {groups length : Nat} (first second : Interpretation)
    (same : ProviderEquivalent first second) (input : Fin length → Nat)
    (direction : Direction) (mode : Comparison) (captures : Captures groups length)
    (group : Fin groups) (position : Fin (length + 1)) :
    backreference first input direction mode captures group position =
      backreference second input direction mode captures group position := by
  have comparisons : pairwiseEquivalent first mode = pairwiseEquivalent second mode := by
    funext left right
    exact pairwiseEquivalent_congr first second same mode left right
  simp only [backreference, comparisons]

theorem action_provider_congr {states groups length : Nat} (first second : Interpretation)
    (same : ProviderEquivalent first second) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (body : BodyObservation states groups length)
    (configuration : Configuration states groups length) :
    action first input direction code body configuration = action second input direction code body configuration := by
  simp only [action, backreference_congr first second same]

theorem observedAction_provider_congr {states groups length : Nat} (first second : Interpretation)
    (same : ProviderEquivalent first second) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups)
    (body : LookKind → Fin states → Configuration states groups length → Option (Winner states groups length))
    (configuration : Configuration states groups length) :
    RegexObservationTrace.observedAction first input direction code body configuration =
      RegexObservationTrace.observedAction second input direction code body configuration := by
  simp only [RegexObservationTrace.observedAction, action_provider_congr first second same]

theorem localWinner_congr {states groups length : Nat} (first second : Observation states groups length)
    (same : ∀ direction eligible position captures,
      first direction eligible position captures = second direction eligible position captures)
    (kind : LookKind) (caller : Configuration states groups length) :
    localWinner first kind caller = localWinner second kind caller := by
  have equal : first = second := funext fun direction => funext fun eligible =>
    funext fun position => funext fun captures => same direction eligible position captures
  rw [equal]

theorem controlAction_provider_congr {states groups length : Nat} (first second : Interpretation)
    (same : ProviderEquivalent first second) (input : Fin length → Nat) (direction : Direction)
    (code : Fin states → Instruction states groups) (root : Fin states)
    (recurse : ∀ entry, DirectBodyCall code entry root → Observation states groups length)
    (configuration : Licensed code length root) :
    controlAction first input direction code root recurse configuration =
      controlAction second input direction code root recurse configuration := by
  simp only [controlAction, observedAction_provider_congr first second same]

theorem layer_provider_congr {states groups length : Nat} (first second : Interpretation)
    (same : ProviderEquivalent first second) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (root : Fin states)
    (recurse : ∀ entry, DirectBodyCall code entry root → Observation states groups length) :
    layer first input code root recurse = layer second input code root recurse := by
  funext direction eligible position captures
  simp only [layer, controlAction_provider_congr first second same]

theorem evaluate_provider_congr {states groups length : Nat} (first second : Interpretation)
    (same : ProviderEquivalent first second) (input : Fin length → Nat)
    (code : Fin states → Instruction states groups) (certificate : Certificate code) (root : Fin states) :
    evaluate first input code certificate root = evaluate second input code certificate root := by
  have layers : layer first input code = layer second input code := by
    funext entry recurse
    exact layer_provider_congr first second same input code entry recurse
  unfold evaluate
  rw [layers]

/-- The premise is local instruction agreement, earned independently of
matching. The conclusion includes nested body observations and all captures. -/
theorem evaluate_code_congr {states groups length : Nat} (interpretation : Interpretation)
    (input : Fin length → Nat) (source target : Fin states → Instruction states groups)
    (sourceCertificate : Certificate source) (targetCertificate : Certificate target)
    (operations : ∀ pc, source pc = target pc) (root : Fin states) :
    evaluate interpretation input source sourceCertificate root =
      evaluate interpretation input target targetCertificate root := by
  have same : source = target := funext operations
  subst target
  exact certificate_independent interpretation input source sourceCertificate targetCertificate root

theorem evaluate_congr {states groups length : Nat} (sourceInterpretation targetInterpretation : Interpretation)
    (providers : ProviderEquivalent sourceInterpretation targetInterpretation)
    (input : Fin length → Nat) (source target : Fin states → Instruction states groups)
    (sourceCertificate : Certificate source) (targetCertificate : Certificate target)
    (operations : ∀ pc, source pc = target pc) (root : Fin states) :
    evaluate sourceInterpretation input source sourceCertificate root =
      evaluate targetInterpretation input target targetCertificate root :=
  (evaluate_provider_congr sourceInterpretation targetInterpretation providers input source sourceCertificate root).trans
    (evaluate_code_congr targetInterpretation input source target sourceCertificate targetCertificate operations root)

namespace Controls

private def identityProvider : Interpretation := ⟨id⟩
private def renamedProvider : Interpretation := ⟨fun scalar => scalar + 1000⟩
private def collapsingProvider : Interpretation := ⟨fun _ => 0⟩

theorem canonical_representative_labels_are_not_observable :
    ProviderEquivalent identityProvider renamedProvider := by
  intro first second
  apply Bool.eq_iff_iff.mpr
  simp [identityProvider, renamedProvider]

theorem backreference_preserves_observation_under_provider_relabeling :
    backreference identityProvider (fun _ : Fin 1 => 97) .forward .unicodeFold
        (fun _ : Fin 1 => .closed 0 1) 0 0 =
      backreference renamedProvider (fun _ : Fin 1 => 97) .forward .unicodeFold
        (fun _ : Fin 1 => .closed 0 1) 0 0 :=
  backreference_congr _ _ canonical_representative_labels_are_not_observable _ _ _ _ _ _

theorem changing_equivalence_classes_is_not_provider_transport :
    ¬ ProviderEquivalent identityProvider collapsingProvider := by
  intro same
  have wrong := same 97 98
  cases wrong

end Controls

end Mettapedia.GSLT.LanguageDef.RegexObservationTransport
