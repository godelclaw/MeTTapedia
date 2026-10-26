import Mettapedia.GSLT.Causality.FactLinearResources
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Rho communication cannot be rendered by keep-only rules up to output barbs

The rho calculus's communication consumes both the output and the input it joins:

  `{n!(q) | for(<-n){0}} ⇝ {0}`.

The output on `n` that the source shows is gone after the step (`comm_loses_output`). A resource system
whose rules keep everything they read only ever grows its bag
(`ResourceInteraction.System.le_of_run_of_keepOnly`), so a test of bags that is closed upwards can never
lose what it saw.

* **No keep-only target** (`keepOnly_not_outputFaithful`): no encoding of rho processes into a keep-only
  resource system is operationally complete (each rho reduction is matched by a run of the target, of any
  length) and reflects the output barb on `n` through an upward-closed test.
* **No fact-only observation** (`factObservation_not_outputFaithful`): in a system that consumes some
  resources, the same holds for any upward-closed test that reads only resources declared facts. The
  output barb must be carried by a linear resource.
* **The obstruction is keeping, not the test** (`consuming_target_tracks_loss`): a two-resource system
  whose single rule consumes an output and an input matches the step, and the upward-closed test "an
  output is present" holds before and fails after.

The barb is read syntactically at the top of a parallel composition; only the two processes of the step
are inspected, so no invariance of the barb under structural congruence is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.KeepOnlyCommBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.GSLT.Causality.ResourceInteraction

/-- An output on the channel `n` among the top-level parallel components. -/
def OutputOn (n : Pattern) : Pattern → Prop
  | .collection .hashBag elements none => ∃ payload, Pattern.apply "POutput" [n, payload] ∈ elements
  | _ => False

/-- The inactive process. -/
def nilProc : Pattern := .collection .hashBag [] none

/-- An output of `q` on `n` beside an input on `n` that continues inactively. -/
def redex (n q : Pattern) : Pattern :=
  .collection .hashBag [.apply "POutput" [n, q], .apply "PInput" [n, .lambda none nilProc]] none

/-- The contractum: the inactive continuation. -/
def contractum : Pattern := .collection .hashBag [nilProc] none

theorem commSubst_nil (q : Pattern) : semanticCommSubst nilProc q = nilProc := rfl

/-- **The communication step** `{n!(q) | for(<-n){0}} ⇝ {0}`. -/
def comm_step (n q : Pattern) : redex n q ⇝ contractum := by
  have step := @Reduces.comm n q nilProc []
  simp only [List.append_nil, commSubst_nil] at step
  exact step

/-- **The step loses the output**: the redex shows an output on `n`, the contractum shows none. -/
theorem comm_loses_output (n q : Pattern) : OutputOn n (redex n q) ∧ ¬ OutputOn n contractum := by
  refine ⟨⟨q, by simp⟩, ?_⟩
  rintro ⟨payload, member⟩
  simp [nilProc] at member

variable {R : Type*} [DecidableEq R] {S : System R}

/-- **No keep-only encoding of rho is faithful to output barbs.** -/
theorem keepOnly_not_outputFaithful (keep : S.KeepOnly) (n : Pattern) (encode : Pattern → Multiset R)
    (test : Multiset R → Prop) (upward : ∀ {M N : Multiset R}, M ≤ N → test M → test N)
    (complete : ∀ {P Q : Pattern}, Nonempty (P ⇝ Q) →
      Relation.ReflTransGen S.theory.rewrites (encode P) (encode Q))
    (reflects : ∀ P, test (encode P) ↔ OutputOn n P) : False :=
  System.keepOnly_not_faithful keep (fun P Q => Nonempty (P ⇝ Q)) (OutputOn n)
    ⟨comm_step n nilProc⟩ (comm_loses_output n nilProc).1 (comm_loses_output n nilProc).2
    encode test upward complete reflects

/-- **No observation of facts alone is faithful to output barbs**, in any system respecting a declaration
of facts. -/
theorem factObservation_not_outputFaithful {fact : R → Prop} [DecidablePred fact]
    (respects : S.ConsumesNoFacts fact) (n : Pattern) (encode : Pattern → Multiset R)
    (test : Multiset R → Prop) (upward : ∀ {M N : Multiset R}, M ≤ N → test M → test N)
    (complete : ∀ {P Q : Pattern}, Nonempty (P ⇝ Q) →
      Relation.ReflTransGen S.theory.rewrites (encode P) (encode Q))
    (reflects : ∀ P, test (System.factPart fact (encode P)) ↔ OutputOn n P) : False :=
  S.factObservation_not_faithful respects (fun P Q => Nonempty (P ⇝ Q)) (OutputOn n)
    ⟨comm_step n nilProc⟩ (comm_loses_output n nilProc).1 (comm_loses_output n nilProc).2
    encode test upward complete reflects

/-! ## Positive control: a consuming target tracks the loss -/

/-- Resources of the control: an output and an input. -/
inductive Endpoint where
  | output | input
  deriving DecidableEq, Repr

/-- One rule: communication consumes an output and an input and produces nothing. -/
def commSystem : System Endpoint where
  Site := Unit
  Instance := fun _ => Unit
  consume := fun _ => {Endpoint.output, Endpoint.input}
  read := fun _ => 0
  produce := fun _ => 0

/-- The two rho processes of the step, as bags of endpoints. -/
def endpoints (P : Pattern) : Multiset Endpoint :=
  if P = contractum then 0 else {Endpoint.output, Endpoint.input}

/-- **The consuming target matches the step and loses the output**, read by the upward-closed test
"an output is present". -/
theorem consuming_target_tracks_loss (n q : Pattern) :
    commSystem.theory.rewrites (endpoints (redex n q)) (endpoints contractum) ∧
      Endpoint.output ∈ endpoints (redex n q) ∧ Endpoint.output ∉ endpoints contractum := by
  have distinct : redex n q ≠ contractum := by simp [redex, contractum]
  simp only [endpoints, distinct, if_false, if_true]
  refine ⟨⟨(), (), ?_, ?_⟩, by decide, by decide⟩
  · unfold System.Enables
    decide
  · unfold System.fire
    decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.KeepOnlyCommBoundary
