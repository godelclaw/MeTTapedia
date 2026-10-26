import Mettapedia.MachineLearning.NeuralNetworks.EquivariantLinearKernel

/-!
# Hidden-neuron permutation symmetry

Navon et al., *Equivariant Architectures for Learning in Deep Weight Spaces*
(ICML 2023, arXiv:2301.12780), Equation (5), act on an MLP parameter
sequence by simultaneously permuting the rows entering an intermediate layer,
its bias coordinates, and the columns leaving that layer.  The transformed
parameters represent the same function.

This file formalizes the two-layer semantic core for finite input and hidden
index types and arbitrary output index types:

* hidden-coordinate pullback acts on incoming and outgoing parameters;
  inverse permutations give the standard left action;
* every pointwise hidden activation gives exactly the same represented output
  after the action;
* every output-only evaluator is therefore invariant;
* an equivariant weight processor maps equivalent parameterizations to
  equivalent outputs;
* pooling across hidden coordinates is invariant;
* probing or editing one distinguished hidden coordinate need not be
  invariant or equivariant.

The orbit readout preserves represented functions, but it is not injective:
a linear-activation scaling example gives equal functions in different orbits.
The results do not characterize every affine equivariant map as in the source's
Theorem 5.1, prove universal approximation, classify scaling symmetries, or
establish empirical performance.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry

noncomputable section

open scoped BigOperators

/-- Parameters of a two-layer network with a pointwise hidden activation.
Weights are functions so the result applies to arbitrary finite index types,
not only `Fin n` matrices. -/
structure TwoLayerParams (Input Hidden Output : Type*) where
  firstWeight : Hidden → Input → ℝ
  hiddenBias : Hidden → ℝ
  secondWeight : Output → Hidden → ℝ
  outputBias : Output → ℝ

variable {Input Hidden Output Result : Type*}

/-- Activity of one hidden coordinate. -/
def hiddenActivation [Fintype Input] (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ) (input : Input → ℝ) (hidden : Hidden) : ℝ :=
  activation ((∑ index, params.firstWeight hidden index * input index) + params.hiddenBias hidden)

/-- The represented two-layer function, with a linear output layer. An
output activation may be postcomposed without changing invariance. -/
def twoLayerOutput [Fintype Input] [Fintype Hidden]
    (params : TwoLayerParams Input Hidden Output) (activation : ℝ → ℝ)
    (input : Input → ℝ) : Output → ℝ :=
  fun output => (∑ hidden, params.secondWeight output hidden *
    hiddenActivation params activation input hidden) + params.outputBias output

/-- Pull hidden coordinates back along an equivalence, including between different carriers. -/
def reindexHidden {Hidden' : Type*} (equiv : Hidden' ≃ Hidden)
    (params : TwoLayerParams Input Hidden Output) : TwoLayerParams Input Hidden' Output where
  firstWeight hidden input := params.firstWeight (equiv hidden) input
  hiddenBias hidden := params.hiddenBias (equiv hidden)
  secondWeight output hidden := params.secondWeight output (equiv hidden)
  outputBias := params.outputBias

/-- Equation (5): pull incoming rows, biases, and outgoing columns back together. -/
def permuteHidden (permutation : Equiv.Perm Hidden) (params : TwoLayerParams Input Hidden Output) :
    TwoLayerParams Input Hidden Output := reindexHidden permutation params

/-- The identity renaming changes no parameter. -/
@[simp] theorem permuteHidden_refl (params : TwoLayerParams Input Hidden Output) :
    permuteHidden (Equiv.refl Hidden) params = params := rfl

/-- Pullbacks compose contravariantly: `first.trans second` applies `second` after `first`. -/
theorem permuteHidden_comp (first second : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    permuteHidden first (permuteHidden second params) =
      permuteHidden (first.trans second) params := rfl

/-- Inverse pullback is the standard left action, consistent with `actVector`. -/
instance hiddenPermutationMulAction :
    MulAction (Equiv.Perm Hidden) (TwoLayerParams Input Hidden Output) where
  smul g params := permuteHidden g⁻¹ params
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The action exposes the inverse pullback without unfolding its typeclass. -/
@[simp] theorem smul_eq_permuteHidden (g : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    g • params = permuteHidden g⁻¹ params := rfl

/-- Hidden activities follow the corresponding original coordinate. -/
@[simp] theorem hiddenActivation_permuteHidden [Fintype Input] (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) (activation : ℝ → ℝ)
    (input : Input → ℝ) (hidden : Hidden) :
    hiddenActivation (permuteHidden permutation params) activation input hidden =
      hiddenActivation params activation input (permutation hidden) := rfl

/-- Evaluation commutes with changing the finite hidden-coordinate carrier. -/
theorem twoLayerOutput_reindexHidden {Hidden' : Type*}
    [Fintype Input] [Fintype Hidden] [Fintype Hidden'] (equiv : Hidden' ≃ Hidden)
    (params : TwoLayerParams Input Hidden Output) (activation : ℝ → ℝ) (input : Input → ℝ) :
    twoLayerOutput (reindexHidden equiv params) activation input =
      twoLayerOutput params activation input := by
  funext output
  exact congrArg (· + params.outputBias output)
    (kernelApply_reindex equiv id params.secondWeight (hiddenActivation params activation input) output)

/-- Simultaneous incoming/bias/outgoing permutation preserves every pointwise
activation and input's represented output. -/
theorem twoLayerOutput_permuteHidden [Fintype Input] [Fintype Hidden]
    (permutation : Equiv.Perm Hidden) (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ) (input : Input → ℝ) :
    twoLayerOutput (permuteHidden permutation params) activation input =
      twoLayerOutput params activation input :=
  twoLayerOutput_reindexHidden permutation params activation input

/-- Every evaluator observing only the represented output is invariant. -/
theorem outputFunctional_permuteHidden [Fintype Input] [Fintype Hidden]
    (functional : (Output → ℝ) → Result) (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) (activation : ℝ → ℝ) (input : Input → ℝ) :
    functional (twoLayerOutput (permuteHidden permutation params) activation input) =
      functional (twoLayerOutput params activation input) := by rw [twoLayerOutput_permuteHidden]

/-- An invariant raw-parameter statistic is constant on permutation orbits. -/
def IsHiddenPermutationInvariant (processor : TwoLayerParams Input Hidden Output → Result) : Prop :=
  ∀ (permutation : Equiv.Perm Hidden) params,
    processor (permuteHidden permutation params) = processor params

/-- An equivariant processor commutes with hidden-coordinate pullback. -/
def IsHiddenPermutationEquivariant
    (processor : TwoLayerParams Input Hidden Output → TwoLayerParams Input Hidden Output) : Prop :=
  ∀ (permutation : Equiv.Perm Hidden) params,
    processor (permuteHidden permutation params) = permuteHidden permutation (processor params)

/-- The represented output is an invariant raw-parameter evaluator. -/
theorem representedOutput_isHiddenPermutationInvariant [Fintype Input] [Fintype Hidden]
    (activation : ℝ → ℝ) (input : Input → ℝ) :
    IsHiddenPermutationInvariant
      (fun params : TwoLayerParams Input Hidden Output => twoLayerOutput params activation input) :=
  fun permutation params => twoLayerOutput_permuteHidden permutation params activation input

/-- Equivariant processors preserve permutation orbits, hence their output readouts.
This does not assert preservation of every pair of functionally equal parameterizations. -/
theorem equivariantProcessor_preserves_output_orbits [Fintype Input] [Fintype Hidden]
    (processor : TwoLayerParams Input Hidden Output → TwoLayerParams Input Hidden Output)
    (processor_equivariant : IsHiddenPermutationEquivariant processor)
    (permutation : Equiv.Perm Hidden) (params : TwoLayerParams Input Hidden Output)
    (activation : ℝ → ℝ) (input : Input → ℝ) :
    twoLayerOutput (processor (permuteHidden permutation params)) activation input =
      twoLayerOutput (processor params) activation input := by
  rw [processor_equivariant permutation params, twoLayerOutput_permuteHidden]

/-- Equivariance supplies the relation-preservation premise of `Quotient.map`. -/
theorem IsHiddenPermutationEquivariant.preserves_orbit
    {processor : TwoLayerParams Input Hidden Output → TwoLayerParams Input Hidden Output}
    (equivariant : IsHiddenPermutationEquivariant processor)
    {params other : TwoLayerParams Input Hidden Output}
    (related : MulAction.orbitRel (Equiv.Perm Hidden) _ params other) :
    MulAction.orbitRel (Equiv.Perm Hidden) _ (processor params) (processor other) := by
  rcases related with ⟨g, rfl⟩
  exact ⟨g, (equivariant g⁻¹ other).symm⟩

/-- Parameters identified precisely up to hidden-neuron permutations. -/
abbrev ParameterOrbit := Quotient
  (MulAction.orbitRel (Equiv.Perm Hidden) (TwoLayerParams Input Hidden Output))

/-- A permutation orbit has a well-defined represented function for each activation. -/
def outputOnOrbits [Fintype Input] [Fintype Hidden] (activation : ℝ → ℝ) :
    ParameterOrbit (Input := Input) (Hidden := Hidden) (Output := Output) → (Input → ℝ) → Output → ℝ :=
  Quotient.lift (fun params input => twoLayerOutput params activation input) (by
    rintro params other ⟨g, rfl⟩
    funext input
    exact twoLayerOutput_permuteHidden g⁻¹ other activation input)

@[simp] theorem outputOnOrbits_mk [Fintype Input] [Fintype Hidden] (activation : ℝ → ℝ)
    (params : TwoLayerParams Input Hidden Output) :
    outputOnOrbits activation ⟦params⟧ = twoLayerOutput params activation := rfl

/-- Pooling all incoming weights across hidden coordinates is invariant. -/
def pooledFirstWeight [Fintype Input] [Fintype Hidden]
    (params : TwoLayerParams Input Hidden Output) : ℝ :=
  ∑ hidden, ∑ input, params.firstWeight hidden input

theorem pooledFirstWeight_isHiddenPermutationInvariant [Fintype Input] [Fintype Hidden] :
    IsHiddenPermutationInvariant
      (pooledFirstWeight (Input := Input) (Hidden := Hidden) (Output := Output)) := by
  intro permutation params
  exact Equiv.sum_comp permutation (fun hidden => ∑ input, params.firstWeight hidden input)

/-- A coordinate-sensitive diagnostic that reads one named hidden bias. -/
def hiddenBiasProbe (chosen : Hidden) (params : TwoLayerParams Input Hidden Output) : ℝ :=
  params.hiddenBias chosen

/-- The coordinate-sensitive probe follows the coordinate renaming. -/
@[simp] theorem hiddenBiasProbe_permuteHidden (chosen : Hidden) (permutation : Equiv.Perm Hidden)
    (params : TwoLayerParams Input Hidden Output) :
    hiddenBiasProbe chosen (permuteHidden permutation params) = params.hiddenBias (permutation chosen) :=
  rfl

/-- A coordinate-sensitive processor that zeroes one named hidden bias. -/
def zeroHiddenBias [DecidableEq Hidden] (chosen : Hidden)
    (params : TwoLayerParams Input Hidden Output) : TwoLayerParams Input Hidden Output :=
  { params with hiddenBias := Function.update params.hiddenBias chosen 0 }

section Fixtures

/-- Swap the two hidden coordinates in the executable fixture. -/
def finTwoSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- Nondegenerate two-hidden-unit fixture: every weight and bias is nonzero. -/
def permutationFixture : TwoLayerParams (Fin 1) (Fin 2) (Fin 1) where
  firstWeight hidden _ := if hidden = 0 then 2 else 3
  hiddenBias hidden := if hidden = 0 then 5 else 7
  secondWeight _ hidden := if hidden = 0 then 11 else 13
  outputBias _ := 17

/-- The original fixture evaluates to a nontrivial output. -/
theorem permutationFixture_output : twoLayerOutput permutationFixture id (fun _ => 1) 0 = 224 := by
  norm_num [twoLayerOutput, hiddenActivation, permutationFixture]

/-- Swapping the two hidden units preserves that same nontrivial output. -/
theorem permutationFixture_permuted_output :
    twoLayerOutput (permuteHidden finTwoSwap permutationFixture) id (fun _ => 1) 0 = 224 := by
  rw [twoLayerOutput_permuteHidden]
  exact permutationFixture_output

/-- A raw coordinate probe distinguishes functionally equal parameter vectors. -/
theorem hiddenBiasProbe_not_invariant :
    hiddenBiasProbe 0 (permuteHidden finTwoSwap permutationFixture) ≠
      hiddenBiasProbe 0 permutationFixture := by
  norm_num [hiddenBiasProbe, permuteHidden, reindexHidden, finTwoSwap,
    permutationFixture, Equiv.swap_apply_def]

/-- Editing a fixed raw coordinate is not an equivariant weight-space processor. -/
theorem zeroFirstHiddenBias_not_equivariant :
    ¬ IsHiddenPermutationEquivariant
      (zeroHiddenBias (Input := Fin 1) (Output := Fin 1) (0 : Fin 2)) := by
  intro supposedly_equivariant
  have bias_equality := congrArg (fun params : TwoLayerParams (Fin 1) (Fin 2) (Fin 1) =>
    params.hiddenBias 0) (supposedly_equivariant finTwoSwap permutationFixture)
  norm_num [zeroHiddenBias, permuteHidden, reindexHidden, finTwoSwap,
    permutationFixture, Equiv.swap_apply_def] at bias_equality

/-- Equal represented functions need not lie in one permutation orbit. All
weights and biases in this linear-activation example are nonzero. -/
theorem scaling_not_just_permutation :
    ∃ params other : TwoLayerParams (Fin 1) (Fin 2) (Fin 1),
      (∀ h i, params.firstWeight h i ≠ 0 ∧ other.firstWeight h i ≠ 0) ∧
      (∀ h, params.hiddenBias h ≠ 0 ∧ other.hiddenBias h ≠ 0) ∧
      (∀ o h, params.secondWeight o h ≠ 0 ∧ other.secondWeight o h ≠ 0) ∧
      (∀ o, params.outputBias o ≠ 0 ∧ other.outputBias o ≠ 0) ∧
      (∀ input, twoLayerOutput params id input = twoLayerOutput other id input) ∧
        ¬ ∃ permutation, other = permuteHidden permutation params := by
  let scaled : TwoLayerParams (Fin 1) (Fin 2) (Fin 1) :=
    { firstWeight := fun h _ => if h = 0 then 4 else 6
      hiddenBias := fun h => if h = 0 then 10 else 14
      secondWeight := fun _ h => if h = 0 then 11 / 2 else 13 / 2
      outputBias := fun _ => 17 }
  refine ⟨permutationFixture, scaled, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h i
    dsimp [permutationFixture, scaled]
    split_ifs <;> norm_num
  · intro h
    dsimp [permutationFixture, scaled]
    split_ifs <;> norm_num
  · intro o h
    dsimp [permutationFixture, scaled]
    split_ifs <;> norm_num
  · intro o
    norm_num [permutationFixture, scaled]
  · intro input
    funext output
    fin_cases output
    norm_num [twoLayerOutput, hiddenActivation, permutationFixture, scaled, Fin.sum_univ_two]
    ring
  · rintro ⟨permutation, equal⟩
    have weight := congrArg (fun params => params.firstWeight 0 0) equal
    change (4 : ℝ) = (if permutation 0 = 0 then 2 else 3) at weight
    split_ifs at weight <;> norm_num at weight

end Fixtures

end

end Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry

#print axioms Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry.twoLayerOutput_permuteHidden
#print axioms Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry.equivariantProcessor_preserves_output_orbits
#print axioms Mettapedia.MachineLearning.NeuralNetworks.HiddenNeuronPermutationSymmetry.zeroFirstHiddenBias_not_equivariant
