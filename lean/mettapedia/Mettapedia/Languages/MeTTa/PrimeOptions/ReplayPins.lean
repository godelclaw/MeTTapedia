import Mettapedia.GSLT.Distinction.OptionGraph

/-!
# Replay pins of the fixtures the Prime option graph cites

For each fixture the registry cites, the source hashes at which it was last replayed: its test
and its expected output, and for a fixture a gate script checks that script, by path relative to
the root of the source tree its suite names, with their SHA-256. The suites `prime` and `c-draft`
name the C draft; `weights-tree` names the tree of the weight algebras, whose hashes here are
the ones its qualification receipt records for the replay. The generator of
the published graph recomputes the hashes; an item whose file has moved is stale, and stale
evidence does not count until it is replayed and pinned again.

The fixtures are also run against the current build of the C draft each time the graph is
regenerated with its fixtures; the build itself is not pinned.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.ReplayPins

open Mettapedia.GSLT.Distinction.OptionGraph

/-- The replay pin of every fixture the registry cites. -/
def fixturePins : List FixturePin := [
  { suite := "c-draft", test := "tests/prime/causal/adaptive_policy.metta"
    files := [
      { path := "tests/prime/causal/adaptive_policy.metta"
        sha256 := "feb25a7fb72f931ae6c371b805a3ad5ffcc725ab5d3d5f4129d12f64f129ff7f" },
      { path := "tests/prime/causal/adaptive_policy.expected"
        sha256 := "b0c94173cdc69879576c9a719c322f38bea63a1a48e0c0736b094e5d92090833" }] },
  { suite := "weights-tree", test := "tests/prime/weights/law_breaking.metta"
    files := [
      { path := "tests/prime/weights/law_breaking.metta"
        sha256 := "7573edc722d585112e90e2d25bf058f2157bc877cafcb86c7ab48becf74c6002" },
      { path := "scripts/test_prime_weights.py"
        sha256 := "2051984fddc7ade892a287dac72b4c56a5761b54c3a9382ae7bc601c5649a019" }] },
  { suite := "c-draft", test := "tests/prime/causal/composition_regions.metta"
    files := [
      { path := "tests/prime/causal/composition_regions.metta"
        sha256 := "dc892eb90620d1a1f99639d087b5bcbe4197439c032360ad4664f1aeafbe7c5c" },
      { path := "tests/prime/causal/composition_regions.expected"
        sha256 := "a6118bffb7f632bc80cd54f75bcec95e3704eef7eed8b9af5259b43550c34f9a" }] },
  { suite := "c-draft", test := "tests/prime/causal/feedback.metta"
    files := [
      { path := "tests/prime/causal/feedback.metta"
        sha256 := "830b6fc9b3991311d9455caa4f6be2b079cee2ec288accc9cea22920cb8ac4f1" },
      { path := "tests/prime/causal/feedback.expected"
        sha256 := "d581ea61600ba2fe5d3c52ae1698ebb609831c85ccaf581ffd04334f66e6dcd4" }] },
  { suite := "c-draft", test := "tests/prime/causal/structural_model.metta"
    files := [
      { path := "tests/prime/causal/structural_model.metta"
        sha256 := "551d3636e74ae8ba927c90f0fc41b9da96ca98ca233b6656f279784ce38220f3" },
      { path := "tests/prime/causal/structural_model.expected"
        sha256 := "834d337f908637b33f417d518edb5cd40e84936d7864e28f5246a41afbb0a5b2" }] },
  { suite := "c-draft", test := "tests/prime/causal/twin_experiment.metta"
    files := [
      { path := "tests/prime/causal/twin_experiment.metta"
        sha256 := "99b6f6116fa89e44910a533fe42dcd7bdc9b2472c3a23ed796199e77f29fcd42" },
      { path := "tests/prime/causal/twin_experiment.expected"
        sha256 := "33cd079c032a89a1bc1ea8cef64b4fdc50af3e49c6f6aad4197d52d4d6e7c40b" }] },
  { suite := "c-draft", test := "tests/prime/demand/bubbles.metta"
    files := [
      { path := "tests/prime/demand/bubbles.metta"
        sha256 := "d928bb6c62c9cd0b7c964aa105608ec7b4f65921d9c7cad83ebd9f1c054c9487" },
      { path := "tests/prime/demand/bubbles.expected"
        sha256 := "81c436d63d9b29774da2c6bc2b4ea9f56fd51db937c0d5182816bc44c5bb6072" }] },
  { suite := "c-draft", test := "tests/prime/shared_cause_probability.metta"
    files := [
      { path := "tests/prime/shared_cause_probability.metta"
        sha256 := "23d9a2e3f21864a7fe34693fd8f5f4a9272558b55905b3dced7955f6c5c80d46" }] },
  { suite := "prime", test := "profiles/megalodon_hotg/scoped/curriculum_naproche"
    files := [
      { path := "tests/prime/profiles/megalodon_hotg/scoped/curriculum_naproche.metta"
        sha256 := "0ca7a025753ba671690b64a1be83fd3f4d58e696a7867e12c07df843b95cd3e8" },
      { path := "tests/prime/profiles/megalodon_hotg/scoped/curriculum_naproche.expected"
        sha256 := "7bdedb657240e7ade03b0ff10474694fa37e3e5041d1e51f31dda117ad0d91ec" }] },
  { suite := "prime", test := "profiles/megalodon_hotg/scoped/equality_routes"
    files := [
      { path := "tests/prime/profiles/megalodon_hotg/scoped/equality_routes.metta"
        sha256 := "2154b0dc8cfee1233234a42b5d807fe31d96753874cb25baab6976ce76d30620" },
      { path := "tests/prime/profiles/megalodon_hotg/scoped/equality_routes.expected"
        sha256 := "167fe063337865edc0f8234e096114f1d6f0b968b9a37847d2e4e1f6a555b2d2" }] },
  { suite := "prime", test := "theory_profiles/isolation"
    files := [
      { path := "tests/prime/theory_profiles/isolation.metta"
        sha256 := "89f8014fb252d6739df824864346e41e94fbe6dfaf1218ecb9a8813e37f3384e" },
      { path := "tests/prime/theory_profiles/isolation.expected"
        sha256 := "9ac0663ae27dc71536b25257f05fbc307def105990225d8d560f07e902a1df22" }] },
  { suite := "prime", test := "trinity/reverse.extensional"
    files := [
      { path := "tests/prime/trinity/reverse.extensional.metta"
        sha256 := "58d866f8e9edcd4e697be4f8d4576854bfdd926f76fc251dab92d44d7094dee6" },
      { path := "tests/prime/trinity/reverse.extensional.expected"
        sha256 := "478a3f40c0f00573e45d9306023f4f35ae70ada2ce593e8bba105beb088ba1fa" }] },
  { suite := "prime", test := "trinity/reverse.intensional"
    files := [
      { path := "tests/prime/trinity/reverse.intensional.metta"
        sha256 := "70b3bb2c14ba22c044873174e2e9bf9e52bd7c74d04e26a30b95e583f219f3b2" },
      { path := "tests/prime/trinity/reverse.intensional.expected"
        sha256 := "8411b03af8d81a5fea1a107f5ce29423e03421153b7f03f3cced5851e4fb81c0" }] },
  { suite := "prime", test := "trinity/reverse.operational"
    files := [
      { path := "tests/prime/trinity/reverse.operational.metta"
        sha256 := "2ad38d38e7464b0a96abab1f1fb85e3336ae9aa2069e04daa27ed82aa5706e7a" },
      { path := "tests/prime/trinity/reverse.operational.expected"
        sha256 := "5e298c98723e2f75d64c4b417e4e10e41fee1c9c15badab4785ebac3743e7dab" }] }
]

end Mettapedia.Languages.MeTTa.PrimeOptions.ReplayPins
