import Mettapedia.Languages.MeTTa.HE.Correctness

/-!
# Historical HE certificate interface

`EvalAtomCertified` explicitly combines a historical `EvalSpec` derivation with
stable executable support. `evalAtomCertified_to_EvalAtom` and
`evalAtomCertified_to_stably_reaches` project those independently present facts;
`evalAtomCertified_to_filtered_witness` proves the actual filter consequence.
There is no unconditional stability-to-historical-meaning theorem.

Independent source evidence and actual selected-frame invocation are connected
in `RecursiveSemanticSoundness`. First-success source admission remains an
explicitly separate evaluation policy.
-/
