import Mettapedia.Languages.MeTTa.Seal.Capability
import Mettapedia.Languages.MeTTa.Seal.Observation
import Mettapedia.Languages.MeTTa.Seal.Abstraction
import Mettapedia.Languages.MeTTa.Seal.Eliminability
import Mettapedia.Languages.MeTTa.Seal.ClosedResolver

/-!
# Seals

`new-seal`, `sealer-of`, `unsealer-of`, `seal` and `unseal`, studied in five
parts.

* `Capability`: the primitive among principals that act only through what they
  hold. Rights only shrink; no unseal without the unsealer; no mint without the
  sealer (Morris's induction rule); a kernel with public checked inference and a
  private sealing right makes exactly the derivable judgments available.
* `Observation`: what a client without the unsealer can observe. The observer
  model is a class of handle relations (all relations: no identity; partial
  bijections: identity and aliasing). Bisimilar modules are indistinguishable
  by every parametric client; identity, handle numbers and result order each
  break a stated equivalence. Under unordered delivery the bisimulation is sound
  but not complete.
* `Abstraction`: sealed modules of two simulating implementations are
  indistinguishable even by identity clients; content equality, an exported
  unsealer or a foreign read, timing, and reflection each distinguish one such
  pair.
* `Eliminability`: sealing is not eliminable from a transparent seal-free
  core (Felleisen's Definition 3.3, hence not macro-expressible): no
  translation homomorphic in the core preserves every observation.  A library
  emulation fails through each pinned leak; syntactic sugar is a macro
  elimination; with `quote`, equivalence is equality and nothing is
  eliminable.

* `ClosedResolver`: a kernel that seals what its rules compute is forged by
  one added equation for a helper it resolves in the live space, without
  touching any capability; a closed resolver, ownership of the helper's head,
  or a derivability certificate for each installed equation keeps it sound.

The equation kernel's sealed theorems (`EquationKernel.Sealed`) are the
theorem-level instance: inspection returns the retained judgment, instantiation
is a separate inference, and theories are identified exactly and joined only
along checked maps.
-/
