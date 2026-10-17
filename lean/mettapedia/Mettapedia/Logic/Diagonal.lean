import Mettapedia.Logic.Diagonal.Lawvere
import Mettapedia.Logic.Diagonal.Kleene
import Mettapedia.Logic.Diagonal.Combinatory
import Mettapedia.CategoryTheory.LawvereFixedPoint
import Mettapedia.GSLT.Logic.ReflectiveBubble
import Mettapedia.GSLT.Logic.KripkeFixedPoint
import Mettapedia.GSLT.Logic.CircularPropositions
import Mettapedia.GSLT.Logic.CircularHypersets
import Mettapedia.GSLT.Logic.KnowledgeBasedPrograms
import Mettapedia.GSLT.Logic.RankedDecision
import Mettapedia.Logic.Diagonal.Provability
import Mettapedia.Logic.Diagonal.Arithmetic
import Mettapedia.Logic.Diagonal.InductionSchemeDelta1
import Mettapedia.GSLT.GraphTheory.ReflectiveBetaBubble
import Mettapedia.GSLT.GraphTheory.OracleStratification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DropFreeTermination
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuoteMeetingPoint
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelInternalDecision
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ProofByReflection

/-!
# Reflection and the diagonal: one structure behind rho and carved fragments

Codes that run on codes, point-surjectively up to a relation, force fixed
points (positive reading) and forbid total internal decisions (negative
reading).  The escapes are partiality and stratification.

* `Logic.Diagonal.Lawvere`: the diagonal step relative to a relation and a
  class of maps; Lawvere's theorem for types, Cantor, Tarski's form, the
  abstract Rice theorem, and code/behaviour retractions.
* `CategoryTheory.LawvereFixedPoint`: weak point-surjectivity and Lawvere's
  theorem with finite products and with exponentials, with controls in the
  category of types.
* `Logic.Diagonal.Kleene`: Kleene's recursion theorem and Rice's theorem from
  the diagonal, for partial recursive codes up to extensional equality.
* `Logic.Diagonal.Combinatory`: reflexive structures (point-surjective onto
  polynomial maps up to an equivalence): fixed points, the Scott–Curry form of
  the negative reading, undetermined diagonals of sound deciders, and proper
  internal carve-outs.
* `GSLT.Logic.ReflectiveBubble`, `GSLT.GraphTheory.ReflectiveBetaBubble`: the
  default β-bubble is reflective; no λ-term decides β-conversion, and every
  internally realised fragment decision leaves its diagonal `outsideFragment`;
  a classical total decision exists one stage up.
* `GSLT.Logic.KripkeFixedPoint`: the partial escape, as the least fixed point
  in the knowledge order, consistent by duality, with the diagonal undetermined
  and verdicts as outcomes; grounded truth read three ways (stages, well-founded
  evidence, the fixed point), and the greatest fixed point as circular
  justification.
* `GSLT.Logic.CircularPropositions`: self-reference without coding.  Circular
  propositions form the final coalgebra of the strong Kleene signature; every
  system of judgments unfolds into it uniquely, with its grounded verdicts.  The
  universe has consistent partial truth, no Boolean valuation commuting with
  negation, and only the trivial classical Hilbert system (Curry).
* `GSLT.Logic.CircularHypersets`: over countable base facts, circular propositions
  read faithfully as hypersets; grounded truth and falsity are hypersets of the same
  universe with the truth and negation schemas, the self-negating proposition in
  neither, and a circular proposition among the truths.
* `GSLT.Logic.KnowledgeBasedPrograms`: knowledge-based programs read through
  the partial escape.  Knowledge tests are three-valued, implementations are the
  two-valued fixed points, every finite stage of the grounded inquiry is below
  every implementation, and the liar, the asker and the truth-teller have no,
  one and two implementations.
* `Logic.Diagonal.Provability`: provability stages; Löb's theorem and the second
  incompleteness theorem from Löb sentences, strict zoom-out, and Curry's paradox
  as Löb's theorem for the identity operator.
* `Logic.Diagonal.Arithmetic`: every `Δ₁` extension of `𝗜𝚺₁` is a provability stage,
  diagonalizable along the code map of formulas applied to Gödel numbers; its Löb
  sentences come from the relative Lawvere step, so Löb's theorem and the second
  incompleteness theorem for arithmetic follow from the abstract ones.
* `Logic.Diagonal.InductionSchemeDelta1`: `𝗣𝗔` and `𝗜𝚺₁` have constructed `Δ₁`
  presentations (a recognizer for the induction scheme, correct over `ℕ` and provably
  proper in `𝗜𝚺₁`), so the arithmetic stages and the consistency tower have concrete
  instances.
* `GSLT.GraphTheory.OracleStratification`: the stratified escape through the
  oracle-stage criterion; an admissible oracle decides without distinguishing,
  an inadmissible one distinguishes.
* `RhoCalculus.ReflectiveReplication`, `RhoCalculus.DropFreeTermination`:
  replication through quote and drop as the diagonal fixed point, and the
  bounded drop-free fragment in which no such fixed point exists.
* `RhoCalculus.QuoteMeetingPoint`: structural congruence passes through quote,
  drop and substitution; the value equality of sent names is strictly coarser
  and payload positions do not preserve it.
* `RhoCalculus.QuotedChannelInternalDecision`: a non-reflective bubble decides
  its own equality internally and has no diagonal fixed point.
* `SingleBaseSTLC.ProofByReflection`: the carved simple fragment comes with a
  sound, complete internal decision procedure on codes, used to prove
  equations by computation.
-/
