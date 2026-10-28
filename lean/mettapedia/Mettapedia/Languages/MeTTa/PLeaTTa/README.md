# PLeaTTa: a versioned mathematical model of PeTTa

This library maintains the mathematical development from
[`godelclaw/LeaTTa`](https://github.com/godelclaw/LeaTTa), revision
`ff1cd945890571905d1e8083d52b84a2df0205b4`. Its compatibility target is PeTTa
`6b7f52f064bdbc82fabd0a0998404121fb01d52e`. `PROVENANCE.json` records the
original paths and source digests; `LICENSE` and `NOTICE` retain the upstream
Apache-2.0 license and attribution.

The development separates several proof boundaries:

| Layer | Mathematical content |
| --- | --- |
| `PeTTaSpec.Reader` | Independent relations for tokenization, source reading, and runtime `sread` |
| `Proofs.ReaderAdequacy` | Soundness and completeness of the versioned executable reader against those relations |
| `PeTTaSpec.PrologCore`, `PrologSemantics`, `PrologTraceSemantics` | Independent target syntax, ordered search, observable prefixes, effects, and completion boundaries |
| `Types`, `Compile`, `Machine`, `Semantics` | Compiler representation, executable machine, and its sealed step relation |
| `Proofs.StepCases` | Successful steps and completed runs refine the sealed relation; reported errors satisfy its raising judgment |
| `Proofs.CompilerAdequacy` and the local bridge modules | Proved compiler and search fragments with their explicit hypotheses |
| `HostProtocol`, `HostMachine`, `HostReplay` | Typed external requests and responses, suspension, and transcript replay |

`machineMirrorsSpecTotal_proved` certifies the executable machine against the
sealed relation. End-to-end compiler adequacy and correspondence with the
independent demand-driven search have remaining obligations. The source
obligation ledgers under `Evidence/` retain those distinctions and refer to the
original source paths recorded in the provenance manifest. Their historical
counts describe the archived revision.

`Source/` owns the small historical syntax and runtime profile used in these
theorems. This keeps the mathematical meaning stable while the external
LeaTTa implementation evolves. `SourceEmbedding` proves an injective embedding
into the shared `MeTTailCore.MeTTaSyntax.Atom` carrier, with a partial inverse.
The inverse explicitly rejects the shared carrier's additional structured
binding packets. Operational correspondences have their own hypotheses and
proofs.

`Logic.LP` supplies the general first-order logic-programming theory and the
maintained graph runtime; `Logic.Prolog` supplies its typed Prolog extension.
PLeaTTa retains the versioned PeTTa compiler model and the distinct mathematical
questions about its ordered observations. The model's external-response
interface records the trusted host boundary explicitly.
