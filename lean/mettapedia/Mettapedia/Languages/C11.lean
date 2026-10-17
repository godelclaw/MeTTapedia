import Mettapedia.Languages.C11.IntegerConversion
import Mettapedia.Languages.C11.IntegerDivision
import Mettapedia.Languages.C11.IntegerArithmetic
import Mettapedia.Languages.C11.IntegerControls
import Mettapedia.Languages.C11.IntegerStep
import Mettapedia.Languages.C11.IntegerStepControls
import Mettapedia.Languages.C11.IntegerTypes
import Mettapedia.Languages.C11.IntegerProfiles
import Mettapedia.Languages.C11.UsualIntegerConversions
import Mettapedia.Languages.C11.TypedIntegerArithmetic
import Mettapedia.Languages.C11.TypedIntegerStep
import Mettapedia.Languages.C11.TypedIntegerControls
import Mettapedia.Languages.C11.ByteRanges
import Mettapedia.Languages.C11.ArrayPointers
import Mettapedia.Languages.C11.ObjectLayout
import Mettapedia.Languages.C11.ObjectStep
import Mettapedia.Languages.C11.ByteStorageData
import Mettapedia.Languages.C11.ObjectStepData
import Mettapedia.Languages.C11.ObjectControls
import Mettapedia.Languages.C11.BytePacking
import Mettapedia.Languages.C11.IntegerBits
import Mettapedia.Languages.C11.IntegerObject
import Mettapedia.Languages.C11.IntegerMemory
import Mettapedia.Languages.C11.IntegerObjectControls
import Mettapedia.Languages.C11.Sequencing
import Mettapedia.Languages.C11.SequencingSchedule
import Mettapedia.Languages.C11.ValueSequencing
import Mettapedia.Languages.C11.SequencingData
import Mettapedia.Languages.C11.ScheduledObjects
import Mettapedia.Languages.C11.ScheduledObjectHistory
import Mettapedia.Languages.C11.SequencingControls
import Mettapedia.Languages.C11.AccessTypes
import Mettapedia.Languages.C11.EffectiveTypes
import Mettapedia.Languages.C11.ObjectAccessMemory
import Mettapedia.Languages.C11.ScopedLvalues
import Mettapedia.Languages.C11.CestaObjectAccess
import Mettapedia.Languages.C11.ObjectAccessControls
import Mettapedia.Languages.C11.CestaAccessExecution
import Mettapedia.Languages.C11.CestaAccessCorrespondence
import Mettapedia.Languages.C11.IntegerScalar
import Mettapedia.Languages.C11.ReadExpressionSyntax
import Mettapedia.Languages.C11.ReadExpressionHead
import Mettapedia.Languages.C11.ReadExpressionStep
import Mettapedia.Languages.C11.ReadExpressionExecution
import Mettapedia.Languages.C11.ReadExpressionData
import Mettapedia.Languages.C11.ReadExpressionControls
import Mettapedia.Languages.C11.ObjectStores
import Mettapedia.Languages.C11.IntegerMemoryModel
import Mettapedia.Languages.C11.IntegerMemoryProfiles
import Mettapedia.Languages.C11.IntegerAssignment
import Mettapedia.Languages.C11.IntegerMemoryControls
import Mettapedia.Languages.C11.IntegerObjectConstruction
import Mettapedia.Languages.C11.IntegerObjectInitialization
import Mettapedia.Languages.C11.IntegerObjectSequences
import Mettapedia.Languages.C11.AutomaticObjectScopes
import Mettapedia.Languages.C11.CestaIntegerDeclarations
import Mettapedia.Languages.C11.CestaDeclarationReservations
import Mettapedia.Languages.C11.IntegerObjectLifetimeControls
import Mettapedia.Languages.C11.IntegerOperators
import Mettapedia.Languages.C11.IntegerOperatorControls
import Mettapedia.Languages.C11.ExpressionEvents
import Mettapedia.Languages.C11.ExpressionPlanConstruction
import Mettapedia.Languages.C11.LocatedExpressions
import Mettapedia.Languages.C11.ExpressionSourceOrder
import Mettapedia.Languages.C11.ExpressionSourceActions
import Mettapedia.Languages.C11.ExpressionEventExecution
import Mettapedia.Languages.C11.ExpressionEventHistory
import Mettapedia.Languages.C11.ExpressionSourceExecution
import Mettapedia.Languages.C11.ExpressionSourceHistory
import Mettapedia.Languages.C11.LocatedExpressionControls
import Mettapedia.Languages.C11.LocatedExpressionData
import Mettapedia.Languages.C11.LocatedExpressionDataControls
import Mettapedia.Languages.C11.CestaExpressionElaboration
import Mettapedia.Languages.C11.CestaLocatedExpressions
import Mettapedia.Languages.C11.CestaExpressionCorrespondence
import Mettapedia.Languages.C11.CestaExpressionControls
import Mettapedia.Languages.C11.LocatedStatements
import Mettapedia.Languages.C11.StatementSemantics
import Mettapedia.Languages.C11.StatementExecution
import Mettapedia.Languages.C11.StatementMachine
import Mettapedia.Languages.C11.StatementHistory
import Mettapedia.Languages.C11.CestaStatements
import Mettapedia.Languages.C11.StatementControls
import Mettapedia.Languages.C11.StatementData
import Mettapedia.Languages.C11.StatementDataExecution
import Mettapedia.Languages.C11.StatementDataInteraction
import Mettapedia.Languages.C11.StatementDataHistory
import Mettapedia.Languages.C11.StatementDataControls
import Mettapedia.Languages.C11.StatementMachineRefinement
import Mettapedia.Languages.C11.StatementMachineRefinementControls
import Mettapedia.Languages.C11.FixedCore
import Mettapedia.Languages.C11.FixedCoreStatements
import Mettapedia.Languages.C11.FixedCoreControls
import Mettapedia.Languages.C11.CestaFixedCore
import Mettapedia.Languages.C11.CestaFixedCoreControls
import Mettapedia.Languages.C11.FixedCoreServices
import Mettapedia.Languages.C11.FixedCoreServiceControls

/-!
# C11 language semantics

The numeric layer exposes value conversions, canonical integer ranks,
promotions, usual integer arithmetic conversions and five typed operations.
Represented configurations retain input/result types and have exact numeric
reduction correspondence. The object layer supplies byte-range memory,
array-relative pointer operations, constructed natural aggregate layouts,
and represented object requests with independent memory-reduction laws.
Both use the common retained-state resumption driver.

The representation layer constructs byte-order packing and all three signed
integer interpretations, including negative-zero/minimum trap policies. Its
named contiguous-bit/padding profiles have general valid-value store/read
laws, connected to the owned byte memory kernel and disjoint frames.

The sequencing layer retains complete strict occurrence relations and checks
ordinary scalar conflicts across permitted alternatives. Operand-value
components distinguish result computation from pending modifications.
An executable scheduler preserves that relation, and its object-operation
driver has independent reduction, exact history, prefix resumption and
occurrence-conservation laws. Plain matrix/list codecs have inverse laws.

The access layer checks resolved object-type views, effective-type read
permissions and non-character type-establishing stores. Whole-object integer
lvalues retain identity through casts and preserve declared object qualifiers.
General read/store correspondence and store/read laws join those checks to byte
memory. Scoped lookup has independent binding laws for arbitrary finite nesting
and shadowing. A schema-indexed Cesta identifier adapter constructs sorted
representations and connects them to the scoped memory judgments.
The common driver retains memory, scopes, pending requests and occurrence
counters across arbitrary finite access histories. Independent histories
have constructive realization with exact ordered observations and semantic
endpoints; shadowed finite-storage records remain explicit retained data.

The integer read-expression layer joins those scoped memory judgments to typed
arithmetic, casts, truth, short-circuit operators, conditionals and comma.
An executable enumeration covers every independently specified contextual
reduction at arbitrary nesting, retaining occurrence contexts. Every finite
history constructs scheduler choices with exact observations and endpoints.
A decreasing expression weight excludes administrative stuttering in this
call-free layer. Complete configuration codecs and prefix resumption retain
memory, scopes, choices and occurrence counters.

Heterogeneous integer memory families share one character representation while
selecting a checked object layout for each canonical integer type. Constructed
ILP32, LP64 and LLP64 families retain signed/unsigned extents and byte order.
Character stores preserve retained type information. Assignment conversion
and storage have independent soundness, constructive endpoint completeness
and typed readback. Read/store frame laws preserve separately owned resources.
The integer operator layer adds promoted unary operators, independently
promoted shifts, usual-converted bitwise operations and integer comparisons.
Independent bit clauses retain negative zero and trap policies across the
three signed representations. Scalar adapters select canonical operands;
propagating noncanonical words through every surrounding source operation
remains a separate representation obligation.

Integer object construction supplies executable reservations, initialized
representations and automatic-scope release, with source judgments and
preservation of separately owned storage. Cesta declarations construct these
requests from supported integer declarators. General statement-level
initializer timing and binding visibility require the declaration/control
join; object construction alone does not establish those laws.

The located integer expression layer constructs its occurrence identities,
typed primitive operations and sequencing from arbitrary nested source
expressions. Loads, five arithmetic operations, casts, assignments,
prefix/postfix updates and comma have independent source action and order
rules. Assignment result computation and the memory modification are distinct
occurrences. Conflicting unsequenced accesses cannot be repaired by choosing
a chronological order. Every independently admitted finite source history
has constructive realization with exact observations and semantic endpoints.

The common occurrence driver retains pending modifications, values, memory
and choices. Prefix resumption conserves occurrences without replaying a
consumed store. Checked source/configuration codecs have both inverse laws;
the represented step reconstructs its plan from decoded source and has
soundness and constructive completeness for the independent source judgment.
Representability of a supplied cache is distinct from its historical authority.

The Cesta expression connection uses its sorted canonical schema, primitive
integer type-specifier permutations and independent scoped lvalue reading.
Unsuffixed decimal literals fitting int, the admitted arithmetic/cast forms,
assignments, prefix/postfix updates and comma elaborate at arbitrary nesting.
Independent elaboration has executable soundness and completeness. Source
occurrence inspection constructs action/order witnesses. Residual admission
requires the exact elaborated source, so an otherwise executable packet from
another source cannot be spliced into it. Represented steps have independent
source-advance correspondence with constructive semantic endpoints.
These structural and type laws do not prove native byte parsing, declaration
history, lifetime authority or compiler/ABI trace refinement.

The declaration-free integer statement layer retains continuations for
blocks, conditionals, while/do/for loops, break, continue and return. Complete
expression boundaries drain pending modifications before subsequent control.
The independently specified statement transitions have executable soundness
and constructive endpoint completeness at arbitrary nesting and iteration
counts. Every finite independent history has exact ordered observations and
an executable endpoint. A decreasing rank rules out silent administrative
stuttering; visible loop iterations can continue indefinitely. The common
driver preserves complete residuals and separate work accounts across budget
splits. Terminal arithmetic/conversion outcomes, unsequenced conflicts and
invalid scheduler input remain distinct retained outcomes.

Cesta's actual statement wrappers and ordered block items elaborate through
an independent statement-reading judgment. Unsupported declarations, labels,
switch and goto are refused rather than erased. Plain statement-configuration
codecs retain control, memory, pending expressions and outcome distinctions.
Their executable steps have source correspondence, exact finite histories,
prefix resumption and checked request/reply endpoints. The represented and
structured statement machines instantiate the common cost-simulation stage.
Dynamic declaration/lifetime transitions, function call stacks and full
ordinary-source or native-execution correspondence remain obligations for this
located layer.

The fixed core (`FixedCore`, `FixedCoreStatements`) is a source language over
the same representation and memory modules. Names resolve through the lexical
scopes of the current activation. Pure expressions read integer elements,
compute with the typed operations, take addresses and move pointers within live
arrays. Statements assign through places, set pointer variables, call functions
recursively with parameter objects initialized by assignment conversion, return
values, branch, loop, break and continue, open blocks that reserve declared
objects and retire every owned lifetime on every exit, allocate and release
dynamic objects, and suspend on external requests that a reply resumes. The
executable step is sound and complete for an independent step relation whose
premises are the memory, scope and expression judgments (`step_iff`), up to the
two choices C11 leaves open: the identity of every new object and whether an
allocation succeeds. Undefined behaviors stop with their reason (arithmetic
overflow or division by zero, an access to a dead, indeterminate,
out-of-bounds or misaligned element, a trap representation, a pointer formed
outside its array, an invalid or repeated release, a used missing return); a
constraint violation is reported separately. Object layouts are the selected
ABI's, an explicit parameter; pointer variables are not addressable and hold an
abstract provenance-carrying value, which is the core's ABI assumption for
pointers. External services are assumed to answer each request at most once
with a value; the machine refuses a second reply. Differential runs of the
defined controls under GCC and Clang print the same results, and their
sanitizers report the same undefined behaviors on the undefined controls.

Named extensions outside the fixed core: side effects and calls inside
expressions (the located layer models unsequenced evaluation), pointers to
pointers and pointer-typed objects in byte memory, structures and unions,
floating and complex types, `switch`, `goto` and labels, variable-length arrays,
array and nonzero aggregate initializers, function pointers, variadic
functions, `setjmp`/`longjmp`, signals, threads and atomics, volatile accesses,
and the remaining standard library. On the admitted common fragment,
`FixedLocated.terminal_observation_iff` proves equality of completed integer/void
returns and source refusal under the common observer. Every supplied scheduler
choice must name a ready occurrence; operand order remains free. The reached
control invariant reconstructs actual fixed histories from arbitrary located
prefixes. Budgets and requests preserve exact residuals and causal receipts;
located diagnostics retain their detail even though the common refusal observer
forgets which independent fault occurred first. This join does not extend the
fragment to allocation, calls or effectful nested operands.

`CestaFixedCore` reads Cesta's canonical translation units into core programs.
It is a static checker for the fragment: names resolve through the C block
scopes, operands are classified as integers or pointers to a declared integer
type, calls are checked against the signatures of the program's functions and
of the host's services, and `malloc`/`free` denote allocation and release.
Interleaved declarations become nested core blocks, `E1[E2]`, `&*E` and
`&E1[E2]` follow their C11 equivalences, returned values and service arguments
are converted to the declared types, and the end of `int main` returns `0`.
Every reading function is equivalent to an independent reading relation
(`readUnit_iff` and the lemmas below it). Sources parsed by Cesta run to the
values GCC and Clang compute; `for`, `do`, `switch`, `goto`, operators outside
the core, pointer subtraction and comparison, calls inside expressions, array
initializers and file-scope declarations are refused.

`FixedCoreServices` serves a core program's requests by service machines
through the common callback protocol: the core's events, each request, the
service's own events and each reply form one trace; a returned value resumes
the program as `reply` does, and a failed request stops it with the service's
fault. Serving by machines is a compilation stage from atomic answers
(`servedStage`). The controls serve Cesta-parsed C programs by the retained HE
evaluator: a C loop calling a MeTTa function returns what GCC computes for the
same loop over a C definition, and several MeTTa results, or an unreadable one,
stop the program without choosing a result.

The full C11 expression/statement machine, floating/complex types,
source-type elaboration, remaining object/subobject and padding profiles,
character subobject/partial-copy effective-type rules, remaining source sequencing,
external/volatile interactions and full source representation remain separate
obligations in the C11 coverage ledger. Storage-kernel retirement,
codec admission and semantic receipts do not grant external effect authority.
-/
