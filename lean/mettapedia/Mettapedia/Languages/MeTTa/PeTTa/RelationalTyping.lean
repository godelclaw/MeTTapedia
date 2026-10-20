import Mettapedia.Languages.MeTTa.PeTTa.ResidualTypeChecks
import Mettapedia.Languages.MeTTa.PeTTa.JointSchemeContracts
import Mettapedia.Languages.MeTTa.PeTTa.SchematicCallTyping
import Mettapedia.Languages.MeTTa.PeTTa.DeclarationTypeCandidates
import Mettapedia.Languages.MeTTa.PeTTa.SynthesisCandidateComposition
import Mettapedia.Languages.MeTTa.PeTTa.TypingSourceViews
import Mettapedia.Languages.MeTTa.PeTTa.TypingSchemeInstantiation
import Mettapedia.Logic.LP.ListSpine
import Mettapedia.Languages.MeTTa.PeTTa.JointCallExecution
import Mettapedia.Languages.MeTTa.PeTTa.ResidualSchemeTruth
import Mettapedia.Languages.MeTTa.PeTTa.CheckedInstantiation
import Mettapedia.Languages.MeTTa.PeTTa.CheckedCardinality

/-!
# Relational PeTTa typing and checked modes

The independent components cover resolved value checks, schematic call
constraints, conditional truth, instantiation and answer occurrences. Their
scope statements remain in the individual modules: this import does not
assert a complete source-to-SWI or source-to-native realization theorem.
-/
