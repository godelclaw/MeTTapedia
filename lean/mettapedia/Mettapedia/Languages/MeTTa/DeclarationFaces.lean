import Mettapedia.Languages.MeTTa.DeclarationFaces.Syntax
import Mettapedia.Languages.MeTTa.DeclarationFaces.Termination
import Mettapedia.Languages.MeTTa.DeclarationFaces.LexicographicDescent
import Mettapedia.Languages.MeTTa.DeclarationFaces.Sorting
import Mettapedia.Languages.MeTTa.DeclarationFaces.Admission
import Mettapedia.Languages.MeTTa.DeclarationFaces.Confluence
import Mettapedia.Languages.MeTTa.DeclarationFaces.Faces
import Mettapedia.Languages.MeTTa.DeclarationFaces.Agreement
import Mettapedia.Languages.MeTTa.DeclarationFaces.Controls
import Mettapedia.Languages.MeTTa.DeclarationFaces.Intensional
import Mettapedia.Languages.MeTTa.DeclarationFaces.IntensionalOrthogonal
import Mettapedia.Languages.MeTTa.DeclarationFaces.DataInVOmega
import Mettapedia.Languages.MeTTa.DeclarationFaces.CollectionTypes
import Mettapedia.Languages.MeTTa.DeclarationFaces.Comprehension
import Mettapedia.Languages.MeTTa.DeclarationFaces.TypedTransforms
import Mettapedia.Languages.MeTTa.DeclarationFaces.GSLTPresentation
import Mettapedia.Languages.MeTTa.DeclarationFaces.WeakOrthogonality
import Mettapedia.Languages.MeTTa.DeclarationFaces.DeterministicLane

/-!
# One declaration, three faces

A MeTTa declaration of first-order data and functions (type declarations and equations) has an
operational face (MeTTa evaluation: every matching equation, results as a multiset, unmatched calls
inert), an intensional face (sorting, and the theory of the λΠ-calculus modulo rewriting that
receives the equations as rewrite rules), and an extensional face (each sort denotes its data, a set
of hereditarily finite trees; each function the unique solution of its equations).

`Admission.admit` decides when a declaration carries all three; `Agreement.Admitted.faces_agree`,
`Intensional`, `IntensionalOrthogonal` and `Faces` prove that they agree for every admitted
declaration, under every evaluation strategy, relative to the declaration's scope. Collections,
comprehensions, typed transforms and the reading as a GSLT presentation extend the same
declarations.
-/
