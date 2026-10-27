import Mettapedia.Algorithms.Compression.GuidedTemplateGrammar

/-! Bounded simultaneous-guide generation and exact-score transport. Native
correspondence uses separate late-filter references and source execution;
these declarations do not verify physical decoding or the C evaluator. -/

namespace Mettapedia.Examples.Compression.GuidedGrammarControls

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.Algorithms.Compression
open GuidedTemplateGrammar

def signature : List TemplateGrammar.Operator :=
  [⟨"T", []⟩, ⟨"T", [⟨.value, "T"⟩]⟩]

def captures : Captures := fun _ => none

theorem guide_restricts_constructors_but_keeps_parameter_choices :
    (terms signature 3 ⟨.root, "T"⟩ ⟨0, []⟩ captures [.node 1 [.node 0 []]]).length = 3 := by rfl

theorem different_heads_retain_the_root_parameter :
    (terms signature 3 ⟨.root, "T"⟩ ⟨0, []⟩ captures [.node 1 [.node 0 []], .node 0 []]).length = 1 := by rfl

theorem repeated_capture_disagreement_in_one_guide_is_rejected :
    (matchVector captures (.node 2 [.hole .value 0, .hole .value 0])
      [.node 2 [.node 0 [], .node 0 []], .node 2 [.node 0 [], .node 1 []]]).isSome = false := by
  simp [matchVector, matchForests, nodes, columns, TemplateMatching.assign, captures]

theorem repeated_capture_agreement_keeps_both_guides :
    (matchVector captures (.node 2 [.hole .value 0, .hole .value 0])
      [.node 2 [.node 0 [], .node 0 []], .node 2 [.node 1 [], .node 1 []]]).isSome = true := by
  simp [matchVector, matchForests, nodes, columns, emptyForests, TemplateMatching.assign, captures]

theorem two_ready_permissions_have_four_conventions :
    (CallingConventions.choices [0, 1] []).length = 4 := by rfl

end Mettapedia.Examples.Compression.GuidedGrammarControls

#print axioms Mettapedia.Algorithms.Compression.TemplateMatching.assign_sound
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.nodes_sound
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.columns_length
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.forests_mem_iff
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.terms_mem_iff
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.supported_region_iff
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.score_range_iff
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.minimum_score_eq
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.CallingConventions.choices_mem_iff
#print axioms Mettapedia.Algorithms.Compression.GuidedTemplateGrammar.CallingConventions.effective_subset_covered
#print axioms Mettapedia.Examples.Compression.GuidedGrammarControls.guide_restricts_constructors_but_keeps_parameter_choices
#print axioms Mettapedia.Examples.Compression.GuidedGrammarControls.different_heads_retain_the_root_parameter
#print axioms Mettapedia.Examples.Compression.GuidedGrammarControls.repeated_capture_disagreement_in_one_guide_is_rejected
#print axioms Mettapedia.Examples.Compression.GuidedGrammarControls.repeated_capture_agreement_keeps_both_guides
#print axioms Mettapedia.Examples.Compression.GuidedGrammarControls.two_ready_permissions_have_four_conventions
