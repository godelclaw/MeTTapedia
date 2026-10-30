import Mettapedia.Algorithms.Compression.SkeletonInstantiation

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.SkeletonInstantiationControls

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.Algorithms.Compression
open SkeletonInstantiation

def choices : Choices := fun _ => [.node 0 [], .node 1 []]
def repeated : SchemaPattern := .node 2 [.hole .code 0, .hole .code 0]
def independent : SchemaPattern := .node 2 [.hole .code 0, .hole .code 1]

theorem repeated_name_has_one_choice_not_two :
    (terms choices TemplateMatching.empty repeated).map Prod.fst =
      [.node 2 [.node 0 [], .node 0 []], .node 2 [.node 1 [], .node 1 []]] := by rfl

theorem mixed_assignment_is_not_emitted :
    Prog.node 2 [.node 0 [], .node 1 []] ∉
      (terms choices TemplateMatching.empty repeated).map Prod.fst := by
  rw [repeated_name_has_one_choice_not_two]
  simp

theorem independent_names_keep_the_full_product :
    (terms choices TemplateMatching.empty independent).length = 4 := by rfl

theorem equal_numbers_in_different_roles_are_distinct :
    (terms choices TemplateMatching.empty (.node 2 [.hole .code 0, .hole .value 0])).length = 4 := by rfl

theorem both_rule_sides_reuse_one_assignment :
    (forests choices TemplateMatching.empty [.node 2 [.hole .code 0], .node 3 [.hole .code 0]]).map Prod.fst =
      [[.node 2 [.node 0 []], .node 3 [.node 0 []]],
       [.node 2 [.node 1 []], .node 3 [.node 1 []]]] := by rfl

theorem duplicate_vocabulary_occurrences_are_retained :
    (terms (fun _ => [.node 0 [], .node 0 []]) TemplateMatching.empty repeated).length = 2 := by rfl

#print axioms Mettapedia.Algorithms.Compression.SkeletonInstantiation.terms_sound
#print axioms Mettapedia.Algorithms.Compression.SkeletonInstantiation.forests_sound
#print axioms Mettapedia.Algorithms.Compression.SkeletonInstantiation.terms_existing
#print axioms Mettapedia.Algorithms.Compression.SkeletonInstantiation.forests_existing
#print axioms Mettapedia.Algorithms.Compression.SkeletonInstantiation.chosen_binding_preserved
#print axioms Mettapedia.Algorithms.Compression.SkeletonInstantiation.rule_sides_share_environment
#print axioms repeated_name_has_one_choice_not_two
#print axioms mixed_assignment_is_not_emitted
#print axioms independent_names_keep_the_full_product
#print axioms equal_numbers_in_different_roles_are_distinct
#print axioms both_rule_sides_reuse_one_assignment
#print axioms duplicate_vocabulary_occurrences_are_retained

end Mettapedia.Examples.Compression.SkeletonInstantiationControls
