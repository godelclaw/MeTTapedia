import Mettapedia.Algorithms.Retrieval.TopKSelection
import Mettapedia.Algorithms.Retrieval.BlendedTopK

/-! Kernel dependencies of utility regret and exact selection certificates. -/
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.isTopK_iff
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.topk_frozen
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.certified_topk
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.topk_scale
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.topk_regret_le_symmDiff
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.topk_regret_le_l1
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.topk_regret_le_l1_scaled
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.topk_regret_le_uniform
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.calibrated_topk_optimal
#print axioms Mettapedia.Algorithms.Retrieval.TopKSelection.topk_regret_le_max
#print axioms Mettapedia.Algorithms.Retrieval.BlendedTopK.ratio_error
#print axioms Mettapedia.Algorithms.Retrieval.BlendedTopK.max_close
#print axioms Mettapedia.Algorithms.Retrieval.BlendedTopK.blend_error
#print axioms Mettapedia.Algorithms.Retrieval.BlendedTopK.certified_blend_topk
