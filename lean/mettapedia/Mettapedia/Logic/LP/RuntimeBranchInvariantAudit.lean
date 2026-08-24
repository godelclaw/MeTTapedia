import Mettapedia.Logic.LP.RuntimeBranchInvariant

/-! Trusted-base audit for exact structured-branch checkpoint restoration. -/

#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.branchStep_creates_checkpoint
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.LiveBranchCheckpoint.branchStep
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.NestedLiveBranchCheckpoint.branchStep
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.NestedLiveBranchCheckpoint.backtrackStep
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.LiveBranchCheckpoint.cutStep_preserves
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.LiveBranchCheckpoint.cutStep_prunes
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.BranchCheckpoint.restore_exact
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.BranchCheckpoint.advance_unifier_success
#print axioms Mettapedia.Logic.LP.RuntimeBranchInvariant.backtrackStep_branch_of_checkpoint
