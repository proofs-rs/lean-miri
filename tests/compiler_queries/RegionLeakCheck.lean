import Miri.Input.TraitSelection.RegionLeakCheck

open Miri.Input.TraitSelection.RegionLeakCheck
private def rejected (value : Except String α) : Bool := match value with | .error _ => true | .ok _ => false
private def p : Region := .placeholder 1 0
private def q : Region := .placeholder 1 1
example : check 0 #[p] #[] = .ok () := by cbv
example : check 0 #[p] #[⟨0,0⟩] = .ok () := by cbv
example : rejected (check 0 #[p,q] #[⟨0,1⟩]) = true := by cbv
example : rejected (check 0 #[p,q] #[⟨0,1⟩,⟨1,0⟩]) = true := by cbv
example : rejected (check 0 #[p,.root 0] #[⟨0,1⟩]) = true := by cbv
-- The edge direction matters: the root region may be chosen as 'static.
example : check 0 #[p,.root 0] #[⟨1,0⟩] = .ok () := by cbv
example : rejected (check 0 #[p,.inference 0 0] #[⟨0,1⟩]) = true := by cbv
example : check 0 #[p,.inference 0 1] #[⟨0,1⟩,⟨1,0⟩] = .ok () := by cbv
example : rejected (check 0 #[p,.inference 0 1,q] #[⟨0,1⟩,⟨1,2⟩]) = true := by cbv
example : check 1 #[p,.root 0] #[⟨0,1⟩] = .ok () := by cbv
example : rejected (check 0 #[p] #[⟨0,1⟩]) = true := by cbv
example : rejected (check 0 #[p] #[⟨1,0⟩]) = true := by cbv
example : check 0 #[p,.inference 0 1,.inference 1 1] #[⟨0,1⟩,⟨1,2⟩,⟨2,1⟩] = .ok () := by cbv
example : rejected (check 0 #[p,.inference 0 1,.inference 1 0]
    #[⟨0,1⟩,⟨1,2⟩,⟨2,1⟩]) = true := by cbv
