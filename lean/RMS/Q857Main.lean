import Mathlib
import RMS.Q857
import RMS.Q857ComplexLower

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Q857 aggregate verification harness

This module makes the complete normalized dependency chain reachable from `RMS.lean` and checks
the exact real and complex terminal declarations. The source is a candidate pending independent
CI; these commands do not claim a local build.
-/

#check Q857.real_dist
#check Q857.exists_nearest
#check Q857.complex_upper
#check Q857.exists_structure_of_min
#check Q857.cmin_le_of_det_one
#check Q857.complex_isLeast

#print axioms Q857.real_dist
#print axioms Q857.exists_structure_of_min
#print axioms Q857.cmin_le_of_det_one
#print axioms Q857.complex_isLeast
