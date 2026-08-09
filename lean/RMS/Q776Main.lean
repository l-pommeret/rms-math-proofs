import Mathlib
import RMS.Q776Asymptotics

/-!
# Q776 — terminal gates

This module imports the full Q776 development and checks the two canonical gates,
together with the axiom dependencies of the central multidimensional Laplace step.
-/

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

set_option grind.warning false

#check Q776.f_two_leading_stationary_phase
#check Q776.leading_additive

#print axioms Q776.local_estimate
#print axioms Q776.f_two_leading_stationary_phase
#print axioms Q776.leading_additive
