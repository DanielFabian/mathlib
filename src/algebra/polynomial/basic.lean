/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
open polynomial finset

/-!
# Polynomials

Eventually, much of data/polynomial.lean should land here.

## Main results

We define two `ring_hom`s of type `polynomial R →+* R`,
- `eval_ring_hom`
- `coeff_zero_ring_hom`

We define a `monoid_hom` of type `polynomial R →* R`,
- `leading_coeff_monoid_hom`
-/

universes u w

noncomputable theory

variables {R : Type u} {α : Type w}

namespace polynomial

section comm_semiring
variables [comm_semiring R]

/-- A `ring_hom` which evaluates polynomials at a particular value -/
def eval_ring_hom : R → (polynomial R →+* R) := eval₂_ring_hom (ring_hom.id R)

@[simp]
lemma coe_eval_ring_hom (r : R) (p : polynomial R) : eval_ring_hom r p = eval r p := rfl

/-- A `ring_hom` returning the constant term, by evaluating at 0 -/
def coeff_zero_ring_hom : polynomial R →+* R := eval_ring_hom 0

@[simp]
lemma coe_coeff_zero_ring_hom (p : polynomial R) : coeff_zero_ring_hom p = p.coeff 0 :=
by { rw coeff_zero_eq_eval_zero p, refl }

end comm_semiring

section integral_domain
variable [integral_domain R]

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` is an `integral_domain`, and thus
  `leading_coeff` is multiplicative -/
def leading_coeff_monoid_hom : polynomial R →* R :=
{to_fun := leading_coeff, map_one' := by simp, map_mul' := leading_coeff_mul}

@[simp] lemma coe_leading_coeff_monoid_hom (p : polynomial R) :
  leading_coeff_monoid_hom p = leading_coeff p := rfl

end integral_domain
end polynomial
