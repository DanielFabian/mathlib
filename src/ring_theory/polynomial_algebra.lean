/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.tensor_product
import ring_theory.matrix_algebra
import data.polynomial

/-!
We show `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`,
and combining this with the isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)` proved earlier,
we obtain
```
def matrix_polynomial_equiv_polynomial_matrix :
  matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)
```
which is characterized by
```
coeff (matrix_polynomial_equiv_polynomial_matrix m) k i j = coeff (m i j) k
```
-/

universes u v w

open_locale tensor_product

open polynomial
open tensor_product
open algebra.tensor_product

noncomputable theory

variables (R : Type u) [comm_ring R]
variables (A : Type v) [ring A] [algebra R A]

-- TODO move this back to `polynomial.lean`?
instance turkle : algebra R (polynomial A) := add_monoid_algebra.algebra

lemma turkle_map_apply (r : R) :
  algebra_map R (polynomial A) r = C (algebra_map R A r) :=
rfl

namespace polynomial_equiv_tensor

/--
(Implementation detail).
The bare function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`, on pure tensors.
-/
def to_fun (a : A) (p : polynomial R) : polynomial A :=
p.sum (λ n r, monomial n (a * algebra_map R A r))

-- move this
@[simp] lemma monomial_zero (i : ℕ) :
  monomial i (0 : A) = 0 :=
by simp [monomial]

-- move this
@[simp] lemma monomial_add (i : ℕ) (r s : A) :
  monomial i (r + s) = monomial i r + monomial i s :=
by simp [monomial]

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a linear map in the second factor.
-/
def to_fun_linear_right (a : A) : polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun R A a,
  map_smul' := λ r p,
  begin
    dsimp [to_fun],
    rw finsupp.sum_smul_index,
    { dsimp [finsupp.sum],
      rw finset.smul_sum,
      apply finset.sum_congr rfl,
      intros k hk,
      rw [monomial_eq_smul_X, monomial_eq_smul_X, algebra.smul_def, ← C_mul', ← C_mul',
          ← _root_.mul_assoc],
      congr' 1,
      rw [← algebra.commutes, ← algebra.commutes],
      simp only [ring_hom.map_mul, turkle_map_apply, _root_.mul_assoc] },
    { intro i, simp only [ring_hom.map_zero, mul_zero, monomial_zero] },
  end,
  map_add' := λ p q,
  begin
    simp only [to_fun],
    rw finsupp.sum_add_index,
    { simp only [monomial_zero, forall_const, ring_hom.map_zero, mul_zero], },
    { intros i r s, simp only [ring_hom.map_add, mul_add, monomial_add], },
  end, }

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a bilinear function of two arguments.
-/
def to_fun_bilinear : A →ₗ[R] polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun_linear_right R A,
  map_smul' := sorry,
  map_add' := sorry, }

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a linear map.
-/
def to_fun_linear : A ⊗[R] polynomial R →ₗ[R] polynomial A :=
tensor_product.lift (to_fun_bilinear R A)

/--
(Implementation detail).
The algebra homomorphism `A ⊗[R] polynomial R →ₐ[R] polynomial A`.
-/
def to_fun_alg_hom : A ⊗[R] polynomial R →ₐ[R] polynomial A :=
alg_hom_of_linear_map_tensor_product (to_fun_linear R A) sorry sorry

/--
(Implementation detail.)

The bare function `polynomial A → A ⊗[R] polynomial R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def inv_fun (p : polynomial A) : A ⊗[R] polynomial R :=
p.eval₂ include_left ((1 : A) ⊗ₜ[R] (X : polynomial R))

/--
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] polynomial R) ≃ polynomial A`.
-/
def equiv : (A ⊗[R] polynomial R) ≃ polynomial A :=
{ to_fun := to_fun_alg_hom R A,
  inv_fun := inv_fun R A,
  left_inv := sorry,
  right_inv := sorry, }

end polynomial_equiv_tensor

open polynomial_equiv_tensor

/--
The `R`-algebra isomorphism `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`.
-/
def polynomial_equiv_tensor : polynomial A ≃ₐ[R] (A ⊗[R] polynomial R) :=
alg_equiv.symm { ..(polynomial_equiv_tensor.to_fun_alg_hom R A), ..(polynomial_equiv_tensor.equiv R A) }

-- TODO update these if the definitions get changed above!

@[simp]
lemma polynomial_equiv_tensor_apply (p : polynomial A) :
  polynomial_equiv_tensor R A p = p.eval₂ include_left ((1 : A) ⊗ₜ[R] (X : polynomial R)) :=
rfl

@[simp]
lemma polynomial_equiv_tensor_symm_apply_tmul (a : A) (p : polynomial R) :
  (polynomial_equiv_tensor R A).symm (a ⊗ₜ p) = p.sum (λ n r, monomial n (a * algebra_map R A r)) :=
begin
  simp [polynomial_equiv_tensor, to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear],
  refl,
end

open matrix
open_locale big_operators

variables {R}
variables {n : Type w} [fintype n] [decidable_eq n]

/--
The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".
-/
noncomputable def matrix_polynomial_equiv_polynomial_matrix :
  matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R) :=
(((matrix_equiv_tensor R (polynomial R) n)).trans
  (algebra.tensor_product.comm R _ _)).trans
  (polynomial_equiv_tensor R (matrix n n R)).symm

-- maybe we don't need this?
lemma matrix_eq {X : Type*} [add_comm_monoid X] (m : matrix n n X) :
  m = ∑ (x : n × n), (λ i j, if (i, j) = x then m i j else 0) := by { ext, simp }

-- TODO move
-- @[elab_as_eliminator] protected lemma matrix.induction_on
--   {X : Type*} [add_comm_monoid X] {M : matrix n n X → Prop} (m : matrix n n X)
--   (h_add : ∀p q, M p → M q → M (p + q))
--   (h_elementary : ∀ i j x, M (λ i' j', if i' = i ∧ j' = j then x else 0)) :
--   M m := sorry -- is_basis.repr

-- TODO move
instance is_ring_hom_of_alg_hom
  {R : Type u} [comm_ring R] {A : Type v} [ring A] [algebra R A] {B : Type w} [ring B] [algebra R B]
  (f : A →ₐ[R] B) :
is_ring_hom f :=
{ map_one := by simp, map_mul := by simp, map_add := by simp }

lemma matrix_polynomial_equiv_polynomial_matrix_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
  matrix_polynomial_equiv_polynomial_matrix (λ i' j', if i' = i ∧ j' = j then monomial k x else 0) =
    monomial k (λ i' j', if i' = i ∧ j' = j then x else 0) :=
begin
  dsimp only [matrix_polynomial_equiv_polynomial_matrix, alg_equiv.trans_apply],
  simp only [matrix_equiv_tensor_apply_elementary],
  apply (polynomial_equiv_tensor R (matrix n n R)).injective,
  simp only [alg_equiv.apply_symm_apply],
  convert algebra.tensor_product.comm_tmul _ _ _ _ _,
  simp only [polynomial_equiv_tensor_apply],
  convert eval₂_monomial _ _,
  { simp only [algebra.tensor_product.tmul_mul_tmul, one_pow, _root_.one_mul, matrix.mul_one,
     algebra.tensor_product.tmul_pow, algebra.tensor_product.include_left_apply, mul_eq_mul],
    -- almost there: just use `R` bilinearity
    rw monomial_eq_smul_X,
    rw ← tensor_product.smul_tmul,
    congr, ext, simp },
  { apply_instance },
end

-- TODO add appropriate other versions, and move
lemma ite_add_zero {α : Type*} [add_monoid α] {P : Prop} [decidable P] {a b : α} :
  ite P (a + b) 0 = ite P a 0 + ite P b 0 :=
by { split_ifs; simp, }

lemma matrix_polynomial_equiv_polynomial_matrix_coeff_apply_aux_2
  (i j : n) (p : polynomial R) (k : ℕ) :
  coeff (matrix_polynomial_equiv_polynomial_matrix (λ i' j', if i' = i ∧ j' = j then p else 0)) k =
    (λ i' j', if i' = i ∧ j' = j then coeff p k else 0) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq,
    ext i' j',
    simp only [ite_add_zero],
    erw matrix_polynomial_equiv_polynomial_matrix.map_add,
    simp only [hp, hq, coeff_add, add_val],
    split_ifs; simp, },
  { intros k x,
    rw matrix_polynomial_equiv_polynomial_matrix_coeff_apply_aux_1,
    simp [coeff_single],
    split_ifs; { funext, simp, }, }
end

@[simp] lemma matrix_polynomial_equiv_polynomial_matrix_coeff_apply
  (m : matrix n n (polynomial R)) (k : ℕ) (i j : n) :
  coeff (matrix_polynomial_equiv_polynomial_matrix m) k i j = coeff (m i j) k :=
begin
  apply matrix.induction_on m,
  { intros p q hp hq, simp [hp, hq], },
  { intros i' j' x,
    rw matrix_polynomial_equiv_polynomial_matrix_coeff_apply_aux_2,
    dsimp,
    split_ifs; simp },
end

lemma matrix_polynomial_equiv_polynomial_matrix_smul_one (p : polynomial R) :
  matrix_polynomial_equiv_polynomial_matrix (p • 1) = p.map (algebra_map R (matrix n n R)) :=
begin
  ext m i j,
  simp [coeff_map, matrix.one_val],
  simp [algebra_map_matrix_val],
  split_ifs; simp,
end
