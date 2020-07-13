/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import algebra.polynomial.basic
import algebra.polynomial.big_operators
open polynomial finset

/-
# Monic polynomials

## Main results
- `card_pred_coeff_prod_X_sub_C` : yields that the trace is a coefficient of the characteristic polynomial
-/

noncomputable theory
open_locale big_operators

universes u w

variables {R : Type u} {α : Type w}

namespace polynomial

variables [comm_ring R]

namespace monic

lemma coeff_nat_degree {p : polynomial R} (hp : p.monic) : p.coeff (p.nat_degree) = 1 := by apply hp


@[simp]
lemma degree_one {p : polynomial R} (hp : p.monic) :
p.nat_degree = 0 ↔ p = 1 :=
begin
  split; intro h,
  swap, { rw h, exact nat_degree_one },
  have : p = C (p.coeff 0),
  { rw ← polynomial.degree_le_zero_iff,
    rwa polynomial.nat_degree_eq_zero_iff_degree_le_zero at h },
  rw this, convert C_1, rw ← h, apply hp,
end

lemma nat_degree_mul_eq [nontrivial R] {p q : polynomial R} (hp : p.monic) (hq : q.monic) :
(p * q).nat_degree = p.nat_degree + q.nat_degree :=
by { apply nat_degree_mul_eq', rw [hp.leading_coeff, hq.leading_coeff], simp }

lemma next_coeff_mul {p q : polynomial R} (hp : monic p) (hq : monic q) :
next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  classical,
  by_cases h : nontrivial R, swap,
  { rw nontrivial_iff at h, push_neg at h, apply h, },
  letI := h,
  have := monic.nat_degree_mul_eq hp hq,
  dsimp [next_coeff], rw this, simp [hp, hq], clear this,
  split_ifs; try {tauto <|> simp *},
  rename h_2 hp0, rename h_3 hq0, clear h_1,
  rw ← degree_one at hp0 hq0, any_goals {assumption},
  rw coeff_mul,
  transitivity ∑ (x : ℕ × ℕ) in _, ite (x.fst = p.nat_degree ∨ x.snd = q.nat_degree) (p.coeff x.fst * q.coeff x.snd) 0,
  { apply sum_congr rfl,
    intros x hx, split_ifs with hx1, refl,
    simp only [nat.mem_antidiagonal] at hx,
    push_neg at hx1, cases hx1 with hxp hxq,
    by_cases h_deg : x.fst < p.nat_degree,
    { suffices : q.coeff x.snd = 0, simp [this],
      apply coeff_eq_zero_of_nat_degree_lt, omega },
    suffices : p.coeff x.fst = 0, simp [this],
    apply coeff_eq_zero_of_nat_degree_lt, omega,
  },
  rw sum_ite, simp,
  have : filter (λ (x : ℕ × ℕ), x.fst = p.nat_degree ∨ x.snd = q.nat_degree) (nat.antidiagonal (p.nat_degree + q.nat_degree - 1))
    = {(p.nat_degree - 1, q.nat_degree),(p.nat_degree, q.nat_degree - 1)},
  { ext, rw mem_filter, simp only [mem_insert, mem_singleton, nat.mem_antidiagonal],
    split; intro ha,
    { rcases ha with ⟨ha, _ | _ ⟩,
      { right, ext, assumption, omega, },
      left, ext, omega, assumption },
    split, cases ha; { rw ha, ring, omega },
    cases ha; { rw ha, simp }},
  rw [this, sum_insert, sum_singleton],
  { dsimp, iterate 2 { rw coeff_nat_degree }, ring, assumption' },

  suffices : p.nat_degree - 1 ≠ p.nat_degree, { simp [this] },
  omega,
end

lemma next_coeff_prod
  (s : finset α) (f : α → polynomial R) (h : ∀ a : α, a ∈ s → monic (f a)) :
next_coeff (s.prod f) = s.sum (λ (a : α), next_coeff (f a)) :=
begin
  classical,
  revert h, apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty,
  finset.prod_empty, not_false_iff, forall_true_iff],
  rw ← C_1, rw next_coeff_C_eq_zero },
  { intros a s ha hs monic,
    rw finset.prod_insert ha,
    rw finset.sum_insert ha,
    rw next_coeff_mul (monic a (finset.mem_insert_self a s)), swap,
    { apply monic_prod_monic, intros b bs,
      apply monic, apply finset.mem_insert_of_mem bs },
    { refine congr rfl (hs _),
      intros b bs, apply monic, apply finset.mem_insert_of_mem bs }}
end

end monic

open monic
--sort of a special case of Vieta?
lemma card_pred_coeff_prod_X_sub_C' [nontrivial R] {s : finset α} (f : α → R) :
next_coeff ∏ i in s, (X - C (f i)) = -s.sum f :=
by { rw next_coeff_prod; { simp [monic_X_sub_C] } }

lemma card_pred_coeff_prod_X_sub_C [nontrivial R] (s : finset α) (f : α → R) (hs : 0 < s.card) :
(∏ i in s, (X - C (f i))).coeff (s.card - 1) = -s.sum f :=
begin
  convert card_pred_coeff_prod_X_sub_C' (by assumption),
  rw next_coeff, split_ifs,
  { rw nat_degree_prod_eq_of_monic at h,
    swap, { intros, apply monic_X_sub_C },
    rw sum_eq_zero_iff at h,
    simp_rw nat_degree_X_sub_C at h, contrapose! h, norm_num,
    exact multiset.card_pos_iff_exists_mem.mp hs },
  congr, rw nat_degree_prod_eq_of_monic; { simp [nat_degree_X_sub_C, monic_X_sub_C] },
end


end polynomial