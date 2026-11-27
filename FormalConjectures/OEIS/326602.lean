/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import FormalConjecturesUtil

/-!
# OEIS A326602: Parity of Coefficients of $\sum_{n \ge 0} \frac{(x^{2n-1}+1)^n x^n}{(1+x^{2n+1})^{n+1}}$

In August 2019, Paul D. Hanna defined the formal power series
$$A(x) = \sum_{n \ge 0} \frac{(x^{2n-1} + 1)^n x^n}{(1 + x^{2n+1})^{n+1}}
       = \sum_{n \ge 0} \frac{(x^{2n} + x)^n}{(1 + x^{2n+1})^{n+1}} \in \mathbb{Z}[[x]],$$
observed that $A(x)$ is an even function $A(x) = \sum_{n \ge 0} a(n) x^{2n}$ (OEIS A326602),
and conjectured that $a(n)$ is odd if and only if $n$ is a perfect square.

In this file we prove:
1. `termSeries_spec`: each summand satisfies $(1 + x^{2n+1})^{n+1} T_n(x) = (x^{2n} + x)^n$.
2. `coeff_termSeries_eq_zero_of_lt`: $[x^N] T_n(x) = 0$ for all $n > N$, justifying convergence
   in the $x$-adic topology of $\mathbb{Z}[[x]]$.
3. `coeff_A_eq_triple_sum`: the exact multinomial triple-sum representation
   $$[x^N] A(x) = \sum_{\substack{a,b,c \ge 0 \\ a + c + 2(b+a)(b+c) = N}}
     (-1)^a \binom{b+c}{b} \binom{a+b+c}{a}.$$
4. `coeff_A_odd_eq_zero`: $[x^{2n+1}] A(x) = 0$ for all $n \in \mathbb{N}$ (so $A(x)$ is even).
5. `conjecture_parity`: for all $n \in \mathbb{N}$, `Odd (a n) ↔ ∃ b : ℕ, n = b ^ 2`,
   resolving Paul D. Hanna's 2019 conjecture.

*References:*
- [A326602](https://oeis.org/A326602), Paul D. Hanna, Aug 8, 2019.
-/

@[expose] public section

namespace OeisA326602

open PowerSeries Finset

/-- The formal power series $\sum_{r \ge 0} (-1)^r x^{d r} = (1 + x^d)^{-1} \in \mathbb{Z}[[x]]$. -/
noncomputable def geomAlt (d : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun N => if d ∣ N then (-1 : ℤ) ^ (N / d) else 0

/-- The $n$-th summand $\frac{(x^{2n} + x)^n}{(1 + x^{2n+1})^{n+1}} \in \mathbb{Z}[[x]]$
of the generating function of OEIS A326602. Note that $(x^{2n-1} + 1)^n x^n = (x^{2n} + x)^n$
for every $n \ge 0$, avoiding negative exponents at $n = 0$. -/
noncomputable def termSeries (n : ℕ) : ℤ⟦X⟧ :=
  (X ^ (2 * n) + X) ^ n * (geomAlt (2 * n + 1)) ^ (n + 1)

/-- The generating function $A(x) = \sum_{n \ge 0} \frac{(x^{2n} + x)^n}{(1 + x^{2n+1})^{n+1}}
\in \mathbb{Z}[[x]]$ of OEIS A326602. -/
noncomputable def A : ℤ⟦X⟧ :=
  PowerSeries.mk fun N => ∑ n ∈ range (N + 1), coeff N (termSeries n)

/-- The sequence OEIS A326602: $a(n) = [x^{2n}] A(x)$. -/
noncomputable def a (n : ℕ) : ℤ :=
  coeff (2 * n) A

/-- The finite set of nonnegative integer triples $(a, b, c)$ satisfying
$a + c + 2(b + a)(b + c) = N$. -/
def tripleSet (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ (range (N + 1) ×ˢ range (N + 1))).filter
    fun t => t.1 + t.2.2 + 2 * (t.2.1 + t.1) * (t.2.1 + t.2.2) = N

/-- The signed multinomial weight $(-1)^a \frac{(a+b+c)!}{a!\,b!\,c!}
= (-1)^a \binom{b+c}{b}\binom{a+b+c}{a}$ of a triple $(a, b, c)$. -/
def tripleWeight (t : ℕ × ℕ × ℕ) : ℤ :=
  (-1 : ℤ) ^ t.1 * (Nat.choose (t.2.1 + t.2.2) t.2.1 : ℤ) *
    (Nat.choose (t.2.1 + t.2.2 + t.1) t.1 : ℤ)

/-! ### Part 1: Verification of the inverse series `(1 + X^d) * geomAlt d = 1` -/

section Helpers
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

private lemma coeff_geomAlt (d N : ℕ) :
    coeff N (geomAlt d) = if d ∣ N then (-1 : ℤ) ^ (N / d) else 0 := by
  simp [geomAlt]

private lemma one_add_X_pow_mul_geomAlt {d : ℕ} (hd : 0 < d) :
    (1 + X ^ d) * geomAlt d = 1 := by
  ext N
  rw [add_mul, one_mul, map_add, coeff_X_pow_mul']
  by_cases hN : N < d
  · have hnot : ¬ d ≤ N := not_le.mpr hN
    simp only [hnot, ↓reduceIte, add_zero, coeff_geomAlt, coeff_one]
    by_cases h0 : N = 0
    · subst h0; simp
    · have hnd : ¬ d ∣ N := fun h => h0 (Nat.eq_zero_of_dvd_of_lt h hN)
      simp [h0, hnd]
  · have hle : d ≤ N := not_lt.mp hN
    have hne : N ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le hd hle)
    simp only [hle, ↓reduceIte, coeff_geomAlt, coeff_one, hne]
    by_cases hdvd : d ∣ N
    · have hdvd' : d ∣ N - d := (Nat.dvd_sub_iff_left hle (dvd_refl d)).mpr hdvd
      have hdiv : N / d = (N - d) / d + 1 := by
        obtain ⟨k, hk⟩ := hdvd
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · simp at hk; exact absurd hk hne
          · exact hpos
        rw [hk, Nat.mul_div_cancel_left k hd]
        have hsub : d * k - d = d * (k - 1) := by rw [Nat.mul_sub_one]
        rw [hsub, Nat.mul_div_cancel_left (k - 1) hd]
        omega
      simp only [hdvd, hdvd', ↓reduceIte, hdiv, pow_succ]
      ring
    · have hdvd' : ¬ d ∣ N - d := fun h => hdvd ((Nat.dvd_sub_iff_left hle (dvd_refl d)).mp h)
      simp [hdvd, hdvd']

private lemma sum_range_choose_add (n r : ℕ) :
    ∑ i ∈ range (r + 1), Nat.choose (n + i) i = Nat.choose (n + 1 + r) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : n + 1 + (r + 1) = (n + 1 + r) + 1 := by omega
    have h2 : n + (r + 1) = n + 1 + r := by omega
    rw [h1, h2, Nat.choose_succ_succ', add_comm]

private lemma coeff_geomAlt_pow {d : ℕ} (hd : 0 < d) (n N : ℕ) :
    coeff N ((geomAlt d) ^ (n + 1)) =
      if d ∣ N then (-1 : ℤ) ^ (N / d) * (Nat.choose (n + N / d) (N / d) : ℤ) else 0 := by
  induction n generalizing N with
  | zero =>
    simp [pow_one, coeff_geomAlt]
  | succ n ih =>
    rw [pow_succ, coeff_mul]
    by_cases hdvd : d ∣ N
    · obtain ⟨r, rfl⟩ := hdvd
      simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left r hd]
      have hsum :
          ∑ p ∈ antidiagonal (d * r),
            coeff p.1 ((geomAlt d) ^ (n + 1)) * coeff p.2 (geomAlt d)
          = ∑ i ∈ range (r + 1),
              coeff (d * i) ((geomAlt d) ^ (n + 1)) * coeff (d * (r - i)) (geomAlt d) := by
        symm
        refine Finset.sum_of_injOn (fun i => (d * i, d * (r - i))) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro i₁ _ i₂ _ h
          have h1 : d * i₁ = d * i₂ := congrArg Prod.fst h
          exact Nat.eq_of_mul_eq_mul_left hd h1
        · intro i hi
          rw [Finset.mem_coe, Finset.mem_range] at hi
          rw [Finset.mem_coe, HasAntidiagonal.mem_antidiagonal]
          have : d * i + d * (r - i) = d * (i + (r - i)) := by rw [← Nat.mul_add]
          rw [this, Nat.add_sub_of_le (Nat.lt_succ_iff.mp hi)]
        · intro p hp hnot
          rw [HasAntidiagonal.mem_antidiagonal] at hp
          by_cases h1 : d ∣ p.1
          · exfalso
            apply hnot
            obtain ⟨i, hi⟩ := h1
            have hir : i ≤ r := by
              have : d * i ≤ d * r := by omega
              exact Nat.le_of_mul_le_mul_left this hd
            refine ⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hir)), ?_⟩
            ext
            · exact hi.symm
            · dsimp only
              have h2 : d * (r - i) = d * r - d * i := Nat.mul_sub_left_distrib d r i
              omega
          · rw [ih p.1]
            simp [h1]
      rw [hsum]
      have hterm : ∀ i ∈ range (r + 1),
          coeff (d * i) ((geomAlt d) ^ (n + 1)) * coeff (d * (r - i)) (geomAlt d)
          = (-1 : ℤ) ^ r * (Nat.choose (n + i) i : ℤ) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [ih (d * i), coeff_geomAlt]
        simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hd]
        have hpow : (-1 : ℤ) ^ i * (-1 : ℤ) ^ (r - i) = (-1 : ℤ) ^ r := by
          rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp hi)]
        calc
          (-1 : ℤ) ^ i * (Nat.choose (n + i) i : ℤ) * (-1 : ℤ) ^ (r - i)
              = ((-1 : ℤ) ^ i * (-1 : ℤ) ^ (r - i)) * (Nat.choose (n + i) i : ℤ) := by ring
          _ = (-1 : ℤ) ^ r * (Nat.choose (n + i) i : ℤ) := by rw [hpow]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Nat.cast_sum, sum_range_choose_add]
    · simp only [hdvd, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro p hp
      rw [HasAntidiagonal.mem_antidiagonal] at hp
      rw [ih p.1, coeff_geomAlt]
      by_cases h1 : d ∣ p.1
      · have h2 : ¬ d ∣ p.2 := fun h2 => hdvd (hp ▸ dvd_add h1 h2)
        simp [h2]
      · simp [h1]

private lemma coeff_X_pow_add_X_pow (n M : ℕ) :
    coeff M ((X ^ (2 * n) + X : ℤ⟦X⟧) ^ n) =
      ∑ b ∈ range (n + 1),
        if 2 * n * b + (n - b) = M then (Nat.choose n b : ℤ) else 0 := by
  rw [add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hpow : (X ^ (2 * n) : ℤ⟦X⟧) ^ b * X ^ (n - b) = X ^ (2 * n * b + (n - b)) := by
    rw [← pow_mul, ← pow_add]
  have hcast : ((Nat.choose n b : ℕ) : ℤ⟦X⟧) = C (Nat.choose n b : ℤ) := by
    simp
  rw [hpow, hcast, coeff_mul_C, coeff_X_pow]
  by_cases h : 2 * n * b + (n - b) = M
  · simp [h]
  · have h' : M ≠ 2 * n * b + (n - b) := Ne.symm h
    simp [h, h']

private lemma coeff_termSeries_eq_sum (n N : ℕ) :
    coeff N (termSeries n) =
      ∑ b ∈ range (n + 1), ∑ a ∈ range (N + 1),
        if 2 * n * b + (n - b) + (2 * n + 1) * a = N then
          (-1 : ℤ) ^ a * (Nat.choose n b : ℤ) * (Nat.choose (n + a) a : ℤ)
        else 0 := by
  unfold termSeries
  rw [coeff_mul]
  have h1 :
      ∑ p ∈ antidiagonal N,
        coeff p.1 ((X ^ (2 * n) + X : ℤ⟦X⟧) ^ n) * coeff p.2 ((geomAlt (2 * n + 1)) ^ (n + 1))
      = ∑ p ∈ antidiagonal N, ∑ b ∈ range (n + 1),
          (if 2 * n * b + (n - b) = p.1 then (Nat.choose n b : ℤ) else 0) *
            coeff p.2 ((geomAlt (2 * n + 1)) ^ (n + 1)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [coeff_X_pow_add_X_pow, Finset.sum_mul]
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  let E := 2 * n * b + (n - b)
  by_cases hEN : E ≤ N
  · have hleft :
        ∑ p ∈ antidiagonal N,
          (if E = p.1 then (Nat.choose n b : ℤ) else 0) *
            coeff p.2 ((geomAlt (2 * n + 1)) ^ (n + 1))
        = (Nat.choose n b : ℤ) * coeff (N - E) ((geomAlt (2 * n + 1)) ^ (n + 1)) := by
      rw [Finset.sum_eq_single (E, N - E)]
      · simp
      · intro p hp hne
        rw [HasAntidiagonal.mem_antidiagonal] at hp
        have hp1 : E ≠ p.1 := by
          intro heq
          apply hne
          ext
          · exact heq.symm
          · omega
        simp [hp1]
      · intro hnot
        exfalso
        apply hnot
        rw [HasAntidiagonal.mem_antidiagonal]
        omega
    rw [hleft, coeff_geomAlt_pow (Nat.succ_pos (2 * n))]
    by_cases hdvd : (2 * n + 1) ∣ (N - E)
    · simp only [hdvd, ↓reduceIte]
      set q := (N - E) / (2 * n + 1)
      have hq_mul : (2 * n + 1) * q = N - E := Nat.mul_div_cancel' hdvd
      have hq_le : q ≤ N := by
        have : q ≤ (2 * n + 1) * q := Nat.le_mul_of_pos_left q (Nat.succ_pos (2 * n))
        omega
      symm
      rw [Finset.sum_eq_single q]
      · have heq : E + (2 * n + 1) * q = N := by omega
        simp only [E] at heq ⊢
        simp only [heq, ↓reduceIte]
        ring
      · intro a _ haq
        have hne : E + (2 * n + 1) * a ≠ N := by
          intro h
          have : (2 * n + 1) * a = (2 * n + 1) * q := by omega
          exact haq (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos (2 * n)) this)
        simp only [E] at hne ⊢
        simp [hne]
      · intro hnot
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hq_le)) hnot
    · simp only [hdvd, ↓reduceIte, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro a _
      have hne : E + (2 * n + 1) * a ≠ N := by
        intro h
        apply hdvd
        exact ⟨a, by omega⟩
      simp only [E] at hne ⊢
      simp [hne]
  · have hleft :
        ∑ p ∈ antidiagonal N,
          (if E = p.1 then (Nat.choose n b : ℤ) else 0) *
            coeff p.2 ((geomAlt (2 * n + 1)) ^ (n + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [HasAntidiagonal.mem_antidiagonal] at hp
      have hne : E ≠ p.1 := by omega
      simp [hne]
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro a _
    have hne : E + (2 * n + 1) * a ≠ N := by omega
    simp only [E] at hne ⊢
    simp [hne]

private lemma exponent_identity (a b c : ℕ) :
    2 * (b + c) * b + c + (2 * (b + c) + 1) * a =
      a + c + 2 * (b + a) * (b + c) := by
  ring

private def swapTriple (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t.2.2, t.2.1, t.1)

private lemma swapTriple_invol (t : ℕ × ℕ × ℕ) : swapTriple (swapTriple t) = t := by
  rcases t with ⟨a, b, c⟩; rfl

private lemma swapTriple_mem_tripleSet {N : ℕ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ tripleSet N) : swapTriple t ∈ tripleSet N := by
  rcases t with ⟨a, b, c⟩
  simp only [tripleSet, swapTriple, Finset.mem_filter, Finset.mem_product] at ht ⊢
  refine ⟨⟨ht.1.2.2, ht.1.2.1, ht.1.1⟩, ?_⟩
  linarith [ht.2]

private lemma multinomial_symm (a b c : ℕ) :
    Nat.choose (b + c) b * Nat.choose (b + c + a) a =
      Nat.choose (b + a) b * Nat.choose (b + a + c) c := by
  have hpos : 0 < a.factorial * b.factorial * c.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hL :
      Nat.choose (b + c) b * Nat.choose (b + c + a) a * (a.factorial * b.factorial * c.factorial)
      = (a + b + c).factorial := by
    have h1 : Nat.choose (b + c) b * b.factorial * c.factorial = (b + c).factorial := by
      simpa [Nat.add_sub_cancel_left] using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right b c)
    have h2 : Nat.choose (b + c + a) a * a.factorial * (b + c).factorial = (b + c + a).factorial := by
      simpa [Nat.add_sub_cancel_right] using
        Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left a (b + c))
    calc
      Nat.choose (b + c) b * Nat.choose (b + c + a) a * (a.factorial * b.factorial * c.factorial)
          = Nat.choose (b + c + a) a * a.factorial *
              (Nat.choose (b + c) b * b.factorial * c.factorial) := by ring
      _ = Nat.choose (b + c + a) a * a.factorial * (b + c).factorial := by rw [h1]
      _ = (b + c + a).factorial := h2
      _ = (a + b + c).factorial := by congr 1; omega
  have hR :
      Nat.choose (b + a) b * Nat.choose (b + a + c) c * (a.factorial * b.factorial * c.factorial)
      = (a + b + c).factorial := by
    have h1 : Nat.choose (b + a) b * b.factorial * a.factorial = (b + a).factorial := by
      simpa [Nat.add_sub_cancel_left] using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right b a)
    have h2 : Nat.choose (b + a + c) c * c.factorial * (b + a).factorial = (b + a + c).factorial := by
      simpa [Nat.add_sub_cancel_right] using
        Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left c (b + a))
    calc
      Nat.choose (b + a) b * Nat.choose (b + a + c) c * (a.factorial * b.factorial * c.factorial)
          = Nat.choose (b + a + c) c * c.factorial *
              (Nat.choose (b + a) b * b.factorial * a.factorial) := by ring
      _ = Nat.choose (b + a + c) c * c.factorial * (b + a).factorial := by rw [h1]
      _ = (b + a + c).factorial := h2
      _ = (a + b + c).factorial := by congr 1; omega
  rw [hL, hR]

private lemma neg_one_pow_eq_neg_of_odd_add {a c : ℕ} (h : Odd (a + c)) :
    (-1 : ℤ) ^ c = -((-1 : ℤ) ^ a) := by
  obtain ⟨k, hk⟩ := h
  have h1 : (-1 : ℤ) ^ a * (-1 : ℤ) ^ c = -1 := by
    rw [← pow_add, hk, pow_add, pow_mul]
    norm_num
  have h2 : (-1 : ℤ) ^ a * (-1 : ℤ) ^ a = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℤ) ^ c = ((-1 : ℤ) ^ a * (-1 : ℤ) ^ a) * (-1 : ℤ) ^ c := by rw [h2, one_mul]
    _ = (-1 : ℤ) ^ a * ((-1 : ℤ) ^ a * (-1 : ℤ) ^ c) := by ring
    _ = (-1 : ℤ) ^ a * (-1) := by rw [h1]
    _ = -((-1 : ℤ) ^ a) := by ring

private lemma neg_one_pow_eq_of_even_add {a c : ℕ} (h : Even (a + c)) :
    (-1 : ℤ) ^ c = (-1 : ℤ) ^ a := by
  obtain ⟨k, hk⟩ := h
  have h1 : (-1 : ℤ) ^ a * (-1 : ℤ) ^ c = 1 := by
    rw [← pow_add, hk, ← two_mul, pow_mul]
    norm_num
  have h2 : (-1 : ℤ) ^ a * (-1 : ℤ) ^ a = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℤ) ^ c = ((-1 : ℤ) ^ a * (-1 : ℤ) ^ a) * (-1 : ℤ) ^ c := by rw [h2, one_mul]
    _ = (-1 : ℤ) ^ a * ((-1 : ℤ) ^ a * (-1 : ℤ) ^ c) := by ring
    _ = (-1 : ℤ) ^ a := by rw [h1, mul_one]

private lemma even_central_choose {a : ℕ} (ha : 0 < a) : Even (Nat.choose (2 * a) a) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [h1, Nat.choose_succ_succ]
  have hsym : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    have := Nat.choose_symm (show m ≤ 2 * m + 1 by omega)
    have hsub : 2 * m + 1 - m = m + 1 := by omega
    rw [hsub] at this
    exact this
  rw [hsym]
  exact ⟨Nat.choose (2 * m + 1) m, rfl⟩

private lemma even_fixed_multinomial {a : ℕ} (ha : 0 < a) (b : ℕ) :
    Even (Nat.choose (b + a) b * Nat.choose (b + a + a) a) := by
  have hfac :
      Nat.choose (b + a) b * Nat.choose (b + a + a) a =
        Nat.choose (b + 2 * a) (2 * a) * Nat.choose (2 * a) a := by
    have hpos : 0 < a.factorial * a.factorial * b.factorial := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    have hL :
        Nat.choose (b + a) b * Nat.choose (b + a + a) a * (a.factorial * a.factorial * b.factorial)
        = (b + 2 * a).factorial := by
      have h1 : Nat.choose (b + a) b * b.factorial * a.factorial = (b + a).factorial := by
        simpa [Nat.add_sub_cancel_left] using
          Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right b a)
      have h2 : Nat.choose (b + a + a) a * a.factorial * (b + a).factorial = (b + a + a).factorial := by
        simpa [Nat.add_sub_cancel_right] using
          Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left a (b + a))
      calc
        Nat.choose (b + a) b * Nat.choose (b + a + a) a * (a.factorial * a.factorial * b.factorial)
            = Nat.choose (b + a + a) a * a.factorial *
                (Nat.choose (b + a) b * b.factorial * a.factorial) := by ring
        _ = Nat.choose (b + a + a) a * a.factorial * (b + a).factorial := by rw [h1]
        _ = (b + a + a).factorial := h2
        _ = (b + 2 * a).factorial := by congr 1; omega
    have hR :
        Nat.choose (b + 2 * a) (2 * a) * Nat.choose (2 * a) a *
          (a.factorial * a.factorial * b.factorial)
        = (b + 2 * a).factorial := by
      have h1 : Nat.choose (2 * a) a * a.factorial * a.factorial = (2 * a).factorial := by
        have hsub : 2 * a - a = a := by omega
        simpa [hsub] using Nat.choose_mul_factorial_mul_factorial (show a ≤ 2 * a by omega)
      have h2 : Nat.choose (b + 2 * a) (2 * a) * (2 * a).factorial * b.factorial =
          (b + 2 * a).factorial := by
        simpa [Nat.add_sub_cancel_right] using
          Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left (2 * a) b)
      calc
        Nat.choose (b + 2 * a) (2 * a) * Nat.choose (2 * a) a *
            (a.factorial * a.factorial * b.factorial)
            = Nat.choose (b + 2 * a) (2 * a) *
                (Nat.choose (2 * a) a * a.factorial * a.factorial) * b.factorial := by ring
        _ = Nat.choose (b + 2 * a) (2 * a) * (2 * a).factorial * b.factorial := by rw [h1]
        _ = (b + 2 * a).factorial := h2
    rw [hL, hR]
  rw [hfac]
  exact Even.mul_left (even_central_choose ha) _

end Helpers

/-! ### Main Theorems -/

/-- Each summand `termSeries n` satisfies the defining rational-function equation
`(1 + X^(2n+1))^(n+1) * termSeries n = (X^(2n) + X)^n`. -/
@[category test, AMS 5 11]
theorem termSeries_spec (n : ℕ) :
    (1 + X ^ (2 * n + 1)) ^ (n + 1) * termSeries n = (X ^ (2 * n) + X) ^ n := by
  unfold termSeries
  calc
    (1 + X ^ (2 * n + 1)) ^ (n + 1) * ((X ^ (2 * n) + X) ^ n * (geomAlt (2 * n + 1)) ^ (n + 1))
        = (X ^ (2 * n) + X) ^ n * ((1 + X ^ (2 * n + 1)) * geomAlt (2 * n + 1)) ^ (n + 1) := by
          rw [mul_pow]; ring
    _ = (X ^ (2 * n) + X) ^ n := by
          rw [one_add_X_pow_mul_geomAlt (Nat.succ_pos (2 * n)), one_pow, mul_one]

/-- The $N$-th coefficient of `termSeries n` vanishes whenever $N < n$, justifying
the formal infinite sum $A(x) = \sum_{n \ge 0} T_n(x)$. -/
@[category test, AMS 5 11]
theorem coeff_termSeries_eq_zero_of_lt {n N : ℕ} (h : N < n) :
    coeff N (termSeries n) = 0 := by
  unfold termSeries
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : coeff p.1 ((X ^ (2 * n) + X : ℤ⟦X⟧) ^ n) = 0 := by
    rw [coeff_X_pow_add_X_pow]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_range] at hb
    have hge : n ≤ 2 * n * b + (n - b) := by
      rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · simp
      · have : 2 * n ≤ 2 * n * b := Nat.le_mul_of_pos_right (2 * n) hbpos
        omega
    have hne : 2 * n * b + (n - b) ≠ p.1 := by omega
    simp [hne]
  rw [h1, zero_mul]

/-- **Theorem 1 (Exact Triple-Sum Representation).**
For every $N \in \mathbb{N}$,
$$[x^N] A(x) = \sum_{\substack{a, b, c \ge 0 \\ a + c + 2(b + a)(b + c) = N}}
  (-1)^a \binom{b+c}{b}\binom{a+b+c}{a}.$$ -/
@[category research solved, AMS 5 11]
theorem coeff_A_eq_triple_sum (N : ℕ) :
    coeff N A = ∑ t ∈ tripleSet N, tripleWeight t := by
  simp only [A, coeff_mk]
  have h1 :
      ∑ n ∈ range (N + 1), coeff N (termSeries n)
      = ∑ n ∈ range (N + 1), ∑ b ∈ range (n + 1), ∑ a ∈ range (N + 1),
          if 2 * n * b + (n - b) + (2 * n + 1) * a = N then
            (-1 : ℤ) ^ a * (Nat.choose n b : ℤ) * (Nat.choose (n + a) a : ℤ)
          else 0 := by
    apply Finset.sum_congr rfl
    intro n _
    exact coeff_termSeries_eq_sum n N
  rw [h1]
  let S_nba : Finset (Σ _ : ℕ, ℕ × ℕ) :=
    (range (N + 1)).sigma fun n => range (n + 1) ×ˢ range (N + 1)
  have h2 :
      (∑ n ∈ range (N + 1), ∑ b ∈ range (n + 1), ∑ a ∈ range (N + 1),
        if 2 * n * b + (n - b) + (2 * n + 1) * a = N then
          (-1 : ℤ) ^ a * (Nat.choose n b : ℤ) * (Nat.choose (n + a) a : ℤ)
        else 0)
      = ∑ x ∈ S_nba,
          if 2 * x.1 * x.2.1 + (x.1 - x.2.1) + (2 * x.1 + 1) * x.2.2 = N then
            (-1 : ℤ) ^ x.2.2 * (Nat.choose x.1 x.2.1 : ℤ) * (Nat.choose (x.1 + x.2.2) x.2.2 : ℤ)
          else 0 := by
    simp only [S_nba, Finset.sum_sigma, Finset.sum_product]
  rw [h2, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun t => ⟨t.2.1 + t.2.2, (t.2.1, t.1)⟩)
    (fun x => (x.2.2, x.2.1, x.1 - x.2.1)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rcases t with ⟨a, b, c⟩
    simp only [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
    obtain ⟨⟨ha, hb, hc⟩, heq⟩ := ht
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [S_nba, Finset.mem_sigma, Finset.mem_product, Finset.mem_range]
      have hbc : b + c ≤ N := by
        rcases Nat.eq_zero_or_pos b with rfl | hbpos
        · omega
        · have hmul : b + c ≤ (b + a) * (b + c) := Nat.le_mul_of_pos_left (b + c) (by omega)
          have hmul2 : 2 * (b + a) * (b + c) = 2 * ((b + a) * (b + c)) := by ring
          omega
      exact ⟨by omega, by omega, ha⟩
    · simp only
      have hsub : b + c - b = c := Nat.add_sub_cancel_left b c
      rw [hsub, exponent_identity]
      exact heq
  · intro x hx
    rcases x with ⟨n, b, a⟩
    rw [Finset.mem_filter] at hx
    obtain ⟨hxmem, heq⟩ := hx
    simp only [S_nba, Finset.mem_sigma, Finset.mem_product, Finset.mem_range] at hxmem
    obtain ⟨hn, hb, ha⟩ := hxmem
    simp only [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨ha, by omega, by omega⟩, ?_⟩
    dsimp only at heq
    have hbc : b + (n - b) = n := Nat.add_sub_of_le (Nat.lt_succ_iff.mp hb)
    have hid := exponent_identity a b (n - b)
    rw [hbc] at hid ⊢
    rw [← hid, heq]
  · intro t _
    rcases t with ⟨a, b, c⟩
    simp
  · intro x hx
    rcases x with ⟨n, b, a⟩
    rw [Finset.mem_filter] at hx
    obtain ⟨hxmem, _⟩ := hx
    simp only [S_nba, Finset.mem_sigma, Finset.mem_product, Finset.mem_range] at hxmem
    obtain ⟨_, hb, _⟩ := hxmem
    have hbc : b + (n - b) = n := Nat.add_sub_of_le (Nat.lt_succ_iff.mp hb)
    exact Sigma.ext hbc (by simp)
  · intro t _
    rfl

/-- **Theorem 2 (Evenness of $A(x)$).**
Every odd-degree coefficient of $A(x)$ vanishes: $[x^{2n+1}] A(x) = 0$ for all $n \in \mathbb{N}$. -/
@[category research solved, AMS 5 11]
theorem coeff_A_odd_eq_zero (n : ℕ) : coeff (2 * n + 1) A = 0 := by
  rw [coeff_A_eq_triple_sum]
  set S := ∑ t ∈ tripleSet (2 * n + 1), tripleWeight t
  have hneg : S = -S := by
    calc
      S = ∑ t ∈ tripleSet (2 * n + 1), tripleWeight (swapTriple t) := by
            symm
            refine Finset.sum_nbij' swapTriple swapTriple ?_ ?_ ?_ ?_ ?_
            · intro t ht; exact swapTriple_mem_tripleSet ht
            · intro t ht; exact swapTriple_mem_tripleSet ht
            · intro t _; exact swapTriple_invol t
            · intro t _; exact swapTriple_invol t
            · intro _ _; rfl
      _ = ∑ t ∈ tripleSet (2 * n + 1), -tripleWeight t := by
            apply Finset.sum_congr rfl
            intro t ht
            rcases t with ⟨a, b, c⟩
            simp only [tripleSet, Finset.mem_filter] at ht
            have hmul2 : 2 * (b + a) * (b + c) = 2 * ((b + a) * (b + c)) := by ring
            have hodd : Odd (a + c) := by
              refine ⟨n - (b + a) * (b + c), ?_⟩
              omega
            simp only [tripleWeight, swapTriple]
            have hsym :
                (Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + c) c : ℤ) =
                (Nat.choose (b + c) b : ℤ) * (Nat.choose (b + c + a) a : ℤ) := by
              exact_mod_cast (multinomial_symm a b c).symm
            rw [neg_one_pow_eq_neg_of_odd_add hodd]
            calc
              -((-1 : ℤ) ^ a) * (Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + c) c : ℤ)
                  = -((-1 : ℤ) ^ a * ((Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + c) c : ℤ))) := by ring
              _ = -((-1 : ℤ) ^ a * ((Nat.choose (b + c) b : ℤ) * (Nat.choose (b + c + a) a : ℤ))) := by rw [hsym]
              _ = -((-1 : ℤ) ^ a * (Nat.choose (b + c) b : ℤ) * (Nat.choose (b + c + a) a : ℤ)) := by ring
      _ = -S := Finset.sum_neg_distrib tripleWeight
  omega

/-- **Theorem 3 (Resolution of Paul D. Hanna's 2019 Conjecture on OEIS A326602).**
For every $n \in \mathbb{N}$, the $n$-th term $a(n) = [x^{2n}] A(x)$ of OEIS A326602 is odd
if and only if $n$ is a perfect square. -/
@[category research solved, AMS 5 11]
theorem conjecture_parity (n : ℕ) : Odd (a n) ↔ ∃ b : ℕ, n = b ^ 2 := by
  unfold a
  rw [coeff_A_eq_triple_sum]
  set T := tripleSet (2 * n)
  have hpart1 :
      ∑ t ∈ T, tripleWeight t =
        (∑ t ∈ T.filter (fun t => t.1 = t.2.2), tripleWeight t) +
        (∑ t ∈ T.filter (fun t => t.1 ≠ t.2.2), tripleWeight t) :=
    (Finset.sum_filter_add_sum_filter_not T (fun t => t.1 = t.2.2) tripleWeight).symm
  have hoff_even : Even (∑ t ∈ T.filter (fun t => t.1 ≠ t.2.2), tripleWeight t) := by
    have hsplit :
        ∑ t ∈ T.filter (fun t => t.1 ≠ t.2.2), tripleWeight t =
          (∑ t ∈ (T.filter (fun t => t.1 ≠ t.2.2)).filter (fun t => t.1 < t.2.2), tripleWeight t) +
          (∑ t ∈ (T.filter (fun t => t.1 ≠ t.2.2)).filter (fun t => ¬ t.1 < t.2.2), tripleWeight t) :=
      (Finset.sum_filter_add_sum_filter_not _ (fun t => t.1 < t.2.2) tripleWeight).symm
    have hbij :
        ∑ t ∈ (T.filter (fun t => t.1 ≠ t.2.2)).filter (fun t => t.1 < t.2.2), tripleWeight t =
        ∑ t ∈ (T.filter (fun t => t.1 ≠ t.2.2)).filter (fun t => ¬ t.1 < t.2.2), tripleWeight t := by
      refine Finset.sum_nbij' swapTriple swapTriple ?_ ?_ ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_filter] at ht ⊢
        refine ⟨⟨swapTriple_mem_tripleSet ht.1.1, ?_⟩, ?_⟩
        · simp only [swapTriple]; omega
        · simp only [swapTriple]; omega
      · intro t ht
        simp only [Finset.mem_filter] at ht ⊢
        refine ⟨⟨swapTriple_mem_tripleSet ht.1.1, ?_⟩, ?_⟩
        · simp only [swapTriple]; omega
        · simp only [swapTriple]; omega
      · intro t _; exact swapTriple_invol t
      · intro t _; exact swapTriple_invol t
      · intro t ht
        rcases t with ⟨a, b, c⟩
        simp only [Finset.mem_filter] at ht
        have hmem := ht.1.1
        simp only [T, tripleSet, Finset.mem_filter] at hmem
        have hmul2 : 2 * (b + a) * (b + c) = 2 * ((b + a) * (b + c)) := by ring
        have heven : Even (a + c) := by
          refine ⟨n - (b + a) * (b + c), ?_⟩
          omega
        simp only [tripleWeight, swapTriple]
        have hsym :
            (Nat.choose (b + c) b : ℤ) * (Nat.choose (b + c + a) a : ℤ) =
            (Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + c) c : ℤ) := by
          exact_mod_cast multinomial_symm a b c
        rw [neg_one_pow_eq_of_even_add heven]
        calc
          (-1 : ℤ) ^ a * (Nat.choose (b + c) b : ℤ) * (Nat.choose (b + c + a) a : ℤ)
              = (-1 : ℤ) ^ a * ((Nat.choose (b + c) b : ℤ) * (Nat.choose (b + c + a) a : ℤ)) := by ring
          _ = (-1 : ℤ) ^ a * ((Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + c) c : ℤ)) := by rw [hsym]
          _ = (-1 : ℤ) ^ a * (Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + c) c : ℤ) := by ring
    rw [hsplit, ← hbij]
    exact ⟨_, rfl⟩
  set D := T.filter (fun t => t.1 = t.2.2)
  have hpart2 :
      ∑ t ∈ D, tripleWeight t =
        (∑ t ∈ D.filter (fun t => t.1 = 0), tripleWeight t) +
        (∑ t ∈ D.filter (fun t => t.1 ≠ 0), tripleWeight t) :=
    (Finset.sum_filter_add_sum_filter_not D (fun t => t.1 = 0) tripleWeight).symm
  have hdiag_pos_even : Even (∑ t ∈ D.filter (fun t => t.1 ≠ 0), tripleWeight t) := by
    have hall : ∀ t ∈ D.filter (fun t => t.1 ≠ 0), Even (tripleWeight t) := by
      intro t ht
      rcases t with ⟨a, b, c⟩
      simp only [D, Finset.mem_filter] at ht
      obtain ⟨⟨_, hac⟩, ha0⟩ := ht
      subst hac
      have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      obtain ⟨k, hk⟩ := even_fixed_multinomial hapos b
      refine ⟨(-1 : ℤ) ^ a * (k : ℤ), ?_⟩
      simp only [tripleWeight]
      have hcast :
          (Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + a) a : ℤ) = (k : ℤ) + (k : ℤ) := by
        exact_mod_cast hk
      calc
        (-1 : ℤ) ^ a * (Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + a) a : ℤ)
            = (-1 : ℤ) ^ a * ((Nat.choose (b + a) b : ℤ) * (Nat.choose (b + a + a) a : ℤ)) := by ring
        _ = (-1 : ℤ) ^ a * ((k : ℤ) + (k : ℤ)) := by rw [hcast]
        _ = (-1 : ℤ) ^ a * (k : ℤ) + (-1 : ℤ) ^ a * (k : ℤ) := by ring
    exact Finset.even_sum _ hall
  have htotal :
      ∑ t ∈ T, tripleWeight t =
        (∑ t ∈ D.filter (fun t => t.1 = 0), tripleWeight t) +
        ((∑ t ∈ D.filter (fun t => t.1 ≠ 0), tripleWeight t) +
         (∑ t ∈ T.filter (fun t => t.1 ≠ t.2.2), tripleWeight t)) := by
    rw [hpart1, hpart2]; ring
  rw [htotal]
  have hrest_even : Even ((∑ t ∈ D.filter (fun t => t.1 ≠ 0), tripleWeight t) +
      (∑ t ∈ T.filter (fun t => t.1 ≠ t.2.2), tripleWeight t)) :=
    hdiag_pos_even.add hoff_even
  have hodd_iff :
      Odd ((∑ t ∈ D.filter (fun t => t.1 = 0), tripleWeight t) +
        ((∑ t ∈ D.filter (fun t => t.1 ≠ 0), tripleWeight t) +
         (∑ t ∈ T.filter (fun t => t.1 ≠ t.2.2), tripleWeight t)))
      ↔ Odd (∑ t ∈ D.filter (fun t => t.1 = 0), tripleWeight t) := by
    simp [Int.odd_add, hrest_even]
  rw [hodd_iff]
  set Z := D.filter (fun t => t.1 = 0)
  by_cases hsq : ∃ b : ℕ, n = b ^ 2
  · obtain ⟨b, hb⟩ := hsq
    have hZ : Z = {(0, b, 0)} := by
      ext ⟨x, y, z⟩
      simp only [Z, D, T, tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨⟨_, _, _⟩, heq⟩, hxz⟩, hx0⟩
        subst hx0
        have hz0 : z = 0 := hxz.symm
        subst hz0
        have hy2 : y ^ 2 = b ^ 2 := by
          have : 2 * y ^ 2 = 2 * b ^ 2 := by
            calc
              2 * y ^ 2 = 0 + 0 + 2 * (y + 0) * (y + 0) := by ring
              _ = 2 * n := heq
              _ = 2 * b ^ 2 := by rw [hb]
          omega
        have hyb : y = b := by nlinarith
        exact ⟨rfl, hyb, rfl⟩
      · rintro ⟨hx0, hyb, hz0⟩
        rw [hx0, hyb, hz0]
        have hble : b ≤ 2 * n := by
          have : b ≤ b ^ 2 := by nlinarith
          omega
        refine ⟨⟨⟨⟨by omega, by omega, by omega⟩, ?_⟩, rfl⟩, rfl⟩
        rw [hb]; ring
    rw [hZ, Finset.sum_singleton]
    have hw : tripleWeight (0, b, 0) = 1 := by simp [tripleWeight]
    rw [hw]
    exact ⟨fun _ => ⟨b, hb⟩, fun _ => odd_one⟩
  · have hZ : Z = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨x, y, z⟩ hmem
      simp only [Z, D, T, tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
      obtain ⟨⟨⟨_, heq⟩, hxz⟩, hx0⟩ := hmem
      subst hx0
      have hz0 : z = 0 := hxz.symm
      subst hz0
      apply hsq
      refine ⟨y, ?_⟩
      have : 2 * y ^ 2 = 2 * n := by
        calc
          2 * y ^ 2 = 0 + 0 + 2 * (y + 0) * (y + 0) := by ring
          _ = 2 * n := heq
      omega
    rw [hZ, Finset.sum_empty]
    exact ⟨fun h0 => absurd h0 (by decide), fun h => absurd h hsq⟩

/-! ### Initial Terms Verification (Matching OEIS A326602) -/

@[category test, AMS 5 11]
theorem a_0 : a 0 = 1 := by
  unfold a; rw [coeff_A_eq_triple_sum]; decide

@[category test, AMS 5 11]
theorem a_1 : a 1 = 3 := by
  unfold a; rw [coeff_A_eq_triple_sum]; decide

@[category test, AMS 5 11]
theorem a_2 : a 2 = 0 := by
  unfold a; rw [coeff_A_eq_triple_sum]; decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 2 := by
  unfold a; rw [coeff_A_eq_triple_sum]; decide

end OeisA326602
