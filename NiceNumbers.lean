/-
  NiceNumbers.lean
  ================

  Four theorems about nice / quasi-nice numbers, formalised in Lean 4.

  `n` is **(e₁,e₂)-nice in base b** when the base-`b` digits of `n^e₁` and `n^e₂`
  together are exactly {0,…,b-1}, each once.  `(2,3)` is the classical "nice
  number" problem, whose only known solution is 69 in base 10.

  Pandigitality has two immediate consequences, and both are formalised here as
  hypotheses so that theorems A, B and D apply to *any* notion of solution
  satisfying them:

    * the digit-length identity   `numDigits b (n^e₁) + numDigits b (n^e₂) = b`
    * the digit-sum identity      `2 * (digitSum b (n^e₁) + digitSum b (n^e₂)) = b * (b-1)`

  Theorem G is about a digit *collision*, which neither consequence sees, so §5
  defines pandigitality outright (`Pandigital`, from a `digits` list built by
  repeated division) and proves it satisfiable at 69.

  **Theorem A** (`no_nice_of_dvd`): if `(e₁+e₂) ∣ e₁*(b-1)` — equivalently
  `b ≡ 1 mod (e₁+e₂)/gcd(e₁,e₂)` — the length identity is unsatisfiable.
  Special cases: `b ≡ 1 mod 5` kills `(2,3)`, `b ≡ 1 mod 4` kills `(1,3)`,
  `b ≡ 1 mod 3` kills `(2,4)`.

  **Theorem B** (`no_nice_of_mod_four`): for *every* pair with `e₁,e₂ ≥ 1`, if
  `b ≡ 3 (mod 4)` the digit-sum identity is unsatisfiable.

  **Proposition D** (`base_unique`, `bands_disjoint`): the length identity holds
  for at most one base, so distinct bases' candidate bands are disjoint and each
  `n` is a candidate in at most one base.  Proved for arbitrary values, hence for
  every exponent pair.

  **Theorem G** (`no_nice_of_universal_clash`, `clash_iff_dvd_clashMod`,
  `clash_prime_pow_iff`): if `x^e₁ ≡ x^e₂ (mod b)` for *every* `x` — a universal
  last-digit clash — then no `n` is pandigital in base `b`.  The bases where that
  happens are **exactly the divisors of one number** `N(e₁,e₂)`, computed here as
  a finite gcd (`N(1,3) = 6`, `N(2,4) = 12`, `N(3,7) = 120`, `N(2,3) = 2`); and
  `p^a ∣ N` iff `a ≤ e₁` and every unit mod `p` has order dividing `e₂-e₁`, which
  is `λ(p^a) ∣ e₂-e₁` once the unit group's exponent is known.  Evaluating that
  exponent is the one step of Theorem G left unformalised.

  Together these replace exhaustive machine checks over `e₁ ≤ 8`, `e₂ ≤ 9`,
  `b < 400` (A, B), `b < 500`, five pairs, ~2700 values of `n` (D), and
  `e₁ ≤ 5`, `e₂ ≤ 7`, `b < 200` (G) with proofs valid for all bases, all
  exponent pairs and all `n`.

  Lean 4.16-4.33, core only.  No Mathlib, no `sorry`.  `#print axioms` at the end
  shows only the three standard foundational axioms.
-/

set_option linter.unusedVariables false

namespace Nice

/-! ## §0  Digits, from first principles

`numDigits` and `digitSum` are defined by the usual repeated division, so they
really are "how many digits does `x` print in base `b`" and "what do they add
up to".  Nothing else about digits is assumed anywhere below. -/

/-- Number of base-`b` digits of `x`; zero has none. -/
def numDigits (b x : Nat) : Nat :=
  if h : 1 < b ∧ 0 < x then numDigits b (x / b) + 1 else 0
decreasing_by exact Nat.div_lt_self h.2 h.1

/-- Sum of the base-`b` digits of `x`. -/
def digitSum (b x : Nat) : Nat :=
  if h : 1 < b ∧ 0 < x then x % b + digitSum b (x / b) else 0
decreasing_by exact Nat.div_lt_self h.2 h.1

theorem numDigits_zero (b : Nat) : numDigits b 0 = 0 := by rw [numDigits]; simp

theorem digitSum_zero (b : Nat) : digitSum b 0 = 0 := by rw [digitSum]; simp

theorem eq_zero_of_numDigits_eq_zero {b x : Nat} (hb : 1 < b)
    (h : numDigits b x = 0) : x = 0 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · exact h0
  · rw [numDigits, dif_pos ⟨hb, h0⟩] at h; omega

theorem numDigits_pos {b x : Nat} (hb : 1 < b) (hx : 0 < x) : 0 < numDigits b x := by
  rw [numDigits, dif_pos ⟨hb, hx⟩]; omega

/-- `numDigits b x = k+1` means exactly `b^k ≤ x < b^(k+1)`. -/
theorem bounds_of_numDigits {b : Nat} (hb : 1 < b) :
    ∀ x k, numDigits b x = k + 1 → b ^ k ≤ x ∧ x < b ^ (k + 1) := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro k hk
    have hx : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | h
      · rw [numDigits_zero] at hk; omega
      · exact h
    rw [numDigits, dif_pos ⟨hb, hx⟩] at hk
    have hkk : numDigits b (x / b) = k := by omega
    have hdm : b * (x / b) + x % b = x := Nat.div_add_mod x b
    have hmod : x % b < b := Nat.mod_lt _ (by omega)
    match k with
    | 0 =>
      have h0 : x / b = 0 := eq_zero_of_numDigits_eq_zero hb hkk
      rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
      refine ⟨by rw [Nat.pow_zero]; omega, ?_⟩
      rw [Nat.pow_one]; omega
    | (j+1) =>
      have hlt : x / b < x := Nat.div_lt_self hx hb
      have hIH := ih (x / b) hlt j hkk
      refine ⟨?_, ?_⟩
      · calc b ^ (j+1) = b ^ j * b := rfl
          _ ≤ (x / b) * b := Nat.mul_le_mul_right b hIH.1
          _ ≤ x := Nat.div_mul_le_self x b
      · calc x < b * (x / b) + b := by omega
          _ = b * (x / b + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ b * b ^ (j+1) := Nat.mul_le_mul_left b (by omega)
          _ = b ^ (j+1+1) := (Nat.mul_comm b (b^(j+1))).trans (Nat.pow_succ b (j+1)).symm

/-- Casting out `b-1`s: the classical digit-sum congruence. -/
theorem digitSum_mod {b : Nat} (hb : 1 < b) : ∀ x, x % (b - 1) = digitSum b x % (b - 1) := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [digitSum_zero]
    · rw [digitSum, dif_pos ⟨hb, hx⟩]
      have hlt : x / b < x := Nat.div_lt_self hx hb
      have hIH : (x / b) % (b - 1) = digitSum b (x / b) % (b - 1) := ih (x / b) hlt
      have hdm : b * (x / b) + x % b = x := Nat.div_add_mod x b
      -- b * q = q + (b-1) * q, so b*q ≡ q  (mod b-1)
      have hsplit : b * (x / b) = (x / b) + (b - 1) * (x / b) := by
        have : b = 1 + (b - 1) := by omega
        calc b * (x / b) = (1 + (b - 1)) * (x / b) := by rw [← this]
          _ = (x / b) + (b - 1) * (x / b) := by rw [Nat.add_mul, Nat.one_mul]
      have key : ((x / b + x % b) + (b - 1) * (x / b)) % (b - 1) = (x / b + x % b) % (b - 1) :=
        Nat.add_mul_mod_self_left _ _ _
      have hxeq : (x / b + x % b) + (b - 1) * (x / b) = x := by omega
      rw [hxeq] at key
      rw [key, Nat.add_mod, hIH, ← Nat.add_mod, Nat.add_comm]

/-! ## §1  Theorem A — the length obstruction -/

/-- Core lacks the strict form of `pow_le_pow_left`. -/
theorem pow_lt_pow_left' {x y : Nat} (h : x < y) : ∀ k, k ≠ 0 → x ^ k < y ^ k := by
  intro k hk
  match k, hk with
  | (k+1), _ =>
    have hy : 0 < y ^ k := Nat.pow_pos (Nat.lt_of_le_of_lt (Nat.zero_le x) h)
    calc x ^ (k+1) = x ^ k * x := rfl
      _ < y ^ k * y := Nat.mul_lt_mul_of_le_of_lt (Nat.pow_le_pow_left (Nat.le_of_lt h) k) h hy
      _ = y ^ (k+1) := rfl

/-- Comparing `b^a ≤ n^e₁` and `n^e₂ < b^(c+1)` through the common value
`n^(e₁e₂)` pins `a·e₂` strictly below `(c+1)·e₁`.  Used both ways round, this
confines `(a,c)` to a window of width exactly `e₁+e₂` — the whole theorem. -/
theorem exp_lt {b e₁ e₂ n a c : Nat} (hb : 1 < b) (he₁ : e₁ ≠ 0)
    (ha : b ^ a ≤ n ^ e₁) (hc' : n ^ e₂ < b ^ (c + 1)) :
    a * e₂ < (c + 1) * e₁ := by
  have h1 : b ^ (a * e₂) ≤ n ^ (e₁ * e₂) := by
    rw [Nat.pow_mul, Nat.pow_mul]; exact Nat.pow_le_pow_left ha e₂
  have h2 : n ^ (e₂ * e₁) < b ^ ((c + 1) * e₁) := by
    rw [Nat.pow_mul, Nat.pow_mul]; exact pow_lt_pow_left' hc' e₁ he₁
  rw [Nat.mul_comm e₁ e₂] at h1
  exact (Nat.pow_lt_pow_iff_right hb).mp (Nat.lt_of_le_of_lt h1 h2)

theorem no_candidate {b e₁ e₂ n a c : Nat}
    (hb : 1 < b) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0)
    (ha : b ^ a ≤ n ^ e₁) (ha' : n ^ e₁ < b ^ (a + 1))
    (hc : b ^ c ≤ n ^ e₂) (hc' : n ^ e₂ < b ^ (c + 1))
    (hlen : (a + 1) + (c + 1) = b)
    (hdvd : (e₁ + e₂) ∣ e₁ * (b - 1)) : False := by
  have h₁ : a * e₂ < (c + 1) * e₁ := exp_lt hb he₁ ha hc'
  have h₂ : c * e₁ < (a + 1) * e₂ := exp_lt hb he₂ hc ha'
  have h₁' : a * e₂ < c * e₁ + e₁ := by rw [Nat.succ_mul] at h₁; exact h₁
  have h₂' : c * e₁ < a * e₂ + e₂ := by rw [Nat.succ_mul] at h₂; exact h₂
  obtain ⟨k, hk⟩ := hdvd
  have hb1 : b - 1 = a + c + 1 := by omega
  rw [hb1] at hk
  have hA : e₁ * (a + c + 1) = a * e₁ + c * e₁ + e₁ := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm e₁ a, Nat.mul_comm e₁ c]
  have hB : (e₁ + e₂) * (a + 1) = a * e₁ + a * e₂ + (e₁ + e₂) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_comm e₁ a, Nat.mul_comm e₂ a]
  have hC : (e₁ + e₂) * (k + 1) = (e₁ + e₂) * k + (e₁ + e₂) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hA] at hk
  have hlt1 : (e₁ + e₂) * k < (e₁ + e₂) * (a + 1) := by omega
  have hlt2 : (e₁ + e₂) * (a + 1) < (e₁ + e₂) * (k + 1) := by omega
  have hk1 : k < a + 1 := Nat.lt_of_mul_lt_mul_left hlt1
  have hk2 : a + 1 < k + 1 := Nat.lt_of_mul_lt_mul_left hlt2
  omega

/--
**Theorem A.**  If `(e₁+e₂) ∣ e₁*(b-1)` then no `n` has
`numDigits b (n^e₁) + numDigits b (n^e₂) = b`, so base `b` contains no
`(e₁,e₂)`-nice number.
-/
theorem no_nice_of_dvd {b e₁ e₂ n : Nat}
    (hb : 1 < b) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0)
    (hdvd : (e₁ + e₂) ∣ e₁ * (b - 1)) :
    numDigits b (n ^ e₁) + numDigits b (n ^ e₂) ≠ b := by
  intro hsum
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_pow (Nat.pos_of_ne_zero he₁), Nat.zero_pow (Nat.pos_of_ne_zero he₂),
        numDigits_zero] at hsum
    omega
  have hp1 : 0 < numDigits b (n ^ e₁) := numDigits_pos hb (Nat.pow_pos hn)
  have hp2 : 0 < numDigits b (n ^ e₂) := numDigits_pos hb (Nat.pow_pos hn)
  obtain ⟨a, hae⟩ : ∃ a, numDigits b (n ^ e₁) = a + 1 := ⟨numDigits b (n ^ e₁) - 1, by omega⟩
  obtain ⟨c, hce⟩ : ∃ c, numDigits b (n ^ e₂) = c + 1 := ⟨numDigits b (n ^ e₂) - 1, by omega⟩
  obtain ⟨ha, ha'⟩ := bounds_of_numDigits hb _ _ hae
  obtain ⟨hc, hc'⟩ := bounds_of_numDigits hb _ _ hce
  exact no_candidate hb he₁ he₂ ha ha' hc hc' (by omega) hdvd

/-! ### Named corollaries -/

/-- Square/cube ("nice") numbers: base `b ≡ 1 (mod 5)` is empty. -/
theorem nice_no_solution {b n : Nat} (hb : 1 < b) (hmod : b % 5 = 1) :
    numDigits b (n ^ 2) + numDigits b (n ^ 3) ≠ b := by
  refine no_nice_of_dvd (e₁ := 2) (e₂ := 3) hb (by decide) (by decide) ?_
  obtain ⟨t, ht⟩ : 5 ∣ (b - 1) := by omega
  exact ⟨2 * t, by omega⟩

/-- The `(1,3)` problem: base `b ≡ 1 (mod 4)` is empty. -/
theorem one_three_no_solution {b n : Nat} (hb : 1 < b) (hmod : b % 4 = 1) :
    numDigits b (n ^ 1) + numDigits b (n ^ 3) ≠ b := by
  refine no_nice_of_dvd (e₁ := 1) (e₂ := 3) hb (by decide) (by decide) ?_
  obtain ⟨t, ht⟩ : 4 ∣ (b - 1) := by omega
  exact ⟨t, by omega⟩

/-- The `(2,4)` problem: base `b ≡ 1 (mod 3)` is empty — a *third* of all bases.
    This is the `gcd(e₁,e₂) > 1` phenomenon, free from the divisibility form. -/
theorem two_four_no_solution {b n : Nat} (hb : 1 < b) (hmod : b % 3 = 1) :
    numDigits b (n ^ 2) + numDigits b (n ^ 4) ≠ b := by
  refine no_nice_of_dvd (e₁ := 2) (e₂ := 4) hb (by decide) (by decide) ?_
  obtain ⟨t, ht⟩ : 3 ∣ (b - 1) := by omega
  exact ⟨t, by omega⟩

/-! ## §2  Theorem B — the parity obstruction, for every exponent pair -/

theorem pow_mod_two {n : Nat} : ∀ e, e ≠ 0 → n ^ e % 2 = n % 2 := by
  intro e he
  induction e with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Nat.pow_one]
    · have hIH := ih (by omega)
      have : n ^ (j + 1) % 2 = (n ^ j % 2) * (n % 2) % 2 := by
        rw [Nat.pow_succ, Nat.mul_mod]
      rw [this, hIH]
      have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h2 with h | h <;> rw [h] <;> decide

/--
**Theorem B.**  For every exponent pair with `e₁, e₂ ≥ 1`, base `b ≡ 3 (mod 4)`
contains no `(e₁,e₂)`-nice number: the digit-sum identity
`2·(digitSum(n^e₁) + digitSum(n^e₂)) = b(b-1)` is already unsatisfiable.
-/
theorem no_nice_of_mod_four {b e₁ e₂ n : Nat}
    (hb : 1 < b) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) (hmod : b % 4 = 3)
    (hT : 2 * (digitSum b (n ^ e₁) + digitSum b (n ^ e₂)) = b * (b - 1)) : False := by
  have h2m : 2 ∣ (b - 1) := by omega
  -- the two powers are congruent to their digit sums mod b-1 ...
  have hd1 : n ^ e₁ % (b-1) = digitSum b (n ^ e₁) % (b-1) := digitSum_mod hb _
  have hd2 : n ^ e₂ % (b-1) = digitSum b (n ^ e₂) % (b-1) := digitSum_mod hb _
  -- ... hence mod 2, since 2 ∣ b-1
  have step : ∀ x y : Nat, x % (b-1) = y % (b-1) → x % 2 = y % 2 := by
    intro x y h
    rw [← Nat.mod_mod_of_dvd x h2m, ← Nat.mod_mod_of_dvd y h2m, h]
  have e1 : n ^ e₁ % 2 = digitSum b (n ^ e₁) % 2 := step _ _ hd1
  have e2 : n ^ e₂ % 2 = digitSum b (n ^ e₂) % 2 := step _ _ hd2
  -- left side: n^e ≡ n (mod 2) for any e ≥ 1, so the sum of the two is even
  rw [pow_mod_two e₁ he₁] at e1
  rw [pow_mod_two e₂ he₂] at e2
  have hsum_even : (digitSum b (n ^ e₁) + digitSum b (n ^ e₂)) % 2 = 0 := by
    have := Nat.add_mod (digitSum b (n ^ e₁)) (digitSum b (n ^ e₂)) 2
    rw [← e1, ← e2] at this
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with h | h <;> rw [h] at this <;> omega
  -- right side: b odd and (b-1)/2 odd force the digit-sum total to be odd
  obtain ⟨S, hS⟩ : ∃ S, digitSum b (n ^ e₁) + digitSum b (n ^ e₂) = 2 * S := by
    exact ⟨(digitSum b (n ^ e₁) + digitSum b (n ^ e₂)) / 2, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, b - 1 = 2 * u := ⟨(b-1)/2, by omega⟩
  have hodd_u : u % 2 = 1 := by omega
  have hodd_b : b % 2 = 1 := by omega
  -- 4S = b*m = b*2*u  ⇒  2S = b*u, which is odd·odd = odd, contradicting 2 ∣ 2S
  have hmul : 2 * (2 * S) = b * (2 * u) := by rw [← hS, ← hu]; exact hT
  have hbu2 : b * (2 * u) = 2 * (b * u) := by
    rw [Nat.mul_comm b (2*u), Nat.mul_assoc, Nat.mul_comm u b]
  have h4 : 2 * S = b * u := by omega
  have hbu : (b * u) % 2 = 1 := by
    rw [Nat.mul_mod, hodd_b, hodd_u]
  omega


/--
**Theorem B, residue-set form.**  The same parity obstruction stated the way the
sieve uses it: for `b ≡ 3 (mod 4)` the residue set
`R_b = {ρ : ρ^e₁ + ρ^e₂ ≡ T (mod b-1)}`, `2T = b(b-1)`, is **empty**.

`no_nice_of_mod_four` rules out an actual solution's digit sums; this rules out
the congruence class it would have to live in, which is the statement
`verify.py`'s gate B used to check over `e₁ ≤ 8`, `e₂ ≤ 9`, `b < 400`.
-/
theorem residues_empty_of_mod_four {b e₁ e₂ T ρ : Nat}
    (hb : 1 < b) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) (hmod : b % 4 = 3)
    (hT : 2 * T = b * (b - 1)) :
    (ρ ^ e₁ + ρ ^ e₂) % (b - 1) ≠ T % (b - 1) := by
  intro h
  have h2m : 2 ∣ (b - 1) := by omega
  have step : ∀ x y : Nat, x % (b-1) = y % (b-1) → x % 2 = y % 2 := by
    intro x y hxy
    rw [← Nat.mod_mod_of_dvd x h2m, ← Nat.mod_mod_of_dvd y h2m, hxy]
  have hpar : (ρ ^ e₁ + ρ ^ e₂) % 2 = T % 2 := step _ _ h
  -- ρ^e ≡ ρ (mod 2) for e ≥ 1, so the left side is ρ + ρ: even
  have hl : (ρ ^ e₁ + ρ ^ e₂) % 2 = 0 := by
    have h1 := pow_mod_two (n := ρ) e₁ he₁
    have h2 := pow_mod_two (n := ρ) e₂ he₂
    have hadd := Nat.add_mod (ρ ^ e₁) (ρ ^ e₂) 2
    rw [h1, h2] at hadd
    have hn : ρ % 2 = 0 ∨ ρ % 2 = 1 := by omega
    rcases hn with hq | hq <;> rw [hq] at hadd <;> omega
  -- b odd and (b-1)/2 odd make T = b·(b-1)/2 odd
  obtain ⟨u, hu⟩ : ∃ u, b - 1 = 2 * u := ⟨(b-1)/2, by omega⟩
  have hodd_u : u % 2 = 1 := by omega
  have hodd_b : b % 2 = 1 := by omega
  have hbu2 : b * (2 * u) = 2 * (b * u) := by
    rw [Nat.mul_comm b (2*u), Nat.mul_assoc, Nat.mul_comm u b]
  rw [hu, hbu2] at hT
  have hTbu : T = b * u := by omega
  have hodd_T : (b * u) % 2 = 1 := by rw [Nat.mul_mod, hodd_b, hodd_u]
  omega

/-- Theorem B's residue form firing: base 7 has no `(2,3)` residue at all
(`T = 21`, `2·21 = 7·6`). -/
theorem base_seven_no_residue (ρ : Nat) : (ρ ^ 2 + ρ ^ 3) % 6 ≠ 21 % 6 :=
  residues_empty_of_mod_four (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! ## §3  Proposition D — one base per `n`, and the bands are disjoint

The candidate band of base `b` is `{n : numDigits b (n^e₁) + numDigits b (n^e₂) = b}`.
Distinct bases have **disjoint** bands, so each `n` is a candidate in at most one
base and "search more bases" and "search more numbers" are the same axis.

The proof needs nothing about exponents at all: `numDigits b x` is *antitone* in
`b`, so `numDigits b x + numDigits b y - b` is strictly decreasing in `b` and can
vanish once.  What is formalised is therefore the general two-value statement,
with the exponent form as a corollary. -/

/-- `b^k ≤ x` forces `x` to have at least `k+1` digits — the converse direction
of `bounds_of_numDigits`, and all that antitonicity needs. -/
theorem le_numDigits_of_pow_le {b x k : Nat} (hb : 1 < b) (h : b ^ k ≤ x) :
    k + 1 ≤ numDigits b x := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.pow_pos (a := b) (n := k) (by omega)) h
  obtain ⟨j, hj⟩ : ∃ j, numDigits b x = j + 1 :=
    ⟨numDigits b x - 1, by have := numDigits_pos hb hx; omega⟩
  obtain ⟨-, g2⟩ := bounds_of_numDigits hb x j hj
  have hpow : b ^ k < b ^ (j + 1) := Nat.lt_of_le_of_lt h g2
  have := (Nat.pow_lt_pow_iff_right hb).mp hpow
  omega

/-- A bigger base never needs more digits. -/
theorem numDigits_antitone {b b' : Nat} (hb : 1 < b) (hbb : b ≤ b') (x : Nat) :
    numDigits b' x ≤ numDigits b x := by
  rcases Nat.eq_zero_or_pos (numDigits b' x) with h | h
  · omega
  obtain ⟨k, hk⟩ : ∃ k, numDigits b' x = k + 1 := ⟨numDigits b' x - 1, by omega⟩
  have hb' : 1 < b' := by omega
  obtain ⟨g1, -⟩ := bounds_of_numDigits hb' x k hk
  have hle : b ^ k ≤ x := Nat.le_trans (Nat.pow_le_pow_left hbb k) g1
  rw [hk]
  exact le_numDigits_of_pow_le hb hle

/--
**Proposition D.**  For any two values `x, y`, at most one base `b` satisfies the
length identity `numDigits b x + numDigits b y = b`.
-/
theorem base_unique {b b' x y : Nat} (hb : 1 < b) (hb' : 1 < b')
    (h : numDigits b x + numDigits b y = b)
    (h' : numDigits b' x + numDigits b' y = b') : b = b' := by
  rcases Nat.lt_trichotomy b b' with hlt | heq | hgt
  · have h1 := numDigits_antitone hb (Nat.le_of_lt hlt) x
    have h2 := numDigits_antitone hb (Nat.le_of_lt hlt) y
    omega
  · exact heq
  · have h1 := numDigits_antitone hb' (Nat.le_of_lt hgt) x
    have h2 := numDigits_antitone hb' (Nat.le_of_lt hgt) y
    omega

/-- `n` lies in the base-`b` candidate band for the pair `(e₁,e₂)`. -/
def InBand (b e₁ e₂ n : Nat) : Prop :=
  numDigits b (n ^ e₁) + numDigits b (n ^ e₂) = b

/-- **Prop D, band form.**  The bands of two distinct bases are disjoint: no `n`
is a candidate in both.  Holds for every exponent pair, `n` included `0`. -/
theorem bands_disjoint {b b' e₁ e₂ n : Nat} (hb : 1 < b) (hb' : 1 < b')
    (hne : b ≠ b') : ¬(InBand b e₁ e₂ n ∧ InBand b' e₁ e₂ n) := by
  rintro ⟨h, h'⟩
  exact hne (base_unique hb hb' h h')

/-! ## §4  Non-vacuity

An impossibility theorem is worthless if its hypotheses are secretly
contradictory.  They are not: **69 in base 10** satisfies both of them, and it
is the only known (2,3)-nice number.  Everything below is kernel-checked. -/

/-- Converse of `bounds_of_numDigits`, so non-vacuity reduces to arithmetic on
numerals that `decide` can do. -/
theorem numDigits_eq_of_bounds {b x k : Nat} (hb : 1 < b)
    (h1 : b ^ k ≤ x) (h2 : x < b ^ (k + 1)) : numDigits b x = k + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.pow_pos (a := b) (n := k) (by omega)) h1
  obtain ⟨j, hj⟩ : ∃ j, numDigits b x = j + 1 :=
    ⟨numDigits b x - 1, by have := numDigits_pos hb hx; omega⟩
  obtain ⟨g1, g2⟩ := bounds_of_numDigits hb x j hj
  have : j = k := by
    rcases Nat.lt_trichotomy j k with h | h | h
    · have : b ^ (j + 1) ≤ b ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact h
    · have : b ^ (k + 1) ≤ b ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  omega

/-- One unfolding of `digitSum`. -/
theorem digitSum_step {b x : Nat} (hb : 1 < b) (hx : 0 < x) :
    digitSum b x = x % b + digitSum b (x / b) := by
  rw [digitSum, dif_pos ⟨hb, hx⟩]

/-- 69² = 4761 has 4 base-10 digits. -/
theorem nd_sq : numDigits 10 (69 ^ 2) = 4 := numDigits_eq_of_bounds (by decide) (by decide) (by decide)

/-- 69³ = 328509 has 6 base-10 digits. -/
theorem nd_cb : numDigits 10 (69 ^ 3) = 6 := numDigits_eq_of_bounds (by decide) (by decide) (by decide)

/-- The length identity really is satisfiable: 4 + 6 = 10. -/
theorem length_identity_holds : numDigits 10 (69 ^ 2) + numDigits 10 (69 ^ 3) = 10 := by
  rw [nd_sq, nd_cb]

theorem ds_sq : digitSum 10 (69 ^ 2) = 18 := by
  show digitSum 10 4761 = 18
  rw [digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_zero]

theorem ds_cb : digitSum 10 (69 ^ 3) = 27 := by
  show digitSum 10 328509 = 27
  rw [digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_step (by decide) (by decide), digitSum_step (by decide) (by decide),
      digitSum_zero]

/-- The digit-sum identity really is satisfiable: 18 + 27 = 45 = 10·9/2. -/
theorem digitsum_identity_holds :
    2 * (digitSum 10 (69 ^ 2) + digitSum 10 (69 ^ 3)) = 10 * (10 - 1) := by
  rw [ds_sq, ds_cb]

/-- Theorem A firing: base 11 ≡ 1 (mod 5) admits no square/cube candidate. -/
theorem base_eleven_dead (n : Nat) : numDigits 11 (n ^ 2) + numDigits 11 (n ^ 3) ≠ 11 :=
  nice_no_solution (by decide) (by decide)

/-- Theorem B firing where Theorem A says nothing: 7 ≢ 1 (mod 5), but 7 ≡ 3
(mod 4), so the digit-sum identity is already impossible in base 7. -/
theorem base_seven_dead (n : Nat) :
    2 * (digitSum 7 (n ^ 2) + digitSum 7 (n ^ 3)) ≠ 7 * (7 - 1) :=
  fun h => no_nice_of_mod_four (by decide) (by decide) (by decide) (by decide) h

/-- Prop D needs a witness too, or "at most one base" could mean "no base": 69 is
in the base-10 `(2,3)` band. -/
theorem sixtynine_in_band : InBand 10 2 3 69 := length_identity_holds

/-- Prop D firing on that witness: base 10 is the *only* base 69 is a candidate
in — no finite search, and no appeal to the exponents being `(2,3)`. -/
theorem sixtynine_only_base_ten {b : Nat} (hb : 1 < b) (h : InBand b 2 3 69) : b = 10 :=
  base_unique hb (by decide) h sixtynine_in_band

/-- Theorem B is genuinely pair-independent: same base, exponents (3,8). -/
theorem base_seven_dead' (n : Nat) :
    2 * (digitSum 7 (n ^ 3) + digitSum 7 (n ^ 8)) ≠ 7 * (7 - 1) :=
  fun h => no_nice_of_mod_four (by decide) (by decide) (by decide) (by decide) h

/-! ## §5  Theorem G — the universal last-digit clash

If `x^e₁ ≡ x^e₂ (mod b)` for *every* `x` then the last base-`b` digits of `n^e₁`
and `n^e₂` coincide for every `n`, one digit value is used twice, and base `b` is
dead for reasons that have nothing to do with the size of the band.  Theorem G
classifies the bases where that happens.

Two halves, and only the first needs pandigitality:

* `no_nice_of_universal_clash` — a clashing base contains no pandigital `n`.
* `clash_iff_dvd_clashMod` — the clashing bases for a pair are **exactly the
  divisors of one number** `N(e₁,e₂)`, computed here as a finite gcd.
* `clash_prime_pow_iff` — and the prime powers dividing `N` are exactly those
  with `a ≤ e₁` whose unit group has exponent dividing `e₂-e₁`.  Evaluating that
  exponent is the classical `λ(p^a)`, the one step left to Mathlib.

This is also the first section that needs pandigitality itself rather than one of
its consequences, so §5.0 defines it. -/

/-! ### §5.0  Pandigitality, from the digits up -/

/-- The base-`b` digits of `x`, least significant first. -/
def digits (b x : Nat) : List Nat :=
  if h : 1 < b ∧ 0 < x then x % b :: digits b (x / b) else []
decreasing_by exact Nat.div_lt_self h.2 h.1

theorem digits_zero (b : Nat) : digits b 0 = [] := by rw [digits]; simp

theorem digits_step {b x : Nat} (hb : 1 < b) (hx : 0 < x) :
    digits b x = x % b :: digits b (x / b) := by rw [digits, dif_pos ⟨hb, hx⟩]

/-- Occurrences of `v` in `l`.  Core's `List.count` would do; this keeps the
section self-contained and reduces in the kernel. -/
def occ (v : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => (if a = v then 1 else 0) + occ v l

theorem occ_cons_self (v : Nat) (l : List Nat) : occ v (v :: l) = 1 + occ v l := by
  show (if v = v then 1 else 0) + occ v l = 1 + occ v l
  rw [if_pos rfl]

theorem occ_append (v : Nat) : ∀ l₁ l₂ : List Nat,
    occ v (l₁ ++ l₂) = occ v l₁ + occ v l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; show occ v l₂ = 0 + occ v l₂; omega
  | cons a t ih =>
    intro l₂
    show (if a = v then 1 else 0) + occ v (t ++ l₂)
        = ((if a = v then 1 else 0) + occ v t) + occ v l₂
    rw [ih]
    omega

/-- `n` is **`(e₁,e₂)`-pandigital in base `b`**: the base-`b` digits of `n^e₁`
and of `n^e₂`, taken together, contain every value `< b` exactly once.  This is
the definition the rest of the repo searches for; §1-§3 above use only its two
numerical consequences. -/
def Pandigital (b e₁ e₂ n : Nat) : Prop :=
  ∀ v, v < b → occ v (digits b (n ^ e₁) ++ digits b (n ^ e₂)) = 1

/-! ### §5.1  A universal clash kills the base -/

/-- Base `b` has a **universal clash** for `(e₁,e₂)` when the last digits of
`x^e₁` and `x^e₂` agree for every `x`. -/
def UniversalClash (b e₁ e₂ : Nat) : Prop := ∀ x, x ^ e₁ % b = x ^ e₂ % b

/-- A pandigital `n` is positive: `0` supplies no digit `0` in any base. -/
theorem pos_of_pandigital {b e₁ e₂ n : Nat} (hb : 1 < b)
    (hp : Pandigital b e₁ e₂ n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exfalso
    have key : ∀ e : Nat, occ 0 (digits b ((0 : Nat) ^ e)) = 0 := by
      intro e
      rcases Nat.eq_zero_or_pos e with rfl | he
      · rw [Nat.pow_zero, digits_step hb Nat.one_pos, Nat.mod_eq_of_lt hb,
            Nat.div_eq_of_lt hb, digits_zero]
        decide
      · rw [Nat.zero_pow he, digits_zero]
        rfl
    have h0 := hp 0 (by omega)
    rw [occ_append, key, key] at h0
    omega
  · exact h

/--
**Theorem G, the operative half.**  A base with a universal clash contains no
pandigital `n` at all — the last digits of `n^e₁` and `n^e₂` are the same value,
so that value is used twice.  Every exponent pair, every `n`, no search.
-/
theorem no_nice_of_universal_clash {b e₁ e₂ n : Nat} (hb : 1 < b)
    (hclash : UniversalClash b e₁ e₂) : ¬ Pandigital b e₁ e₂ n := by
  intro hp
  have hn : 0 < n := pos_of_pandigital hb hp
  have h1 : digits b (n ^ e₁) = n ^ e₁ % b :: digits b (n ^ e₁ / b) :=
    digits_step hb (Nat.pow_pos hn)
  have h2 : digits b (n ^ e₂) = n ^ e₂ % b :: digits b (n ^ e₂ / b) :=
    digits_step hb (Nat.pow_pos hn)
  have hcount := hp (n ^ e₁ % b) (Nat.mod_lt _ (by omega))
  rw [occ_append, h1, h2, ← hclash n, occ_cons_self, occ_cons_self] at hcount
  omega

/-! ### §5.2  The classification: the clashing bases are the divisors of one number -/

/-- `gcd_{x < m} (x^e₂ - x^e₁)`. -/
def clashGcd (e₁ e₂ : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => Nat.gcd (m ^ e₂ - m ^ e₁) (clashGcd e₁ e₂ m)

theorem clashGcd_succ (e₁ e₂ m : Nat) :
    clashGcd e₁ e₂ (m + 1) = Nat.gcd (m ^ e₂ - m ^ e₁) (clashGcd e₁ e₂ m) := rfl

/-- `N(e₁,e₂)` — the modulus of Theorem G.  The range stops at `2^e₂ - 2^e₁`
because the `x = 2` term already bounds every clashing base by it. -/
def clashMod (e₁ e₂ : Nat) : Nat := clashGcd e₁ e₂ (2 ^ e₂ - 2 ^ e₁ + 1)

/-- `x^e₁ ≤ x^e₂` for `1 ≤ e₁ ≤ e₂`, `x = 0` included. -/
theorem pow_le_pow_exp {x e₁ e₂ : Nat} (he₁ : 1 ≤ e₁) (he : e₁ ≤ e₂) :
    x ^ e₁ ≤ x ^ e₂ := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have h1 : (0 : Nat) ^ e₁ = 0 := Nat.zero_pow (by omega)
    have h2 : (0 : Nat) ^ e₂ = 0 := Nat.zero_pow (by omega)
    omega
  · exact Nat.pow_le_pow_right hx he

/-- Congruence as divisibility of the (truncated) difference. -/
theorem dvd_sub_iff_mod_eq {b x y : Nat} (hb : 0 < b) (hyx : y ≤ x) :
    b ∣ x - y ↔ x % b = y % b := by
  constructor
  · rintro ⟨k, hk⟩
    have hx : x = y + b * k := by omega
    rw [hx, Nat.add_mul_mod_self_left]
  · intro h
    have hdx : b * (x / b) + x % b = x := Nat.div_add_mod x b
    have hdy : b * (y / b) + y % b = y := Nat.div_add_mod y b
    have hq : y / b ≤ x / b := Nat.div_le_div_right hyx
    obtain ⟨t, ht⟩ : ∃ t, x / b = y / b + t := ⟨x / b - y / b, by omega⟩
    have hmul : b * (y / b + t) = b * (y / b) + b * t := Nat.mul_add b _ _
    rw [ht] at hdx
    exact ⟨t, by omega⟩

theorem clash_iff_dvd_sub {b e₁ e₂ : Nat} (hb : 0 < b) (he₁ : 1 ≤ e₁) (he : e₁ ≤ e₂) :
    UniversalClash b e₁ e₂ ↔ ∀ x, b ∣ x ^ e₂ - x ^ e₁ := by
  constructor
  · intro h x
    exact (dvd_sub_iff_mod_eq hb (pow_le_pow_exp he₁ he)).mpr (h x).symm
  · intro h x
    exact ((dvd_sub_iff_mod_eq hb (pow_le_pow_exp he₁ he)).mp (h x)).symm

theorem dvd_clashGcd_iff {b e₁ e₂ : Nat} :
    ∀ m, b ∣ clashGcd e₁ e₂ m ↔ ∀ x, x < m → b ∣ x ^ e₂ - x ^ e₁ := by
  intro m
  induction m with
  | zero =>
    exact ⟨fun _ x hx => absurd hx (Nat.not_lt_zero x), fun _ => Nat.dvd_zero b⟩
  | succ m ih =>
    rw [clashGcd_succ]
    constructor
    · intro h x hx
      rcases Nat.lt_or_ge x m with hlt | hge
      · exact (ih.mp (Nat.dvd_trans h (Nat.gcd_dvd_right _ _))) x hlt
      · have hxm : x = m := by omega
        subst hxm
        exact Nat.dvd_trans h (Nat.gcd_dvd_left _ _)
    · intro h
      exact Nat.dvd_gcd (h m (by omega)) (ih.mpr (fun x hx => h x (by omega)))

/--
**Theorem G (classification).**  For `1 ≤ e₁ < e₂` and any `b > 0`, base `b` has
a universal clash **iff** `b ∣ N(e₁,e₂)`.  So the clashing bases of a pair are
exactly the divisors of a single computable number — divisor-closed, closed under
lcm, and bounded, all at once.
-/
theorem clash_iff_dvd_clashMod {b e₁ e₂ : Nat} (hb : 0 < b) (he₁ : 1 ≤ e₁) (he : e₁ < e₂) :
    UniversalClash b e₁ e₂ ↔ b ∣ clashMod e₁ e₂ := by
  -- the x = 2 term is at least 2, so it is inside the range and bounds b
  have hp1 : 2 ^ (e₁ + 1) ≤ 2 ^ e₂ := Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : 2 ^ 1 ≤ 2 ^ e₁ := Nat.pow_le_pow_right (by omega) he₁
  have hp3 : 2 ^ (e₁ + 1) = 2 ^ e₁ * 2 := Nat.pow_succ 2 e₁
  have hp4 : (2 : Nat) ^ 1 = 2 := Nat.pow_one 2
  have hK : 2 ≤ 2 ^ e₂ - 2 ^ e₁ := by omega
  constructor
  · intro h
    exact (dvd_clashGcd_iff _).mpr
      (fun x _ => (clash_iff_dvd_sub hb he₁ (Nat.le_of_lt he)).mp h x)
  · intro h x
    have hall := (dvd_clashGcd_iff _).mp h
    have hble : b ≤ 2 ^ e₂ - 2 ^ e₁ := Nat.le_of_dvd (by omega) (hall 2 (by omega))
    have hmod := (dvd_sub_iff_mod_eq hb (pow_le_pow_exp he₁ (Nat.le_of_lt he))).mp
      (hall (x % b) (by have := Nat.mod_lt x hb; omega))
    rw [Nat.pow_mod x e₁ b, Nat.pow_mod x e₂ b]
    exact hmod.symm

/-- Divisor-closure, the half of the structure that is obvious. -/
theorem clash_of_dvd {b b' e₁ e₂ : Nat} (hbb : b ∣ b') (h : UniversalClash b' e₁ e₂) :
    UniversalClash b e₁ e₂ := by
  intro x
  have h1 : x ^ e₁ % b' % b = x ^ e₂ % b' % b := by rw [h x]
  rwa [Nat.mod_mod_of_dvd _ hbb, Nat.mod_mod_of_dvd _ hbb] at h1

/-- Closure under lcm, which is what makes "divisors of one number" possible. -/
theorem clash_lcm {b b' e₁ e₂ : Nat} (hb : 0 < b) (hb' : 0 < b') (he₁ : 1 ≤ e₁) (he : e₁ < e₂)
    (h : UniversalClash b e₁ e₂) (h' : UniversalClash b' e₁ e₂) :
    UniversalClash (Nat.lcm b b') e₁ e₂ := by
  have hd := (clash_iff_dvd_clashMod hb he₁ he).mp h
  have hd' := (clash_iff_dvd_clashMod hb' he₁ he).mp h'
  exact (clash_iff_dvd_clashMod (Nat.lcm_pos hb hb') he₁ he).mpr (Nat.lcm_dvd hd hd')

/-! ### §5.3  Which prime powers divide `N`

The local criterion, stated without Carmichael's `λ`: the unit condition is
"every unit has order dividing `e₂-e₁`", which is what `λ(p^a) ∣ e₂-e₁` says
once the unit group's exponent is known.  That evaluation is the classical
structure theorem for `(ℤ/p^aℤ)ˣ` and is the only part of Theorem G left
unformalised. -/

/-- Core has no `Nat.Prime`, and only one consequence of primality is used. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ k, k ∣ p → k = 1 ∨ k = p

theorem coprime_of_not_dvd {p u : Nat} (hp : IsPrime p) (h : ¬ p ∣ u) :
    Nat.Coprime p u := by
  rcases hp.2 (Nat.gcd p u) (Nat.gcd_dvd_left p u) with h1 | h1
  · exact h1
  · exact absurd (by rw [← h1]; exact Nat.gcd_dvd_right p u) h

/-- Primality of a numeral: a divisor of `p` is at most `p`, so the unbounded
quantifier in `IsPrime` becomes a bounded one that `decide` can do. -/
theorem isPrime_of_bounded {p : Nat} (hp : 2 ≤ p)
    (h : ∀ k, k < p + 1 → k ∣ p → k = 1 ∨ k = p) : IsPrime p :=
  ⟨hp, fun k hk => h k (by have := Nat.le_of_dvd (show 0 < p by omega) hk; omega) hk⟩

theorem isPrime_two : IsPrime 2 := isPrime_of_bounded (by decide) (by decide)

theorem isPrime_three : IsPrime 3 := isPrime_of_bounded (by decide) (by decide)

theorem pow_dvd_pow_of_dvd {a b : Nat} (h : a ∣ b) (n : Nat) : a ^ n ∣ b ^ n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k ^ n, Nat.mul_pow a k n⟩

/--
**Theorem G (local criterion).**  For a prime power `p^a` with `a ≥ 1` and
`1 ≤ e₁ < e₂`, the universal clash holds mod `p^a` **iff** `a ≤ e₁` and every
unit mod `p` satisfies `u^(e₂-e₁) ≡ 1 (mod p^a)`.

The `x = p` half of the proof forces `a ≤ e₁`; the unit half forces the exponent
condition; and the two together suffice, by the dichotomy `p ∣ x` or not.
-/
theorem clash_prime_pow_iff {p a e₁ e₂ : Nat} (hp : IsPrime p) (ha : 1 ≤ a)
    (he₁ : 1 ≤ e₁) (he : e₁ < e₂) :
    UniversalClash (p ^ a) e₁ e₂ ↔
      (a ≤ e₁ ∧ ∀ u, ¬ p ∣ u → u ^ (e₂ - e₁) % p ^ a = 1) := by
  have hp2 : 2 ≤ p := hp.1
  have hm1 : p ^ 1 ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
  have hm : 1 < p ^ a := by rw [Nat.pow_one] at hm1; omega
  have hmpos : 0 < p ^ a := by omega
  have hfac : ∀ x : Nat, x ^ e₁ * (x ^ (e₂ - e₁) - 1) = x ^ e₂ - x ^ e₁ := by
    intro x
    have hsum : e₁ + (e₂ - e₁) = e₂ := by omega
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, hsum]
  constructor
  · intro hcl
    have hdvd : ∀ x, p ^ a ∣ x ^ e₂ - x ^ e₁ :=
      (clash_iff_dvd_sub hmpos he₁ (Nat.le_of_lt he)).mp hcl
    refine ⟨?_, ?_⟩
    · -- x = p: p^a ∣ p^e₁·(p^(e₂-e₁) - 1) and the second factor is prime to p
      rcases Nat.lt_or_ge e₁ a with hlt | hge
      case inr => exact hge
      exfalso
      have h1 : p ^ (e₁ + 1) ∣ p ^ a := Nat.pow_dvd_pow p (by omega)
      have h2 : p ^ a ∣ p ^ e₁ * (p ^ (e₂ - e₁) - 1) := by rw [hfac]; exact hdvd p
      have h3 : p ^ e₁ * p ∣ p ^ e₁ * (p ^ (e₂ - e₁) - 1) := by
        rw [← Nat.pow_succ p e₁]
        exact Nat.dvd_trans h1 h2
      have h4 : p ∣ p ^ (e₂ - e₁) - 1 :=
        (Nat.mul_dvd_mul_iff_left (Nat.pow_pos (show 0 < p by omega))).mp h3
      have h5 : p ∣ p ^ (e₂ - e₁) := by
        have := Nat.pow_dvd_pow p (show 1 ≤ e₂ - e₁ by omega)
        rwa [Nat.pow_one] at this
      have h6 : p ∣ p ^ (e₂ - e₁) - (p ^ (e₂ - e₁) - 1) := Nat.dvd_sub h5 h4
      have h7 : 1 ≤ p ^ (e₂ - e₁) := Nat.pow_pos (show 0 < p by omega)
      have h8 : p ^ (e₂ - e₁) - (p ^ (e₂ - e₁) - 1) = 1 := by omega
      rw [h8] at h6
      have := Nat.le_of_dvd Nat.one_pos h6
      omega
    · -- x = u a unit: cancel u^e₁, which is prime to p
      intro u hu
      have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with rfl | h
        · exact absurd (Nat.dvd_zero p) hu
        · exact h
      have hco : Nat.Coprime (p ^ a) (u ^ e₁) :=
        Nat.Coprime.pow a e₁ (coprime_of_not_dvd hp hu)
      have h2 : p ^ a ∣ u ^ e₁ * (u ^ (e₂ - e₁) - 1) := by rw [hfac]; exact hdvd u
      have h3 : p ^ a ∣ u ^ (e₂ - e₁) - 1 := hco.dvd_of_dvd_mul_left h2
      have h5 := (dvd_sub_iff_mod_eq hmpos (Nat.pow_pos hu0)).mp h3
      rwa [Nat.mod_eq_of_lt hm] at h5
  · rintro ⟨hae, hunit⟩ x
    by_cases hpx : p ∣ x
    · -- p ∣ x: both powers are ≡ 0, since a ≤ e₁ ≤ e₂
      have h1 : p ^ a ∣ x ^ e₁ :=
        Nat.dvd_trans (Nat.pow_dvd_pow p hae) (pow_dvd_pow_of_dvd hpx e₁)
      have h2 : p ^ a ∣ x ^ e₂ :=
        Nat.dvd_trans (Nat.pow_dvd_pow p (by omega)) (pow_dvd_pow_of_dvd hpx e₂)
      rw [Nat.dvd_iff_mod_eq_zero.mp h1, Nat.dvd_iff_mod_eq_zero.mp h2]
    · -- x a unit: multiply the congruence u^(e₂-e₁) ≡ 1 by x^e₁
      have hd : x ^ (e₂ - e₁) % p ^ a = 1 := hunit x hpx
      have hsplit : x ^ e₂ = x ^ e₁ * x ^ (e₂ - e₁) := by
        rw [← Nat.pow_add]
        have : e₁ + (e₂ - e₁) = e₂ := by omega
        rw [this]
      rw [hsplit, Nat.mul_mod, hd, Nat.mul_one, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]

/-- The valuation form of Theorem G: `p^a ∣ N(e₁,e₂)` exactly when `a ≤ e₁` and
every unit mod `p` has order dividing `e₂-e₁`.  Feed in `λ(p^a)` — the exponent
of `(ℤ/p^aℤ)ˣ` — and this is the report's closed form
`N = ∏_p p^{a_p}`, `a_p = max{a ≤ e₁ : λ(p^a) ∣ e₂-e₁}`. -/
theorem prime_pow_dvd_clashMod_iff {p a e₁ e₂ : Nat} (hp : IsPrime p) (ha : 1 ≤ a)
    (he₁ : 1 ≤ e₁) (he : e₁ < e₂) :
    p ^ a ∣ clashMod e₁ e₂ ↔ (a ≤ e₁ ∧ ∀ u, ¬ p ∣ u → u ^ (e₂ - e₁) % p ^ a = 1) := by
  have hppos : 0 < p := by have := hp.1; omega
  exact (clash_iff_dvd_clashMod (Nat.pow_pos hppos) he₁ he).symm.trans
    (clash_prime_pow_iff hp ha he₁ he)

/-! ### §5.4  `N(e₁,e₂)`, computed, and the theorem firing

The values agree with `verify.py`'s Carmichael product `∏ p^{a_p}`, which is the
form Theorem G is stated in.  These are kernel computations, not `native_decide`. -/

theorem clashMod_one_two : clashMod 1 2 = 2 := by decide
theorem clashMod_two_three : clashMod 2 3 = 2 := by decide
theorem clashMod_one_four : clashMod 1 4 = 2 := by decide
theorem clashMod_one_three : clashMod 1 3 = 6 := by decide
theorem clashMod_two_four : clashMod 2 4 = 12 := by decide
theorem clashMod_one_five : clashMod 1 5 = 30 := by decide
theorem clashMod_one_seven : clashMod 1 7 = 42 := by decide
theorem clashMod_two_six : clashMod 2 6 = 60 := by decide
theorem clashMod_three_seven : clashMod 3 7 = 120 := by decide

/-- Every divisor of `N(e₁,e₂)` is a dead base, for every `n`. -/
theorem no_pandigital_of_dvd_clashMod {b e₁ e₂ n : Nat} (hb : 1 < b) (he₁ : 1 ≤ e₁)
    (he : e₁ < e₂) (hdvd : b ∣ clashMod e₁ e₂) : ¬ Pandigital b e₁ e₂ n :=
  no_nice_of_universal_clash hb ((clash_iff_dvd_clashMod (by omega) he₁ he).mpr hdvd)

/-- Theorem G firing where A and B both say nothing: `6 % 4 = 2` so Theorem A
misses it and `6` is even so Theorem B misses it, but `x ≡ x³ (mod 6)` for every
`x` because `6 ∣ N(1,3) = 6`.  So base 6 has no `(1,3)` pandigital number. -/
theorem one_three_base_six_dead (n : Nat) : ¬ Pandigital 6 1 3 n :=
  no_pandigital_of_dvd_clashMod (by decide) (by decide) (by decide) (by decide)

/-- The same at `(2,4)`, base 12: `12 ≡ 0 (mod 3)` so Theorem A misses it too,
and `12 ∣ N(2,4) = 12`. -/
theorem two_four_base_twelve_dead (n : Nat) : ¬ Pandigital 12 2 4 n :=
  no_pandigital_of_dvd_clashMod (by decide) (by decide) (by decide) (by decide)

/-! ### §5.5  Non-vacuity

Two directions matter here.  `Pandigital` must be satisfiable, or §5.1 proves
nothing; and Theorem G must **not** kill base 10 at `(2,3)`, or it would
contradict 69. -/

theorem digits_69sq : digits 10 (69 ^ 2) = [1, 6, 7, 4] := by
  show digits 10 4761 = [1, 6, 7, 4]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_zero]

theorem digits_69cb : digits 10 (69 ^ 3) = [9, 0, 5, 8, 2, 3] := by
  show digits 10 328509 = [9, 0, 5, 8, 2, 3]
  rw [digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_step (by decide) (by decide), digits_step (by decide) (by decide),
      digits_zero]

/-- 69 in base 10 really is `(2,3)`-pandigital: `69² = 4761`, `69³ = 328509`,
and the ten digits are `{0,…,9}` once each. -/
theorem sixtynine_pandigital : Pandigital 10 2 3 69 := by
  have h : ∀ v, v < 10 → occ v ([1, 6, 7, 4] ++ [9, 0, 5, 8, 2, 3]) = 1 := by decide
  intro v hv
  rw [digits_69sq, digits_69cb]
  exact h v hv

/-- Theorem G does not kill base 10 at `(2,3)` — it had better not.
`N(2,3) = 2` and `10 ∤ 2`. -/
theorem base_ten_no_clash : ¬ UniversalClash 10 2 3 := by
  intro h
  have hd := (clash_iff_dvd_clashMod (by decide) (by decide) (by decide)).mp h
  rw [clashMod_two_three] at hd
  have := Nat.le_of_dvd (by decide) hd
  omega

/-- The local criterion running forwards: `3 = 3¹` clashes for `(1,3)` because
`1 ≤ e₁` and every unit mod 3 squares to 1. -/
theorem clash_three_one_three : UniversalClash 3 1 3 := by
  refine (clash_prime_pow_iff (p := 3) (a := 1) isPrime_three (by decide) (by decide)
    (by decide)).mpr ⟨by decide, ?_⟩
  intro u hu
  have h0 : u % 3 ≠ 0 := fun h => hu (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hlt : u % 3 < 3 := Nat.mod_lt u (by decide)
  have hpm := Nat.pow_mod u 2 3
  have h3 : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases h3 with h | h <;> rw [h] at hpm <;> omega

/-- And backwards: base 9 does *not* clash for `(1,3)`, because `a = 2` exceeds
`e₁ = 1`.  No unit-group computation is needed to see it. -/
theorem nine_no_clash_one_three : ¬ UniversalClash 9 1 3 := by
  intro h
  have hc := (clash_prime_pow_iff (p := 3) (a := 2) isPrime_three (by decide) (by decide)
    (by decide)).mp h
  omega
end Nice

#print axioms Nice.no_nice_of_dvd
#print axioms Nice.nice_no_solution
#print axioms Nice.one_three_no_solution
#print axioms Nice.two_four_no_solution
#print axioms Nice.no_nice_of_mod_four
#print axioms Nice.residues_empty_of_mod_four
#print axioms Nice.base_seven_no_residue
#print axioms Nice.length_identity_holds
#print axioms Nice.digitsum_identity_holds
#print axioms Nice.base_eleven_dead
#print axioms Nice.base_seven_dead
#print axioms Nice.base_unique
#print axioms Nice.bands_disjoint
#print axioms Nice.sixtynine_only_base_ten
#print axioms Nice.no_nice_of_universal_clash
#print axioms Nice.clash_iff_dvd_clashMod
#print axioms Nice.clash_prime_pow_iff
#print axioms Nice.prime_pow_dvd_clashMod_iff
#print axioms Nice.clashMod_three_seven
#print axioms Nice.one_three_base_six_dead
#print axioms Nice.sixtynine_pandigital
#print axioms Nice.base_ten_no_clash
